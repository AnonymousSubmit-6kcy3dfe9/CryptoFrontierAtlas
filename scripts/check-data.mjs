import fs from 'node:fs';
import crypto from 'node:crypto';
import { execFileSync } from 'node:child_process';
import path from 'node:path';
import Ajv2020 from 'ajv/dist/2020.js';
import addFormats from 'ajv-formats';

const root = path.resolve('data/problems');
const repositoryRoot = path.resolve('.');
const githubBase = 'https://github.com/AnonymousSubmit-6kcy3dfe9/CryptoFrontierAtlas';
const files = fs.readdirSync(root).filter((file) => file.endsWith('.json')).sort();
const taxonomy = JSON.parse(fs.readFileSync('data/taxonomy.json', 'utf8'));
const manifest = JSON.parse(fs.readFileSync('data/manifest.json', 'utf8'));
const problemSchema = JSON.parse(fs.readFileSync('data/schema/problem.schema.json', 'utf8'));
const ajv = new Ajv2020({ allErrors: true, strict: true, strictRequired: false });
addFormats(ajv);
const validateProblem = ajv.compile(problemSchema);
const taxonomyIds = new Set(taxonomy.domains.flatMap((domain) => domain.children.map((child) => child.id)));
const areaIds = new Set(taxonomy.areas.map((area) => area.id));
const ids = new Set();
const records = [];
const forbidden = ['/data_600G/', 'solved_open_questions', 'LeanCipher', 'private_solution'];
let cachedLocalLeanSourceFiles;
const cachedCommittedLeanSourceFiles = new Map();

const progressCitationRoles = {
  source_statement: new Set(['original_source']),
  restatement: new Set(['restatement']),
  prior_result: new Set(['prior_progress']),
  public_result: new Set(['prior_progress', 'resolution']),
  independent_result: new Set(['independent_resolution']),
};
const historicalSourceCue = /\b(?:restates?|recalls?|previously posed|long-standing open problem|posed by|conjectured by|repeats?\s+(?:a|the|this|an existing)\s+(?:problem|question|conjecture))\b/i;

function validateLineage(record, file) {
  const source = record.source;
  const citations = source.citations;
  const citationByLabel = new Map();
  for (const [index, citation] of citations.entries()) {
    if (typeof citation.label !== 'string' || citation.label.trim().length === 0) {
      throw new Error(`${file} source.citations[${index}] label must be non-empty`);
    }
    if (citationByLabel.has(citation.label)) {
      throw new Error(`${file} citation label is duplicated: ${citation.label}`);
    }
    citationByLabel.set(citation.label, citation);
  }

  const provenance = source.provenance;
  const originStatus = provenance?.origin_status ?? 'confirmed';
  if (provenance) {
    if (!['confirmed', 'unresolved'].includes(provenance.origin_status)) {
      throw new Error(`${file} source.provenance.origin_status is invalid`);
    }
    if (!['explicit_cited_antecedent', 'undetermined'].includes(provenance.method)) {
      throw new Error(`${file} source.provenance.method is invalid`);
    }
    const expectedMethod = originStatus === 'confirmed'
      ? 'explicit_cited_antecedent'
      : 'undetermined';
    if (provenance.method !== expectedMethod) {
      throw new Error(`${file} ${originStatus} provenance must use ${expectedMethod}`);
    }
  }

  const roles = citations.map((citation) => citation.role);
  const lineageAware = Boolean(provenance)
    || roles.includes('restatement')
    || record.progress.some((event) => event.kind === 'restatement');
  if (lineageAware && !provenance) {
    throw new Error(`${file} records with restatement lineage must declare source.provenance`);
  }
  if (originStatus === 'confirmed') {
    if (roles.filter((role) => role === 'original_source').length !== 1) {
      throw new Error(`${file} confirmed provenance requires exactly one original_source citation`);
    }
    if (citations[0]?.role !== 'original_source') {
      throw new Error(`${file} confirmed provenance requires original_source as the first citation`);
    }
  } else {
    if (roles.includes('original_source')) {
      throw new Error(`${file} unresolved provenance must not claim an original_source citation`);
    }
    if (!roles.includes('restatement')) {
      throw new Error(`${file} unresolved provenance requires a restatement citation`);
    }
    if (citations[0]?.role !== 'restatement') {
      throw new Error(`${file} unresolved provenance requires restatement as the first citation`);
    }
  }

  let previousDate = '';
  for (const [index, event] of record.progress.entries()) {
    if (event.date < previousDate) {
      throw new Error(`${file} progress timeline is not in non-decreasing date order at index ${index}`);
    }
    previousDate = event.date;
    const labels = event.citation_labels;
    const eventRoles = new Set();
    for (const label of labels) {
      const citation = citationByLabel.get(label);
      if (!citation) {
        throw new Error(`${file} progress[${index}] references unknown citation label ${label}`);
      }
      eventRoles.add(citation.role);
    }
    const expectedRoles = lineageAware ? progressCitationRoles[event.kind] : undefined;
    if (expectedRoles) {
      if (![...eventRoles].some((role) => expectedRoles.has(role))) {
        throw new Error(`${file} progress[${index}] ${event.kind} must cite ${[...expectedRoles].join(' or ')}`);
      }
      if ([...eventRoles].some((role) => !expectedRoles.has(role))) {
        throw new Error(`${file} progress[${index}] ${event.kind} cites an inconsistent evidence role`);
      }
    }
    if (event.kind === 'source_statement' && historicalSourceCue.test(event.summary)) {
      throw new Error(`${file} progress[${index}] source_statement contains historical-source wording; use a restatement event and cite the antecedent as original_source`);
    }
  }

  if (originStatus === 'confirmed') {
    const sourceEvents = record.progress.filter((event) => event.kind === 'source_statement');
    if (sourceEvents.length !== 1) {
      throw new Error(`${file} confirmed provenance requires exactly one source_statement event`);
    }
  } else if (record.progress.some((event) => event.kind === 'source_statement')) {
    throw new Error(`${file} unresolved provenance must not contain a source_statement event`);
  }

  for (const citation of citations) {
    if (citation.role === 'restatement' && !record.progress.some((event) =>
      event.kind === 'restatement' && event.citation_labels.includes(citation.label)
    )) {
      throw new Error(`${file} restatement citation is not represented by a restatement progress event: ${citation.label}`);
    }
  }
}

function resolveRepositoryFile(relativePath, file) {
  if (typeof relativePath !== 'string' || relativePath.length === 0) {
    throw new Error(file + ' has no Lean repository path');
  }
  const normalized = path.posix.normalize(relativePath);
  if (path.posix.isAbsolute(relativePath) || normalized !== relativePath || normalized.startsWith('../')) {
    throw new Error(file + ' has an unsafe Lean repository path');
  }
  const absolute = path.resolve(repositoryRoot, relativePath);
  if (path.relative(repositoryRoot, absolute).startsWith('..')) {
    throw new Error(file + ' has a Lean path outside the repository');
  }
  return absolute;
}

function gitText(args, file) {
  try {
    return execFileSync('git', args, {
      cwd: repositoryRoot,
      encoding: 'utf8',
      stdio: ['ignore', 'pipe', 'pipe'],
    }).trim();
  } catch (error) {
    throw new Error(`${file} git check failed for ${args.join(' ')}: ${error.message}`);
  }
}

function gitBytes(args, file) {
  try {
    return execFileSync('git', args, {
      cwd: repositoryRoot,
      encoding: null,
      stdio: ['ignore', 'pipe', 'pipe'],
    });
  } catch (error) {
    throw new Error(`${file} git check failed for ${args.join(' ')}: ${error.message}`);
  }
}

function digestSourceTree(files) {
  const digest = crypto.createHash('sha256');
  for (const {relative, bytes} of files) {
    digest.update(relative);
    digest.update('\0');
    digest.update(crypto.createHash('sha256').update(bytes).digest());
    digest.update('\n');
  }
  return digest.digest('hex');
}

function normalizeLeanLineEndings(bytes) {
  if (!bytes.includes(0x0d)) return bytes;
  const normalized = Buffer.allocUnsafe(bytes.length);
  let writeOffset = 0;
  for (let readOffset = 0; readOffset < bytes.length; readOffset += 1) {
    if (bytes[readOffset] === 0x0d && bytes[readOffset + 1] === 0x0a) {
      normalized[writeOffset] = 0x0a;
      writeOffset += 1;
      readOffset += 1;
    } else {
      normalized[writeOffset] = bytes[readOffset];
      writeOffset += 1;
    }
  }
  return normalized.subarray(0, writeOffset);
}

function localLeanSourceFiles() {
  if (cachedLocalLeanSourceFiles) return cachedLocalLeanSourceFiles;
  const leanRoot = path.resolve(repositoryRoot, 'data/lean');
  const found = [];
  function visit(directory) {
    for (const entry of fs.readdirSync(directory, {withFileTypes: true}).sort((a, b) =>
      a.name < b.name ? -1 : a.name > b.name ? 1 : 0)) {
      if (entry.name === '.lake') continue;
      const absolute = path.join(directory, entry.name);
      if (entry.isDirectory()) {
        visit(absolute);
      } else if (entry.isFile() && entry.name.endsWith('.lean')) {
        found.push({
          relative: path.relative(leanRoot, absolute).split(path.sep).join('/'),
          bytes: normalizeLeanLineEndings(fs.readFileSync(absolute)),
        });
      }
    }
  }
  visit(leanRoot);
  found.sort((a, b) => a.relative < b.relative ? -1 : a.relative > b.relative ? 1 : 0);
  cachedLocalLeanSourceFiles = found;
  return cachedLocalLeanSourceFiles;
}

function committedLeanSourceFiles(commit, file) {
  if (cachedCommittedLeanSourceFiles.has(commit)) {
    return cachedCommittedLeanSourceFiles.get(commit);
  }
  const prefix = 'data/lean/';
  const paths = gitText(['ls-tree', '-r', '--name-only', commit, 'data/lean'], file)
    .split('\n')
    .filter((entry) => entry.startsWith(prefix) && entry.endsWith('.lean'))
    .map((entry) => entry.slice(prefix.length))
    .filter((entry) => !entry.split('/').includes('.lake'))
    .sort();
  const files = paths.map((relative) => ({
    relative,
    bytes: gitBytes(['cat-file', 'blob', `${commit}:data/lean/${relative}`], file),
  }));
  cachedCommittedLeanSourceFiles.set(commit, files);
  return files;
}

function verifyLeanCommit(lean, sourceArtifact, absolutePath, file) {
  if (!/^[0-9a-f]{40}$/.test(lean.commit)) {
    throw new Error(`${file} lean.commit must be a full 40-hex Git commit SHA`);
  }
  if (gitText(['cat-file', '-t', lean.commit], file) !== 'commit') {
    throw new Error(`${file} lean.commit does not name a Git commit`);
  }
  const trackedPath = gitText(['ls-files', '--error-unmatch', lean.path], file);
  if (trackedPath !== lean.path) {
    throw new Error(`${file} Lean path is not Git-tracked: ${lean.path}`);
  }
  const committedBytes = gitBytes(['cat-file', 'blob', `${lean.commit}:${lean.path}`], file);
  const committedDigest = crypto.createHash('sha256').update(committedBytes).digest('hex');
  if (sourceArtifact.sha256 !== committedDigest) {
    throw new Error(`${file} source artifact SHA-256 does not match the immutable commit`);
  }
  const localDigest = crypto.createHash('sha256')
    .update(normalizeLeanLineEndings(fs.readFileSync(absolutePath)))
    .digest('hex');
  if (localDigest !== committedDigest) {
    throw new Error(`${file} working-tree Lean source differs from lean.commit`);
  }
  const localTree = localLeanSourceFiles();
  const committedTree = committedLeanSourceFiles(lean.commit, file);
  if (localTree.length !== committedTree.length) {
    throw new Error(`${file} Lean source-tree file count differs from lean.commit`);
  }
  const localTreeHash = digestSourceTree(localTree);
  const committedTreeHash = digestSourceTree(committedTree);
  if (localTreeHash !== committedTreeHash || localTreeHash !== lean.source_tree_sha256) {
    throw new Error(`${file} Lean source-tree SHA-256 does not match lean.commit`);
  }
  if (Number(lean.source_tree_file_count) !== localTree.length) {
    throw new Error(`${file} Lean source-tree file count is incorrect`);
  }
}
for (const domain of taxonomy.domains) {
  if (!areaIds.has(domain.area)) throw new Error(`taxonomy domain ${domain.id} has unknown area ${domain.area}`);
}
for (const file of files) {
  const record = JSON.parse(fs.readFileSync(path.join(root, file), 'utf8'));
  if (!validateProblem(record)) {
    throw new Error(`${file} schema validation failed: ${ajv.errorsText(validateProblem.errors)}`);
  }
  validateLineage(record, file);
  records.push({file, record});
  if (ids.has(record.id)) throw new Error(`duplicate id: ${record.id}`);
  ids.add(record.id);
  if (`${record.id}.json` !== file) throw new Error(`${file} does not match record id ${record.id}`);
  const serialized = JSON.stringify(record);
  for (const token of forbidden) {
    if (serialized.includes(token)) throw new Error(`${file} contains forbidden token ${token}`);
  }
  for (const key of ['schema_version', 'id', 'group_id', 'title', 'summary', 'formal_statement', 'scope', 'classification', 'source', 'status', 'progress', 'artifacts', 'lean', 'relations']) {
    if (!(key in record)) throw new Error(`${file} is missing required field ${key}`);
  }
  if (record.classification.taxonomy_version !== taxonomy.taxonomy_version) {
    throw new Error(`${file} uses taxonomy ${record.classification.taxonomy_version}, expected ${taxonomy.taxonomy_version}`);
  }
  if (!taxonomyIds.has(record.classification.primary)) throw new Error(`${file} has unknown primary taxonomy id`);
  for (const secondary of record.classification.secondary) {
    if (!taxonomyIds.has(secondary)) throw new Error(`${file} has unknown secondary taxonomy id ${secondary}`);
    if (secondary === record.classification.primary) {
      throw new Error(`${file} repeats primary taxonomy id ${secondary} in secondary taxonomy`);
    }
  }
  if (record.lean.available_in_repo) {
    const lean = record.lean;
    if (lean.status === 'none') throw new Error(file + ' has a repository Lean source but status none');
    if (!['computer_checked', 'repository_checked'].includes(record.status.public_verification_status)) {
      throw new Error(file + ' has a repository Lean source without a checked public-verification status');
    }
    if (!lean.path || !lean.path.startsWith('data/lean/') || !lean.path.endsWith('.lean')) {
      throw new Error(file + ' must point to a data/lean/*.lean source');
    }
    const absolutePath = resolveRepositoryFile(lean.path, file);
    if (!fs.statSync(absolutePath).isFile()) throw new Error(file + ' Lean path is not a regular file');
    for (const key of ['commit', 'lean_version', 'mathlib_version', 'trusted_base', 'replay_command', 'source_tree_sha256']) {
      if (typeof lean[key] !== 'string' || lean[key].length === 0) {
        throw new Error(file + ' is missing lean.' + key);
      }
    }
    if (!Number.isInteger(lean.source_tree_file_count) || lean.source_tree_file_count < 1) {
      throw new Error(file + ' has an invalid lean.source_tree_file_count');
    }
    const sourceArtifacts = record.artifacts.filter((artifact) =>
      artifact.role === 'source_code' && artifact.visibility === 'repository_file');
    if (sourceArtifacts.length !== 1) {
      throw new Error(file + ' must have exactly one repository source_code artifact');
    }
    const [sourceArtifact] = sourceArtifacts;
    const expectedUrl = githubBase + '/blob/' + lean.commit + '/' + lean.path;
    if (sourceArtifact.url !== expectedUrl) {
      throw new Error(file + ' source artifact URL does not match lean.path and lean.commit');
    }
    const digest = crypto.createHash('sha256')
      .update(normalizeLeanLineEndings(fs.readFileSync(absolutePath)))
      .digest('hex');
    if (sourceArtifact.sha256 !== digest) {
      throw new Error(file + ' source artifact SHA-256 does not match ' + lean.path);
    }
    if (sourceArtifact.license !== 'Apache-2.0') {
      throw new Error(file + ' source artifact must declare the repository Apache-2.0 license');
    }
    verifyLeanCommit(lean, sourceArtifact, absolutePath, file);
  }
}
for (const {file, record} of records) {
  for (const relation of ['related', 'supersedes', 'superseded_by']) {
    for (const target of record.relations[relation]) {
      if (!ids.has(target)) throw new Error(`${file} has dangling ${relation} relation ${target}`);
    }
  }
}
if (manifest.record_count !== files.length) throw new Error('manifest record_count does not match public records');
if (manifest.taxonomy_version !== taxonomy.taxonomy_version) throw new Error('manifest taxonomy version does not match taxonomy');
const manifestIds = [...manifest.records].sort();
const recordIds = [...ids].sort();
if (JSON.stringify(manifestIds) !== JSON.stringify(recordIds)) throw new Error('manifest record list does not match public records');
console.log(`Public data check passed: ${files.length} records, ${ids.size} unique ids.`);
