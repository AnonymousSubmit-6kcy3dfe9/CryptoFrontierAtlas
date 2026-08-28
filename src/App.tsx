import { useEffect, useLayoutEffect, useMemo, useRef, useState } from 'react';
import type { ReactNode } from 'react';
import katex from 'katex';
import {
  ArrowLeft,
  ArrowUpRight,
  Binary,
  BookOpen,
  Check,
  ChevronDown,
  ChevronLeft,
  ChevronRight,
  CircleAlert,
  Code2,
  ExternalLink,
  FileCheck2,
  Filter,
  Layers3,
  Link2,
  ListFilter,
  Search,
  ShieldCheck,
  SlidersHorizontal,
  Sparkles,
  X,
} from 'lucide-react';
import { areaLabels, areaOf, datasetVersion, domainOf, problems, researchTopicCategories, taxonomyPath } from './data';
import type { Problem } from './data';

type Status = Problem['status']['public_mathematical_status'];

const statusLabels: Record<Status, string> = {
  open: 'Open',
  partial_progress: 'Partial progress',
  resolved: 'Resolved',
  refuted: 'Refuted',
  corrected: 'Corrected',
  historically_settled: 'Historically settled',
};

const statusTone: Record<Status, string> = {
  open: 'status-open',
  partial_progress: 'status-partial',
  resolved: 'status-resolved',
  refuted: 'status-refuted',
  corrected: 'status-corrected',
  historically_settled: 'status-history',
};

const progressLabels: Record<string, string> = {
  source_statement: 'Original statement',
  restatement: 'Restatement',
  prior_result: 'Prior result',
  public_result: 'Public result',
  independent_result: 'Independent result',
  audit: 'Audit',
};

const sourceKindLabels: Record<Problem['source']['kind'], string> = {
  explicit_open_problem: 'Explicit open problem',
  explicit_conjecture: 'Explicit conjecture',
  open_challenge: 'Open challenge',
  public_thesis_conjecture: 'Public thesis conjecture',
};

const verificationLabels: Record<Problem['status']['public_verification_status'], string> = {
  none: 'None',
  computer_checked: 'Computer checked',
  externally_claimed: 'Externally claimed',
  externally_reproducible: 'Externally reproducible',
  repository_checked: 'Repository checked',
};

const peerReviewLabels: Record<Problem['status']['peer_review_status'], string> = {
  not_submitted: 'Not submitted',
  preprint: 'Preprint',
  under_review: 'Under review',
  published: 'Published',
  independently_audited: 'Independently audited',
};

const artifactRoleLabels: Record<Problem['artifacts'][number]['role'], string> = {
  canonical_manuscript: 'Canonical manuscript',
  source_code: 'Source code',
  verifier: 'Verifier',
  data: 'Data',
  superseded_draft: 'Superseded draft',
};

const artifactVisibilityLabels: Record<Problem['artifacts'][number]['visibility'], string> = {
  not_listed: 'Not listed',
  external_link: 'External link',
  repository_file: 'Repository file',
};

function classificationIds(problem: Problem) {
  return [problem.classification.primary, ...problem.classification.secondary];
}

function matchesArea(problem: Problem, area: string) {
  return area === 'all' || areaOf(problem.classification.primary) === area;
}

function matchesDomain(problem: Problem, domain: string) {
  return domain === 'all' || domainOf(problem.classification.primary) === domain;
}

function ClassificationPath({ id }: { id: string }) {
  const path = taxonomyPath(id);
  return (
    <span className="classification-path">
      <span>{path.area}</span><span aria-hidden="true">/</span>
      <span>{path.domain}</span><span aria-hidden="true">/</span>
      <strong>{path.leaf}</strong>
    </span>
  );
}

function renderMathText(body: string): ReactNode[] {
  const tokenPattern = /(\$\$[\s\S]*?\$\$|\$[^$\n]+\$|\\\([\s\S]*?\\\)|\\\[[\s\S]*?\\\])/g;
  const nodes: ReactNode[] = [];
  let cursor = 0;
  let match: RegExpExecArray | null;
  let index = 0;

  while ((match = tokenPattern.exec(body)) !== null) {
    if (match.index > cursor) nodes.push(<span key={`text-${index++}`}>{body.slice(cursor, match.index)}</span>);
    const token = match[0];
    const displayMode = token.startsWith('$$') || token.startsWith('\\[');
    const formula = token.startsWith('$$') ? token.slice(2, -2) : token.startsWith('\\') ? token.slice(2, -2) : token.slice(1, -1);
    try {
      const html = katex.renderToString(formula, { throwOnError: false, displayMode });
      nodes.push(<span className={displayMode ? 'math-display' : 'math-inline'} key={`math-${index++}`} dangerouslySetInnerHTML={{ __html: html }} />);
    } catch {
      nodes.push(<span key={`fallback-${index++}`}>{token}</span>);
    }
    cursor = match.index + token.length;
  }
  if (cursor < body.length) nodes.push(<span key={`text-${index}`}>{body.slice(cursor)}</span>);
  return nodes;
}

function readHash() {
  const match = window.location.hash.match(/^#question\/(.+)$/);
  return match?.[1] ?? null;
}

function eprintUrl(identifier: string) {
  const arxiv = identifier.match(/^arXiv:\s*([0-9]{4}\.[0-9]{4,5}(?:v[0-9]+)?)$/i);
  if (arxiv) return `https://arxiv.org/abs/${arxiv[1]}`;
  const iacr = identifier.match(/^(?:(?:IACR\s+)?ePrint\s+)?([0-9]{4}\/[0-9]+)$/i);
  if (iacr) return `https://eprint.iacr.org/${iacr[1]}`;
  return null;
}

function readableEnum(value: string) {
  return value.replaceAll('_', ' ');
}

function canonicalUrl(value: string) {
  try {
    const url = new URL(value);
    const pathname = url.pathname === '/' ? '/' : url.pathname.replace(/\/$/, '');
    return `${url.protocol.toLowerCase()}//${url.host.toLowerCase()}${pathname}${url.search}${url.hash}`;
  } catch {
    return value.replace(/\/$/, '');
  }
}

function CitationLinks({ citation, iconSize = 12 }: { citation: Problem['source']['citations'][number]; iconSize?: number }) {
  const eprintHref = citation.eprint ? eprintUrl(citation.eprint) : null;
  const links = [
    citation.doi && { href: `https://doi.org/${citation.doi}`, label: 'DOI' },
    citation.eprint && eprintHref && { href: eprintHref, label: citation.eprint },
    citation.url && { href: citation.url, label: 'Open link' },
  ].filter((item): item is { href: string; label: string } => Boolean(item));
  const seen = new Set<string>();
  const uniqueLinks = links.filter((item) => {
    const key = canonicalUrl(item.href);
    if (seen.has(key)) return false;
    seen.add(key);
    return true;
  });
  return (
    <>
      {uniqueLinks.map((item) => <a href={item.href} target="_blank" rel="noreferrer" aria-label={`${citation.label}: ${item.label}`} key={item.href}>{item.label} <ExternalLink size={iconSize} /></a>)}
      {citation.eprint && !eprintHref && <span className="citation-identifier">{citation.eprint}</span>}
    </>
  );
}

function App() {
  const PAGE_SIZE = 12;
  const [query, setQuery] = useState('');
  const [area, setArea] = useState('all');
  const [domain, setDomain] = useState('all');
  const [category, setCategory] = useState('all');
  const [expandedDomain, setExpandedDomain] = useState<string | null>(null);
  const [status, setStatus] = useState<'all' | Status>('all');
  const [selectedId, setSelectedId] = useState<string | null>(() => readHash());
  const [sort, setSort] = useState<'alphabetical' | 'reviewed'>('alphabetical');
  const [currentPage, setCurrentPage] = useState(1);
  const listReturnRef = useRef<{ scrollY: number; recordId: string } | null>(null);
  const restoreListRef = useRef(false);
  const detailOpenRef = useRef(Boolean(selectedId));

  useEffect(() => {
    const previousScrollRestoration = window.history.scrollRestoration;
    window.history.scrollRestoration = 'manual';

    const handleHash = () => {
      const nextId = readHash();
      if (!nextId && detailOpenRef.current && listReturnRef.current) {
        restoreListRef.current = true;
      }
      detailOpenRef.current = Boolean(nextId);
      setSelectedId(nextId);
    };
    window.addEventListener('hashchange', handleHash);
    return () => {
      window.history.scrollRestoration = previousScrollRestoration;
      window.removeEventListener('hashchange', handleHash);
    };
  }, []);

  useLayoutEffect(() => {
    if (selectedId || !restoreListRef.current || !listReturnRef.current) return;

    const { scrollY, recordId } = listReturnRef.current;
    restoreListRef.current = false;
    const restoreListPosition = () => {
      const root = document.documentElement;
      const previousScrollBehavior = root.style.scrollBehavior;
      root.style.scrollBehavior = 'auto';
      window.scrollTo({ top: scrollY, left: 0, behavior: 'auto' });
      root.style.scrollBehavior = previousScrollBehavior;
      document.querySelector<HTMLElement>(`[data-record-id="${CSS.escape(recordId)}"]`)?.focus({ preventScroll: true });
    };

    restoreListPosition();
    const frame = window.requestAnimationFrame(restoreListPosition);
    return () => window.cancelAnimationFrame(frame);
  }, [selectedId]);

  useEffect(() => {
    if (!selectedId) return;
    window.setTimeout(() => {
      document.querySelector('.detail-panel')?.scrollIntoView({ behavior: 'smooth', block: 'start' });
      document.querySelector<HTMLElement>('.detail-heading h2')?.focus({ preventScroll: true });
    }, 0);
  }, [selectedId]);

  const filtered = useMemo(() => {
    const normalized = query.trim().toLowerCase();
    return [...problems]
      .filter((problem) => matchesArea(problem, area))
      .filter((problem) => matchesDomain(problem, domain))
      .filter((problem) => category === 'all' || problem.classification.primary === category)
      .filter((problem) => status === 'all' || problem.status.public_mathematical_status === status)
      .filter((problem) => {
        if (!normalized) return true;
        const classifications = classificationIds(problem).map((id) => taxonomyPath(id));
        return [
          problem.title,
          problem.summary,
          ...classifications.flatMap((item) => [item.area, item.domain, item.leaf]),
          problem.classification.tags.join(' '),
        ].join(' ').toLowerCase().includes(normalized);
      })
      .sort((a, b) => sort === 'alphabetical'
        ? a.title.localeCompare(b.title)
        : b.status.last_reviewed.localeCompare(a.status.last_reviewed));
  }, [area, category, domain, query, sort, status]);

  const totalPages = Math.max(1, Math.ceil(filtered.length / PAGE_SIZE));
  const pageStart = (currentPage - 1) * PAGE_SIZE;
  const paginated = filtered.slice(pageStart, pageStart + PAGE_SIZE);

  useEffect(() => {
    setCurrentPage(1);
  }, [area, category, domain, query, sort, status]);

  useEffect(() => {
    setCurrentPage((page) => Math.min(page, totalPages));
  }, [totalPages]);

  const selected = problems.find((problem) => problem.id === selectedId) ?? null;

  function openProblem(id: string) {
    listReturnRef.current = { scrollY: window.scrollY, recordId: id };
    detailOpenRef.current = true;
    window.location.hash = `question/${id}`;
    setSelectedId(id);
  }

  function closeProblem() {
    restoreListRef.current = Boolean(listReturnRef.current);
    detailOpenRef.current = false;
    window.history.replaceState(null, '', `${window.location.pathname}${window.location.search}`);
    setSelectedId(null);
  }

  function toggleTopicGroup(group: (typeof researchTopicCategories)[number]) {
    if (expandedDomain === group.id) {
      setExpandedDomain(null);
      return;
    }

    setExpandedDomain(group.id);
    setArea(group.area);
    if (domain !== group.id) {
      setDomain(group.id);
      setCategory('all');
    }
  }

  function selectTopicCategory(group: (typeof researchTopicCategories)[number], categoryId: string) {
    setArea(group.area);
    setDomain(group.id);
    setCategory(categoryId);
    setExpandedDomain(group.id);
  }

  const areaCounts = Object.entries(areaLabels).map(([id, label]) => ({
    id,
    label,
    count: problems.filter((problem) => matchesArea(problem, id)).length,
  }));
  const domainCounts = researchTopicCategories
    .filter((item) => area === 'all' || item.area === area)
    .map((item) => ({
      ...item,
      count: problems.filter((problem) => matchesDomain(problem, item.id)).length,
    }));
  const categoryCount = researchTopicCategories.reduce((count, group) => count + group.children.length, 0);

  return (
    <div className="app-shell">
      <header className="topbar">
        <a className="brand" href="#top" aria-label="CryptoFrontierAtlas home" onClick={() => closeProblem()}>
          <span className="brand-mark"><Binary size={19} strokeWidth={2.4} /></span>
          <span>CryptoFrontierAtlas</span>
        </a>
        <nav className="topnav" aria-label="Primary navigation">
          <a className="topnav-link active" href="#atlas">Atlas</a>
          <a className="topnav-link" href="#method">Method</a>
          <a className="topnav-link" href="https://github.com/AnonymousSubmit-6kcy3dfe9/CryptoFrontierAtlas" target="_blank" rel="noreferrer">
            Repository <ArrowUpRight size={14} />
          </a>
        </nav>
      </header>

      <main id="top">
        <section className="masthead" id="atlas">
          <div className="masthead-copy">
            <div className="eyebrow"><span className="eyebrow-dot" /> Cryptography / research index</div>
            <h1>Crypto<wbr />Frontier<wbr />Atlas: Open Problems in Cryptography</h1>
            <p className="masthead-lede">A source-aware atlas of open questions, formal statements, and public evidence in cryptography. The current release covers symmetric cryptography.</p>
          </div>
          <div className="signal-panel" aria-label="Dataset snapshot">
            <div className="signal-head"><span>Dataset snapshot</span><span className="signal-live"><span /> v{datasetVersion}</span></div>
            <div className="signal-number">{problems.length.toString().padStart(2, '0')}</div>
            <div className="signal-label">public problem records</div>
            <div className="signal-rule" />
            <div className="signal-grid">
              <div><strong>{Object.keys(areaLabels).length.toString().padStart(2, '0')}</strong><span>areas</span></div>
              <div><strong>{categoryCount.toString().padStart(2, '0')}</strong><span>topic leaves</span></div>
              <div><strong>{problems.filter((problem) => problem.status.public_mathematical_status === 'partial_progress').length.toString().padStart(2, '0')}</strong><span>partial</span></div>
            </div>
          </div>
        </section>

        <section className="workspace" aria-label="Question atlas">
          <aside className="sidebar">
            <div className="sidebar-label"><Filter size={15} /> Cryptography area</div>
            <div className="domain-list">
              <button className={`domain-button ${area === 'all' && domain === 'all' && category === 'all' ? 'selected' : ''}`} onClick={() => { setArea('all'); setDomain('all'); setCategory('all'); setExpandedDomain(null); }}>
                <span className="domain-swatch all-swatch" />
                <span>All questions</span><strong>{problems.length}</strong>
              </button>
              {areaCounts.map((item) => (
                <button key={item.id} className={`domain-button ${area === item.id && domain === 'all' && category === 'all' ? 'selected' : ''}`} onClick={() => { setArea(item.id); setDomain('all'); setCategory('all'); setExpandedDomain(null); }}>
                  <span className={`domain-swatch ${item.id}`} />
                  <span>{item.label}</span><strong>{item.count}</strong>
                </button>
              ))}
            </div>

            <div className="sidebar-divider compact-divider" />
            <div className="sidebar-label"><Layers3 size={15} /> Research topic category</div>
            <div className="domain-list topic-category-list">
              <button className={`domain-button ${domain === 'all' && category === 'all' ? 'selected' : ''}`} onClick={() => { setDomain('all'); setCategory('all'); setExpandedDomain(null); }}>
                <span className="domain-swatch all-domains-swatch" />
                <span>All topic categories</span><strong>{area === 'all' ? problems.length : problems.filter((problem) => matchesArea(problem, area)).length}</strong>
              </button>
              {domainCounts.map((item) => {
                const isExpanded = expandedDomain === item.id;
                const isActive = domain === item.id;
                const childListId = `topic-children-${item.id}`;
                return (
                  <div className={`topic-group ${isActive ? 'active' : ''}`} key={item.id}>
                    <button
                      className={`domain-button topic-group-button ${isActive && category === 'all' ? 'selected' : ''} ${isActive ? 'active-parent' : ''} ${isExpanded ? 'expanded' : ''}`}
                      type="button"
                      aria-expanded={isExpanded}
                      aria-controls={childListId}
                      onClick={() => toggleTopicGroup(item)}
                    >
                      <span className={`domain-swatch ${item.id}`} />
                      <span>{item.label}</span>
                      <strong>{item.count}</strong>
                      <ChevronDown className="topic-chevron" size={14} aria-hidden="true" />
                    </button>
                    {isExpanded && (
                      <div className="topic-child-list" id={childListId} role="group" aria-label={`${item.label} subcategories`}>
                        {item.children.map((child) => {
                          const childCount = problems.filter((problem) => problem.classification.primary === child.id).length;
                          const isSelected = category === child.id;
                          return (
                            <button
                              className={`topic-child-button ${isSelected ? 'selected' : ''}`}
                              type="button"
                              aria-pressed={isSelected}
                              onClick={() => selectTopicCategory(item, child.id)}
                              key={child.id}
                            >
                              <span>{child.label}</span>
                              <strong>{childCount}</strong>
                            </button>
                          );
                        })}
                      </div>
                    )}
                  </div>
                );
              })}
            </div>

            <div className="sidebar-divider" />
            <div className="sidebar-label"><SlidersHorizontal size={15} /> Status</div>
            <label className="select-wrap">
              <span className="sr-only">Filter by mathematical status</span>
              <select value={status} onChange={(event) => setStatus(event.target.value as 'all' | Status)}>
                <option value="all">All statuses</option>
                <option value="open">Open</option>
                <option value="partial_progress">Partial progress</option>
                <option value="resolved">Resolved</option>
                <option value="refuted">Refuted</option>
              </select>
              <ChevronDown size={15} />
            </label>

            <div className="sidebar-note">
              <Sparkles size={16} />
              <p>Every record keeps its original scope visible. A partial result is never presented as a complete resolution.</p>
            </div>
          </aside>

          <section className="results-column">
            <div className="results-toolbar">
              <div>
                <div className="section-kicker">Question index</div>
                <h2>{filtered.length} <span>records in view</span></h2>
              </div>
              <div className="toolbar-actions">
                <label className="search-box">
                  <Search size={17} />
                  <span className="sr-only">Search questions</span>
                  <input value={query} onChange={(event) => setQuery(event.target.value)} placeholder="Search title, topic, or term" />
                  {query && <button className="icon-button compact" aria-label="Clear search" onClick={() => setQuery('')}><X size={15} /></button>}
                </label>
                <label className="sort-wrap">
                  <ListFilter size={15} />
                  <span className="sr-only">Sort records</span>
                  <select value={sort} onChange={(event) => setSort(event.target.value as 'alphabetical' | 'reviewed')}>
                    <option value="alphabetical">A - Z</option>
                    <option value="reviewed">Recently reviewed</option>
                  </select>
                  <ChevronDown size={14} />
                </label>
              </div>
            </div>

            <div className="record-list">
              {paginated.map((problem, index) => (
                <button className={`record-row ${selectedId === problem.id ? 'active' : ''}`} data-record-id={problem.id} key={problem.id} onClick={() => openProblem(problem.id)}>
                  <span className="record-index">{String(pageStart + index + 1).padStart(2, '0')}</span>
                  <span className="record-main">
                    <span className="record-topline">
                      <span className={`status-pill ${statusTone[problem.status.public_mathematical_status]}`}><span />{statusLabels[problem.status.public_mathematical_status]}</span>
                      <ClassificationPath id={problem.classification.primary} />
                    </span>
                    <strong>{problem.title}</strong>
                    <span className="record-summary">{renderMathText(problem.summary)}</span>
                    <span className="record-tags">{problem.classification.tags.slice(0, 3).map((tag) => <span key={tag}>#{tag}</span>)}</span>
                  </span>
                  <ArrowUpRight className="record-arrow" size={18} />
                </button>
              ))}
              {!filtered.length && <div className="empty-state"><Search size={24} /><strong>No questions match this view.</strong><span>Try a broader term or reset the filters.</span></div>}
            </div>
            {filtered.length > 0 && (
              <nav className="pagination" aria-label="Question index pagination">
                <span className="pagination-range">Showing {pageStart + 1}-{Math.min(pageStart + PAGE_SIZE, filtered.length)} of {filtered.length}</span>
                <div className="pagination-controls">
                  <button className="pagination-button" type="button" aria-label="Previous page" title="Previous page" disabled={currentPage === 1} onClick={() => setCurrentPage((page) => Math.max(1, page - 1))}><ChevronLeft size={16} /></button>
                  <span className="pagination-status" aria-live="polite">Page {currentPage} of {totalPages}</span>
                  <button className="pagination-button" type="button" aria-label="Next page" title="Next page" disabled={currentPage === totalPages} onClick={() => setCurrentPage((page) => Math.min(totalPages, page + 1))}><ChevronRight size={16} /></button>
                </div>
              </nav>
            )}
          </section>
        </section>

        <section className={`detail-panel ${selected ? 'is-open' : ''}`} aria-live="polite">
          {selected ? <Detail problem={selected} onClose={closeProblem} /> : <EmptyDetail />}
        </section>

        <section className="method-band" id="method">
          <div className="method-heading"><div className="section-kicker">Atlas method</div><h2>Trace the question before the claim.</h2></div>
          <div className="method-grid">
            <div><span>01</span><strong>Source</strong><p>Every record starts from a public problem, conjecture, or challenge with a citation trail.</p></div>
            <div><span>02</span><strong>Scope</strong><p>Parameters, assumptions, and unresolved remainder stay attached to the formal statement.</p></div>
            <div><span>03</span><strong>Evidence</strong><p>Mathematical progress, computation, review, and Lean availability are separate signals.</p></div>
          </div>
        </section>
      </main>

      <footer className="footer"><span>CryptoFrontierAtlas / cryptography</span><span>Dataset v{datasetVersion} <span className="footer-dot" /> CC BY 4.0 metadata</span></footer>
    </div>
  );
}

function EmptyDetail() {
  return <div className="detail-empty"><Code2 size={28} /><strong>Select a question to inspect its formal surface.</strong><span>Source, scope, public progress, and evidence appear here.</span></div>;
}

function Detail({ problem, onClose }: { problem: Problem; onClose: () => void }) {
  const sourceCitation = problem.source.citations.find((citation) => citation.role === 'original_source')
    ?? problem.source.citations.find((citation) => citation.role === 'restatement')
    ?? problem.source.citations[0];
  const relationGroups = [
    { label: 'Related questions', ids: problem.relations.related },
    { label: 'Supersedes', ids: problem.relations.supersedes },
    { label: 'Superseded by', ids: problem.relations.superseded_by },
  ].filter((group) => group.ids.length > 0);

  return (
    <div className="detail-inner">
      <div className="detail-topbar"><button className="back-button" onClick={onClose}><ArrowLeft size={16} /> Back to index</button><span className="detail-id">{problem.id}</span></div>
      <div className="detail-heading">
        <div className="record-topline"><span className={`status-pill ${statusTone[problem.status.public_mathematical_status]}`}><span />{statusLabels[problem.status.public_mathematical_status]}</span><ClassificationPath id={problem.classification.primary} /></div>
        <h2 tabIndex={-1}>{problem.title}</h2>
        <p>{renderMathText(problem.summary)}</p>
      </div>
      <div className="detail-grid">
        <div className="detail-main">
          <section className="detail-section">
            <div className="section-kicker">Formal statement</div>
            <div className="formula-block">{renderMathText(problem.formal_statement.body)}</div>
          </section>
          <section className="detail-section">
            <div className="section-kicker">Scope and boundary</div>
            <div className="scope-list">
              <div><span>Domain</span><strong>{renderMathText(problem.scope.domain)}</strong></div>
              <div><span>Assumptions</span><strong>{renderMathText(problem.scope.assumptions.join(' · '))}</strong></div>
              <div><span>Parameters</span><strong>{renderMathText(problem.scope.parameters.join(' · '))}</strong></div>
              <div><span>Unresolved remainder</span><strong>{renderMathText(problem.scope.unresolved_remainder)}</strong></div>
            </div>
          </section>
          <section className="detail-section">
            <div className="section-kicker">Progress timeline</div>
            <div className="timeline">
              {problem.progress.map((entry, index) => <div className="timeline-item" key={`${entry.date}-${entry.kind}-${entry.citation_labels.join('|')}-${index}`}><span className="timeline-date">{entry.date}</span><div><strong>{progressLabels[entry.kind] ?? entry.kind.replaceAll('_', ' ')}</strong><p>{renderMathText(entry.summary)}</p>{entry.citation_labels.length > 0 && <span className="citation-ref">{entry.citation_labels.join(' · ')}</span>}</div></div>)}
            </div>
          </section>
        </div>
        <aside className="detail-side">
          <div className="side-block source-block">
            <div className="section-kicker">Source</div>
            <div className="source-kind"><span>Source kind</span><strong>{sourceKindLabels[problem.source.kind] ?? readableEnum(problem.source.kind)}</strong></div>
            <span className="metadata-label">{sourceCitation.role === 'original_source' ? 'Historical source' : 'Ingested restatement'}</span>
            <strong>{sourceCitation.label}</strong>
            {sourceCitation.locator && <span className="source-citation-locator">{sourceCitation.locator}</span>}
            <CitationLinks citation={sourceCitation} iconSize={13} />
          </div>
          <div className="side-block evidence-block">
            <div className="section-kicker">Evidence</div>
            <div className="evidence-line"><Check size={15} /><span>Mathematical status</span><strong>{statusLabels[problem.status.public_mathematical_status]}</strong></div>
            <div className="evidence-line"><ShieldCheck size={15} /><span>Public verification</span><strong>{verificationLabels[problem.status.public_verification_status] ?? readableEnum(problem.status.public_verification_status)}</strong></div>
            <div className="evidence-line"><BookOpen size={15} /><span>Peer review</span><strong>{peerReviewLabels[problem.status.peer_review_status] ?? readableEnum(problem.status.peer_review_status)}</strong></div>
            <div className="evidence-line"><CircleAlert size={15} /><span>Disclosure</span><strong>{problem.status.disclosure.replaceAll('_', ' ')}</strong></div>
            <div className="evidence-line"><Code2 size={15} /><span>Lean status</span><strong>{readableEnum(problem.lean.status)}</strong></div>
            <div className="evidence-line"><Code2 size={15} /><span>Lean source</span><strong>{problem.lean.available_in_repo ? 'Available' : 'Not publicly available'}</strong></div>
          </div>
          <div className="side-block literature-block">
            <div className="section-kicker"><BookOpen size={14} /> Literature trail</div>
            {problem.source.citations.map((citation) => (
              <div className="citation-entry" key={`${citation.role}-${citation.label}`}>
                <strong>{citation.label}</strong>
                <span>{citation.role === 'restatement' ? 'restatement' : citation.role.replaceAll('_', ' ')}{citation.locator ? ` · ${citation.locator}` : ''}</span>
                <CitationLinks citation={citation} />
              </div>
            ))}
          </div>
          <div className="side-block classification-block">
            <div className="section-kicker"><Layers3 size={14} /> Classification</div>
            <span className="metadata-label">Primary category</span>
            <ClassificationPath id={problem.classification.primary} />
            <span className="metadata-label">Related research topics</span>
            {problem.classification.secondary.length > 0
              ? <div className="taxonomy-path-list">{problem.classification.secondary.map((id) => <ClassificationPath id={id} key={id} />)}</div>
              : <span className="empty-metadata">No related research topics</span>}
            <span className="metadata-label metadata-label-spaced">Topics</span>
            <div className="tag-cloud">{problem.classification.tags.map((tag) => <span key={tag}>#{tag}</span>)}</div>
          </div>
          <div className="side-block artifact-block">
            <div className="section-kicker"><FileCheck2 size={14} /> Public artifacts</div>
            {problem.artifacts.length > 0
              ? problem.artifacts.map((artifact, index) => (
                <div className="artifact-entry" key={`${artifact.role}-${artifact.url ?? index}`}>
                  <div className="artifact-head"><strong>{artifactRoleLabels[artifact.role] ?? readableEnum(artifact.role)}</strong><span>{artifactVisibilityLabels[artifact.visibility] ?? readableEnum(artifact.visibility)}</span></div>
                  {artifact.license && <span>License: {artifact.license}</span>}
                  {artifact.sha256 && <code>SHA-256 {artifact.sha256}</code>}
                  {artifact.url && <a href={artifact.url} target="_blank" rel="noreferrer">Open artifact <ExternalLink size={12} /></a>}
                </div>
              ))
              : <span className="empty-metadata">No public artifacts listed</span>}
          </div>
          <div className="side-block relation-block">
            <div className="section-kicker"><Link2 size={14} /> Question relations</div>
            {relationGroups.length > 0
              ? relationGroups.map((group) => (
                <div className="relation-group" key={group.label}>
                  <span>{group.label}</span>
                  {group.ids.map((id) => {
                    const target = problems.find((candidate) => candidate.id === id);
                    return (
                      <a className="relation-link" href={`#question/${id}`} key={id} aria-label={`Open ${target?.title ?? id}`}>
                        <span><strong>{target?.title ?? id}</strong><small>{id}</small></span>
                        <ArrowUpRight size={13} />
                      </a>
                    );
                  })}
                </div>
              ))
              : <span className="empty-metadata">No question relations listed</span>}
          </div>
        </aside>
      </div>
      <div className="detail-footer"><span className="last-reviewed">Last reviewed {problem.status.last_reviewed}</span><span className="record-group">Record group: {problem.group_id}</span><a href="https://github.com/AnonymousSubmit-6kcy3dfe9/CryptoFrontierAtlas" target="_blank" rel="noreferrer">View repository <ExternalLink size={13} /></a></div>
    </div>
  );
}

export default App;
