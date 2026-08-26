import LeanCipher.BalancedEightCertificateData

namespace LeanCipher.BalancedEightCertificates

def quadraticWeights : List Nat := [0, 32, 48, 56, 64, 72, 80, 96, 128]

def quadraticWeightsInt : List Int := [0, 32, 48, 56, 64, 72, 80, 96, 128]

def margins (t : LocalTable) : Profile :=
  { n20 := t.a + t.b + t.d
  , n12 := t.c + t.f + t.g
  , n4 := t.e + t.h + t.i
  , n16 := t.a + t.c + t.e
  , n8 := t.b + t.f + t.h
  , n0 := t.d + t.g + t.i }

def tableSum (t : LocalTable) : Nat :=
  t.a + t.b + t.c + t.d + t.e + t.f + t.g + t.h + t.i

def distinguishedCount (weight : Nat) (t : LocalTable) : Nat :=
  if weight = 59 then t.d else if weight = 61 then t.g else t.i

def zeroType (weight : Nat) : Nat :=
  if weight = 59 then 3 else if weight = 61 then 6 else 8

def zeroEnergy (zeroIndex : Nat) : Nat :=
  if zeroIndex = 8 then 2 else if zeroIndex = 6 then 18 else 50

def deltas (n : Nat) : List Int :=
  (List.range (n + 1)).map fun j => -(n : Int) + 2 * (j : Int)

def countsAt (extreme zeroIndex : Nat) : List LocalTable :=
  let numerator := zeroEnergy zeroIndex + 24 * extreme
  if numerator < 826 then [] else
    let target := (numerator - 826) / 8
    (List.range (target / 3 + 1)).flatMap fun e =>
      (List.range ((target - 3 * e) / 4 + 1)).flatMap fun f =>
        let rem0 := target - 3 * e - 4 * f
        (List.range (rem0 / 5 + 1)).flatMap fun gAdd =>
          (List.range ((rem0 - 5 * gAdd) / 6 + 1)).flatMap fun h =>
            let rem1 := rem0 - 5 * gAdd - 6 * h
            (List.range (rem1 / 7 + 1)).flatMap fun iAdd =>
              let cdTotal := rem1 - 7 * iAdd
              (List.range (cdTotal + 1)).filterMap fun c =>
                let d0 := cdTotal - c
                let d := d0 + if zeroIndex = 3 then 1 else 0
                let g := gAdd + if zeroIndex = 6 then 1 else 0
                let i := iAdd + if zeroIndex = 8 then 1 else 0
                let withoutB := extreme + c + d + e + f + g + h + i
                if withoutB <= 128 then
                  some
                    { a := extreme, b := 128 - withoutB, c := c, d := d
                    , e := e, f := f, g := g, h := h, i := i }
                else none

def signedMoment (t : LocalTable) : Int :=
  -2 * t.a - 5 * t.b + 2 * t.c - 6 * t.d + 4 * t.e - t.f -
    2 * t.g + t.h

def fourthMoment (t : LocalTable) : Nat :=
  6562 * t.a + 2482 * t.b + 2402 * t.c + 1250 * t.d +
    706 * t.e + 626 * t.f + 162 * t.g + 82 * t.h + 2 * t.i

def scalarFilters (t : LocalTable) : Option Nat :=
  let totalFourth := fourthMoment t
  if !(quadraticWeights.contains (t.b + t.f + t.h)) then none
  else if signedMoment t % 32 != 0 then none
  else if totalFourth % 1024 != 768 then none
  else some totalFourth

def totalScore (t : LocalTable) : Int :=
  10 * t.a - 10 * t.b - 6 * t.c + 10 * t.d + 2 * t.e +
    6 * t.f - 6 * t.g - 2 * t.h + 2 * t.i

def scoreTargets (score : Int) : List Int :=
  if score = -128 then [0]
  else if score = 0 then [-128, 128]
  else if score = 128 then [0]
  else []

abbrev RightKey := Int × Int × Int

def addRight
    (map : Std.HashMap RightKey (List Int)) (key : RightKey) (value : Int) :
    Std.HashMap RightKey (List Int) :=
  map.insert key (value :: (map.get? key).getD [])

def rightIndex (t : LocalTable) : Std.HashMap RightKey (List Int) :=
  (deltas t.e).foldl (fun map de =>
    (deltas t.f).foldl (fun map df =>
      (deltas t.h).foldl (fun map dh =>
        addRight map
          (16 * de + 24 * df + 8 * dh,
            (544 * de + 624 * df + 80 * dh) % 2048,
            8 * de + 4 * df - 4 * dh)
          (df + dh)) map) map) {}

def orientationPossible (t : LocalTable) (totalFourth : Nat) : Bool :=
  let targets := scoreTargets (totalScore t)
  if targets.isEmpty then false else
    let right := rightIndex t
    let fourthTarget : Int := (1792 - (totalFourth : Int)) % 2048
    let totalQ : Int := t.b + 2 * t.d + 2 * t.e + t.f + 2 * t.g + t.h
    (deltas t.a).any fun da =>
      (deltas t.b).any fun db =>
        (deltas t.c).any fun dc =>
          let d2 := 80 * da + 40 * db + 48 * dc
          let d4 := (6560 * da + 2320 * db + 2400 * dc) % 2048
          let ds := 8 * da - 4 * db - 8 * dc
          targets.any fun target =>
            let key := (-d2, (fourthTarget - d4) % 2048, target - ds)
            match right.get? key with
            | none => false
            | some differences => differences.any fun dqRight =>
                let diffQ := -db + dqRight
                let sumQ := totalQ + diffQ
                let q1 := sumQ / 2
                let q2 := totalQ - q1
                sumQ % 2 = 0 && quadraticWeightsInt.contains q1 &&
                  quadraticWeightsInt.contains q2

def admissibleTable (weight : Nat) (t : LocalTable) : Bool :=
  tableSum t = 128 && distinguishedCount weight t > 0 &&
    match scalarFilters t with
    | none => false
    | some totalFourth => orientationPossible t totalFourth

def enumerateWeight (weight : Nat) : List (Profile × LocalTable) :=
  (List.range 77).flatMap fun extreme =>
    (countsAt extreme (zeroType weight)).filterMap fun table =>
      match scalarFilters table with
      | none => none
      | some totalFourth =>
          if orientationPossible table totalFourth then some (margins table, table)
          else none

abbrev TableEntry := Nat × Profile × LocalTable

def generatedEntries : List TableEntry :=
  [59, 61, 63].flatMap fun weight =>
    (enumerateWeight weight).map fun item => (weight, item.1, item.2)

def generatedEntriesFor (weight : Nat) : List TableEntry :=
  (enumerateWeight weight).map fun item => (weight, item.1, item.2)

def declaredEntries : List TableEntry :=
  declaredFamilies.flatMap fun family =>
    family.rows.map fun table => (family.weight, family.profile, table)

def declaredEntriesFor (weight : Nat) : List TableEntry :=
  (declaredFamilies.filter fun family => family.weight = weight).flatMap fun family =>
    family.rows.map fun table => (family.weight, family.profile, table)

def compareEntry (left right : TableEntry) : Ordering :=
  match compare left.1 right.1 with
  | .eq =>
      match compare left.2.1 right.2.1 with
      | .eq => compare left.2.2 right.2.2
      | order => order
  | order => order

def entryLess (left right : TableEntry) : Bool :=
  compareEntry left right = Ordering.lt

def canonicalEntries (entries : List TableEntry) : List TableEntry :=
  entries.mergeSort entryLess

def familyStructurallyValid (family : Family) : Bool :=
  [59, 61, 63].contains family.weight && !family.rows.isEmpty &&
    family.rows.all fun table =>
      tableSum table = 128 && margins table = family.profile &&
        distinguishedCount family.weight table > 0

def declaredTablesStructurallyValid : Bool :=
  declaredFamilies.all familyStructurallyValid

def localEnumerationReplay : Bool :=
  canonicalEntries generatedEntries = canonicalEntries declaredEntries

def rowsFor (weight : Nat) (profile : Profile) : List LocalTable :=
  match declaredFamilies.find? fun family =>
      family.weight = weight && family.profile = profile with
  | none => []
  | some family => family.rows

def weightCount (profile : Profile) (weight : Nat) : Nat :=
  if weight = 59 then profile.n20 else if weight = 61 then profile.n12
  else profile.n4

def profiles59 : List Profile :=
  (declaredFamilies.filter fun family => family.weight = 59).map (·.profile)

def missingFamily (profile : Profile) : Bool :=
  (profile.n12 > 0 && (rowsFor 61 profile).isEmpty) ||
    (profile.n4 > 0 && (rowsFor 63 profile).isEmpty)

def missingProfiles : List Profile := profiles59.filter missingFamily

def candidateProfiles : List Profile := profiles59.filter fun profile => !missingFamily profile

def certificateProfiles : List Profile := declaredCertificates.map (·.profile)

def computedSurvivors : List Profile :=
  candidateProfiles.filter fun profile => !(certificateProfiles.contains profile)

def rhs (profile : Profile) : List Int :=
  [ profile.n20, profile.n12, profile.n4
  , profile.n20 * profile.n16, profile.n20 * profile.n8,
      profile.n20 * profile.n0
  , profile.n12 * profile.n16, profile.n12 * profile.n8,
      profile.n12 * profile.n0
  , profile.n4 * profile.n16, profile.n4 * profile.n8,
      profile.n4 * profile.n0 ]

def column (owner : Nat) (table : LocalTable) : List Int :=
  [ if owner = 0 then 1 else 0
  , if owner = 1 then 1 else 0
  , if owner = 2 then 1 else 0
  , table.a, table.b, table.d, table.c, table.f, table.g,
      table.e, table.h, table.i ]

def columns (profile : Profile) : List (List Int) :=
  [(59, profile.n20, 0), (61, profile.n12, 1), (63, profile.n4, 2)].flatMap
    fun item =>
      if item.2.1 = 0 then []
      else (rowsFor item.1 profile).map (column item.2.2)

def valueAt (values : List Int) (index : Fin 12) : Int :=
  values.getD index.val 0

def dot12 (left right : List Int) : Int :=
  ∑ index : Fin 12, valueAt left index * valueAt right index

def ValidCertificate (certificate : IntCertificate) : Prop :=
  0 < certificate.scale ∧ certificate.z.length = 12 ∧
    certificate.profile ∈ candidateProfiles ∧
    dot12 (rhs certificate.profile) certificate.z = -(certificate.scale : Int) ∧
    ∀ index : Fin (columns certificate.profile).length,
      0 <= dot12 ((columns certificate.profile).get index) certificate.z

instance (certificate : IntCertificate) : Decidable (ValidCertificate certificate) :=
  by unfold ValidCertificate; infer_instance

def profileLess (left right : Profile) : Bool := compare left right = Ordering.lt

def canonicalProfiles (profiles : List Profile) : List Profile :=
  profiles.mergeSort profileLess

def localDataShape : Prop :=
  declaredFamilies.length = 258 ∧ declaredEntries.length = 3652 ∧
    (declaredFamilies.filter fun family => family.weight = 59).length = 96 ∧
    (declaredFamilies.filter fun family => family.weight = 61).length = 85 ∧
    (declaredFamilies.filter fun family => family.weight = 63).length = 77 ∧
    (declaredEntries.filter fun entry => entry.1 = 59).length = 1461 ∧
    (declaredEntries.filter fun entry => entry.1 = 61).length = 1254 ∧
    (declaredEntries.filter fun entry => entry.1 = 63).length = 937

def profilePartition : Prop :=
  profiles59.length = 96 ∧ missingProfiles.length = 14 ∧
    candidateProfiles.length = 82 ∧ declaredCertificates.length = 69 ∧
    computedSurvivors.length = 13 ∧ computedSurvivors = declaredSurvivors ∧
    List.Nodup certificateProfiles ∧
    canonicalProfiles (missingProfiles ++ certificateProfiles ++ computedSurvivors) =
      canonicalProfiles profiles59

instance : Decidable localDataShape := by
  unfold localDataShape
  infer_instance

instance : Decidable profilePartition := by
  unfold profilePartition
  infer_instance

theorem declared_tables_structurally_valid : declaredTablesStructurallyValid := by
  native_decide

theorem declared_local_data_shape : localDataShape := by
  native_decide

theorem all_integer_farkas_certificates_valid :
    ∀ certificate ∈ declaredCertificates, ValidCertificate certificate := by
  native_decide

theorem weight59_profiles_partition : profilePartition := by
  native_decide

end LeanCipher.BalancedEightCertificates
