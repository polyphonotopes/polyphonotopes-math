import PolyphonotopesMath.PCS.BitOps

/-!
# Linear Algebra over Z₂

PitchClassSet ≃ (Z₂)^12 is a vector space over Z₂.
XOR is addition. Diffs between PCS elements form subspaces.

This module provides computational linear algebra for analyzing
the structure of pitch class set collections.

## Constructive Diff Computation

Rather than enumerating all n² pairs, we exploit the group structure:
- Within a transposition orbit, diffs depend only on the rotation difference
- Cross-orbit diffs are rotations of a small set of base diffs
-/

namespace PCS

/-! ### Constructive (non-enumerative) diff computation -/

/-- Base within-orbit diffs: diffs from reference to each rotation. -/
def baseWithinOrbitDiffs (a : Nat) : List Nat :=
  (List.range 12).map fun k => a ^^^ rotateBits a k

/-- Within-orbit diff span: base diffs plus rotations (closure under transposition).
    diff(rotate(a,i), rotate(a,j)) = rotate(diff(a, rotate(a,j-i)), i) -/
def withinOrbitDiffs (a : Nat) : List Nat :=
  let base := baseWithinOrbitDiffs a
  (base.flatMap fun d => (List.range 12).map fun k => rotateBits d k).eraseDups

/-- Base cross-diffs between two PCS: only 12 values needed.
    All cross-diffs are rotations of these. -/
def baseCrossDiffs (a b : Nat) : List Nat :=
  (List.range 12).map fun k => a ^^^ rotateBits b k

/-- Cross-diffs span: base diffs plus their rotations.
    This generates the same subspace as full enumeration. -/
def crossDiffSpan (a b : Nat) : List Nat :=
  let base := baseCrossDiffs a b
  (base.flatMap fun d => (List.range 12).map fun k => rotateBits d k).eraseDups

/-! ### Enumerative versions (for verification/compatibility) -/

/-- All pairwise XOR diffs between elements of a list (enumerative) -/
def allDiffs (bits : List Nat) : List Nat :=
  (bits.flatMap fun a => bits.map fun b => a ^^^ b).eraseDups

/-- Cross-diffs between two collections (enumerative) -/
def crossDiffs (xs ys : List Nat) : List Nat :=
  (xs.flatMap fun a => ys.map fun b => a ^^^ b).eraseDups

/-- Find the position of the highest set bit (0-indexed from right) -/
def highBit (n : Nat) : Nat :=
  if n = 0 then 0 else Nat.log2 n

/-- Row reduce over Z₂ using echelon form. Returns basis vectors. -/
def rowReduceZ2 (rows : List Nat) : List Nat :=
  let emptyBasis : List Nat := List.replicate 12 0
  let finalBasis := rows.foldl (fun basis r =>
    let r' := (List.range 12).foldl (fun acc i =>
      if acc != 0 && (acc >>> i) &&& 1 = 1 && basis[i]! != 0
      then acc ^^^ basis[i]!
      else acc) r
    if r' = 0 then basis
    else basis.set (highBit r') r'
  ) emptyBasis
  finalBasis.filter (· != 0)

/-- Rank = dimension of subspace spanned by vectors -/
def rankZ2 (bits : List Nat) : Nat :=
  (rowReduceZ2 (bits.mergeSort (· < ·))).length

/-- Generators (basis) for the subspace -/
def generatorsZ2 (bits : List Nat) : List Nat :=
  rowReduceZ2 (bits.mergeSort (· < ·))

/-- Check if a vector is in the span of a basis -/
def inSpanZ2 (basis : List Nat) (v : Nat) : Bool :=
  let reduced := basis.foldl (fun acc b =>
    if acc != 0 && (acc &&& b) != 0 then acc ^^^ b else acc) v
  reduced == 0 || basis.contains v

/-- Greedy minimum-weight basis: sort by popcount, add if independent -/
def minWeightBasis (diffs : List Nat) : List Nat :=
  let sorted := diffs.eraseDups.mergeSort (fun a b => popCount a < popCount b)
  sorted.foldl (fun basis v =>
    if rankZ2 (basis ++ [v]) > rankZ2 basis then basis ++ [v] else basis
  ) []

/-- Analyze a collection: returns (orbit_size, rank, min_weight, generators) -/
def analyzeDiffSpace (orbit : List Nat) : Nat × Nat × Nat × List Nat :=
  let diffs := allDiffs orbit
  let orbitSize := orbit.eraseDups.length
  let basis := minWeightBasis diffs
  let rank := basis.length
  let weights := basis.map popCount
  let minWeight := weights.foldl min (weights.head?.getD 0)
  (orbitSize, rank, minWeight, basis)

/-- Pretty-print diff space analysis -/
def showAnalysis (name : String) (orbit : List Nat) : String :=
  let (size, rank, minW, _) := analyzeDiffSpace orbit
  s!"{name}: orbit={size}, rank={rank}, minWeight={minW}"

/-! ## Direct Transitions (Graph View)

The algebraic generators span the diff space, but direct transitions
are the actual diffs that connect two elements in the orbit.
-/

/-- All non-zero diffs (direct transitions) -/
def directDiffs (orbit : List Nat) : List Nat :=
  (allDiffs orbit).filter (· != 0)

/-- Minimum weight among direct transitions -/
def minDirectWeight (orbit : List Nat) : Nat :=
  let weights := (directDiffs orbit).map popCount
  weights.foldl min (weights.head?.getD 12)

/-- Direct transitions of minimum weight -/
def minWeightDirectDiffs (orbit : List Nat) : List Nat :=
  let diffs := directDiffs orbit
  let minW := minDirectWeight orbit
  diffs.filter (fun d => popCount d == minW)

/-- Full analysis: algebraic vs graph view -/
def fullAnalysis (orbit : List Nat) : String × String × List Nat × List Nat :=
  let (size, algRank, algMinW, algGens) := analyzeDiffSpace orbit
  let graphMinW := minDirectWeight orbit
  let graphMinDiffs := minWeightDirectDiffs orbit
  let algebraic := s!"Algebraic: rank={algRank}, minWeight={algMinW}"
  let graph := s!"Graph: minDirectWeight={graphMinW}, #minDiffs={graphMinDiffs.length}"
  (algebraic, graph, algGens, graphMinDiffs)

/-- Pretty-print full analysis -/
def showFullAnalysis (name : String) (orbit : List Nat) : String :=
  let (alg, graph, _, _) := fullAnalysis orbit
  s!"{name}\n  {alg}\n  {graph}"

/-! ## Navigation Structure (Constructive)

Essential moves within and between equivalence classes,
computed using group structure rather than enumeration.
-/

/-- Within-class essential moves: basis for diffs within a transposition orbit.
    Uses only 12 diffs (one per rotation amount) rather than n² enumeration. -/
def withinClassBasis (representative : Nat) : List Nat :=
  minWeightBasis (withinOrbitDiffs representative)

/-- Between-class essential bridges: basis for cross-diffs between two classes.
    Uses constructive cross-diff span. -/
def betweenClassBasis (repA repB : Nat) : List Nat :=
  minWeightBasis (crossDiffSpan repA repB)

/-- Minimum distance between two equivalence classes.
    Computed as min weight over base cross-diffs (only 12 checks). -/
def classDistance (repA repB : Nat) : Nat :=
  let diffs := baseCrossDiffs repA repB
  let weights := diffs.map popCount
  weights.foldl min (weights.head?.getD 12)

/-- Best-aligned diff between two classes (achieves minimum distance). -/
def bestAlignedDiff (repA repB : Nat) : Nat :=
  let diffs := baseCrossDiffs repA repB
  let minW := classDistance repA repB
  (diffs.filter fun d => popCount d == minW).head?.getD 0

/-- Full navigation structure between two classes -/
def navigationStructure (repA repB : Nat) :
    (List Nat × List Nat × List Nat × Nat) :=
  let internalA := withinClassBasis repA
  let internalB := withinClassBasis repB
  let bridges := betweenClassBasis repA repB
  let dist := classDistance repA repB
  (internalA, internalB, bridges, dist)

/-- Pretty-print navigation structure -/
def showNavigation (nameA nameB : String) (repA repB : Nat) : String :=
  let (intA, intB, bridges, dist) := navigationStructure repA repB
  let showList := fun l => l.map (fun b => s!"w{popCount b}")
  s!"{nameA} ↔ {nameB}: distance={dist}\n" ++
  s!"  {nameA} internal: {showList intA}\n" ++
  s!"  {nameB} internal: {showList intB}\n" ++
  s!"  bridges: {showList bridges}"

end PCS
