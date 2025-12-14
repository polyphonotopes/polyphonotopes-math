import PolyphonotopesMath.PCS.BitOps

/-!
# Normal Form for Pitch Class Sets

Computes the canonical (normal form) representation of a pitch class set,
invariant under transposition. Used for identifying equivalent structures.

Two PCS are transposition-equivalent if one can be obtained from the other
by adding a constant mod 12. For example, C major and D major triads are
equivalent - same shape, different root.
-/

namespace PCS

/-- Interval sequence: gaps between adjacent pitch classes (including wraparound).
    For a sorted PCS like [0, 3, 7], returns [3, 4, 5] (semitones between notes). -/
def intervalSequence (pcs : List Nat) : List Nat :=
  match pcs with
  | [] => []
  | [_] => [12]
  | first :: rest =>
    let pairs := pcs.zip (rest ++ [first + 12])
    pairs.map (fun (a, b) => b - a)

/-- Legacy alias for intervalSequence -/
abbrev intervalVector := intervalSequence

/-- Compare interval sequences lexicographically.
    Returns true if seq1 < seq2 (first difference wins). -/
def intervalSequenceLessThan (seq1 seq2 : List Nat) : Bool :=
  match seq1, seq2 with
  | [], [] => false
  | [], _ => true
  | _, [] => false
  | a :: as, b :: bs =>
    if a < b then true
    else if a > b then false
    else intervalSequenceLessThan as bs

/-- Legacy alias for intervalSequenceLessThan -/
abbrev ivLt := intervalSequenceLessThan

/-- Compute normal form: the rotation with lexicographically smallest interval sequence.
    This is the canonical representative under transposition equivalence. -/
def normalForm (bits : Nat) : List Nat :=
  let pcs := bitsToList bits
  if pcs.isEmpty then []
  else
    let rotations := (List.range 12).map fun k =>
      let rotated := pcs.map (fun pc => (pc + 12 - k) % 12) |>.mergeSort (· ≤ ·)
      (rotated, intervalSequence rotated)
    let sorted := rotations.mergeSort (fun (_, seq1) (_, seq2) => intervalSequenceLessThan seq1 seq2)
    match sorted.head? with
    | some (r, _) => r
    | none => pcs

/-- Compute normal form as bits -/
def normalFormBits (bits : Nat) : Nat :=
  listToBits (normalForm bits)

/-- Check if two PCS are transposition-equivalent -/
def isTranspositionEquivalent (a b : Nat) : Bool :=
  normalFormBits a == normalFormBits b

/-- Find the transposition amount from a to b (if equivalent), or none -/
def transpositionAmount (a b : Nat) : Option Nat :=
  (List.range 12).find? fun k => rotateBits a k == b

/-- Count distinct equivalence classes under transposition -/
def countTranspositionClasses (pcsList : List Nat) : Nat :=
  (pcsList.map normalFormBits).eraseDups.length

end PCS
