import PolyphonotopesMath.PCS.BitOps

/-!
# Normal Form for Pitch Class Sets

Computes the canonical (normal form) representation of a pitch class set,
invariant under transposition. Used for identifying equivalent structures.

Two PCS are transposition-equivalent if one can be obtained from the other
by adding a constant mod 12. For example, C major and D major triads are
equivalent - same shape, different root.

## Algorithm: Minimal Bitset

We use the minimal bitset rotation as the canonical form. This is:
- Simpler and faster than interval sequence comparison
- Produces a unique representative for each equivalence class
- Compatible with the vibe-grammars Rust implementation

For a PCS, we try all 12 rotations and pick the one with the smallest
numerical value. The transposition is how many steps we rotated.
-/

namespace PCS

/-- Compute normal form as bits: the rotation with smallest numerical value.
    Returns (normalized_bits, transposition) where transposition is how many
    steps the original was rotated to reach the normalized form. -/
def normalizeWithTransposition (bits : Nat) : Nat × Nat :=
  if bits = 0 then (0, 0)
  else
    let rotations := (List.range 12).map fun k => (rotateBits bits k, k)
    match rotations.foldl (fun (minBits, minK) (b, k) =>
      if b < minBits then (b, k) else (minBits, minK)) (bits, 0) with
    | (minBits, minK) => (minBits, minK)

/-- Compute normal form as bits (minimal rotation) -/
def normalFormBits (bits : Nat) : Nat :=
  (normalizeWithTransposition bits).1

/-- Get the transposition amount to reach normal form -/
def transpositionToNormal (bits : Nat) : Nat :=
  (normalizeWithTransposition bits).2

/-- Compute normal form as a list of pitch classes -/
def normalForm (bits : Nat) : List Nat :=
  bitsToList (normalFormBits bits)

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
