import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Fin.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Tactic

/-!
# Pitch Class Sets and XOR Transformations

We formalize pitch class sets as 12-dimensional vectors over Z₂,
where XOR provides both the group operation and the transformation action.

## Key structures:
- `PitchClassSet`: 12-bit representation of pitch classes
- XOR as group operation makes this (Z₂)^12
- Each PCS acts as a transformation via XOR (regular representation)
-/

/-- A pitch class set is a function from the 12 pitch classes to Z₂.
    Equivalently, a 12-dimensional vector over the field with 2 elements. -/
def PitchClassSet := Fin 12 → ZMod 2

namespace PitchClassSet

/-- The empty pitch class set (no pitches). Identity for XOR. -/
def empty : PitchClassSet := fun _ => 0

/-- XOR of two pitch class sets (pointwise addition in Z₂). -/
def xor (a b : PitchClassSet) : PitchClassSet := fun i => a i + b i

/-- A singleton pitch class set containing just one pitch. -/
def singleton (pc : Fin 12) : PitchClassSet := fun i => if i = pc then 1 else 0

-- Notation for common pitch classes
def C  : Fin 12 := 0
def Cs : Fin 12 := 1   -- C#
def D  : Fin 12 := 2
def Ds : Fin 12 := 3   -- D#
def E  : Fin 12 := 4
def F  : Fin 12 := 5
def Fs : Fin 12 := 6   -- F#
def G  : Fin 12 := 7
def Gs : Fin 12 := 8   -- G#
def A  : Fin 12 := 9
def As : Fin 12 := 10  -- A#
def B  : Fin 12 := 11

/-- Build a PCS from a list of pitch classes -/
def fromList (pcs : List (Fin 12)) : PitchClassSet :=
  fun i => if pcs.contains i then 1 else 0

-- Example: F and F# as a transformation mask
def F_Fs_mask : PitchClassSet := fromList [F, Fs]

/-!
## Group Structure

PitchClassSet forms an abelian group under XOR:
- Identity: empty set
- Inverse: each element is its own inverse (a ⊕ a = ∅)
- Associativity: inherited from Z₂
-/

instance : Add PitchClassSet where
  add := xor

instance : Zero PitchClassSet where
  zero := empty

instance : Neg PitchClassSet where
  neg a := a  -- Every element is its own inverse in Z₂

theorem xor_assoc (a b c : PitchClassSet) : xor (xor a b) c = xor a (xor b c) := by
  funext i
  simp only [xor]
  exact add_assoc (a i) (b i) (c i)

theorem xor_comm (a b : PitchClassSet) : xor a b = xor b a := by
  funext i
  simp only [xor]
  exact add_comm (a i) (b i)

theorem xor_empty_right (a : PitchClassSet) : xor a empty = a := by
  funext i
  simp only [xor, empty]
  exact add_zero (a i)

theorem xor_empty_left (a : PitchClassSet) : xor empty a = a := by
  funext i
  simp only [xor, empty]
  exact zero_add (a i)

theorem xor_self (a : PitchClassSet) : xor a a = empty := by
  funext i
  simp only [xor, empty]
  -- In ZMod 2, x + x = 0 for all x
  have h : a i + a i = 0 := by
    have : (2 : ZMod 2) = 0 := rfl
    calc a i + a i = 2 * a i := by ring
      _ = 0 * a i := by rw [this]
      _ = 0 := by ring
  exact h

/-!
## Group Action (Regular Representation)

Each PitchClassSet acts on the set of all PitchClassSets via XOR.
This is the regular representation: the group acting on itself.
-/

/-- Apply a PCS as a transformation to another PCS -/
def transform (mask : PitchClassSet) (pcs : PitchClassSet) : PitchClassSet :=
  xor mask pcs

-- Key property: transformation is involutive
theorem transform_involutive (mask : PitchClassSet) :
    Function.Involutive (transform mask) := by
  intro pcs
  simp only [transform]
  rw [← xor_assoc, xor_self, xor_empty_left]

-- Transformations compose via XOR
theorem transform_compose (m₁ m₂ pcs : PitchClassSet) :
    transform m₁ (transform m₂ pcs) = transform (xor m₁ m₂) pcs := by
  simp only [transform]
  rw [← xor_assoc]

end PitchClassSet
