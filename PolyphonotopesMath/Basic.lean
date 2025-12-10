import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Fin.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Tactic

/-!
# Pitch Class Sets and XOR Transformations

We formalize pitch class sets as functions from the cyclic group Z₁₂ to Z₂.

## Key structures:
- `PitchClass`: Elements of Z₁₂ (the 12 pitch classes)
- `PitchClassSet`: Functions Z₁₂ → Z₂ (characteristic functions)
- XOR operates on the codomain (Z₂) - toggles membership
- Transposition operates on the domain (Z₁₂) - shifts pitches
-/

/-- A pitch class is an element of Z/12Z. -/
abbrev PitchClass := ZMod 12

/-- A pitch class set is a function from pitch classes to Z₂.
    This is the characteristic function representation. -/
def PitchClassSet := PitchClass → ZMod 2

namespace PitchClass

-- Named pitch classes for convenience
def F  : PitchClass := 0
def Fs : PitchClass := 1   -- F#/Gb
def G  : PitchClass := 2
def Gs : PitchClass := 3   -- G#/Ab
def A  : PitchClass := 4
def As : PitchClass := 5   -- A#/Bb
def B  : PitchClass := 6
def C  : PitchClass := 7
def Cs : PitchClass := 8   -- C#/Db
def D  : PitchClass := 9
def Ds : PitchClass := 10  -- D#/Eb
def E  : PitchClass := 11

/-!
## Fin 12 ↔ ZMod 12 Interface

Mathlib provides natural conversions between Fin n and ZMod n.
We can use the coercion `(i : Fin 12) → (i : ZMod 12)` directly.
-/

/-- Convert from Fin 12 to PitchClass (ZMod 12) -/
def ofFin (i : Fin 12) : PitchClass := i

/-- Convert from PitchClass to Fin 12 -/
def toFin (pc : PitchClass) : Fin 12 := ⟨pc.val, pc.val_lt⟩

end PitchClass

namespace PitchClassSet

/-- The empty pitch class set (no pitches). Identity for XOR. -/
def empty : PitchClassSet := fun _ => 0

/-- The universal set (all pitches). -/
def universal : PitchClassSet := fun _ => 1

/-- XOR of two pitch class sets (pointwise addition in Z₂). -/
def xor (a b : PitchClassSet) : PitchClassSet := fun i => a i + b i

/-- A singleton pitch class set containing just one pitch. -/
def singleton (pc : PitchClass) : PitchClassSet := fun i => if i = pc then 1 else 0

/-- Build a PCS from a list of pitch classes -/
def fromList (pcs : List PitchClass) : PitchClassSet :=
  fun i => if pcs.contains i then 1 else 0

/-- Check membership -/
def mem (pc : PitchClass) (pcs : PitchClassSet) : Prop := pcs pc = 1

-- Note: `pc ∈ pcs` means `mem pc pcs`
-- Membership α β has `mem : β → α → Prop` (container first, element second)
instance : Membership PitchClass PitchClassSet where
  mem := fun (pcs : PitchClassSet) (pc : PitchClass) => pcs pc = 1

/-!
## XOR Group Structure

PitchClassSet forms an abelian group under XOR:
- Identity: empty set
- Inverse: each element is its own inverse (a ⊕ a = ∅)
- This is (Z₂)^12
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
  have h : a i + a i = 0 := by
    have : (2 : ZMod 2) = 0 := rfl
    calc a i + a i = 2 * a i := by ring
      _ = 0 * a i := by rw [this]
      _ = 0 := by ring
  exact h

/-!
## Transposition (Domain Action)

Transposition acts on the domain Z₁₂. Transposing by k shifts all pitches up by k.
This is the regular action of Z₁₂ on itself.
-/

/-- Transpose a pitch class set by k semitones.
    If C was in the set, now C+k is in the set. -/
def transpose (k : PitchClass) (pcs : PitchClassSet) : PitchClassSet :=
  fun i => pcs (i - k)

theorem transpose_zero (pcs : PitchClassSet) : transpose 0 pcs = pcs := by
  funext i
  simp [transpose]

theorem transpose_add (j k : PitchClass) (pcs : PitchClassSet) :
    transpose j (transpose k pcs) = transpose (j + k) pcs := by
  funext i
  simp only [transpose]
  ring_nf

theorem transpose_neg (k : PitchClass) (pcs : PitchClassSet) :
    transpose (-k) (transpose k pcs) = pcs := by
  rw [transpose_add, neg_add_cancel, transpose_zero]

/-!
## XOR Transform (Codomain Action)

Each PitchClassSet acts as a transformation via XOR.
This toggles membership of specific pitch classes.
-/

/-- Apply a PCS as a transformation mask to another PCS -/
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

/-!
## Interaction: XOR and Transposition

These two operations interact nicely - transposition distributes over XOR.
-/

theorem transpose_xor (k : PitchClass) (a b : PitchClassSet) :
    transpose k (xor a b) = xor (transpose k a) (transpose k b) := by
  funext i
  simp [transpose, xor]

theorem transpose_empty (k : PitchClass) : transpose k empty = empty := by
  funext i
  simp [transpose, empty]

theorem transpose_singleton (k : PitchClass) (pc : PitchClass) :
    transpose k (singleton pc) = singleton (pc + k) := by
  funext i
  simp only [transpose, singleton]
  by_cases h : i - k = pc
  · simp [sub_eq_iff_eq_add.mp h]
  · simp only [h, ↓reduceIte]
    by_cases h2 : i = pc + k
    · exfalso
      apply h
      rw [h2]
      ring
    · simp [h2]

/-!
## Transpose-XOR Equivalence

For any PCS s and transposition k, there exists a unique mask m such that
`transpose k s = xor m s`. This mask is the symmetric difference `xor s (transpose k s)`.

This shows that transposition can always be "simulated" by XOR with the right mask,
though the mask depends on the input PCS.
-/

/-- The mask that transforms s into (transpose k s) via XOR -/
def transposeAsMask (k : PitchClass) (s : PitchClassSet) : PitchClassSet :=
  xor s (transpose k s)

/-- Transposition equals XOR with the transpose-as-mask -/
theorem transpose_eq_xor_mask (k : PitchClass) (s : PitchClassSet) :
    transpose k s = xor (transposeAsMask k s) s := by
  simp only [transposeAsMask]
  rw [xor_comm, ← xor_assoc, xor_self, xor_empty_left]

/-- The mask is unique: if transpose k s = xor m s, then m = transposeAsMask k s -/
theorem transposeAsMask_unique (k : PitchClass) (s : PitchClassSet) (m : PitchClassSet)
    (h : transpose k s = xor m s) : m = transposeAsMask k s := by
  simp only [transposeAsMask]
  -- xor both sides with s
  have : xor (transpose k s) s = xor (xor m s) s := by rw [h]
  rw [xor_assoc, xor_self, xor_empty_right] at this
  rw [xor_comm, this]

/-!
## Fixed Points and Symmetry

A PCS is k-symmetric if transposing by k gives the same set.
For such sets, the transposeAsMask is empty.
-/

/-- A PCS is k-symmetric if transpose k s = s -/
def isSymmetric (k : PitchClass) (s : PitchClassSet) : Prop :=
  transpose k s = s

/-- For k-symmetric sets, transposition by k equals identity (xor with empty) -/
theorem symmetric_mask_empty (k : PitchClass) (s : PitchClassSet) (h : isSymmetric k s) :
    transposeAsMask k s = empty := by
  simp only [transposeAsMask, isSymmetric] at *
  rw [h, xor_self]

/-- Tritone: the interval of 6 semitones -/
def tritone : PitchClass := 6

/-- Example: {C, F#} is tritone-symmetric -/
def C_Fs : PitchClassSet := xor (singleton PitchClass.C) (singleton PitchClass.Fs)

theorem C_Fs_symmetric : isSymmetric tritone C_Fs := by
  simp only [isSymmetric, tritone, C_Fs]
  rw [transpose_xor, transpose_singleton, transpose_singleton]
  simp only [PitchClass.C, PitchClass.Fs]
  -- After transposition: singleton 6 xor singleton 0 = singleton 0 xor singleton 6
  -- This follows by commutativity of xor
  exact xor_comm _ _

/-- The whole-tone scale starting on F -/
def F_wholetone : PitchClassSet :=
  fromList [PitchClass.F, PitchClass.G, PitchClass.A, PitchClass.B, PitchClass.Cs, PitchClass.Ds]

/-- A whole step interval -/
def wholestep : PitchClass := 2

/-- The whole-tone scale is symmetric under transposition by a whole step -/
theorem F_wholetone_wholestep_symmetric : isSymmetric wholestep F_wholetone := by
  simp only [isSymmetric, wholestep, F_wholetone]
  funext i
  simp only [transpose, fromList]
  -- The whole-tone scale contains exactly the even pitch classes (0,2,4,6,8,10)
  -- Subtracting 2 from any even number gives another even number (mod 12)
  fin_cases i <;> rfl

/-- The diatonic scale (F Lydian / C major) -/
def diatonic : PitchClassSet :=
  fromList [PitchClass.F, PitchClass.G, PitchClass.A, PitchClass.B,
            PitchClass.C, PitchClass.D, PitchClass.E]

/-- The mask that transforms whole-tone to diatonic -/
def wholetone_diatonic_mask : PitchClassSet :=
  fromList [PitchClass.C, PitchClass.Cs, PitchClass.D, PitchClass.Ds, PitchClass.E]
  -- {7, 8, 9, 10, 11} in our numbering

/-- The diatonic scale is the whole-tone scale XOR'd with the mask -/
theorem diatonic_eq_wholetone_xor_mask :
    diatonic = xor wholetone_diatonic_mask F_wholetone := by
  simp only [diatonic, F_wholetone, wholetone_diatonic_mask, fromList, xor]
  funext i
  fin_cases i <;> rfl

/-!
## Mask-Transposition Interaction

Key insight: XOR masks and transposition interact via conjugation.
If we want to transform a transposed set, we can either:
1. Transpose first, then apply mask
2. Apply a transposed mask, then transpose

This is because transposition distributes over XOR.
-/

/-- Transposing then masking = masking with transposed mask then transposing -/
theorem mask_transpose_conjugate (mask : PitchClassSet) (k : PitchClass) (s : PitchClassSet) :
    xor mask (transpose k s) = transpose k (xor (transpose (-k) mask) s) := by
  rw [transpose_xor]
  congr 1
  -- Need: mask = transpose k (transpose (-k) mask)
  rw [transpose_add, add_neg_cancel, transpose_zero]

/-- The mask to get from wholetone to a transposed diatonic -/
def diatonic_mask_for_transposition (k : PitchClass) : PitchClassSet :=
  transpose k wholetone_diatonic_mask

/-!
## The Two Whole-Tone Scales

There are exactly two whole-tone scales (related by transposition by 1).
Every diatonic scale can be expressed as XOR of one of these with an appropriate mask.
-/

/-- The other whole-tone scale (starting on F#) -/
def Fs_wholetone : PitchClassSet :=
  fromList [PitchClass.Fs, PitchClass.Gs, PitchClass.As, PitchClass.C, PitchClass.D, PitchClass.E]

/-- Transposing wholetone by any even amount returns wholetone (direct check) -/
theorem transpose_wholetone_0 : transpose 0 F_wholetone = F_wholetone := transpose_zero _
theorem transpose_wholetone_2 : transpose 2 F_wholetone = F_wholetone := by
  simp only [F_wholetone, fromList, transpose]; funext i; fin_cases i <;> rfl
theorem transpose_wholetone_4 : transpose 4 F_wholetone = F_wholetone := by
  simp only [F_wholetone, fromList, transpose]; funext i; fin_cases i <;> rfl
theorem transpose_wholetone_6 : transpose 6 F_wholetone = F_wholetone := by
  simp only [F_wholetone, fromList, transpose]; funext i; fin_cases i <;> rfl
theorem transpose_wholetone_8 : transpose 8 F_wholetone = F_wholetone := by
  simp only [F_wholetone, fromList, transpose]; funext i; fin_cases i <;> rfl
theorem transpose_wholetone_10 : transpose 10 F_wholetone = F_wholetone := by
  simp only [F_wholetone, fromList, transpose]; funext i; fin_cases i <;> rfl

/-- Transposing wholetone by 1 gives Fs_wholetone -/
theorem transpose_wholetone_1 : transpose 1 F_wholetone = Fs_wholetone := by
  simp only [F_wholetone, Fs_wholetone, fromList, transpose]; funext i; fin_cases i <;> rfl

theorem Fs_wholetone_eq_transpose : Fs_wholetone = transpose 1 F_wholetone := by
  simp only [Fs_wholetone, F_wholetone, fromList, transpose]
  funext i
  fin_cases i <;> rfl

/-- The two whole-tone scales partition the chromatic scale -/
theorem wholetone_partition : xor F_wholetone Fs_wholetone = universal := by
  simp only [F_wholetone, Fs_wholetone, fromList]
  funext i
  fin_cases i <;> rfl

/-!
## Characterizing the Mask

The wholetone-diatonic mask {7,8,9,10,11} has special structure:
- It's a contiguous chromatic cluster of 5 notes
- It's the complement of {0,1,2,3,4,5,6} which is... 7 notes!
- Wait, that's not quite right. Let's compute the complement.
-/

/-- Complement of a PCS -/
def complement (s : PitchClassSet) : PitchClassSet := xor s universal

theorem complement_involutive : Function.Involutive complement := by
  intro s
  simp only [complement]
  rw [xor_assoc, xor_self, xor_empty_right]

/-- The mask's complement -/
def wholetone_diatonic_mask_complement : PitchClassSet :=
  complement wholetone_diatonic_mask

theorem mask_complement_is_7_notes :
    wholetone_diatonic_mask_complement =
    fromList [PitchClass.F, PitchClass.Fs, PitchClass.G, PitchClass.Gs,
              PitchClass.A, PitchClass.As, PitchClass.B] := by
  simp only [wholetone_diatonic_mask_complement, complement, wholetone_diatonic_mask]
  funext i
  fin_cases i <;> rfl

/-!
## Complement Mask and the Other Whole-Tone Scale

The complement mask applied to F_wholetone gives pentatonic (5 notes).
But applied to Fs_wholetone (the other whole-tone), it gives diatonic!

This reveals a beautiful symmetry: each whole-tone scale pairs with one of
the two masks (original or complement) to produce diatonic.
-/

/-- The pentatonic scale (complement of diatonic) -/
def pentatonic : PitchClassSet :=
  fromList [PitchClass.Fs, PitchClass.Gs, PitchClass.As, PitchClass.Cs, PitchClass.Ds]

theorem pentatonic_eq_diatonic_complement : pentatonic = complement diatonic := by
  simp only [pentatonic, diatonic, complement, fromList]
  funext i
  fin_cases i <;> rfl

/-- Complement mask on F_wholetone gives pentatonic -/
theorem complement_mask_F_wholetone_eq_pentatonic :
    xor wholetone_diatonic_mask_complement F_wholetone = pentatonic := by
  simp only [wholetone_diatonic_mask_complement, complement, wholetone_diatonic_mask,
             F_wholetone, pentatonic, fromList]
  funext i
  fin_cases i <;> rfl

/-- Complement mask on Fs_wholetone gives diatonic! -/
theorem complement_mask_Fs_wholetone_eq_diatonic :
    xor wholetone_diatonic_mask_complement Fs_wholetone = diatonic := by
  simp only [wholetone_diatonic_mask_complement, complement, wholetone_diatonic_mask,
             Fs_wholetone, diatonic, fromList]
  funext i
  fin_cases i <;> rfl

/-- Original mask on Fs_wholetone gives pentatonic -/
theorem mask_Fs_wholetone_eq_pentatonic :
    xor wholetone_diatonic_mask Fs_wholetone = pentatonic := by
  simp only [wholetone_diatonic_mask, Fs_wholetone, pentatonic, fromList]
  funext i
  fin_cases i <;> rfl

/-!
Summary of the 2x2 structure:

                    | F_wholetone (evens)  | Fs_wholetone (odds)
--------------------|----------------------|---------------------
mask {7,8,9,10,11}  | diatonic             | pentatonic
mask {0,1,2,3,4,5,6}| pentatonic           | diatonic

The two whole-tone scales and two complementary masks give exactly
{diatonic, pentatonic} in a symmetric pattern!
-/

end PitchClassSet
