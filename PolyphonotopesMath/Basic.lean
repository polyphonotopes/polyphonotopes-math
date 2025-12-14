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

/-- Build a PCS from a 12-bit integer (bitset representation).
    Bit i is set iff pitch class i is in the set. -/
def fromBits (bits : Nat) : PitchClassSet :=
  fun i => if (bits >>> i.val) &&& 1 = 1 then 1 else 0

/-- Convert a PCS to a 12-bit integer -/
def toBits (pcs : PitchClassSet) : Nat :=
  (List.finRange 12).foldl (fun acc i => acc ||| (if pcs i = 1 then 1 <<< i.val else 0)) 0

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

/-!
## Cardinality

We can count the number of pitch classes in a PCS.
XOR affects cardinality based on overlap with the mask.
-/

/-- Count the number of pitch classes in a PCS -/
def card (s : PitchClassSet) : ℕ :=
  (List.filter (fun i => s i = 1) (List.finRange 12)).length

theorem card_empty : card empty = 0 := rfl
theorem card_universal : card universal = 12 := rfl
theorem card_singleton_C : card (singleton PitchClass.C) = 1 := rfl

theorem card_F_wholetone : card F_wholetone = 6 := rfl
theorem card_Fs_wholetone : card Fs_wholetone = 6 := rfl
theorem card_diatonic : card diatonic = 7 := rfl
theorem card_pentatonic : card pentatonic = 5 := rfl
theorem card_wholetone_diatonic_mask : card wholetone_diatonic_mask = 5 := rfl
theorem card_wholetone_diatonic_mask_complement : card wholetone_diatonic_mask_complement = 7 := rfl

/-!
## Cardinality Change Under XOR

When XORing s with mask m:
- Notes in (m ∩ s) are removed
- Notes in (m \ s) are added
- Net change = |m| - 2|m ∩ s|

For wholetone (6 notes):
- mask {7,8,9,10,11} (5 notes) overlaps at {8,10} (2 notes): 6 + 5 - 2*2 = 7 ✓
- mask {0,1,2,3,4,5,6} (7 notes) overlaps at {0,2,4,6} (4 notes): 6 + 7 - 2*4 = 5 ✓
-/

/-- Intersection of two PCS (pointwise AND, i.e., multiplication in Z₂) -/
def inter (a b : PitchClassSet) : PitchClassSet := fun i => a i * b i

/-- The diatonic mask overlaps wholetone at exactly 2 notes -/
theorem diatonic_mask_overlap : card (inter wholetone_diatonic_mask F_wholetone) = 2 := rfl

/-- Verify the cardinality formula for diatonic case: 6 + 5 - 2*2 = 7 -/
theorem card_xor_diatonic_example :
    card (xor wholetone_diatonic_mask F_wholetone) =
    card F_wholetone + card wholetone_diatonic_mask - 2 * card (inter wholetone_diatonic_mask F_wholetone) := rfl

end PitchClassSet

/-!
## Standard Scales (C = 0 convention)

Scale data derived from tonal.js: https://github.com/tonaljs/tonal

Note: These use standard music theory convention where C = 0.
Our PitchClass namespace uses F = 0 for circle-of-fifths alignment.
To convert: add 7 (mod 12) to go from C=0 to F=0.
-/

namespace StandardScales

open PitchClassSet

/-- major pentatonic: {0, 2, 4, 7, 9} -/
def major_pentatonic : PitchClassSet := fromBits 0b001010010101

/-- major (ionian): {0, 2, 4, 5, 7, 9, 11} -/
def major : PitchClassSet := fromBits 0b101010110101

/-- minor (aeolian): {0, 2, 3, 5, 7, 8, 10} -/
def minor : PitchClassSet := fromBits 0b010110101101

/-- melodic minor: {0, 2, 3, 5, 7, 9, 11} -/
def melodic_minor : PitchClassSet := fromBits 0b101010101101

/-- harmonic minor: {0, 2, 3, 5, 7, 8, 11} -/
def harmonic_minor : PitchClassSet := fromBits 0b100110101101

/-- dorian: {0, 2, 3, 5, 7, 9, 10} -/
def dorian : PitchClassSet := fromBits 0b011010101101

/-- phrygian: {0, 1, 3, 5, 7, 8, 10} -/
def phrygian : PitchClassSet := fromBits 0b010110101011

/-- lydian: {0, 2, 4, 6, 7, 9, 11} -/
def lydian : PitchClassSet := fromBits 0b101011010101

/-- mixolydian: {0, 2, 4, 5, 7, 9, 10} -/
def mixolydian : PitchClassSet := fromBits 0b011010110101

/-- locrian: {0, 1, 3, 5, 6, 8, 10} -/
def locrian : PitchClassSet := fromBits 0b010101101011

/-- minor pentatonic: {0, 3, 5, 7, 10} -/
def minor_pentatonic : PitchClassSet := fromBits 0b010010101001

/-- whole tone: {0, 2, 4, 6, 8, 10} -/
def whole_tone : PitchClassSet := fromBits 0b010101010101

/-- half-whole diminished (octatonic): {0, 1, 3, 4, 6, 7, 9, 10} -/
def half_whole_diminished : PitchClassSet := fromBits 0b011011011011

/-- whole-half diminished (octatonic): {0, 2, 3, 5, 6, 8, 9, 11} -/
def whole_half_diminished : PitchClassSet := fromBits 0b101101101101

/-- blues: {0, 3, 5, 6, 7, 10} -/
def blues : PitchClassSet := fromBits 0b010011101001

/-- bebop dominant: {0, 2, 4, 5, 7, 9, 10, 11} -/
def bebop : PitchClassSet := fromBits 0b111010110101

/-- augmented (hexatonic): {0, 3, 4, 7, 8, 11} -/
def augmented_scale : PitchClassSet := fromBits 0b100110011001

/-- lydian dominant: {0, 2, 4, 6, 7, 9, 10} -/
def lydian_dominant : PitchClassSet := fromBits 0b011011010101

/-- phrygian dominant (Spanish): {0, 1, 4, 5, 7, 8, 10} -/
def phrygian_dominant : PitchClassSet := fromBits 0b010110110011

/-- double harmonic (Byzantine): {0, 1, 4, 5, 7, 8, 11} -/
def double_harmonic : PitchClassSet := fromBits 0b100110110011

/-- hungarian minor: {0, 2, 3, 6, 7, 8, 11} -/
def hungarian_minor : PitchClassSet := fromBits 0b100111001101

-- Symmetric scales
/-- chromatic: all 12 pitch classes -/
def chromatic : PitchClassSet := fromBits 0b111111111111

/-- diminished 7th chord: {0, 3, 6, 9} -/
def dim7 : PitchClassSet := fromBits 0b001001001001

/-- augmented triad: {0, 4, 8} -/
def aug : PitchClassSet := fromBits 0b000100010001

/-- tritone: {0, 6} -/
def tritone : PitchClassSet := fromBits 0b000001000001

end StandardScales

/-!
## Enriched Groupoid Structure

For any subset S ⊆ PCS, we get a groupoid enriched over (PCS, ⊕, ∅):
- Objects: elements of S
- Hom(A, B) = A ⊕ B (the diff)
- Composition: ⊕
- Identity: ∅

This gives us a way to study structure-preserving operations within S.
-/

namespace EnrichedGroupoid

open PitchClassSet

/-- The diff (symmetric difference) between two PCS -/
def diff (A B : PitchClassSet) : PitchClassSet := xor A B

/-- Diff is symmetric -/
theorem diff_comm (A B : PitchClassSet) : diff A B = diff B A := xor_comm A B

/-- Diff with self is empty -/
theorem diff_self (A : PitchClassSet) : diff A A = empty := xor_self A

/-- Composition of diffs -/
theorem diff_comp (A B C : PitchClassSet) :
    xor (diff A B) (diff B C) = diff A C := by
  simp only [diff, PitchClassSet.xor]
  funext i
  -- In Z₂: (A + B) + (B + C) = A + C because B + B = 0
  have h : B i + B i = 0 := by
    have : (2 : ZMod 2) = 0 := rfl
    calc B i + B i = 2 * B i := by ring
      _ = 0 * B i := by rw [this]
      _ = 0 := by ring
  calc A i + B i + (B i + C i) = A i + (B i + B i) + C i := by ring
    _ = A i + 0 + C i := by rw [h]
    _ = A i + C i := by ring

/-- Hom(A, -): all diffs from A to elements of S -/
def Hom (S : Set PitchClassSet) (A : PitchClassSet) : Set PitchClassSet :=
  { diff A B | B ∈ S }

/-- Diffs: all diffs between elements of S -/
def Diffs (S : Set PitchClassSet) : Set PitchClassSet :=
  { diff A B | (A ∈ S) (B ∈ S) }

/-- Stab: diffs that work from every element of S (stabilizers) -/
def Stab (S : Set PitchClassSet) : Set PitchClassSet :=
  { m | ∀ A ∈ S, xor A m ∈ S }

/-- Empty is always in Stab -/
theorem empty_mem_Stab (S : Set PitchClassSet) : empty ∈ Stab S := by
  intro A hA
  rw [xor_empty_right]
  exact hA

/-- Stab is closed under xor -/
theorem Stab_closed_xor (S : Set PitchClassSet) (m n : PitchClassSet)
    (hm : m ∈ Stab S) (hn : n ∈ Stab S) : xor m n ∈ Stab S := by
  intro A hA
  rw [← xor_assoc]
  exact hn (xor A m) (hm A hA)

/-- The orbit of a PCS under transposition -/
def TransposeOrbit (A : PitchClassSet) : Set PitchClassSet :=
  { transpose k A | k : PitchClass }

/-- Major scales = orbit of major under transposition -/
def MajorScales : Set PitchClassSet := TransposeOrbit StandardScales.major

end EnrichedGroupoid
