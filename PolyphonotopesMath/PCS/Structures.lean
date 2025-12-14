import PolyphonotopesMath.PCS.BitOps

/-!
# Common Musical Structures

Defines standard scales, chords, and intervals as 12-bit PCS representations.
All definitions use C=0 convention.
-/

namespace PCS

/-! ## Intervals (2-note sets) -/

def semitone      : Nat := 0b000000000011  -- {0,1}
def wholeTone     : Nat := 0b000000000101  -- {0,2}
def minorThird    : Nat := 0b000000001001  -- {0,3}
def majorThird    : Nat := 0b000000010001  -- {0,4}
def perfectFourth : Nat := 0b000000100001  -- {0,5}
def tritone       : Nat := 0b000001000001  -- {0,6}
def perfectFifth  : Nat := 0b000010000001  -- {0,7}

/-! ## Triads (3-note sets) -/

def majorTriad      : Nat := 0b000010010001  -- {0,4,7}
def minorTriad      : Nat := 0b000010001001  -- {0,3,7}
def diminishedTriad : Nat := 0b000001001001  -- {0,3,6}
def augmentedTriad  : Nat := 0b000100010001  -- {0,4,8}

/-! ## Seventh Chords (4-note sets) -/

def majorSeventh     : Nat := 0b100010010001  -- {0,4,7,11}
def dominantSeventh  : Nat := 0b010010010001  -- {0,4,7,10}
def minorSeventh     : Nat := 0b010010001001  -- {0,3,7,10}
def diminishedSeventh: Nat := 0b001001001001  -- {0,3,6,9}
def halfDiminished   : Nat := 0b010001001001  -- {0,3,6,10}

/-! ## Scales -/

def majorScale      : Nat := 0b101010110101  -- {0,2,4,5,7,9,11}
def naturalMinor    : Nat := 0b010110101101  -- {0,2,3,5,7,8,10}
def harmonicMinor   : Nat := 0b100110101101  -- {0,2,3,5,7,8,11}
def melodicMinor    : Nat := 0b101011010101  -- {0,2,3,5,7,9,11}
def pentatonicMajor : Nat := 0b001010010101  -- {0,2,4,7,9}
def pentatonicMinor : Nat := 0b010010101001  -- {0,3,5,7,10}
def wholeToneScale  : Nat := 0b010101010101  -- {0,2,4,6,8,10}
def diminishedScale : Nat := 0b011011011011  -- {0,1,3,4,6,7,9,10}
def chromaticScale  : Nat := 0b111111111111  -- all 12

/-! ## Orbit Constructors -/

/-- Full orbit under transposition -/
def orbit (bits : Nat) : List Nat :=
  transposeOrbit bits

/-- Deduplicated orbit (for symmetric structures) -/
def orbitUnique (bits : Nat) : List Nat :=
  (transposeOrbit bits).eraseDups

/-! ## Interval Class Orbits -/

def allSemitones   : List Nat := orbit semitone
def allWholeTones  : List Nat := orbit wholeTone
def allMinorThirds : List Nat := orbit minorThird
def allMajorThirds : List Nat := orbit majorThird
def allTritones    : List Nat := orbit tritone

/-! ## Common Structure Orbits -/

def majorTriads      : List Nat := orbit majorTriad
def minorTriads      : List Nat := orbit minorTriad
def diminishedTriads : List Nat := orbit diminishedTriad
def augmentedTriads  : List Nat := orbitUnique augmentedTriad  -- only 4 due to symmetry
def dim7Chords       : List Nat := orbitUnique diminishedSeventh  -- only 3

def majorScales      : List Nat := orbit majorScale
def melodicMinors    : List Nat := orbit melodicMinor
def wholeToneScales  : List Nat := orbitUnique wholeToneScale  -- only 2
def diminishedScales : List Nat := orbitUnique diminishedScale  -- only 3

/-! ## Mixed Collections -/

def majorAndMinorTriads : List Nat := majorTriads ++ minorTriads
def diatonicAndMelodicMinor : List Nat := majorScales ++ melodicMinors

end PCS
