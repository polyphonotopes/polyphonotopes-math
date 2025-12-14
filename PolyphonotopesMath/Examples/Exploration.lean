import PolyphonotopesMath.PCS

/-!
# Diff Space Exploration

Interactive exploration of pitch class set diff spaces.
Run with: lake env lean --run PolyphonotopesMath/Examples/Exploration.lean
-/

open PCS

/-! ## Helper for display with normal forms -/

def showWithNF (bits : Nat) : String :=
  showPCS bits (some normalFormBits)

def showListWithNF (bits : List Nat) : List String :=
  bits.map showWithNF

/-! ## Single Structure Analysis -/

#eval "=== SCALES ==="
#eval showAnalysis "Major scale" majorScales
#eval showAnalysis "Pentatonic" (orbit pentatonicMajor)
#eval showAnalysis "Whole-tone" wholeToneScales
#eval showAnalysis "Diminished" diminishedScales
#eval showAnalysis "Melodic minor" melodicMinors

#eval "=== TRIADS ==="
#eval showAnalysis "Major triads" majorTriads
#eval showAnalysis "Minor triads" minorTriads
#eval showAnalysis "Diminished triads" diminishedTriads
#eval showAnalysis "Augmented triads" augmentedTriads

#eval "=== SEVENTH CHORDS ==="
#eval showAnalysis "Dim7 chords" dim7Chords
#eval showAnalysis "Dom7 chords" (orbit dominantSeventh)

/-! ## Interval Classes -/

#eval "=== INTERVAL CLASS RANKS ==="
#eval s!"Semitones: rank {rankZ2 allSemitones}"
#eval s!"Whole tones: rank {rankZ2 allWholeTones}"
#eval s!"Minor thirds: rank {rankZ2 allMinorThirds}"
#eval s!"Major thirds: rank {rankZ2 allMajorThirds}"
#eval s!"Tritones: rank {rankZ2 allTritones}"

/-! ## Minimum-Weight Bases -/

#eval "=== MINIMUM-WEIGHT BASES ==="

#eval "Major scale generators:"
#eval showListWithNF (minWeightBasis (allDiffs majorScales))

#eval "Major triad generators:"
#eval showListWithNF (minWeightBasis (allDiffs majorTriads))

#eval "Diminished triad generators:"
#eval showListWithNF (minWeightBasis (allDiffs diminishedTriads))

/-! ## Mixed Collections -/

#eval "=== MIXED COLLECTIONS ==="
#eval showAnalysis "Major+Minor triads" majorAndMinorTriads
#eval showAnalysis "Diatonic+MelodicMinor" diatonicAndMelodicMinor

/-! ## Cross-Orbit Analysis -/

#eval "=== CROSS-ORBIT BRIDGES ==="

def majorMinorCrossDiffs : List Nat := crossDiffs majorTriads minorTriads

#eval s!"Major↔Minor cross-diffs count: {majorMinorCrossDiffs.length}"
#eval s!"Min cross-diff weight: {(majorMinorCrossDiffs.map popCount).foldl min 12}"

#eval "Smallest cross-diffs (major↔minor):"
#eval showListWithNF (majorMinorCrossDiffs.filter fun d => popCount d ≤ 2)

-- Example: C major to C minor
#eval "C major XOR C minor ="
#eval showWithNF (majorTriad ^^^ minorTriad)

/-! ## Summary Table -/

#eval "=== SUMMARY TABLE ==="

def summaryLine (name : String) (orbit : List Nat) : String :=
  let (size, rank, minW, _) := analyzeDiffSpace orbit
  s!"{name}: orbit={size}, rank={rank}, minWeight={minW}"

#eval summaryLine "Major scale     " majorScales
#eval summaryLine "Pentatonic      " (orbit pentatonicMajor)
#eval summaryLine "Whole-tone      " wholeToneScales
#eval summaryLine "Diminished scale" diminishedScales
#eval summaryLine "Major triad     " majorTriads
#eval summaryLine "Minor triad     " minorTriads
#eval summaryLine "Dim triad       " diminishedTriads
#eval summaryLine "Aug triad       " augmentedTriads
#eval summaryLine "Dim7            " dim7Chords
#eval summaryLine "Maj+Min triads  " majorAndMinorTriads
