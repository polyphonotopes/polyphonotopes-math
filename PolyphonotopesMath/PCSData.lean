import PolyphonotopesMath.Basic
import Lean.Data.Json
import Lean.Data.Json.FromToJson

/-!
# Pitch Class Set Data Loader

Loads scales, chords, and intervals from JSON. Uses precomputed bitset
representations and normal forms for fast lookup.
-/

namespace PCSData

open Lean Json PitchClassSet

/-- A named pitch class set with precomputed bits and normal form -/
structure NamedPCS where
  name : String
  bits : Nat
  normalFormBits : Nat
  aliases : List String := []
  deriving Repr

/-- The full data structure matching tonal-pcs.json -/
structure TonalData where
  intervals : List (String × Nat)
  scales : List NamedPCS
  chords : List NamedPCS
  deriving Repr

/-- Parse a JSON object into NamedPCS list -/
def parseNamedPCSMap (json : Json) : Except String (List NamedPCS) := do
  let obj ← json.getObj?
  let mut result := []
  for (name, value) in obj.toArray do
    let bits ← value.getObjVal? "bits" >>= (·.getNat?)
    let normalFormBits ← value.getObjVal? "normalFormBits" >>= (·.getNat?)
    let aliases : List String :=
      if let Except.ok aliasesJson := value.getObjVal? "aliases" then
        if let Except.ok aliasArr := aliasesJson.getArr? then
          aliasArr.toList.filterMap (·.getStr?.toOption)
        else []
      else []
    result := result ++ [{ name, bits, normalFormBits, aliases }]
  return result

/-- Parse intervals from JSON -/
def parseIntervals (json : Json) : Except String (List (String × Nat)) := do
  let obj ← json.getObj?
  let mut result := []
  for (name, value) in obj.toArray do
    let pc ← value.getNat?
    result := result ++ [(name, pc)]
  return result

/-- Parse the full tonal-pcs.json structure -/
def parseTonalData (json : Json) : Except String TonalData := do
  let intervalsJson ← json.getObjVal? "intervals"
  let scalesJson ← json.getObjVal? "scales"
  let chordsJson ← json.getObjVal? "chords"
  let intervals ← parseIntervals intervalsJson
  let scales ← parseNamedPCSMap scalesJson
  let chords ← parseNamedPCSMap chordsJson
  return { intervals, scales, chords }

/-- Load tonal data from a JSON file -/
def loadFromFile (path : System.FilePath) : IO (Except String TonalData) := do
  let contents ← IO.FS.readFile path
  match Json.parse contents with
  | .ok json => return parseTonalData json
  | .error e => return .error s!"JSON parse error: {e}"

/-- Default path to F-centered data -/
def defaultDataPath : System.FilePath := "data/tonal-pcs-F.json"

/-- Load the default F-centered data -/
def loadDefault : IO (Except String TonalData) := loadFromFile defaultDataPath

/-! ## Lookup Functions -/

/-- Lookup by name or alias, returns bits -/
def findByName (data : TonalData) (query : String) : Option Nat :=
  let inScales := data.scales.find? (fun s => s.name == query || s.aliases.contains query)
  let inChords := data.chords.find? (fun c => c.name == query || c.aliases.contains query)
  (inScales <|> inChords).map (·.bits)

/-- Find all entries matching a normal form -/
def findByNormalForm (data : TonalData) (queryNF : Nat) : List String :=
  let scaleHits := data.scales.filterMap fun s =>
    if s.normalFormBits == queryNF then some s.name else none
  let chordHits := data.chords.filterMap fun c =>
    if c.normalFormBits == queryNF then some c.name else none
  scaleHits ++ chordHits

/-- Rotate bits by k positions (for transposition) -/
def rotateBits (bits : Nat) (k : Nat) : Nat :=
  let mask := (1 <<< 12) - 1
  ((bits <<< k) ||| (bits >>> (12 - k))) &&& mask

/-- Find entries matching query bits, with transposition amount -/
def findExact (data : TonalData) (queryBits : Nat) : List (String × Nat) :=
  let tryAll (entries : List NamedPCS) :=
    entries.flatMap fun e =>
      (List.range 12).filterMap fun (k : Nat) =>
        if rotateBits e.bits k == queryBits then some (e.name, k) else none
  tryAll data.scales ++ tryAll data.chords

/-! ## Normal Form Computation (for queries) -/

/-- Get pitch classes from bits -/
def bitsToList (bits : Nat) : List Nat :=
  (List.range 12).filter (fun i => (bits >>> i) &&& 1 = 1)

/-- Interval vector (gaps between adjacent notes) -/
def intervalVector (pcs : List Nat) : List Nat :=
  match pcs with
  | [] => []
  | [_] => [12]
  | first :: rest =>
    let pairs := pcs.zip (rest ++ [first + 12])
    pairs.map (fun (a, b) => b - a)

/-- Compare interval vectors lexicographically -/
def ivLt (iv1 iv2 : List Nat) : Bool :=
  match iv1, iv2 with
  | [], [] => false
  | [], _ => true
  | _, [] => false
  | a :: as, b :: bs => if a < b then true else if a > b then false else ivLt as bs

/-- Compute normal form bits for arbitrary input -/
def normalFormBits (bits : Nat) : Nat :=
  let pcs := bitsToList bits
  if pcs.isEmpty then 0
  else
    let rotations := (List.range 12).map fun k =>
      let rotated := pcs.map (fun pc => (pc + 12 - k) % 12) |>.mergeSort (· ≤ ·)
      (rotated, intervalVector rotated)
    let sorted := rotations.mergeSort (fun (_, iv1) (_, iv2) => ivLt iv1 iv2)
    match sorted.head? with
    | some (r, _) => r.foldl (fun acc pc => acc ||| (1 <<< pc)) 0
    | none => bits

/-! ## Linear Algebra over Z₂

PitchClassSet ≃ (ZMod 2)^12 is a vector space over ZMod 2.
Diffs form a subspace. Mathlib provides the linear algebra.

Note: PitchClassSet = PitchClass → ZMod 2 already has Module (ZMod 2) structure
via Mathlib's Pi.module instance.
-/

/-- All diffs between elements of a list (as bits) -/
def allDiffs (bits : List Nat) : List Nat :=
  (bits.flatMap fun a => bits.map fun b => a ^^^ b).eraseDups

/-- Find the position of the highest set bit (0-indexed from right) -/
def highBit (n : Nat) : Nat :=
  if n = 0 then 0 else Nat.log2 n

/-- Row reduce over Z₂ using echelon form. basis[i] has leading bit i. -/
def rowReduceZ2 (rows : List Nat) : List Nat :=
  -- basis is a list of 12 slots, one per bit position
  let emptyBasis : List Nat := List.replicate 12 0
  let finalBasis := rows.foldl (fun basis r =>
    -- Reduce r using existing basis vectors
    let r' := (List.range 12).foldl (fun acc i =>
      if acc != 0 && (acc >>> i) &&& 1 = 1 && basis[i]! != 0
      then acc ^^^ basis[i]!
      else acc) r
    -- If r' is non-zero, add it at its leading bit position
    if r' = 0 then basis
    else basis.set (highBit r') r'
  ) emptyBasis
  finalBasis.filter (· != 0)

/-- Rank = dimension of subspace spanned by bits -/
def rankZ2 (bits : List Nat) : Nat := (rowReduceZ2 bits).length

/-- Generators for the subspace -/
def generatorsZ2 (bits : List Nat) : List Nat := rowReduceZ2 bits

/-- Population count (number of 1 bits) -/
def popCount (n : Nat) : Nat :=
  (List.range 12).foldl (fun acc i => acc + ((n >>> i) &&& 1)) 0

/-- Show bits as binary string (12 bits, LSB = C) -/
def showBin (bits : Nat) : String :=
  "0b" ++ String.ofList ((List.range 12).reverse.map fun i =>
    if (bits >>> i) &&& 1 = 1 then '1' else '0')

/-- Show bits as pitch class set (C=0 convention) with binary, normal form, and indices -/
def showPCS (bits : Nat) : String :=
  let names := #["C", "C#", "D", "D#", "E", "F", "F#", "G", "G#", "A", "A#", "B"]
  let pcs := (List.range 12).filter fun i => (bits >>> i) &&& 1 = 1
  let indices := "{" ++ String.intercalate "," (pcs.map toString) ++ "}"
  let noteNames := "{" ++ String.intercalate ", " (pcs.map fun i => names[i]!) ++ "}"
  let nf := normalFormBits bits
  showBin bits ++ " nf=" ++ showBin nf ++ " " ++ indices ++ " " ++ noteNames

/-- Show a list of bits as pitch class sets -/
def showPCSList (bits : List Nat) : List String :=
  bits.map showPCS

/-- Example: major scale orbit (12 transpositions) -/
def majorScaleOrbit : List Nat :=
  (List.range 12).map fun k => rotateBits 0b101010110101 k

/-- Pentatonic scale: {0, 2, 4, 7, 9} in C=0 convention -/
def pentatonicScaleOrbit : List Nat :=
  (List.range 12).map fun k => rotateBits 0b001010010101 k

-- Major scale analysis
#eval showPCSList (generatorsZ2 (allDiffs majorScaleOrbit))

-- Pentatonic scale analysis
#eval showPCSList (generatorsZ2 (allDiffs pentatonicScaleOrbit))

-- All 12 chromatic semitone pairs
def chromaticSemitones : List Nat :=
  (List.range 12).map fun k => rotateBits 0b000000000011 k

#eval s!"Chromatic semitones rank: {rankZ2 chromaticSemitones}"
#eval showPCSList (generatorsZ2 chromaticSemitones)

-- All 12 minor thirds {0,3}
def minorThirds : List Nat :=
  (List.range 12).map fun k => rotateBits 0b000000001001 k

#eval s!"Minor thirds rank: {rankZ2 minorThirds}"
#eval showPCSList (generatorsZ2 minorThirds)

-- All 12 whole tones {0,2}
def wholeTones : List Nat :=
  (List.range 12).map fun k => rotateBits 0b000000000101 k

#eval s!"Whole tones rank: {rankZ2 wholeTones}"
#eval showPCSList (generatorsZ2 wholeTones)

-- Greedy minimum-weight basis: sort by popcount, add if independent
def greedyMinWeightBasis (diffs : List Nat) : List Nat :=
  let sorted := diffs.mergeSort (fun a b => popCount a < popCount b)
  sorted.foldl (fun basis v =>
    -- Check if v is independent from current basis
    let reduced := basis.foldl (fun acc b =>
      if acc != 0 && (acc &&& b) != 0 then acc ^^^ b else acc) v
    if reduced != 0 && !basis.contains v then basis ++ [v] else basis
  ) []

-- This isn't quite right - need proper independence check
-- Let's use: try to add, check if rank increases
def greedyMinWeightBasis' (diffs : List Nat) : List Nat :=
  let sorted := diffs.eraseDups.mergeSort (fun a b => popCount a < popCount b)
  sorted.foldl (fun basis v =>
    if rankZ2 (basis ++ [v]) > rankZ2 basis then basis ++ [v] else basis
  ) []

#eval "Minimum-weight basis for major scale diffs:"
#eval showPCSList (greedyMinWeightBasis' (allDiffs majorScaleOrbit))

#eval "Minimum-weight basis for pentatonic diffs:"
#eval showPCSList (greedyMinWeightBasis' (allDiffs pentatonicScaleOrbit))

-- Major triad: {0, 4, 7} = root, major 3rd, perfect 5th
def majorTriadOrbit : List Nat :=
  (List.range 12).map fun k => rotateBits 0b000010010001 k

#eval s!"Major triad diffs rank: {rankZ2 (allDiffs majorTriadOrbit)}"
#eval "Minimum-weight basis for major triad diffs:"
#eval showPCSList (greedyMinWeightBasis' (allDiffs majorTriadOrbit))

-- Diminished scale (octatonic): half-whole = {0,1,3,4,6,7,9,10}
-- Only 3 distinct diminished scales (due to symmetry)
def diminishedScaleOrbit : List Nat :=
  (List.range 12).map fun k => rotateBits 0b011011011011 k

#eval s!"Diminished scale orbit size: {diminishedScaleOrbit.eraseDups.length}"
#eval s!"Diminished scale diffs rank: {rankZ2 (allDiffs diminishedScaleOrbit)}"
#eval "Minimum-weight basis for diminished scale diffs:"
#eval showPCSList (greedyMinWeightBasis' (allDiffs diminishedScaleOrbit))

-- Diminished triad: {0, 3, 6} = root, minor 3rd, diminished 5th
def diminishedTriadOrbit : List Nat :=
  (List.range 12).map fun k => rotateBits 0b000001001001 k

#eval s!"Diminished triad orbit size: {diminishedTriadOrbit.eraseDups.length}"
#eval s!"Diminished triad diffs rank: {rankZ2 (allDiffs diminishedTriadOrbit)}"
#eval "Minimum-weight basis for diminished triad diffs:"
#eval showPCSList (greedyMinWeightBasis' (allDiffs diminishedTriadOrbit))

-- Fully diminished 7th: {0, 3, 6, 9} - has minor 3rd symmetry
def dim7Orbit : List Nat :=
  (List.range 12).map fun k => rotateBits 0b001001001001 k

#eval s!"Dim7 orbit size: {dim7Orbit.eraseDups.length}"
#eval s!"Dim7 diffs rank: {rankZ2 (allDiffs dim7Orbit)}"
#eval "Minimum-weight basis for dim7 diffs:"
#eval showPCSList (greedyMinWeightBasis' (allDiffs dim7Orbit))

-- Whole-tone scale: {0, 2, 4, 6, 8, 10}
def wholeToneScaleOrbit : List Nat :=
  (List.range 12).map fun k => rotateBits 0b010101010101 k

#eval s!"Whole-tone orbit size: {wholeToneScaleOrbit.eraseDups.length}"
#eval s!"Whole-tone diffs rank: {rankZ2 (allDiffs wholeToneScaleOrbit)}"
#eval "Minimum-weight basis for whole-tone diffs:"
#eval showPCSList (greedyMinWeightBasis' (allDiffs wholeToneScaleOrbit))

-- Mixed sets: union of orbits
#eval "--- MIXED SETS ---"

-- Major + Minor triads
def minorTriadOrbit : List Nat :=
  (List.range 12).map fun k => rotateBits 0b000010001001 k  -- {0, 3, 7}

def majorMinorTriads : List Nat := majorTriadOrbit ++ minorTriadOrbit

#eval s!"Major+Minor triads orbit size: {majorMinorTriads.eraseDups.length}"
#eval s!"Major+Minor triads diffs rank: {rankZ2 (allDiffs majorMinorTriads)}"
#eval "Minimum-weight basis:"
#eval showPCSList (greedyMinWeightBasis' (allDiffs majorMinorTriads))

-- Major diatonic + Melodic minor
def melodicMinorOrbit : List Nat :=
  (List.range 12).map fun k => rotateBits 0b101011010101 k  -- {0, 2, 3, 5, 7, 9, 11}

def diatonicMelodicMinor : List Nat := majorScaleOrbit ++ melodicMinorOrbit

#eval s!"Diatonic+MelodicMinor orbit size: {diatonicMelodicMinor.eraseDups.length}"
#eval s!"Diatonic+MelodicMinor diffs rank: {rankZ2 (allDiffs diatonicMelodicMinor)}"
#eval "Minimum-weight basis:"
#eval showPCSList (greedyMinWeightBasis' (allDiffs diatonicMelodicMinor))

-- Cross-orbit diffs: what's the diff between C major and C minor triad?
def cMajor : Nat := 0b000010010001  -- {0, 4, 7}
def cMinor : Nat := 0b000010001001  -- {0, 3, 7}

#eval "C major XOR C minor ="
#eval showPCS (cMajor ^^^ cMinor)  -- should be {3,4} = semitone!

-- What are the smallest cross-diffs between major and minor orbits?
def crossDiffs : List Nat :=
  (majorTriadOrbit.flatMap fun m => minorTriadOrbit.map fun n => m ^^^ n).eraseDups

#eval s!"Cross-diffs (major↔minor) min weight: {(crossDiffs.map popCount).foldl min 12}"
#eval "Smallest cross-diffs:"
#eval showPCSList (crossDiffs.filter fun d => popCount d ≤ 2)

end PCSData
