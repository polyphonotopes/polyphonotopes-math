import PolyphonotopesMath.PCS
import Lean.Data.Json
import Lean.Data.Json.FromToJson

/-!
# Pitch Class Set Data Loader

Loads scales, chords, and intervals from tonal-pcs.json files.
Uses precomputed bitset representations and normal forms.
-/

namespace PCSData

open Lean Json PCS

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

/-- Find entries matching query bits (with transposition), returns (name, transposition) -/
def findExact (data : TonalData) (queryBits : Nat) : List (String × Nat) :=
  let tryAll (entries : List NamedPCS) :=
    entries.flatMap fun e =>
      (List.range 12).filterMap fun (k : Nat) =>
        if rotateBits e.bits k == queryBits then some (e.name, k) else none
  tryAll data.scales ++ tryAll data.chords

end PCSData
