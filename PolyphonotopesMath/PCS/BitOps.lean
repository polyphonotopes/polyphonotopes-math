/-!
# Pitch Class Set Bit Operations

Core operations on 12-bit representations of pitch class sets.
Convention: bit i represents pitch class i, with C=0.
-/

namespace PCS

/-- Rotate bits by k positions (transposition by k semitones) -/
def rotateBits (bits : Nat) (k : Nat) : Nat :=
  let mask := (1 <<< 12) - 1
  ((bits <<< k) ||| (bits >>> (12 - k))) &&& mask

/-- Population count (cardinality of the pitch class set) -/
def popCount (n : Nat) : Nat :=
  (List.range 12).foldl (fun acc i => acc + ((n >>> i) &&& 1)) 0

/-- Get pitch class indices from bits -/
def bitsToList (bits : Nat) : List Nat :=
  (List.range 12).filter (fun i => (bits >>> i) &&& 1 = 1)

/-- Convert list of pitch classes to bits -/
def listToBits (pcs : List Nat) : Nat :=
  pcs.foldl (fun acc pc => acc ||| (1 <<< (pc % 12))) 0

/-- Show bits as 12-bit binary string (MSB=B, LSB=C) -/
def showBin (bits : Nat) : String :=
  "0b" ++ String.ofList ((List.range 12).reverse.map fun i =>
    if (bits >>> i) &&& 1 = 1 then '1' else '0')

/-- Note names for display -/
def noteNames : Array String := #["C", "C#", "D", "D#", "E", "F", "F#", "G", "G#", "A", "A#", "B"]

/-- Show bits as pitch class set with multiple representations -/
def showPCS (bits : Nat) (showNormalForm : Option (Nat → Nat) := none) : String :=
  let pcs := bitsToList bits
  let indices := "{" ++ String.intercalate "," (pcs.map toString) ++ "}"
  let names := "{" ++ String.intercalate ", " (pcs.map fun i => noteNames[i]!) ++ "}"
  match showNormalForm with
  | some nf => showBin bits ++ " nf=" ++ showBin (nf bits) ++ " " ++ indices ++ " " ++ names
  | none => showBin bits ++ " " ++ indices ++ " " ++ names

/-- Show a list of bits as pitch class sets -/
def showPCSList (bits : List Nat) (showNormalForm : Option (Nat → Nat) := none) : List String :=
  bits.map (showPCS · showNormalForm)

/-- Generate orbit of a PCS under transposition -/
def transposeOrbit (bits : Nat) : List Nat :=
  (List.range 12).map fun k => rotateBits bits k

/-- Orbit size (accounting for internal symmetry) -/
def orbitSize (bits : Nat) : Nat :=
  (transposeOrbit bits).eraseDups.length

end PCS
