import PolyphonotopesMath.PCS.BitOps
import PolyphonotopesMath.PCS.NormalForm
import PolyphonotopesMath.PCS.LinearAlgebra
import PolyphonotopesMath.PCS.Structures

/-!
# Pitch Class Set Library

A computational toolkit for analyzing pitch class sets as vectors in (Z₂)^12.

## Modules

- `BitOps`: Core bit operations, display functions
- `NormalForm`: Canonical form computation
- `LinearAlgebra`: Z₂ linear algebra for diff space analysis
- `Structures`: Common musical structures (scales, chords, intervals)

## Key Concepts

- **PCS as bits**: A pitch class set is a 12-bit natural number, bit i = pitch class i
- **XOR = diff**: The symmetric difference A ⊕ B gives the "voice leading" between sets
- **Diff space**: For a collection S, Diffs(S) = {A ⊕ B | A, B ∈ S} forms a Z₂ subspace
- **Minimum-weight basis**: The simplest generators for navigating within a collection
- **Cross-orbit bridges**: When mixing collections, new small-step paths emerge

## Usage

```lean
import PolyphonotopesMath.PCS

open PCS

#eval showAnalysis "Major triads" majorTriads
#eval showPCSList (minWeightBasis (allDiffs majorTriads)) (some normalFormBits)
```
-/
