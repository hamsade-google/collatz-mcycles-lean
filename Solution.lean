module

public import CollatzMCycles.Le91
public import CollatzMCycles.Trivial

/-!
# Solution

Imports the proof development. `lake comparator` checks that every theorem named in
`comparator.json` has exactly the statement given in `Challenge.lean`, and that its proof uses only
`propext`, `Classical.choice` and `Quot.sound`.
-/

@[expose] public section
