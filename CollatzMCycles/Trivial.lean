module

public import CollatzMCycles.SpecDefs

/-!
# The trivial cycle

`1 → 2 → 1` is a `1`-cycle of the shortcut Collatz map, through both `1` and `2`. These two
statements test the definition `IsMCycle` and show why the main theorem needs `n > 2`.
-/

@[expose] public section

theorem isMCycle_one_one : IsMCycle 1 1 := ⟨by decide, 2, by decide⟩

theorem isMCycle_one_two : IsMCycle 1 2 := ⟨by decide, 2, by decide⟩
