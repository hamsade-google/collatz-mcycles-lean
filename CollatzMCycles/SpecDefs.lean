module

public import Mathlib

/-!
# Sorry-free definitions from Moritz Firsching's `formal-conjectures` specification

`collatzStep`, `collatzShortcut` and `IsMCycle`, verbatim from `CollatzMCycles/Spec.lean`.
The unproved statements (the Collatz conjecture, Bařina's `2^71` check, the period bound and the
`m`-cycle targets) stay in `Spec.lean`, which the Palomar proof chain does not import.
-/

@[expose] public section
def collatzStep (n : ℕ) : ℕ :=
  if Even n then n / 2 else 3 * n + 1

def collatzShortcut (n : ℕ) : ℕ :=
  if Even n then n / 2 else (3 * n + 1) / 2

def IsMCycle (m n : ℕ) : Prop :=
  0 < n ∧ ∃ p > 0, collatzShortcut^[p] n = n ∧
    ((List.range p).map (collatzShortcut^[·] n)).Nodup ∧
    ((Finset.range p).filter fun i =>
      collatzShortcut^[i + 1] n < collatzShortcut^[i] n ∧
      collatzShortcut^[i + 1] n < collatzShortcut^[i + 2] n).card = m
