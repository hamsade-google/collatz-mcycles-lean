# Collatz m-cycles for m ≤ 91 and an explicit linear-form bound for log 2 and log 3

Lean 4 / Mathlib (`v4.35.0`) formalization of two theorems and four supporting statements, packaged for
[Palomar](https://palomar-registry.org) verification with `lake comparator`.

| Theorem | Statement | Axioms |
| --- | --- | --- |
| `CollatzMCycles.Diophantine.terminal` | For `K ≥ 2438425051595107335801557824` and any `L`, `Λ = (K + L) log 2 − K log 3` cannot satisfy `0 < Λ < 100 · 2^(1 − K/2^68)`. | `propext`, `Classical.choice`, `Quot.sound` |
| `CollatzMCycles.not_isMCycle_of_le_91_of_barina` | Assuming every `1 ≤ k ≤ 2^71` reaches `1` under the Collatz map (Bařina 2025, explicit hypothesis `hB`), no shortcut-Collatz cycle through `n > 2` has `m ≤ 91` local minima. | `propext`, `Classical.choice`, `Quot.sound` |
| `CollatzMCycles.two_pow_71_lt_iterate` | Under the same hypothesis `hB`, every element of a shortcut-Collatz cycle through some `n > 2` exceeds `2^71`. | same |
| `CollatzMCycles.IsMCycle.ne_zero` | Every `m`-cycle has `m ≠ 0`. | same |
| `isMCycle_one_one`, `isMCycle_one_two` | The trivial cycle `1 → 2 → 1` is a `1`-cycle through `1` and through `2`. | same |

The definitions `collatzStep`, `collatzShortcut` and `IsMCycle` follow Moritz Firsching's
`formal-conjectures` specification. This is an incremental `m`-cycle certificate plus a
formalization: it says nothing about general cycles or divergent orbits.

## Layout

* `Challenge.lean`: the statements (Mathlib imports only). This is the file to audit.
* `Solution.lean`: imports the proof development.
* `comparator.json`: the theorems compared and the permitted axioms.
* `CollatzMCycles/`: the proof development.
  * `SpecDefs.lean`: the definitions.
  * `Orbit.lean`, `Blocks.lean`, `Raney.lean`, `CycleProduct.lean`, `Telescopic.lean`: from an
    `m`-cycle to block data, the Raney rotation, the cycle-product identity and the telescopic
    lower bound on every local minimum.
  * `Unimodular.lean`, `Witnesses.lean`, `WitnessData.lean`: the continued-fraction bootstrap,
    checked with `decide +kernel`.
  * `Diophantine/`: the Padé-approximant proof of `terminal`.
  * `Le91.lean`: the `m ≤ 91` theorem.
  * `Trivial.lean`: the trivial cycle `1 → 2 → 1`.

## Checking

```bash
lake exe cache get
lake build
./scripts/verify-comparator.sh   # lake comparator with the Lean kernel, NanoDa and con-ron
python3 scripts/check-lean-sources.py
ruby scripts/validate-formalization.rb
```

`scripts/verify-comparator.sh`, `scripts/check-lean-sources.py` and
`scripts/validate-formalization.rb` come from
[PalomarRegistry/PalomarTemplate](https://github.com/PalomarRegistry/PalomarTemplate). Submissions go
to <https://submit.palomar-registry.org/>.
