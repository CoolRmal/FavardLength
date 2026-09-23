# FavardLength

A Lean 4 + Mathlib formalization, in progress, of a lower bound for the Favard-length decay
exponent of the four-corner Cantor set.

Let `C_n` be the depth-`n` approximant of the middle-half Cantor set, `K_n = C_n × C_n`, and
`Fav(K_n) = (1/π) ∫_0^π |π_θ(K_n)| dθ` its Favard length. The decay exponent `α_Fav` is the
supremum of the exponents `a ≥ 0` with `Fav(K_n) ≤ C n^{-a}` for all `n ≥ 1`.
Nazarov–Peres–Volberg gave `α_Fav ≥ 1/6`, and Marshall (2025) gave `1/5` for this set. The
target results, stated in [`Challenge.lean`](Challenge.lean), are

* every exponent `a ∈ [0, 1/4)` is admissible, so `1/4 ≤ α_Fav`;
* `α_Fav ≤ 1`, from the elementary bound `Fav(K_n) ≥ c/n`.

**Status:** the statement surface is written and the proof is in progress. See
[`PLAN.md`](PLAN.md) for the architecture and [`PROGRESS.md`](PROGRESS.md) for current status.
`Solution.lean` still contains `sorry`.

## Repository map

- `Challenge.lean`: the small statement surface, with literal definitions.
- `Solution.lean`: restates the Challenge theorems and proves them from the development.
- `FavardLength/`: the proof development.
- `comparator.json`: the declarations Comparator must match.
- `formalization.yaml`: Palomar metadata (draft).

## Checks

```text
lake exe cache get
lake build
ruby scripts/validate-formalization.rb
./scripts/verify-comparator.sh
```

The Comparator script needs Linux (Landrun); CI runs it on every push. Submissions to Palomar
go through https://submit.palomar-registry.org/ once the development is complete.
