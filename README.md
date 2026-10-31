# Erdős Problem 835 when k + 1 is composite (Lean 4)

Erdős Problem 835 asks whether, for some `k > 2`, the `k`-subsets of a `2k`-set can be coloured with
`k + 1` colours so that every `(k + 1)`-set sees all colours among its `k`-subsets; equivalently,
whether the Johnson graph `J(2k, k)` has chromatic number `k + 1`. Jie Ma and Quanyu Tang
([*A note on Erdős Problem #835*](https://github.com/QuanyuTang/erdos-problem-835/blob/main/On_Problem_835.pdf))
showed this fails whenever `k + 1` is not prime. This repository proves, with Mathlib only:

| Declaration (`Erdos835Palomar.`) | Statement |
|---|---|
| `property_iff_chromaticNumber` | for `k > 0`: `χ(J(2k, k)) = k + 1 ↔ Property k` |
| `johnson_chromaticNumber_composite` | for `k > 2`, `k + 1` composite: `k + 1 < χ(J(2k, k))` |
| `johnson_chromaticNumber_odd` | for odd `k > 2`: `k + 1 < χ(J(2k, k))` |
| `johnsonGraph_18_9_chromaticNumber` | `χ(J(18, 9)) > 10` |

`Challenge.lean` states them (Mathlib imports only); `Solution.lean` repeats the definitions verbatim
and proves them; `comparator.json` selects the four theorems. The definitions and statements are copied
from [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
(`FormalConjectures/ErdosProblems/835.lean`, commit `5a2fb85`), where they are stated without proof;
`Challenge.lean` maps each name. The case where `k + 1` is prime, and so the problem itself, remains open.
No new mathematics is claimed.

The proof double counts, for one colour, the `k`-subsets of that colour inside a `(k + j)`-set `W`: each
`(k + 1)`-subset of `W` contains exactly one of them, so `(k + 1) · #{colour-class subsets of W} =
(k + j).choose j`. A prime `p < k + 1` dividing `k + 1` does not let `k + 1` divide `(k + p).choose p`.
Ma and Tang obtain an equivalent divisibility condition by a different argument.

The proofs were written by an AI agent (Claude, Anthropic) directed by the author, and are checked by
the Lean kernel; see `formalization.yaml` for provenance and process.

## Check it

```sh
lake exe cache get
lake build
lake env lean CheckAxioms.lean   # [propext, Classical.choice, Quot.sound] for each theorem
```

Lean `v4.35.0`, Mathlib `v4.35.0`. Licence: Apache-2.0 (`LICENSE`).
