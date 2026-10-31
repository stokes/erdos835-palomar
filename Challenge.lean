/-
Copyright 2026 Matt Stokes.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Data.Nat.Prime.Basic

/-!
# Erdős Problem 835 when `k + 1` is composite: statements

Erdős asked (Problem 835 at erdosproblems.com) whether there is a `k > 2` such that the `k`-element
subsets of a `2k`-element set can be coloured with `k + 1` colours so that every `(k + 1)`-element set
sees all `k + 1` colours among its `k`-element subsets. Equivalently: is the chromatic number of the
Johnson graph `J(2k, k)` equal to `k + 1` for some `k > 2`? (It is always at least `k + 1`, because
the `k`-subsets of one `(k + 1)`-set form a clique.)

Jie Ma and Quanyu Tang (*A note on Erdős Problem #835*, 2025) proved that the answer is no whenever
`k + 1` is not prime. This file states, in Mathlib terms only:

* `property_iff_chromaticNumber`: for `k > 0`, `χ(J(2k, k)) = k + 1` iff the colouring property holds;
* `johnson_chromaticNumber_composite`: for `k > 2` with `k + 1` composite, `k + 1 < χ(J(2k, k))`;
* `johnson_chromaticNumber_odd`: for odd `k > 2`, `k + 1 < χ(J(2k, k))` (then `k + 1` is even);
* `johnsonGraph_18_9_chromaticNumber`: `χ(J(18, 9)) > 10` (the case `k = 9`).

The case where `k + 1` is prime, and so Erdős Problem 835 itself, remains open.

The definitions and statements are copied from google-deepmind/formal-conjectures
(commit `5a2fb85045c86e4a184b15ce7531ba199a3c4580`, Apache-2.0), with these names there:

| here | formal-conjectures |
|---|---|
| `Erdos835Palomar.johnson`, notation `J(n, k)` | `SimpleGraph.johnson`, notation `J(n, k)` (`FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Johnson.lean`) |
| `Erdos835Palomar.Composite n` | `Nat.Composite n`, written `n.Composite` (`FormalConjecturesForMathlib/Data/Nat/Prime/Composite.lean`) |
| `Erdos835Palomar.Property` | `Erdos835.Property` (`FormalConjectures/ErdosProblems/835.lean`) |
| the four theorems | `Erdos835.<same name>` in `FormalConjectures/ErdosProblems/835.lean` |

The only changes are the namespace, and writing `Composite (k + 1)` for `(k + 1).Composite`.
`χ` here is Mathlib's `SimpleGraph.chromaticNumber`, valued in `ℕ∞`.
-/

@[expose] public section

open Finset SimpleGraph

namespace Erdos835Palomar

/--
The Johnson graph $J(n, k)$ has as vertices the $k$-subsets of an $n$-set.
Two vertices are adjacent if their intersection has size $k - 1$.
-/
@[simps -isSimp]
def johnson (n k : ℕ) : SimpleGraph {s : Finset (Fin n) // #s = k} where
  Adj s t := #(s.val ∩ t.val) + 1 = k
  symm.symm s t h := by simpa [inter_comm]
  loopless.irrefl := by simp +contextual

@[inherit_doc] scoped notation "J(" n ", " k ")" => johnson n k

/-- A natural number is composite if it is greater than one and not prime. -/
abbrev Composite (n : ℕ) : Prop := 1 < n ∧ ¬n.Prime

/--
The property that for a given $k$, the $k$-subsets of a $2k$-set can be colored with $k+1$ colors
such that any $(k+1)$-subset contains all colors.
-/
def Property (k : ℕ) : Prop :=
  let K := {s : Finset (Fin (2 * k)) // s.card = k}
  ∃ c : K → Fin (k + 1),
    ∀ A : Finset (Fin (2 * k)), A.card = k + 1 →
      (image c {s : K | s.val ⊂ A}) = (univ : Finset (Fin (k+1)))

/-- For `k > 0`, the chromatic number of `J(2k, k)` is `k + 1` exactly when `Property k` holds. -/
theorem property_iff_chromaticNumber (k : ℕ) (hk : 0 < k) :
    (J(2 * k, k).chromaticNumber = k + 1) ↔
    Property k := by
  sorry

/--
Ma and Tang have proved that the chromatic number of $J(2k,k)$ is $>k+1$ for all $k>2$ not of the
form $p-1$ for prime $p$.
-/
theorem johnson_chromaticNumber_composite (k : ℕ) (hk : 2 < k) (h : Composite (k + 1)) :
    k + 1 < J(2 * k, k).chromaticNumber :=
  sorry

/--
The chromatic number of $J(2k,k)$ is $>k+1$ for all odd $k>2$.
-/
theorem johnson_chromaticNumber_odd (k : ℕ) (hk : 2 < k) (h : Odd k) :
    k + 1 < J(2 * k, k).chromaticNumber :=
  sorry

/--
The chromatic number of $J(18, 9)$ is at least $11$.
-/
theorem johnsonGraph_18_9_chromaticNumber : J(18, 9).chromaticNumber > 9 + 1 := by
  sorry

end Erdos835Palomar
