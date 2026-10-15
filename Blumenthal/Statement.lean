import Blumenthal.Defs

/-!
# The target theorem and the capacity bound

* `SendovAnswer` is the full answer to Blumenthal's problem: Sendov (1995), Theorem 4.1, with the
  corrected constant. It is the target of this project. It is *stated* here, not assumed anywhere.
* `SendovLower` / `SendovUpper` are its two halves.
* `CapacityBound` is the geometric statement behind the lower bounds: a planar set whose angles
  are all at most `(1 - 2/u) π` has at most `capacity u` points. `Blumenthal.Reduction` proves
  `CapacityBound ↔ SendovLower`.
-/

open Real

namespace Blumenthal

/-- The value Sendov's theorem assigns to `α_N` for `2^n < N ≤ 2^(n+1)`, `n ≥ 2`.

The lower band uses `1 - 2/(2n+1)`, as in Sendov's Theorem 4.1. erdosproblems.com/504 prints
numerator `1`; that would make `α_5 = 4π/5`, above the regular pentagon's `3π/5`. -/
noncomputable def bandValue (n N : ℕ) : ℝ :=
  if N ≤ 2 ^ n + 2 ^ (n - 2) then (1 - 2 / (2 * n + 1 : ℝ)) * π else (1 - 1 / (n + 1 : ℝ)) * π

/-- **Blumenthal's problem, full answer** (Sendov's classification):
`α_3 = π/3`, `α_4 = π/2`, and for `n ≥ 2` and `2^n < N ≤ 2^(n+1)`,
`α_N = (1 - 2/(2n+1)) π` if `N ≤ 2^n + 2^(n-2)`, and `α_N = (1 - 1/(n+1)) π` otherwise. -/
def SendovAnswer : Prop :=
  alpha 3 = π / 3 ∧ alpha 4 = π / 2 ∧
    ∀ n N : ℕ, 2 ≤ n → 2 ^ n < N → N ≤ 2 ^ (n + 1) → alpha N = bandValue n N

/-- The lower-bound half of `SendovAnswer`: every `N`-point set has an angle this large. -/
def SendovLower : Prop :=
  π / 3 ≤ alpha 3 ∧ π / 2 ≤ alpha 4 ∧
    ∀ n N : ℕ, 2 ≤ n → 2 ^ n < N → N ≤ 2 ^ (n + 1) → bandValue n N ≤ alpha N

/-- The upper-bound half of `SendovAnswer`: some `N`-point sets have no larger angle. -/
def SendovUpper : Prop :=
  alpha 3 ≤ π / 3 ∧ alpha 4 ≤ π / 2 ∧
    ∀ n N : ℕ, 2 ≤ n → 2 ^ n < N → N ≤ 2 ^ (n + 1) → alpha N ≤ bandValue n N

theorem sendovAnswer_iff : SendovAnswer ↔ SendovLower ∧ SendovUpper := by
  constructor
  · rintro ⟨h3, h4, h⟩
    exact ⟨⟨h3.ge, h4.ge, fun n N hn h1 h2 => (h n N hn h1 h2).ge⟩,
      ⟨h3.le, h4.le, fun n N hn h1 h2 => (h n N hn h1 h2).le⟩⟩
  · rintro ⟨⟨l3, l4, l⟩, ⟨u3, u4, u⟩⟩
    exact ⟨le_antisymm u3 l3, le_antisymm u4 l4,
      fun n N hn h1 h2 => le_antisymm (u n N hn h1 h2) (l n N hn h1 h2)⟩

/-- Sendov's capacity `B(u)`: the claimed largest size of a planar set all of whose angles are at
most `(1 - 2/u) π`. With `n = ⌊u/2⌋ ≥ 2` it is `2^n` for `u < 2n+1` and `2^n + 2^(n-2)` for
`u ≥ 2n+1`; below `u = 4` it is `2` (`u < 3`) or `3`. -/
noncomputable def capacity (u : ℝ) : ℕ :=
  if u < 3 then 2
  else if u < 4 then 3
  else if u < 2 * (⌊u / 2⌋₊ : ℝ) + 1 then 2 ^ ⌊u / 2⌋₊
  else 2 ^ ⌊u / 2⌋₊ + 2 ^ (⌊u / 2⌋₊ - 2)

/-- **The capacity bound.** A planar set whose angles are all at most `(1 - 2/u) π` has at most
`capacity u` points.

`Blumenthal.Reduction` proves this is equivalent to `SendovLower`. It is known for `u ≤ 8`
(`α_N` for `N ≤ 16`) and for even integers `u` (Erdős–Szekeres). Otherwise it is open as far as we
know: Sendov's Lemma 4.1 was meant to supply it but proves only the 2- and 3-centre cases (see
`docs/MATH-CHECK.md`). -/
def CapacityBound : Prop :=
  ∀ u : ℝ, 0 < u → ∀ A : Finset Plane, AnglesLE A ((1 - 2 / u) * π) → A.card ≤ capacity u

end Blumenthal
