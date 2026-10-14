import Mathlib

/-!
# Blumenthal's problem (Erdős #504): definitions

`alpha N` is the supremum of the `α ∈ [0, π]` such that every `N`-point subset of the Euclidean
plane contains three distinct points `x, y, z` with `∠ x y z ≥ α`. This is the statement on
erdosproblems.com/504, transcribed literally: no closed form is built into the definition.

This file also proves the interface lemmas used everywhere else:
* `le_alpha`: a lower bound for `alpha N` from a statement about all `N`-point sets;
* `alpha_le`, `alpha_le_of_approx`: upper bounds for `alpha N` from explicit configurations;
* `alpha_mono`: `alpha` is monotone on `N ≥ 3`;
* `exists_max_angle`: a set with at least three points has a largest angle.
-/

open EuclideanGeometry Real

namespace Blumenthal

/-- The Euclidean plane. -/
abbrev Plane : Type := EuclideanSpace ℝ (Fin 2)

/-- Every angle `∠ x y z` determined by three distinct points of `A` is at most `β`. -/
def AnglesLE (A : Finset Plane) (β : ℝ) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x ≠ y → y ≠ z → x ≠ z → ∠ x y z ≤ β

/-- `A` contains three distinct points `x, y, z` with `∠ x y z ≥ α`. -/
def HasAngleGE (A : Finset Plane) (α : ℝ) : Prop :=
  ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧ α ≤ ∠ x y z

/-- The admissible values in the definition of `alpha N`. -/
def admissible (N : ℕ) : Set ℝ :=
  {α | 0 ≤ α ∧ α ≤ π ∧ ∀ A : Finset Plane, A.card = N → HasAngleGE A α}

/-- Blumenthal's `α_N`: the supremum of `α ∈ [0, π]` such that every `N`-point planar set has
three distinct points `x, y, z` with `∠ x y z ≥ α`. -/
noncomputable def alpha (N : ℕ) : ℝ :=
  sSup (admissible N)

lemma admissible_bddAbove (N : ℕ) : BddAbove (admissible N) :=
  ⟨π, fun _ h => h.2.1⟩

/-- A set with at least three points has a largest angle. -/
theorem exists_max_angle {A : Finset Plane} (hA : 3 ≤ A.card) :
    ∃ x ∈ A, ∃ y ∈ A, ∃ z ∈ A, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧ AnglesLE A (∠ x y z) := by
  classical
  let T := (A ×ˢ A ×ˢ A).filter
    (fun t : Plane × Plane × Plane => t.1 ≠ t.2.1 ∧ t.2.1 ≠ t.2.2 ∧ t.1 ≠ t.2.2)
  have hT : T.Nonempty := by
    obtain ⟨x, hx, y, hy, z, hz, hxy, hxz, hyz⟩ := Finset.two_lt_card.mp (show 2 < A.card by omega)
    exact ⟨(x, y, z), by simp [T, hx, hy, hz, hxy, hyz, hxz]⟩
  obtain ⟨⟨x, y, z⟩, ht, hmax⟩ := T.exists_max_image (fun t => ∠ t.1 t.2.1 t.2.2) hT
  simp only [T, Finset.mem_filter, Finset.mem_product] at ht
  refine ⟨x, ht.1.1, y, ht.1.2.1, z, ht.1.2.2, ht.2.1, ht.2.2.1, ht.2.2.2, ?_⟩
  intro a ha b hb c hc hab hbc hac
  exact hmax (a, b, c) (by simp [T, ha, hb, hc, hab, hbc, hac])

/-- Any set with at least three points has an angle `≥ 0`. -/
lemma hasAngleGE_zero {A : Finset Plane} (hA : 3 ≤ A.card) : HasAngleGE A 0 := by
  obtain ⟨x, hx, y, hy, z, hz, hxy, hyz, hxz, -⟩ := exists_max_angle hA
  exact ⟨x, hx, y, hy, z, hz, hxy, hyz, hxz, angle_nonneg x y z⟩

lemma zero_mem_admissible {N : ℕ} (hN : 3 ≤ N) : (0 : ℝ) ∈ admissible N :=
  ⟨le_rfl, pi_pos.le, fun _ hA => hasAngleGE_zero (hA ▸ hN)⟩

/-- **Lower-bound interface.** If every `N`-point set has an angle `≥ c`, then `c ≤ alpha N`. -/
theorem le_alpha {N : ℕ} {c : ℝ} (h0 : 0 ≤ c) (hπ : c ≤ π)
    (h : ∀ A : Finset Plane, A.card = N → HasAngleGE A c) : c ≤ alpha N :=
  le_csSup (admissible_bddAbove N) ⟨h0, hπ, h⟩

/-- **Upper-bound interface.** An `N`-point set all of whose angles are `≤ β` gives
`alpha N ≤ β`. -/
theorem alpha_le {N : ℕ} {β : ℝ} (hβ : 0 ≤ β) {A : Finset Plane} (hA : A.card = N)
    (hle : AnglesLE A β) : alpha N ≤ β := by
  rcases (admissible N).eq_empty_or_nonempty with hne | hne
  · rw [alpha, hne, Real.sSup_empty]
    exact hβ
  · refine csSup_le hne ?_
    rintro α ⟨-, -, hα⟩
    obtain ⟨x, hx, y, hy, z, hz, hxy, hyz, hxz, h⟩ := hα A hA
    exact h.trans (hle x hx y hy z hz hxy hyz hxz)

/-- **Upper-bound interface, approximate form.** Sendov's constructions only approach their
angle bound, so this is the form they use. -/
theorem alpha_le_of_approx {N : ℕ} {β : ℝ} (hβ : 0 ≤ β)
    (h : ∀ ε > 0, ∃ A : Finset Plane, A.card = N ∧ AnglesLE A (β + ε)) : alpha N ≤ β := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨A, hA, hle⟩ := h ε hε
  exact alpha_le (by linarith) hA hle

/-- `alpha N` lies in `[0, π]` once `N ≥ 3`. -/
lemma alpha_nonneg {N : ℕ} (hN : 3 ≤ N) : 0 ≤ alpha N :=
  le_csSup (admissible_bddAbove N) (zero_mem_admissible hN)

lemma alpha_le_pi (N : ℕ) : alpha N ≤ π := by
  rcases (admissible N).eq_empty_or_nonempty with hne | hne
  · rw [alpha, hne, Real.sSup_empty]
    exact pi_pos.le
  · exact csSup_le hne fun _ h => h.2.1

/-- Every `M`-point set contains an `N`-point subset, so `alpha` is monotone. -/
theorem admissible_mono {N M : ℕ} (hNM : N ≤ M) : admissible N ⊆ admissible M := by
  rintro α ⟨h0, hπ, h⟩
  refine ⟨h0, hπ, fun A hA => ?_⟩
  obtain ⟨B, hBA, hB⟩ := Finset.exists_subset_card_eq (hA ▸ hNM)
  obtain ⟨x, hx, y, hy, z, hz, hxy, hyz, hxz, hα⟩ := h B hB
  exact ⟨x, hBA hx, y, hBA hy, z, hBA hz, hxy, hyz, hxz, hα⟩

theorem alpha_mono {N M : ℕ} (hN : 3 ≤ N) (hNM : N ≤ M) : alpha N ≤ alpha M :=
  csSup_le_csSup (admissible_bddAbove M) ⟨0, zero_mem_admissible hN⟩ (admissible_mono hNM)

end Blumenthal
