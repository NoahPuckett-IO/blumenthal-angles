import Blumenthal.SignSeq
import Blumenthal.N4.DiffCons

/-!
# Grid reduction, part 1: integer positions

Nine sign sequences with three changes per half-turn, `2π < 9ℓ`. Their 27 base change points
`X (i, r) = y_i (j_i + r) ∈ (0, π]` get integer positions `P` on a half-turn of 22 cells such that
(T1) `y_i k ≤ y_i' k'` implies `npos i k ≤ npos i' k'`, and
(T2) `y_i k + ℓ ≤ y_i' k'` implies `npos i k + 5 ≤ npos i' k'`.
The integer positions come from `DiffCons.exists_potential` on the complete graph.
-/

open Real Blumenthal Classical

namespace N4

variable {ℓ : ℝ} (F : Fin 9 → SignSeq ℓ)

abbrev Vx := Fin 9 × Fin 3

/-- base index of member `i`: its first change after `0` -/
noncomputable def jI (i : Fin 9) : ℤ := (F i).idx 0 + 1

/-- base change points -/
noncomputable def X (v : Vx) : ℝ := (F v.1).y (jI F v.1 + (v.2 : ℕ))

variable (hc : ∀ i, (F i).c = 3)
include hc

lemma y_add_three (i : Fin 9) (k : ℤ) : (F i).y (k + 3) = (F i).y k + π := by
  have := (F i).y_add_c k
  rw [hc i] at this
  exact_mod_cast this

lemma X_pos (v : Vx) : 0 < X F v := by
  have h0 : 0 < (F v.1).y ((F v.1).idx 0 + 1) := (F v.1).lt_y_idx_add_one 0
  exact lt_of_lt_of_le h0 ((F v.1).mono.monotone (by simp [jI]))

lemma X_le (v : Vx) : X F v ≤ π := by
  have h1 : (F v.1).y ((F v.1).idx 0) ≤ 0 := (F v.1).y_idx_le 0
  have h2 := y_add_three F hc v.1 ((F v.1).idx 0)
  have h3 : (F v.1).y (jI F v.1 + (v.2 : ℕ)) ≤ (F v.1).y ((F v.1).idx 0 + 3) := by
    apply (F v.1).mono.monotone
    have := v.2.2
    simp only [jI]
    omega
  unfold X
  linarith

/-- every change point is a base point shifted by whole half-turns -/
lemma y_eq_X (i : Fin 9) (k : ℤ) :
    (F i).y k = X F (i, ⟨((k - jI F i) % 3).toNat, by omega⟩) + ((k - jI F i) / 3 : ℤ) * π := by
  have hm := (F i).y_add_mul (jI F i + ((k - jI F i) % 3).toNat) ((k - jI F i) / 3)
  rw [hc i] at hm
  have hk : jI F i + (((k - jI F i) % 3).toNat : ℤ) + (k - jI F i) / 3 * ((3 : ℕ) : ℤ) = k := by
    have := Int.emod_add_ediv_mul (k - jI F i) 3
    have h0 : 0 ≤ (k - jI F i) % 3 := Int.emod_nonneg _ (by norm_num)
    rw [Int.toNat_of_nonneg h0]
    push_cast
    linarith
  rw [hk] at hm
  rw [hm]
  rfl

/-! ### Edge weights -/

/-- `α v w ∈ {0,1}` and shift `μ v w ∈ {0,1}` of the best valid inequality
`X w + μ π - X v ≥ α ℓ`; the integer weight is `5 α - 22 μ`. -/
noncomputable def α (v w : Vx) : ℕ :=
  if X F v + ℓ ≤ X F w then 1 else if X F v ≤ X F w then 0 else if X F v + ℓ ≤ X F w + π then 1 else 0

noncomputable def μ (v w : Vx) : ℕ :=
  if X F v + ℓ ≤ X F w then 0 else if X F v ≤ X F w then 0 else 1

noncomputable def cw (v w : Vx) : ℤ := 5 * (α F v w : ℤ) - 22 * (μ F v w : ℤ)

omit hc in
lemma α_le (v w : Vx) : α F v w ≤ 1 := by unfold α; split_ifs <;> simp

omit hc in
lemma μ_le (v w : Vx) : μ F v w ≤ 1 := by unfold μ; split_ifs <;> simp

lemma valid (v w : Vx) : (α F v w : ℝ) * ℓ ≤ X F w + (μ F v w : ℝ) * π - X F v := by
  have h1 := X_pos F hc w
  have h2 := X_le F hc v
  unfold α μ
  split_ifs <;> push_cast <;> linarith

/-! ### Walk sums -/

/-- along any walk: `(Σα) ℓ ≤ X last - X first + (Σμ) π`, `Σα ≤ #edges`, weights decompose -/
lemma walk_bound : ∀ (l : List Vx) (a z : Vx), l.head? = some a → l.getLast? = some z →
    (DiffCons.wt (fun v w => (α F v w : ℤ)) l : ℝ) * ℓ ≤
      X F z - X F a + (DiffCons.wt (fun v w => (μ F v w : ℤ)) l : ℝ) * π ∧
    DiffCons.wt (fun v w => (α F v w : ℤ)) l + 1 ≤ l.length ∧
    0 ≤ DiffCons.wt (fun v w => (μ F v w : ℤ)) l ∧
    DiffCons.wt (cw F) l = 5 * DiffCons.wt (fun v w => (α F v w : ℤ)) l -
      22 * DiffCons.wt (fun v w => (μ F v w : ℤ)) l
  | [], a, z, h, _ => by simp at h
  | [b], a, z, h1, h2 => by
    simp only [List.head?_cons, Option.some.injEq, List.getLast?_singleton] at h1 h2
    subst h1; subst h2
    simp [DiffCons.wt]
  | b :: c :: l, a, z, h1, h2 => by
    simp only [List.head?_cons, Option.some.injEq] at h1
    subst h1
    have h2' : (c :: l).getLast? = some z := by simpa using h2
    obtain ⟨i1, i2, i3, i4⟩ := walk_bound (c :: l) c z rfl h2'
    have hv := valid F hc b c
    have ha := α_le F b c
    simp only [DiffCons.wt, List.length_cons] at i1 i2 i3 i4 ⊢
    refine ⟨?_, ?_, ?_, ?_⟩
    · push_cast
      nlinarith [hv, i1]
    · simp at i2; omega
    · positivity
    · rw [i4]; unfold cw; ring

variable {F}

/-- **Cycle bound.** Short closed walks have weight `≤ 0` (this is where `2π < 9ℓ` enters). -/
lemma cycle_bound (hℓ : 0 < ℓ) (hband : 2 * π < 9 * ℓ) (l : List Vx) (hne : l ≠ [])
    (hcl : l.head? = l.getLast?) (hlen : l.length ≤ 27 + 1) : DiffCons.wt (cw F) l ≤ 0 := by
  obtain ⟨a, ha⟩ : ∃ a, l.head? = some a := by
    cases l with
    | nil => exact absurd rfl hne
    | cons x xs => exact ⟨x, rfl⟩
  obtain ⟨b1, b2, b3, b4⟩ := walk_bound F hc l a a ha (hcl ▸ ha)
  set k := DiffCons.wt (fun v w => (α F v w : ℤ)) l
  set m := DiffCons.wt (fun v w => (μ F v w : ℤ)) l
  rw [b4]
  simp only [sub_self, zero_add] at b1
  have hk0 : 0 ≤ k := by
    have : ∀ l : List Vx, 0 ≤ DiffCons.wt (fun v w => (α F v w : ℤ)) l := by
      intro l
      induction l with
      | nil => simp [DiffCons.wt]
      | cons x xs ih =>
        cases xs with
        | nil => simp [DiffCons.wt]
        | cons y ys => simp only [DiffCons.wt] at ih ⊢; positivity
    exact this l
  have hπ := pi_pos
  rcases (show m = 0 ∨ 1 ≤ m by omega) with hm | hm
  · rw [hm] at b1
    simp at b1
    have : (k : ℝ) ≤ 0 := by nlinarith
    have : k ≤ 0 := by exact_mod_cast this
    omega
  · -- 2k < 9m
    have h9 : (2 * k : ℝ) < 9 * m := by
      have hmr : (1 : ℝ) ≤ m := by exact_mod_cast hm
      nlinarith
    have : 2 * k < 9 * m := by exact_mod_cast h9
    omega

/-! ### Integer potentials -/

variable (F)

lemma exists_P (hℓ : 0 < ℓ) (hband : 2 * π < 9 * ℓ) :
    ∃ P : Vx → ℤ, ∀ v w, v ≠ w → P v + cw F v w ≤ P w := by
  have := DiffCons.exists_potential (V := Vx) (fun v w => v ≠ w) (cw F) (by
    intro l _ hne hcl hlen
    apply cycle_bound hc hℓ hband l hne hcl
    simpa using hlen)
  exact this

/-! ### Transfer lemmas on base points -/

variable {F}

lemma base_T1 (P : Vx → ℤ) (hP : ∀ v w, v ≠ w → P v + cw F v w ≤ P w)
    (v w : Vx) (a b : ℤ) (h : X F v + a * π ≤ X F w + b * π) : P v + 22 * a ≤ P w + 22 * b := by
  have hπ := pi_pos
  have hv := X_pos F hc v
  have hw := X_le F hc w
  have hv' := X_le F hc v
  have hw' := X_pos F hc w
  by_cases hvw : v = w
  · subst hvw
    have : (a : ℝ) ≤ b := by nlinarith
    have : a ≤ b := by exact_mod_cast this
    omega
  have hPvw := hP v w hvw
  rcases (show b - a ≥ 1 ∨ b = a ∨ b < a by omega) with hd | hd | hd
  · have : -22 ≤ cw F v w := by
      unfold cw; have := μ_le F v w; omega
    omega
  · subst hd
    have hle : X F v ≤ X F w := by linarith
    have : 0 ≤ cw F v w := by
      unfold cw α μ
      split_ifs <;> simp_all
    omega
  · exfalso
    have : (b : ℝ) + 1 ≤ a := by exact_mod_cast (show b + 1 ≤ a by omega)
    nlinarith

lemma base_T2 (hℓ : 0 < ℓ) (P : Vx → ℤ) (hP : ∀ v w, v ≠ w → P v + cw F v w ≤ P w)
    (v w : Vx) (a b : ℤ) (h : X F v + a * π + ℓ ≤ X F w + b * π) :
    P v + 22 * a + 5 ≤ P w + 22 * b := by
  have hπ := pi_pos
  have hv := X_pos F hc v
  have hw := X_le F hc w
  have hv' := X_le F hc v
  have hw' := X_pos F hc w
  by_cases hvw : v = w
  · subst hvw
    have : (a : ℝ) < b := by nlinarith
    have : a < b := by exact_mod_cast this
    omega
  have hPvw := hP v w hvw
  rcases (show b - a ≥ 2 ∨ b = a + 1 ∨ b = a ∨ b < a by omega) with hd | hd | hd | hd
  · have : -22 ≤ cw F v w := by
      unfold cw; have := μ_le F v w; omega
    omega
  · subst hd
    have hle : X F v + ℓ ≤ X F w + π := by push_cast at h; linarith
    have : -17 ≤ cw F v w := by
      unfold cw α μ
      split_ifs <;> simp_all
    omega
  · subst hd
    have hle : X F v + ℓ ≤ X F w := by linarith
    have : cw F v w = 5 := by
      unfold cw α μ
      simp [hle]
    omega
  · exfalso
    have : (b : ℝ) + 1 ≤ a := by exact_mod_cast (show b + 1 ≤ a by omega)
    nlinarith

end N4
