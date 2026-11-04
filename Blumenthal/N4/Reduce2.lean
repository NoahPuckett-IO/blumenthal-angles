import Blumenthal.N4.Reduce1
import Blumenthal.N4.GridMain

/-!
# Grid reduction, part 2: decoding

From the integer positions of part 1, each member becomes a discrete string `Grid.DStr`, and
compatible members become `Grid.DCompat` strings. Nine of them would contradict
`Grid.no_nine_compatible`, so a compatible family with three changes per half-turn has at most 8
members when `2π < 9ℓ`.
-/

open Real Blumenthal Classical

namespace N4

/-! ### Integer sequences with gaps `≥ 5` -/

section Seq

variable (Z : ℤ → ℤ) (hgap : ∀ k, Z k + 5 ≤ Z (k + 1))
include hgap

lemma Z_add_nat (k : ℤ) (n : ℕ) : Z k + 5 * n ≤ Z (k + n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have := hgap (k + n)
    push_cast
    rw [← add_assoc]
    omega

lemma Z_mono {k k' : ℤ} (h : k ≤ k') : Z k + 5 * (k' - k) ≤ Z k' := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, k' = k + n := ⟨(k' - k).toNat, by omega⟩
  have := Z_add_nat Z hgap k n
  simp only [add_sub_cancel_left]
  exact this

lemma Z_lt_iff {k k' : ℤ} : Z k < Z k' ↔ k < k' := by
  constructor
  · intro h; by_contra h'; push Not at h'; have := Z_mono Z hgap h'; omega
  · intro h; have := Z_mono Z hgap h.le; omega

/-- the index of the last change at or before `t` -/
noncomputable def K (t : ℤ) : ℤ := sSup {k : ℤ | Z k ≤ t}

lemma K_spec (t : ℤ) : Z (K Z t) ≤ t ∧ t < Z (K Z t + 1) := by
  have hne : {k : ℤ | Z k ≤ t}.Nonempty := by
    refine ⟨-(|t| + |Z 0|), ?_⟩
    have h0 := abs_nonneg t; have h0' := abs_nonneg (Z 0)
    have := Z_mono Z hgap (show -(|t| + |Z 0|) ≤ 0 by omega)
    show Z (-(|t| + |Z 0|)) ≤ t
    have h2 := neg_abs_le t; have h3 := le_abs_self (Z 0)
    omega
  have hbdd : BddAbove {k : ℤ | Z k ≤ t} := by
    refine ⟨|t| + |Z 0|, fun k hk => ?_⟩
    change Z k ≤ t at hk
    by_contra h; push Not at h
    have h0 := abs_nonneg t; have h0' := abs_nonneg (Z 0)
    have := Z_mono Z hgap (show (0 : ℤ) ≤ k by omega)
    have h2 := le_abs_self t; have h3 := neg_le_abs (Z 0)
    omega
  refine ⟨Int.csSup_mem hne hbdd, ?_⟩
  by_contra h; push Not at h
  have : K Z t + 1 ≤ K Z t := le_csSup hbdd h
  omega

lemma K_unique {t k : ℤ} (h1 : Z k ≤ t) (h2 : t < Z (k + 1)) : K Z t = k := by
  obtain ⟨g1, g2⟩ := K_spec Z hgap t
  have a := (Z_lt_iff Z hgap).1 (lt_of_le_of_lt h1 g2)
  have b := (Z_lt_iff Z hgap).1 (lt_of_le_of_lt g1 h2)
  omega

end Seq

/-! ### The new configuration -/

variable {ℓ : ℝ} {F : Fin 9 → SignSeq ℓ} (hc : ∀ i, (F i).c = 3)
variable (P : Vx → ℤ)

noncomputable def rI (F : Fin 9 → SignSeq ℓ) (i : Fin 9) (k : ℤ) : Fin 3 :=
  ⟨((k - jI F i) % 3).toNat, by omega⟩

/-- new (integer) position of change `k` of member `i` -/
noncomputable def npos (F : Fin 9 → SignSeq ℓ) (P : Vx → ℤ) (i : Fin 9) (k : ℤ) : ℤ :=
  P (i, rI F i k) + 22 * ((k - jI F i) / 3)

include hc

variable {P}

lemma T1 (hP : ∀ v w, v ≠ w → P v + cw F v w ≤ P w) {i i' : Fin 9} {k k' : ℤ} (h : (F i).y k ≤ (F i').y k') :
    npos F P i k ≤ npos F P i' k' := by
  rw [y_eq_X F hc, y_eq_X F hc] at h
  exact base_T1 hc P hP _ _ _ _ h

lemma T2 (hℓ : 0 < ℓ) (hP : ∀ v w, v ≠ w → P v + cw F v w ≤ P w)
    {i i' : Fin 9} {k k' : ℤ} (h : (F i).y k + ℓ ≤ (F i').y k') :
    npos F P i k + 5 ≤ npos F P i' k' := by
  rw [y_eq_X F hc, y_eq_X F hc] at h
  exact base_T2 hc hℓ P hP _ _ _ _ h

lemma npos_gap (hℓ : 0 < ℓ) (hP : ∀ v w, v ≠ w → P v + cw F v w ≤ P w) (i : Fin 9) (k : ℤ) : npos F P i k + 5 ≤ npos F P i (k + 1) :=
  T2 hc hℓ hP ((F i).gap k)

omit hc in
lemma npos_add_six (i : Fin 9) (k : ℤ) (m : ℤ) : npos F P i (k + 6 * m) = npos F P i k + 44 * m := by
  unfold npos rI
  have h1 : (k + 6 * m - jI F i) % 3 = (k - jI F i) % 3 := by omega
  have h2 : (k + 6 * m - jI F i) / 3 = (k - jI F i) / 3 + 2 * m := by omega
  simp only [h1, h2]
  ring

/-- the discrete value of member `i` on cell `t` -/
noncomputable def Dval (F : Fin 9 → SignSeq ℓ) (P : Vx → ℤ) (i : Fin 9) (t : ℤ) : Bool :=
  decide (Even (K (npos F P i) t))

lemma Dval_eq (hℓ : 0 < ℓ) (hP : ∀ v w, v ≠ w → P v + cw F v w ≤ P w) {i : Fin 9} {k t : ℤ} (h1 : npos F P i k ≤ t) (h2 : t < npos F P i (k + 1)) :
    Dval F P i t = decide (Even k) := by
  unfold Dval
  rw [K_unique _ (npos_gap hc hℓ hP i) h1 h2]

lemma Dval_periodic (hℓ : 0 < ℓ) (hP : ∀ v w, v ≠ w → P v + cw F v w ≤ P w) (i : Fin 9) (t m : ℤ) : Dval F P i (t + 44 * m) = Dval F P i t := by
  obtain ⟨g1, g2⟩ := K_spec _ (npos_gap hc hℓ hP i) t
  set k := K (npos F P i) t
  have e1 : npos F P i (k + 6 * m) ≤ t + 44 * m := by rw [npos_add_six]; omega
  have e2 : t + 44 * m < npos F P i (k + 6 * m + 1) := by
    rw [show k + 6 * m + 1 = (k + 1) + 6 * m by ring, npos_add_six]; omega
  rw [Dval_eq hc hℓ hP e1 e2]
  unfold Dval
  congr 1
  apply propext
  rw [Int.even_add]
  have : Even (6 * m) := ⟨3 * m, by ring⟩
  tauto

/-- **Windows.** Compatible members differ on 5 consecutive cells of the new configuration. -/
lemma window (hℓ : 0 < ℓ) (hP : ∀ v w, v ≠ w → P v + cw F v w ≤ P w) {f g : Fin 9} (hcomp : Compat ℓ (F f).val (F g).val) :
    ∃ W : ℤ, ∀ t, W ≤ t → t < W + 5 → Dval F P f t ≠ Dval F P g t := by
  obtain ⟨a, hNf, hNg, hne⟩ := (F f).exists_witness hℓ hcomp
  set kf := (F f).idx a
  set kg := (F g).idx a
  have yf := (F f).y_idx_le a
  have yg := (F g).y_idx_le a
  unfold SignSeq.NoChange at hNf hNg
  have a1 : npos F P f kf + 5 ≤ npos F P f (kf + 1) := T2 hc hℓ hP (by linarith)
  have a2 : npos F P g kg + 5 ≤ npos F P f (kf + 1) := T2 hc hℓ hP (by linarith)
  have a3 : npos F P f kf + 5 ≤ npos F P g (kg + 1) := T2 hc hℓ hP (by linarith)
  have a4 : npos F P g kg + 5 ≤ npos F P g (kg + 1) := T2 hc hℓ hP (by linarith)
  refine ⟨max (npos F P f kf) (npos F P g kg), fun t h1 h2 => ?_⟩
  rw [Dval_eq hc hℓ hP (k := kf) (by omega) (by omega),
    Dval_eq hc hℓ hP (k := kg) (by omega) (by omega)]
  exact hne

/-! ### Each member is a `Grid.DStr` -/

omit hc in
lemma xor_count (k : ℤ) (n : ℕ) :
    decide (Even (k + n)) = xor (decide (Even k)) (n % 2 == 1) := by
  have h : Even (n : ℤ) ↔ n % 2 = 0 := by rw [Int.even_coe_nat, Nat.even_iff]
  rcases Nat.mod_two_eq_zero_or_one n with hn | hn <;> by_cases hk : Even k <;>
    simp [Int.even_add, hk, h, hn]

omit hc in
lemma npos_add_three (i : Fin 9) (k : ℤ) : npos F P i (k + 3) = npos F P i k + 22 := by
  unfold npos rI
  have h1 : (k + 3 - jI F i) % 3 = (k - jI F i) % 3 := by omega
  have h2 : (k + 3 - jI F i) / 3 = (k - jI F i) / 3 + 1 := by omega
  simp only [h1, h2]
  ring

set_option maxHeartbeats 1600000 in
lemma exists_dstr (hℓ : 0 < ℓ) (hP : ∀ v w, v ≠ w → P v + cw F v w ≤ P w) (i : Fin 9) :
    ∃ d : Grid.DStr, ∀ t : ℕ, t < 44 → d.val t = Dval F P i t := by
  have hgap : ∀ k, npos F P i k + 5 ≤ npos F P i (k + 1) := npos_gap hc hℓ hP i
  obtain ⟨g1, g2⟩ := K_spec (npos F P i) hgap 0
  set k := K (npos F P i) 0
  set A := npos F P i (k + 1) with hAdef
  set B := npos F P i (k + 2) with hBdef
  set C := npos F P i (k + 3) with hCdef
  have hAB : A + 5 ≤ B := by
    have := hgap (k + 1); rw [show k + 1 + 1 = k + 2 by ring] at this; exact this
  have hBC : B + 5 ≤ C := by
    have := hgap (k + 2); rw [show k + 2 + 1 = k + 3 by ring] at this; exact this
  have hC : C = npos F P i k + 22 := npos_add_three i k
  have z4 : npos F P i (k + 4) = A + 22 := by
    rw [show k + 4 = (k + 1) + 3 by ring, npos_add_three]
  have z5 : npos F P i (k + 5) = B + 22 := by
    rw [show k + 5 = (k + 2) + 3 by ring, npos_add_three]
  have z6 : npos F P i (k + 6) = C + 22 := by
    rw [show k + 6 = (k + 3) + 3 by ring, npos_add_three]
  have z7 : npos F P i (k + 7) = A + 44 := by
    rw [show k + 7 = (k + 4) + 3 by ring, npos_add_three, z4]; ring
  have hCA : C + 5 ≤ A + 22 := by
    have := hgap (k + 3); rw [show k + 3 + 1 = k + 4 by ring, z4] at this; exact this
  have hA0 : 0 < A := g2
  have hz : npos F P i k ≤ 0 := g1
  have hC22 : C ≤ 22 := by omega
  -- the value on cell t is the parity of k + (number of changes in (0, t])
  have key : ∀ (t : ℕ) (j : ℕ), j ≤ 6 → npos F P i (k + j) ≤ t → (t : ℤ) < npos F P i (k + j + 1) →
      Dval F P i t = xor (decide (Even k)) (j % 2 == 1) := by
    intro t j _ h1 h2
    rw [Dval_eq hc hℓ hP h1 h2, xor_count]
  have hk0 : npos F P i (k + ((0 : ℕ) : ℤ)) = npos F P i k := by simp
  have hk1 : npos F P i (k + ((0 : ℕ) : ℤ) + 1) = A := by simp [hAdef]
  have hk1' : npos F P i (k + ((1 : ℕ) : ℤ)) = A := by simp [hAdef]
  have hk2 : npos F P i (k + ((1 : ℕ) : ℤ) + 1) = B := by
    rw [hBdef]; congr 1; push_cast; ring
  have hk2' : npos F P i (k + ((2 : ℕ) : ℤ)) = B := by simp [hBdef]
  have hk3 : npos F P i (k + ((2 : ℕ) : ℤ) + 1) = C := by
    rw [hCdef]; congr 1; push_cast; ring
  have hk3' : npos F P i (k + ((3 : ℕ) : ℤ)) = C := by simp [hCdef]
  have hk4 : npos F P i (k + ((3 : ℕ) : ℤ) + 1) = A + 22 := by
    rw [← z4]; congr 1; push_cast; ring
  have hk4' : npos F P i (k + ((4 : ℕ) : ℤ)) = A + 22 := by rw [← z4]; push_cast; rfl
  have hk5 : npos F P i (k + ((4 : ℕ) : ℤ) + 1) = B + 22 := by
    rw [← z5]; congr 1; push_cast; ring
  have hk5' : npos F P i (k + ((5 : ℕ) : ℤ)) = B + 22 := by rw [← z5]; push_cast; rfl
  have hk6 : npos F P i (k + ((5 : ℕ) : ℤ) + 1) = C + 22 := by
    rw [← z6]; congr 1; push_cast; ring
  have hk6' : npos F P i (k + ((6 : ℕ) : ℤ)) = C + 22 := by rw [← z6]; push_cast; rfl
  have hk7 : npos F P i (k + ((6 : ℕ) : ℤ) + 1) = A + 44 := by
    rw [← z7]; congr 1; push_cast; ring
  obtain ⟨a, ha⟩ : ∃ a : ℕ, (a : ℤ) = A := ⟨A.toNat, Int.toNat_of_nonneg (by omega)⟩
  obtain ⟨b, hb⟩ : ∃ b : ℕ, (b : ℤ) = B := ⟨B.toNat, Int.toNat_of_nonneg (by omega)⟩
  obtain ⟨c, hcc⟩ : ∃ c : ℕ, (c : ℤ) = C := ⟨C.toNat, Int.toNat_of_nonneg (by omega)⟩
  rcases lt_or_eq_of_le hC22 with hlt | heq
  · refine ⟨⟨decide (Even k), a, b, c, by omega, by omega, by omega, by omega⟩, fun t ht => ?_⟩
    simp only [Grid.DStr.val, Grid.valP]
    by_cases t1 : t < a
    · rw [key t 0 (by norm_num) (by rw [hk0]; omega) (by rw [hk1]; omega)]
      simp [List.filter, show ¬ a ≤ t by omega, show ¬ b ≤ t by omega, show ¬ c ≤ t by omega,
        show ¬ a + 22 ≤ t by omega, show ¬ b + 22 ≤ t by omega, show ¬ c + 22 ≤ t by omega]
    by_cases t2 : t < b
    · rw [key t 1 (by norm_num) (by rw [hk1']; omega) (by rw [hk2]; omega)]
      simp [List.filter, show 0 < a by omega, show a ≤ t by omega, show ¬ b ≤ t by omega,
        show ¬ c ≤ t by omega, show ¬ a + 22 ≤ t by omega, show ¬ b + 22 ≤ t by omega,
        show ¬ c + 22 ≤ t by omega]
    by_cases t3 : t < c
    · rw [key t 2 (by norm_num) (by rw [hk2']; omega) (by rw [hk3]; omega)]
      simp [List.filter, show 0 < a by omega, show a ≤ t by omega, show 0 < b by omega,
        show b ≤ t by omega, show ¬ c ≤ t by omega, show ¬ a + 22 ≤ t by omega,
        show ¬ b + 22 ≤ t by omega, show ¬ c + 22 ≤ t by omega]
    by_cases t4 : t < a + 22
    · rw [key t 3 (by norm_num) (by rw [hk3']; omega) (by rw [hk4]; omega)]
      simp [List.filter, show 0 < a by omega, show a ≤ t by omega, show 0 < b by omega,
        show b ≤ t by omega, show 0 < c by omega, show c ≤ t by omega,
        show ¬ a + 22 ≤ t by omega, show ¬ b + 22 ≤ t by omega, show ¬ c + 22 ≤ t by omega]
    by_cases t5 : t < b + 22
    · rw [key t 4 (by norm_num) (by rw [hk4']; omega) (by rw [hk5]; omega)]
      simp [List.filter, show 0 < a by omega, show a ≤ t by omega, show 0 < b by omega,
        show b ≤ t by omega, show 0 < c by omega, show c ≤ t by omega,
        show a + 22 ≤ t by omega, show ¬ b + 22 ≤ t by omega, show ¬ c + 22 ≤ t by omega]
    by_cases t6 : t < c + 22
    · rw [key t 5 (by norm_num) (by rw [hk5']; omega) (by rw [hk6]; omega)]
      simp [List.filter, show 0 < a by omega, show a ≤ t by omega, show 0 < b by omega,
        show b ≤ t by omega, show 0 < c by omega, show c ≤ t by omega,
        show a + 22 ≤ t by omega, show b + 22 ≤ t by omega, show ¬ c + 22 ≤ t by omega]
    · rw [key t 6 (by norm_num) (by rw [hk6']; omega) (by rw [hk7]; omega)]
      simp [List.filter, show 0 < a by omega, show a ≤ t by omega, show 0 < b by omega,
        show b ≤ t by omega, show 0 < c by omega, show c ≤ t by omega,
        show a + 22 ≤ t by omega, show b + 22 ≤ t by omega, show c + 22 ≤ t by omega]
  · -- the third change is at 22 ≡ 0
    refine ⟨⟨decide (Even k), 0, a, b, by omega, by omega, by omega, by omega⟩, fun t ht => ?_⟩
    simp only [Grid.DStr.val, Grid.valP]
    by_cases t1 : t < a
    · rw [key t 0 (by norm_num) (by rw [hk0]; omega) (by rw [hk1]; omega)]
      simp [List.filter, show ¬ a ≤ t by omega, show ¬ b ≤ t by omega, show ¬ 22 ≤ t by omega,
        show ¬ a + 22 ≤ t by omega, show ¬ b + 22 ≤ t by omega]
    by_cases t2 : t < b
    · rw [key t 1 (by norm_num) (by rw [hk1']; omega) (by rw [hk2]; omega)]
      simp [List.filter, show 0 < a by omega, show a ≤ t by omega, show ¬ b ≤ t by omega,
        show ¬ 22 ≤ t by omega, show ¬ a + 22 ≤ t by omega, show ¬ b + 22 ≤ t by omega]
    by_cases t3 : t < 22
    · rw [key t 2 (by norm_num) (by rw [hk2']; omega) (by rw [hk3]; omega)]
      simp [List.filter, show 0 < a by omega, show a ≤ t by omega, show 0 < b by omega,
        show b ≤ t by omega, show ¬ 22 ≤ t by omega, show ¬ a + 22 ≤ t by omega,
        show ¬ b + 22 ≤ t by omega]
    by_cases t4 : t < a + 22
    · rw [key t 3 (by norm_num) (by rw [hk3']; omega) (by rw [hk4]; omega)]
      simp [List.filter, show 0 < a by omega, show a ≤ t by omega, show 0 < b by omega,
        show b ≤ t by omega, show 22 ≤ t by omega, show ¬ a + 22 ≤ t by omega,
        show ¬ b + 22 ≤ t by omega]
    by_cases t5 : t < b + 22
    · rw [key t 4 (by norm_num) (by rw [hk4']; omega) (by rw [hk5]; omega)]
      simp [List.filter, show 0 < a by omega, show a ≤ t by omega, show 0 < b by omega,
        show b ≤ t by omega, show 22 ≤ t by omega, show a + 22 ≤ t by omega,
        show ¬ b + 22 ≤ t by omega]
    · rw [key t 5 (by norm_num) (by rw [hk5']; omega) (by rw [hk6]; omega)]
      simp [List.filter, show 0 < a by omega, show a ≤ t by omega, show 0 < b by omega,
        show b ≤ t by omega, show 22 ≤ t by omega, show a + 22 ≤ t by omega,
        show b + 22 ≤ t by omega]

end N4
