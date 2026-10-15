import Blumenthal.Expansion

/-!
# The upper bounds: Sendov's constructions

* `alpha_two_pow_le`: Szekeres' configuration of `2^m` points shows `α_{2^m} ≤ (1 - 1/m) π`.
* `alpha_three_le`: the equilateral triangle, `α_3 ≤ π/3`.
* `alpha_lower_band_le`: Sendov's three-centre configuration of `2^n + 2^(n-2)` points shows
  `α_{2^n + 2^(n-2)} ≤ (1 - 2/(2n+1)) π`.
* `sendovUpper`: the upper-bound half of Blumenthal's problem, `SendovUpper`.

All configurations are multi-scale expansions (`Blumenthal.Expansion`); the angle conditions reduce
to integer inequalities on direction indices, checked by `omega`.
-/

open EuclideanGeometry InnerProductGeometry Real

namespace Blumenthal

/-- Bit `j` of `b`, `false` beyond its length. -/
def bit {k : ℕ} (b : Fin k → Bool) (j : ℕ) : Bool := if h : j < k then b ⟨j, h⟩ else false

lemma lt_of_bit_ne {k : ℕ} {b b' : Fin k → Bool} {j : ℕ} (h : bit b j ≠ bit b' j) : j < k := by
  by_contra hj
  simp [bit, hj] at h

lemma exists_bit_ne {k : ℕ} {b b' : Fin k → Bool} (h : b ≠ b') : ∃ j, bit b j ≠ bit b' j := by
  obtain ⟨⟨j, hj⟩, hne⟩ := Function.ne_iff.1 h
  exact ⟨j, by simpa [bit, hj] using hne⟩

/-! ### Szekeres' configuration -/

/-- Digit `j` of the point `v`: the unit vector at angle `jπ/m` if bit `j` is set. -/
noncomputable def szDigit (m : ℕ) (v : Fin m → Bool) (j : ℕ) : ℂ :=
  if bit v j then cis ((j : ℝ) * π / m) else 0

lemma szDigit_ne_iff {m : ℕ} {v w : Fin m → Bool} {j : ℕ} :
    szDigit m v j ≠ szDigit m w j ↔ bit v j ≠ bit w j := by
  unfold szDigit
  cases bit v j <;> cases bit w j <;> simp [cis_ne_zero, (cis_ne_zero _).symm]

/-- Lead index: the first differing bit `t`, plus `m` if the apex has bit `t` set. -/
noncomputable def szIdx (m : ℕ) (v v' : Fin m → Bool) : ℤ :=
  (fd m (szDigit m v) (szDigit m v') : ℤ) +
    (if bit v' (fd m (szDigit m v) (szDigit m v')) then (m : ℤ) else 0)

lemma sz_hdiff {m : ℕ} {v v' : Fin m → Bool} (h : v ≠ v') :
    ∃ j, j < m ∧ szDigit m v j ≠ szDigit m v' j := by
  obtain ⟨j, hj⟩ := exists_bit_ne h
  exact ⟨j, lt_of_bit_ne hj, szDigit_ne_iff.2 hj⟩

theorem alpha_two_pow_le (m : ℕ) (hm : 2 ≤ m) : alpha (2 ^ m) ≤ (1 - 1 / m) * π := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have key := alpha_le_of_construction m 1 (by omega) (by omega) (ι := Fin m → Bool) m
    (szDigit m) (fun v v' h => sz_hdiff h) (szIdx m) ?_ ?_
  · simpa [show ((m : ℝ) - 1) * π / m = (1 - 1 / m) * π by field_simp] using key
  · intro v v' h
    obtain ⟨ht, hne, -⟩ := fd_spec (sz_hdiff h)
    generalize hT : fd m (szDigit m v) (szDigit m v') = t at ht hne
    have hb := szDigit_ne_iff.1 hne
    refine ⟨1, one_pos, ?_⟩
    simp only [lead, szIdx, hT, Complex.ofReal_one, one_mul]
    cases hv' : bit v' t
    · have hv : bit v t = true := by simpa [hv'] using hb
      simp [szDigit, hv, hv']
    · have hv : bit v t = false := by simpa [hv'] using hb
      simp only [szDigit, hv, hv', if_false, if_true, zero_sub, neg_cis]
      congr 1
      push_cast
      field_simp
      try rw [show π * ((t : ℝ) + (m : ℝ)) / (m : ℝ) = (t : ℝ) * π / m + π by field_simp; try ring,
        ← neg_cis, zero_sub]
  · intro v v' v'' h1 h2 h3
    obtain ⟨ht1, -, -⟩ := fd_spec (sz_hdiff h1)
    obtain ⟨ht2, -, -⟩ := fd_spec (sz_hdiff h2)
    apply good_of
    simp only [szIdx]
    set t1 := fd m (szDigit m v) (szDigit m v')
    set t2 := fd m (szDigit m v'') (szDigit m v')
    by_cases ht : t1 = t2
    · rw [ht]
      left
      constructor <;> push_cast <;> linarith
    · split_ifs <;> push_cast <;> omega

/-! ### The equilateral triangle -/

/-- Vertices `0`, `1`, `e^{iπ/3}`. -/
noncomputable def triDigit (i : Fin 3) (_j : ℕ) : ℂ := ![0, 1, cis (π / 3)] i

/-- Direction indices (multiples of `π/3`) from apex `i'` to `i`. -/
def triIdx (i i' : Fin 3) : ℤ := ![![0, 3, 4], ![0, 0, -1], ![1, 2, 0]] i i'

lemma cis_pi_div_three : cis (π / 3) = 1 / 2 + (Real.sqrt 3 / 2 : ℝ) * Complex.I := by
  apply Complex.ext <;> simp [cis_re, cis_im, Real.cos_pi_div_three, Real.sin_pi_div_three]

lemma cos_two_pi_div_three : Real.cos (2 * π / 3) = -1 / 2 := by
  rw [show 2 * π / 3 = π - π / 3 by ring, Real.cos_pi_sub, Real.cos_pi_div_three]; ring

lemma sin_two_pi_div_three : Real.sin (2 * π / 3) = Real.sqrt 3 / 2 := by
  rw [show 2 * π / 3 = π - π / 3 by ring, Real.sin_pi_sub, Real.sin_pi_div_three]

lemma cos_four_pi_div_three : Real.cos (4 * π / 3) = -1 / 2 := by
  rw [show 4 * π / 3 = π / 3 + π by ring, Real.cos_add_pi, Real.cos_pi_div_three]; ring

lemma sin_four_pi_div_three : Real.sin (4 * π / 3) = -(Real.sqrt 3 / 2) := by
  rw [show 4 * π / 3 = π / 3 + π by ring, Real.sin_add_pi, Real.sin_pi_div_three]

lemma cos_three_pi_div_three : Real.cos (3 * π / 3) = -1 := by
  rw [show 3 * π / 3 = π by ring, Real.cos_pi]

lemma sin_three_pi_div_three : Real.sin (3 * π / 3) = 0 := by
  rw [show 3 * π / 3 = π by ring, Real.sin_pi]

theorem alpha_three_le : alpha 3 ≤ π / 3 := by
  have hs : (0 : ℝ) < Real.sqrt 3 := by positivity
  have hdiff : ∀ i i' : Fin 3, i ≠ i' → ∃ j, j < 1 ∧ triDigit i j ≠ triDigit i' j := by
    intro i i' h
    refine ⟨0, one_pos, ?_⟩
    intro he
    have hre := congrArg Complex.re he
    have him := congrArg Complex.im he
    fin_cases i <;> fin_cases i' <;>
      simp [triDigit, cis_pi_div_three] at hre him h <;> linarith
  have key := alpha_le_of_construction 3 2 (by norm_num) (by norm_num) (ι := Fin 3) 1 triDigit
    hdiff (fun i i' => triIdx i i') ?_ ?_
  · simpa [show ((3 : ℝ) - 2) * π / 3 = π / 3 by ring] using key
  · intro i i' h
    refine ⟨1, one_pos, ?_⟩
    have hfd : fd 1 (triDigit i) (triDigit i') = 0 := by
      obtain ⟨j, hj, hne⟩ := hdiff i i' h
      have : j = 0 := by omega
      subst this
      exact fd_eq one_pos (fun j hj => absurd hj (Nat.not_lt_zero _)) hne
    simp only [lead, hfd, Complex.ofReal_one, one_mul]
    apply Complex.ext <;>
    fin_cases i <;> fin_cases i' <;> first
      | exact absurd rfl h
      | simp [triDigit, triIdx, cis_re, cis_im, cis_pi_div_three, cos_two_pi_div_three,
          sin_two_pi_div_three, cos_four_pi_div_three, sin_four_pi_div_three,
          cos_three_pi_div_three, sin_three_pi_div_three, neg_div] <;> norm_num
  · intro i i' i'' h1 h2 h3
    apply good_of
    fin_cases i <;> fin_cases i' <;> fin_cases i'' <;> simp_all [triIdx] <;> try norm_num

/-! ### Sendov's three-centre configuration -/

section ThreeCentre

variable (n : ℕ)

/-- Number of internal levels of each cluster: `n-1`, `n-1`, `n-2`. -/
def kc (c : Fin 3) : ℕ := if c = 2 then n - 2 else n - 1

/-- Points of the configuration: a cluster index and the bits of the point inside the cluster. -/
abbrev TC := Σ c : Fin 3, (Fin (kc n c) → Bool)

/-- `K = 2n + 1`; all directions are integer multiples of `π/K`. -/
abbrev KK : ℕ := 2 * n + 1

/-- `ρ = 1 / (2 cos(π/K))`. -/
noncomputable def rho : ℝ := 1 / (2 * Real.cos (π / (2 * n + 1)))

/-- The three centres: an isosceles triangle with base angles `π/K` and apex angle `(1 - 2/K) π`. -/
noncomputable def zc : Fin 3 → ℂ := ![0, 1, (rho n : ℂ) * cis (π / (2 * n + 1))]

/-- Direction index of internal level `j ≥ 1`: `±(2j + 1)`, i.e. `±(λ/2 + jλ)` with `λ = 2π/K`. -/
def dirI (c : Fin 3) (j : ℕ) : ℤ := if c = 1 then -(2 * j + 1) else 2 * j + 1

noncomputable def tcDigit (i : TC n) (j : ℕ) : ℂ :=
  if j = 0 then zc n i.1
  else if bit i.2 (j - 1) then cis ((dirI i.1 j : ℝ) * π / (KK n : ℕ)) else 0

/-- Index of the direction from centre `a` (apex) to centre `b`. -/
def itab (K : ℤ) (a b : Fin 3) : ℤ := ![![0, 0, 1], ![K, 0, K - 1], ![K + 1, -1, 0]] a b

noncomputable def tcIdx (i i' : TC n) : ℤ :=
  if i.1 = i'.1 then
    dirI i.1 (fd n (tcDigit n i) (tcDigit n i')) +
      (if bit i'.2 (fd n (tcDigit n i) (tcDigit n i') - 1) then ((KK n : ℕ) : ℤ) else 0)
  else itab ((KK n : ℕ) : ℤ) i'.1 i.1

variable {n}

/-- `D` is within `K - s` of a multiple of `2K`. -/
def Good (K s D : ℤ) : Prop := ∃ q : ℤ, |D - 2 * K * q| ≤ K - s

lemma Good.neg {K s D : ℤ} (h : Good K s D) : Good K s (-D) := by
  obtain ⟨q, hq⟩ := h
  exact ⟨-q, by rw [show -D - 2 * K * -q = -(D - 2 * K * q) by ring, abs_neg]; exact hq⟩

lemma good_intra (hn : 2 ≤ n) (c : Fin 3) {f₁ f₂ : ℕ} (h₁ : 1 ≤ f₁) (h₁' : f₁ - 1 < kc n c)
    (h₂ : 1 ≤ f₂) (h₂' : f₂ - 1 < kc n c) (hne : f₁ ≠ f₂) (x y : Bool) :
    Good ((KK n : ℕ) : ℤ) 2 (dirI c f₁ + (if x then ((KK n : ℕ) : ℤ) else 0) -
      (dirI c f₂ + (if y then ((KK n : ℕ) : ℤ) else 0))) := by
  apply good_of
  simp only [KK]
  push_cast
  fin_cases c <;> simp [kc] at h₁' h₂' <;> simp [dirI] <;> cases x <;> cases y <;> simp <;> omega

lemma good_intra_inter (hn : 2 ≤ n) (c c'' : Fin 3) (hc : c'' ≠ c) {f : ℕ} (h₁ : 1 ≤ f)
    (h₁' : f - 1 < kc n c) (x : Bool) :
    Good ((KK n : ℕ) : ℤ) 2 (dirI c f + (if x then ((KK n : ℕ) : ℤ) else 0) -
      itab ((KK n : ℕ) : ℤ) c c'') := by
  apply good_of
  simp only [KK]
  push_cast
  fin_cases c <;> fin_cases c'' <;> simp [kc] at h₁' hc <;> simp [dirI, itab] <;>
    cases x <;> simp <;> omega

lemma good_inter (hn : 2 ≤ n) (c' c c'' : Fin 3) (h₁ : c ≠ c') (h₂ : c'' ≠ c') :
    Good ((KK n : ℕ) : ℤ) 2 (itab ((KK n : ℕ) : ℤ) c' c - itab ((KK n : ℕ) : ℤ) c' c'') := by
  apply good_of
  simp only [KK]
  push_cast
  fin_cases c' <;> fin_cases c <;> fin_cases c'' <;> simp [itab] at h₁ h₂ ⊢ <;> omega

lemma Kn_ge (hn : 2 ≤ n) : (5 : ℝ) ≤ 2 * n + 1 := by
  have : (2 : ℝ) ≤ n := by exact_mod_cast hn
  linarith

lemma cos_gam_pos (hn : 2 ≤ n) : 0 < Real.cos (π / (2 * n + 1)) := by
  have hK := Kn_ge hn
  apply Real.cos_pos_of_mem_Ioo
  constructor
  · have : 0 < π / (2 * n + 1) := by positivity
    linarith [pi_pos]
  · rw [div_lt_div_iff₀ (by linarith) (by norm_num)]
    nlinarith [pi_pos]

lemma sin_gam_pos (hn : 2 ≤ n) : 0 < Real.sin (π / (2 * n + 1)) := by
  have hK := Kn_ge hn
  apply Real.sin_pos_of_pos_of_lt_pi (by positivity)
  rw [div_lt_iff₀ (by linarith)]
  nlinarith [pi_pos]

lemma rho_pos (hn : 2 ≤ n) : 0 < rho n := by
  have := cos_gam_pos hn
  unfold rho
  positivity

lemma rho_cos (hn : 2 ≤ n) : rho n * Real.cos (π / (2 * n + 1)) = 1 / 2 := by
  have := (cos_gam_pos hn).ne'
  unfold rho
  field_simp

lemma zc_ne (hn : 2 ≤ n) {a b : Fin 3} (h : a ≠ b) : zc n a ≠ zc n b := by
  have him : ((rho n : ℂ) * cis (π / (2 * n + 1))).im ≠ 0 := by
    rw [Complex.im_ofReal_mul, cis_im]
    exact (mul_pos (rho_pos hn) (sin_gam_pos hn)).ne'
  have hw0 : (rho n : ℂ) * cis (π / (2 * n + 1)) ≠ 0 := fun e => him (by rw [e]; simp)
  have hw1 : (rho n : ℂ) * cis (π / (2 * n + 1)) ≠ 1 := fun e => him (by rw [e]; simp)
  fin_cases a <;> fin_cases b <;> simp [zc, hw0, hw1, hw0.symm, hw1.symm] at h ⊢

lemma zc_lead (hn : 2 ≤ n) {a b : Fin 3} (h : b ≠ a) :
    ∃ r : ℝ, 0 < r ∧ zc n b - zc n a =
      (r : ℂ) * cis ((itab ((KK n : ℕ) : ℤ) a b : ℝ) * π / (KK n : ℕ)) := by
  have hK := Kn_ge hn
  have hr := rho_pos hn
  have hrc := rho_cos hn
  have e1 : (2 * (n : ℝ) + 1) * π / (2 * n + 1) = π := by field_simp
  have e2 : (2 * (n : ℝ) + 1 - 1) * π / (2 * n + 1) = π - π / (2 * n + 1) := by
    field_simp; try ring
  have e2' : 2 * (n : ℝ) * π / (2 * n + 1) = π - π / (2 * n + 1) := by
    field_simp; try ring
  have e3 : (2 * (n : ℝ) + 1 + 1) * π / (2 * n + 1) = π / (2 * n + 1) + π := by
    field_simp; try ring
  have e3' : (2 * (n : ℝ) + 2) * π / (2 * n + 1) = π / (2 * n + 1) + π := by
    field_simp; try ring
  have e4 : (-1 : ℝ) * π / (2 * n + 1) = -(π / (2 * n + 1)) := by ring
  have e5 : (1 : ℝ) * π / (2 * n + 1) = π / (2 * n + 1) := by ring
  fin_cases a <;> fin_cases b
  · exact absurd rfl h
  · exact ⟨1, one_pos, Complex.ext (by simp [zc, itab, cis_re]) (by simp [zc, itab, cis_im])⟩
  · refine ⟨rho n, hr, ?_⟩
    apply Complex.ext <;> simp [zc, itab, cis_re, cis_im, e5]
  · refine ⟨1, one_pos, ?_⟩
    apply Complex.ext <;> simp [zc, itab, cis_re, cis_im, e1]
  · exact absurd rfl h
  · refine ⟨rho n, hr, ?_⟩
    apply Complex.ext <;> simp [zc, itab, cis_re, cis_im, e2, e2', Real.cos_pi_sub, Real.sin_pi_sub] <;>
      first | linarith | nlinarith [hrc] | (ring_nf; ring_nf at hrc; linarith)
  · refine ⟨rho n, hr, ?_⟩
    apply Complex.ext <;> simp [zc, itab, cis_re, cis_im, e3, e3', Real.cos_add_pi, Real.sin_add_pi]
  · refine ⟨rho n, hr, ?_⟩
    apply Complex.ext <;> simp [zc, itab, cis_re, cis_im, e4, Real.cos_neg, Real.sin_neg] <;>
      first | linarith | (rw [neg_div, Real.cos_neg]; linarith) | (rw [neg_div, Real.sin_neg]; linarith)
  · exact absurd rfl h

lemma tc_hdiff (hn : 2 ≤ n) {i i' : TC n} (h : i ≠ i') :
    ∃ j, j < n ∧ tcDigit n i j ≠ tcDigit n i' j := by
  obtain ⟨c, b⟩ := i
  obtain ⟨c', b'⟩ := i'
  by_cases hc : c = c'
  · subst hc
    have hb : b ≠ b' := fun hb => h (by rw [hb])
    obtain ⟨j, hj⟩ := exists_bit_ne hb
    have hjk := lt_of_bit_ne hj
    have hkn : kc n c ≤ n - 1 := by unfold kc; split_ifs <;> omega
    refine ⟨j + 1, by omega, ?_⟩
    simp only [tcDigit, Nat.add_sub_cancel, if_neg (Nat.succ_ne_zero j)]
    revert hj
    cases bit b j <;> cases bit b' j <;> simp [cis_ne_zero, (cis_ne_zero _).symm]
  · exact ⟨0, by omega, by simpa [tcDigit] using zc_ne hn hc⟩

/-- Facts about the first differing level inside one cluster. -/
lemma tc_fd_same (hn : 2 ≤ n) {c : Fin 3} {b b' : Fin (kc n c) → Bool}
    (h : (⟨c, b⟩ : TC n) ≠ ⟨c, b'⟩) :
    1 ≤ fd n (tcDigit n ⟨c, b⟩) (tcDigit n ⟨c, b'⟩) ∧
      fd n (tcDigit n ⟨c, b⟩) (tcDigit n ⟨c, b'⟩) - 1 < kc n c ∧
      bit b (fd n (tcDigit n ⟨c, b⟩) (tcDigit n ⟨c, b'⟩) - 1) ≠
        bit b' (fd n (tcDigit n ⟨c, b⟩) (tcDigit n ⟨c, b'⟩) - 1) := by
  obtain ⟨-, hne, -⟩ := fd_spec (tc_hdiff hn h)
  generalize fd n (tcDigit n ⟨c, b⟩) (tcDigit n ⟨c, b'⟩) = f at hne ⊢
  have hf : f ≠ 0 := by
    intro hf0
    rw [hf0] at hne
    simp [tcDigit] at hne
  have hb : bit b (f - 1) ≠ bit b' (f - 1) := by
    intro hbe
    apply hne
    simp only [tcDigit, if_neg hf, hbe]
  exact ⟨Nat.one_le_iff_ne_zero.2 hf, lt_of_bit_ne hb, hb⟩

theorem alpha_lower_band_le (hn : 2 ≤ n) :
    alpha (2 ^ n + 2 ^ (n - 2)) ≤ (1 - 2 / (2 * n + 1 : ℝ)) * π := by
  have hcard : Fintype.card (TC n) = 2 ^ n + 2 ^ (n - 2) := by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    rw [Fintype.card_sigma, Fin.sum_univ_three]
    simp [kc, Fintype.card_fun]
    ring
  have key := alpha_le_of_construction (KK n) 2 (by positivity) (by simp only [KK]; omega)
    (ι := TC n) n (tcDigit n) (fun i i' h => tc_hdiff hn h) (tcIdx n) ?_ ?_
  · rw [hcard] at key
    have e : ((KK n : ℕ) - (2 : ℕ) : ℝ) * π / (KK n : ℕ) = (1 - 2 / (2 * n + 1 : ℝ)) * π := by
      simp only [KK]
      push_cast
      field_simp
      try ring
    exact key.trans_eq e
  · rintro ⟨c, b⟩ ⟨c', b'⟩ h
    by_cases hc : c = c'
    · subst hc
      obtain ⟨hf1, -, hb⟩ := tc_fd_same hn h
      refine ⟨1, one_pos, ?_⟩
      dsimp only [lead, tcIdx]
      rw [if_pos rfl]
      generalize fd n (tcDigit n ⟨c, b⟩) (tcDigit n ⟨c, b'⟩) = f at hf1 hb ⊢
      have hf0 : f ≠ 0 := by omega
      simp only [tcDigit, if_neg hf0, Complex.ofReal_one, one_mul]
      revert hb
      cases bit b (f - 1) <;> cases bit b' (f - 1) <;> intro hb <;> simp at hb
      · simp only [if_true, if_false, zero_sub, neg_cis]
        congr 1
        push_cast
        field_simp
        try rw [show π * (((dirI c f : ℤ) : ℝ) + (2 * (n : ℝ) + 1)) / (2 * (n : ℝ) + 1) =
          ((dirI c f : ℤ) : ℝ) * π / (2 * n + 1) + π by field_simp; try ring, ← neg_cis, zero_sub]
      · simp
    · have hfd : fd n (tcDigit n ⟨c, b⟩) (tcDigit n ⟨c', b'⟩) = 0 :=
        fd_eq (by omega) (fun j hj => absurd hj (Nat.not_lt_zero _))
          (by simpa [tcDigit] using zc_ne hn hc)
      obtain ⟨r, hr, e⟩ := zc_lead hn hc
      refine ⟨r, hr, ?_⟩
      dsimp only [lead, tcIdx]
      rw [hfd, if_neg hc]
      simpa [tcDigit] using e
  · rintro ⟨c, b⟩ ⟨c', b'⟩ ⟨c'', b''⟩ h1 h2 h3
    change Good _ _ _
    by_cases hc1 : c = c'
    · subst hc1
      obtain ⟨f1a, f1b, -⟩ := tc_fd_same hn h1
      by_cases hc2 : c'' = c
      · subst hc2
        obtain ⟨f2a, f2b, -⟩ := tc_fd_same hn h2
        dsimp only [tcIdx]
        rw [if_pos rfl, if_pos rfl]
        generalize fd n (tcDigit n ⟨c'', b⟩) (tcDigit n ⟨c'', b'⟩) = f₁ at f1a f1b ⊢
        generalize fd n (tcDigit n ⟨c'', b''⟩) (tcDigit n ⟨c'', b'⟩) = f₂ at f2a f2b ⊢
        by_cases hf : f₁ = f₂
        · subst hf
          refine ⟨0, ?_⟩
          simp only [KK]
          push_cast
          rw [sub_self, mul_zero, sub_zero, abs_zero]
          omega
        · exact good_intra hn c'' f1a f1b f2a f2b hf _ _
      · dsimp only [tcIdx]
        rw [if_pos rfl, if_neg hc2]
        generalize fd n (tcDigit n ⟨c, b⟩) (tcDigit n ⟨c, b'⟩) = f₁ at f1a f1b ⊢
        exact good_intra_inter hn c c'' hc2 f1a f1b _
    · by_cases hc2 : c'' = c'
      · subst hc2
        obtain ⟨f2a, f2b, -⟩ := tc_fd_same hn h2
        dsimp only [tcIdx]
        rw [if_neg hc1, if_pos rfl]
        generalize fd n (tcDigit n ⟨c'', b''⟩) (tcDigit n ⟨c'', b'⟩) = f₂ at f2a f2b ⊢
        have := (good_intra_inter hn c'' c hc1 f2a f2b (bit b' (f₂ - 1))).neg
        convert this using 1
        ring
      · dsimp only [tcIdx]
        rw [if_neg hc1, if_neg hc2]
        exact good_inter hn c' c c'' hc1 hc2

end ThreeCentre

/-! ### The upper-bound half of Blumenthal's problem -/

theorem sendovUpper : SendovUpper := by
  refine ⟨alpha_three_le, ?_, ?_⟩
  · have := alpha_two_pow_le 2 le_rfl
    norm_num at this
    linarith
  · intro n N hn h1 h2
    unfold bandValue
    split_ifs with hband
    · calc alpha N ≤ alpha (2 ^ n + 2 ^ (n - 2)) := by
            apply alpha_mono _ hband
            have : 4 ≤ 2 ^ n := by
              calc 4 = 2 ^ 2 := by norm_num
                _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
            omega
        _ ≤ (1 - 2 / (2 * n + 1 : ℝ)) * π := alpha_lower_band_le hn
    · calc alpha N ≤ alpha (2 ^ (n + 1)) := by
            apply alpha_mono _ h2
            have : 4 ≤ 2 ^ n := by
              calc 4 = 2 ^ 2 := by norm_num
                _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
            omega
        _ ≤ (1 - 1 / ((n + 1 : ℕ) : ℝ)) * π := alpha_two_pow_le (n + 1) (by omega)
        _ = (1 - 1 / (n + 1 : ℝ)) * π := by push_cast; ring

end Blumenthal

namespace Blumenthal

/-- Every triangle has an angle `≥ π/3`, so `α_3 = π/3`. -/
theorem alpha_three : alpha 3 = π / 3 := by
  refine le_antisymm alpha_three_le (le_alpha (by positivity) (by linarith [pi_pos]) fun A hA => ?_)
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.1 hA
  have hsum := EuclideanGeometry.angle_add_angle_add_angle_eq_pi z hxy.symm
  by_contra hno
  simp only [HasAngleGE, Finset.mem_insert, Finset.mem_singleton, not_exists, not_and,
    not_le] at hno
  have h1 := hno x (by simp) y (by simp) z (by simp) hxy hyz hxz
  have h2 := hno y (by simp) z (by simp) x (by simp) hyz hxz.symm hxy.symm
  have h3 := hno z (by simp) x (by simp) y (by simp) hxz.symm hxy hyz.symm
  linarith

end Blumenthal
