import Blumenthal.Dyadic

/-!
# Multi-scale constructions

A configuration is given by digit vectors `d i j ∈ ℂ` (`i` a point, `j < m` a level) and realised
as `p_i(ε) = ∑_j ε^j d i j`. As `ε → 0⁺` the direction from `p_{i'}` to `p_i` tends to the
*lead* `d i t - d i' t`, where `t` is the first level at which the digits differ. Hence every angle
`∠ p_i p_{i'} p_{i''}` tends to the angle between two leads.

`alpha_le_of_construction`: if every lead is a positive multiple of `e^{iπ k/K}` for an integer
index `k`, and at every apex any two lead indices differ by at most `K - s` modulo `2K`, then
`α_N ≤ (K - s) π / K` with `N` the number of points.
-/

open EuclideanGeometry InnerProductGeometry Real Filter Topology

namespace Blumenthal

/-- `cis θ = e^{iθ}`. -/
noncomputable def cis (θ : ℝ) : ℂ := Complex.exp (θ * Complex.I)

lemma cis_ne_zero (θ : ℝ) : cis θ ≠ 0 := Complex.exp_ne_zero _

lemma norm_cis (θ : ℝ) : ‖cis θ‖ = 1 := Complex.norm_exp_ofReal_mul_I θ

lemma cis_re (θ : ℝ) : (cis θ).re = Real.cos θ := Complex.exp_ofReal_mul_I_re θ

lemma cis_im (θ : ℝ) : (cis θ).im = Real.sin θ := Complex.exp_ofReal_mul_I_im θ

lemma cis_div (a b : ℝ) : cis a / cis b = cis (a - b) := by
  rw [cis, cis, cis, ← Complex.exp_sub]
  congr 1
  push_cast
  ring

lemma neg_cis (θ : ℝ) : -cis θ = cis (θ + π) := by
  rw [cis, cis, show ((θ + π : ℝ) : ℂ) * Complex.I = θ * Complex.I + π * Complex.I by push_cast; ring,
    Complex.exp_add, Complex.exp_pi_mul_I]
  ring

lemma cos_angle_cis (a b : ℝ) :
    Real.cos (InnerProductGeometry.angle (cis a) (cis b)) = Real.cos (a - b) := by
  rw [Complex.angle_eq_abs_arg (cis_ne_zero a) (cis_ne_zero b), Real.cos_abs,
    Complex.cos_arg (by rw [cis_div]; exact cis_ne_zero _), cis_div, norm_cis, div_one, cis_re]

lemma angle_cis_le {a b β : ℝ} (hβ0 : 0 ≤ β) (hβ : β ≤ π) (h : Real.cos β ≤ Real.cos (a - b)) :
    InnerProductGeometry.angle (cis a) (cis b) ≤ β := by
  by_contra hlt
  push Not at hlt
  have := Real.cos_lt_cos_of_nonneg_of_le_pi hβ0 (angle_le_pi _ _) hlt
  rw [cos_angle_cis] at this
  linarith

lemma angle_posmul (a b : ℂ) {r₁ r₂ : ℝ} (h₁ : 0 < r₁) (h₂ : 0 < r₂) :
    InnerProductGeometry.angle ((r₁ : ℂ) * a) ((r₂ : ℂ) * b) = InnerProductGeometry.angle a b := by
  rw [← Complex.real_smul, ← Complex.real_smul,
    InnerProductGeometry.angle_smul_left_of_pos _ _ h₁,
    InnerProductGeometry.angle_smul_right_of_pos _ _ h₂]

/-- An integer difference that is within `K - s` of a multiple of `2K` gives a cosine bound. -/
lemma cos_le_of_good {K s : ℕ} (hK : 0 < K) (hs : s ≤ K) {D q : ℤ}
    (h : |D - 2 * K * q| ≤ (K : ℤ) - s) :
    Real.cos ((K - s : ℝ) * π / K) ≤ Real.cos (D * π / K) := by
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  have e : Real.cos (D * π / K) = Real.cos (((D - 2 * K * q : ℤ) : ℝ) * π / K) := by
    rw [show ((D - 2 * K * q : ℤ) : ℝ) * π / K = D * π / K - q * (2 * π) by
      push_cast; field_simp, Real.cos_sub_int_mul_two_pi]
  rw [e, ← Real.cos_abs (((D - 2 * K * q : ℤ) : ℝ) * π / K)]
  have hE : |(((D - 2 * K * q : ℤ) : ℝ) * π / K)| = |((D - 2 * K * q : ℤ) : ℝ)| * π / K := by
    rw [abs_div, abs_mul, abs_of_pos pi_pos, abs_of_pos hK']
  rw [hE]
  have hle : |((D - 2 * K * q : ℤ) : ℝ)| ≤ (K - s : ℝ) := by
    rw [← Int.cast_abs]
    have : ((K : ℤ) - s : ℤ) = ((K - s : ℝ) : ℝ) := by push_cast; ring
    exact_mod_cast h
  apply Real.cos_le_cos_of_nonneg_of_le_pi (by positivity)
  · rw [div_le_iff₀ hK']
    have : (0 : ℝ) ≤ s := by positivity
    nlinarith [pi_pos]
  · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hle pi_pos.le) hK'.le

/-- A sufficient case split for the index condition. -/
lemma good_of (K s D : ℤ)
    (h : (-(K - s) ≤ D ∧ D ≤ K - s) ∨ (K + s ≤ D ∧ D ≤ 3 * K - s) ∨
      (-(3 * K - s) ≤ D ∧ D ≤ -(K + s))) :
    ∃ q : ℤ, |D - 2 * K * q| ≤ K - s := by
  rcases h with h | h | h
  · exact ⟨0, by rw [abs_le]; constructor <;> linarith⟩
  · exact ⟨1, by rw [abs_le]; constructor <;> linarith⟩
  · exact ⟨-1, by rw [abs_le]; constructor <;> linarith⟩

/-! ### Expansions and leads -/

/-- `∑_{j<m} ε^j d_j`. -/
noncomputable def expand (m : ℕ) (d : ℕ → ℂ) (ε : ℝ) : ℂ :=
  ∑ j ∈ Finset.range m, (ε : ℂ) ^ j * d j

open Classical in
/-- The first level `< m` at which `f` and `g` differ (`0` if none). -/
noncomputable def fd (m : ℕ) (f g : ℕ → ℂ) : ℕ :=
  if h : ∃ j, j < m ∧ f j ≠ g j then Nat.find h else 0

/-- The leading difference `f t - g t` at the first differing level `t`. -/
noncomputable def lead (m : ℕ) (f g : ℕ → ℂ) : ℂ := f (fd m f g) - g (fd m f g)

lemma fd_spec {m : ℕ} {f g : ℕ → ℂ} (h : ∃ j, j < m ∧ f j ≠ g j) :
    fd m f g < m ∧ f (fd m f g) ≠ g (fd m f g) ∧ ∀ j < fd m f g, f j = g j := by
  classical
  have e : fd m f g = Nat.find h := by rw [fd, dif_pos h]
  rw [e]
  refine ⟨(Nat.find_spec h).1, (Nat.find_spec h).2, fun j hj => ?_⟩
  by_contra hne
  have := Nat.find_min h hj
  push Not at this
  exact hne (this (lt_trans hj (Nat.find_spec h).1))

lemma fd_eq {m t : ℕ} {f g : ℕ → ℂ} (ht : t < m) (heq : ∀ j < t, f j = g j) (hne : f t ≠ g t) :
    fd m f g = t := by
  classical
  have h : ∃ j, j < m ∧ f j ≠ g j := ⟨t, ht, hne⟩
  rw [fd, dif_pos h, Nat.find_eq_iff]
  refine ⟨⟨ht, hne⟩, fun j hj hP => hP.2 (heq j hj)⟩

lemma tendsto_lead {m : ℕ} {f g : ℕ → ℂ} (h : ∃ j, j < m ∧ f j ≠ g j) :
    Tendsto (fun ε : ℝ => ((ε ^ fd m f g)⁻¹ : ℝ) • (expand m f ε - expand m g ε))
      (𝓝[>] 0) (𝓝 (lead m f g)) := by
  obtain ⟨htm, -, hbefore⟩ := fd_spec h
  set t := fd m f g with ht
  let G : ℝ → ℂ := fun ε =>
    ∑ j ∈ Finset.range m, (if j < t then 0 else (ε : ℂ) ^ (j - t) * (f j - g j))
  have hG : Continuous G := by
    apply continuous_finsetSum
    intro j _
    split_ifs
    · exact continuous_const
    · exact ((Complex.continuous_ofReal.pow _).mul continuous_const)
  have hG0 : G 0 = lead m f g := by
    simp only [G]
    rw [Finset.sum_eq_single t]
    · simp [lead, ← ht]
    · intro j _ hjt
      split_ifs with hj
      · rfl
      · have : 0 < j - t := by omega
        simp [zero_pow this.ne']
    · intro hn
      exact absurd (Finset.mem_range.2 htm) hn
  have heq : G =ᶠ[𝓝[>] 0]
      (fun ε : ℝ => ((ε ^ t)⁻¹ : ℝ) • (expand m f ε - expand m g ε)) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε0 : (ε : ℂ) ≠ 0 := by
      have : (0 : ℝ) < ε := hε
      exact_mod_cast this.ne'
    simp only [G, expand, ← Finset.sum_sub_distrib, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs with hj
    · rw [hbefore j hj]
      simp
    · rw [Complex.real_smul]
      have hp : (ε : ℂ) ^ j = (ε : ℂ) ^ t * (ε : ℂ) ^ (j - t) := by
        rw [← pow_add]
        congr 1
        omega
      rw [hp]
      push_cast
      field_simp
  have := (hG.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  rw [hG0] at this
  exact this.congr' heq

/-! ### The general construction theorem -/

theorem alpha_le_of_construction (K s : ℕ) (hK : 0 < K) (hs : s ≤ K)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (m : ℕ) (d : ι → ℕ → ℂ)
    (hdiff : ∀ i i', i ≠ i' → ∃ j, j < m ∧ d i j ≠ d i' j)
    (idx : ι → ι → ℤ)
    (hlead : ∀ i i', i ≠ i' →
      ∃ r : ℝ, 0 < r ∧ lead m (d i) (d i') = (r : ℂ) * cis (idx i i' * π / K))
    (hgood : ∀ i i' i'', i ≠ i' → i'' ≠ i' → i ≠ i'' →
      ∃ q : ℤ, |idx i i' - idx i'' i' - 2 * K * q| ≤ (K : ℤ) - s) :
    alpha (Fintype.card ι) ≤ (K - s : ℝ) * π / K := by
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  have hsK : (s : ℝ) ≤ K := by exact_mod_cast hs
  set β : ℝ := (K - s : ℝ) * π / K with hβdef
  have hβ0 : 0 ≤ β := by
    rw [hβdef]
    apply div_nonneg (mul_nonneg (by linarith) pi_pos.le) hK'.le
  have hβπ : β ≤ π := by
    rw [hβdef, div_le_iff₀ hK']
    have : (0 : ℝ) ≤ s := by positivity
    nlinarith [pi_pos]
  -- leads are nonzero and their angles are at most `β`
  have hlead0 : ∀ i i', i ≠ i' → lead m (d i) (d i') ≠ 0 := by
    intro i i' h
    obtain ⟨r, hr, e⟩ := hlead i i' h
    rw [e]
    exact mul_ne_zero (by exact_mod_cast hr.ne') (cis_ne_zero _)
  have hleadang : ∀ i i' i'', i ≠ i' → i'' ≠ i' → i ≠ i'' →
      InnerProductGeometry.angle (lead m (d i) (d i')) (lead m (d i'') (d i')) ≤ β := by
    intro i i' i'' h1 h2 h3
    obtain ⟨r₁, hr₁, e₁⟩ := hlead i i' h1
    obtain ⟨r₂, hr₂, e₂⟩ := hlead i'' i' h2
    obtain ⟨q, hq⟩ := hgood i i' i'' h1 h2 h3
    rw [e₁, e₂, angle_posmul _ _ hr₁ hr₂]
    apply angle_cis_le hβ0 hβπ
    rw [show (idx i i' : ℝ) * π / K - idx i'' i' * π / K = ((idx i i' - idx i'' i' : ℤ) : ℝ) * π / K by
      push_cast; ring]
    exact cos_le_of_good hK hs hq
  set P : ι → ℝ → ℂ := fun i ε => expand m (d i) ε with hP
  have hT : ∀ i i', i ≠ i' → Tendsto
      (fun ε : ℝ => ((ε ^ fd m (d i) (d i'))⁻¹ : ℝ) • (P i ε - P i' ε)) (𝓝[>] 0)
      (𝓝 (lead m (d i) (d i'))) := fun i i' h => tendsto_lead (hdiff i i' h)
  -- eventually the points are distinct
  have hdist : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ i i', i ≠ i' → P i ε ≠ P i' ε := by
    refine Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun i' => ?_
    by_cases h : i = i'
    · exact Filter.Eventually.of_forall fun _ h' => absurd h h'
    · filter_upwards [(hT i i' h).eventually_ne (hlead0 i i' h)] with ε hε _ hEq
      rw [hEq, sub_self, smul_zero] at hε
      exact hε rfl
  -- eventually every angle is below `β + η`
  refine alpha_le_of_approx hβ0 fun η hη => ?_
  have hang : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ i i' i'', i ≠ i' → i'' ≠ i' → i ≠ i'' →
      InnerProductGeometry.angle (P i ε - P i' ε) (P i'' ε - P i' ε) < β + η := by
    refine Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun i' =>
      Filter.eventually_all.2 fun i'' => ?_
    by_cases h : i ≠ i' ∧ i'' ≠ i' ∧ i ≠ i''
    · obtain ⟨h1, h2, h3⟩ := h
      have hc := InnerProductGeometry.continuousAt_angle (V := ℂ)
        (x := (lead m (d i) (d i'), lead m (d i'') (d i'))) (hlead0 i i' h1) (hlead0 i'' i' h2)
      have hpair := (hT i i' h1).prodMk_nhds (hT i'' i' h2)
      have hlim := hc.tendsto.comp hpair
      have hev := hlim.eventually (gt_mem_nhds
        (show InnerProductGeometry.angle (lead m (d i) (d i')) (lead m (d i'') (d i')) < β + η by
          linarith [hleadang i i' i'' h1 h2 h3]))
      filter_upwards [hev, self_mem_nhdsWithin] with ε hε hε0 _ _ _
      have hpos : (0 : ℝ) < ε := hε0
      simp only [Function.comp_apply] at hε
      rwa [InnerProductGeometry.angle_smul_left_of_pos _ _ (by positivity),
        InnerProductGeometry.angle_smul_right_of_pos _ _ (by positivity)] at hε
    · exact Filter.Eventually.of_forall fun _ a b c => absurd ⟨a, b, c⟩ h
  obtain ⟨ε, hε1, hε2⟩ := (hdist.and hang).exists
  classical
  let A : Finset Plane := Finset.univ.image fun i => toC.symm (P i ε)
  have hinj : Function.Injective fun i => toC.symm (P i ε) := by
    intro i i' h
    by_contra hne
    exact hε1 i i' hne (toC.symm.injective h)
  refine ⟨A, by rw [Finset.card_image_of_injective _ hinj, Finset.card_univ], ?_⟩
  intro x hx y hy z hz hxy hyz hxz
  simp only [A, Finset.mem_image, Finset.mem_univ, true_and] at hx hy hz
  obtain ⟨i, rfl⟩ := hx
  obtain ⟨i', rfl⟩ := hy
  obtain ⟨i'', rfl⟩ := hz
  have h1 : i ≠ i' := fun h => hxy (by rw [h])
  have h2 : i'' ≠ i' := fun h => hyz (by rw [h])
  have h3 : i ≠ i'' := fun h => hxz (by rw [h])
  simp only [EuclideanGeometry.angle, vsub_eq_sub, ← map_sub]
  have hmap := toC.symm.toLinearIsometry.angle_map (P i ε - P i' ε) (P i'' ε - P i' ε)
  simp only [LinearIsometryEquiv.coe_toLinearIsometry] at hmap
  rw [hmap]
  exact (hε2 i i' i'' h1 h2 h3).le

end Blumenthal
