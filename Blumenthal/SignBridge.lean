import Blumenthal.SignSeq

/-!
# From odd sign functions to sign sequences; (R) for `n ≤ 3`

Every odd `f : ℝ → Bool` with runs `≥ ℓ` agrees, away from its sign changes, with the value of a
sign sequence (`exists_signSeq`): its sign changes (the points where `f` is not locally constant)
are `ℓ` apart and `π`-periodic, so they can be listed as `y : ℤ → ℝ`. Compatibility of two
functions passes to their sign sequences (`compat_of_rep`). With the sign-sequence results of
`Blumenthal.SignSeq` this proves `StatementR n` for `n ≤ 3` (`statementR_of_le_three`).
-/

open Real Set Filter Topology

namespace Blumenthal

namespace SignBridge

variable {ℓ : ℝ} {f : ℝ → Bool}

lemma bool_eq_not_of_ne {a b : Bool} (h : a ≠ b) : b = !a := by
  cases a <;> cases b <;> simp_all

/-- `f` is locally constant at `t`. The sign changes of `f` are the points where it is not. -/
def LC (f : ℝ → Bool) (t : ℝ) : Prop := ∀ᶠ x in 𝓝 t, f x = f t

lemma lc_iff {t : ℝ} : LC f t ↔ ∃ δ > 0, ∀ x, |x - t| < δ → f x = f t := by
  unfold LC
  rw [Metric.eventually_nhds_iff]
  simp only [Real.dist_eq]

lemma lc_add_pi (hf : IsOddSign f) (t : ℝ) : LC f (t + π) ↔ LC f t := by
  rw [lc_iff, lc_iff]
  constructor
  · rintro ⟨δ, hδ, h⟩
    refine ⟨δ, hδ, fun x hx => ?_⟩
    have := h (x + π) (by rw [show x + π - (t + π) = x - t by ring]; exact hx)
    rw [hf, hf] at this
    cases h1 : f x <;> cases h2 : f t <;> simp_all
  · rintro ⟨δ, hδ, h⟩
    refine ⟨δ, hδ, fun x hx => ?_⟩
    have := h (x - π) (by rw [show x - π - t = x - (t + π) by ring]; exact hx)
    have e : f x = !f (x - π) := by rw [← hf (x - π), sub_add_cancel]
    rw [e, this, hf]

lemma lc_add_int_mul_pi (hf : IsOddSign f) (t : ℝ) (m : ℤ) : LC f (t + m * π) ↔ LC f t := by
  refine Int.induction_on m ?_ ?_ ?_
  · simp
  · intro i ih
    have e : t + (((i : ℤ) + 1 : ℤ) : ℝ) * π = (t + (i : ℤ) * π) + π := by push_cast; ring
    rw [e, lc_add_pi hf, ih]
  · intro i ih
    have e : t + (-(i : ℤ) : ℤ) * π = (t + ((-(i : ℤ) - 1 : ℤ) : ℝ) * π) + π := by push_cast; ring
    rw [e, lc_add_pi hf] at ih
    exact ih

/-- Two sign changes are at least `ℓ` apart. -/
lemma sep (hr : RunsGE ℓ f) {t₁ t₂ : ℝ} (h₁ : ¬ LC f t₁) (h₂ : ¬ LC f t₂) (h : t₁ < t₂) :
    ℓ ≤ t₂ - t₁ := by
  by_contra hlt
  push_neg at hlt
  set δ := min ((ℓ - (t₂ - t₁)) / 2) ((t₂ - t₁) / 2) with hδdef
  have hδ : 0 < δ := lt_min (by linarith) (by linarith)
  have hδ1 : δ ≤ (ℓ - (t₂ - t₁)) / 2 := min_le_left _ _
  have hδ2 : δ ≤ (t₂ - t₁) / 2 := min_le_right _ _
  set mid := (t₁ + t₂) / 2 with hmid
  have near : ∀ t, ¬ LC f t → ∃ p, |p - t| < δ ∧ f p ≠ f mid := by
    intro t ht
    rw [lc_iff] at ht
    push_neg at ht
    obtain ⟨x, hx, hfx⟩ := ht δ hδ
    by_cases hm : f t = f mid
    · exact ⟨x, hx, by rwa [← hm]⟩
    · exact ⟨t, by simpa using hδ, hm⟩
  obtain ⟨p₁, hp₁, hf₁⟩ := near t₁ h₁
  obtain ⟨p₂, hp₂, hf₂⟩ := near t₂ h₂
  rw [abs_lt] at hp₁ hp₂
  have heq : f p₁ = f p₂ := by
    revert hf₁ hf₂
    generalize f p₁ = a
    generalize f p₂ = b
    generalize f mid = c
    cases a <;> cases b <;> cases c <;> simp
  have key := hr p₁ mid p₂ (by linarith) (by linarith) (by linarith) heq
  exact hf₁ key.symm

lemma continuousAt_of_lc {t : ℝ} (h : LC f t) : ContinuousAt f t :=
  tendsto_nhds_of_eventually_eq h

/-- Without sign changes on a preconnected set, `f` is constant there. -/
lemma const_of_lc {s : Set ℝ} (hs : IsPreconnected s) (h : ∀ t ∈ s, LC f t) {x y : ℝ}
    (hx : x ∈ s) (hy : y ∈ s) : f x = f y :=
  hs.constant (fun t ht => (continuousAt_of_lc (h t ht)).continuousWithinAt) hx hy

/-- At a sign change, the values on the two sides differ. -/
lemma flip (hr : RunsGE ℓ f) (hℓ : 0 < ℓ) {t δ : ℝ} (hδ : 0 < δ) (ht : ¬ LC f t) {v w : Bool}
    (hv : ∀ x ∈ Ioo (t - δ) t, f x = v) (hw : ∀ x ∈ Ioo t (t + δ), f x = w) : v ≠ w := by
  rintro rfl
  apply ht
  set δ' := min δ (ℓ / 2) with hδ'def
  have hδ' : 0 < δ' := lt_min hδ (by linarith)
  have hδ'1 : δ' ≤ δ := min_le_left _ _
  have hδ'2 : δ' ≤ ℓ / 2 := min_le_right _ _
  have e1 := hv (t - δ' / 2) ⟨by linarith, by linarith⟩
  have e2 := hw (t + δ' / 2) ⟨by linarith, by linarith⟩
  have hft : f t = v := by
    have := hr (t - δ' / 2) t (t + δ' / 2) (by linarith) (by linarith) (by linarith)
      (by rw [e1, e2])
    rw [this, e1]
  rw [lc_iff]
  refine ⟨δ, hδ, fun x hx => ?_⟩
  rw [abs_lt] at hx
  rw [hft]
  rcases lt_trichotomy x t with h | h | h
  · exact hv x ⟨by linarith, h⟩
  · rw [h, hft]
  · exact hw x ⟨h, by linarith⟩

/-- An odd function has a sign change. -/
lemma exists_not_lc (hf : IsOddSign f) : ∃ t, ¬ LC f t := by
  by_contra h
  push_neg at h
  have h0 : (0 : ℝ) ≤ 0 + π := by linarith [pi_pos]
  have := const_of_lc isPreconnected_Icc (fun t _ => h t) (left_mem_Icc.2 h0)
    (right_mem_Icc.2 h0)
  rw [hf] at this
  revert this
  generalize f 0 = a
  cases a <;> simp

/-- The sign changes in `[0, π)` form a finite set. -/
lemma finite_changes (hr : RunsGE ℓ f) (hℓ : 0 < ℓ) : {t | ¬ LC f t ∧ t ∈ Ico 0 π}.Finite := by
  refine Set.Finite.of_finite_image (f := fun t => ⌊t / ℓ⌋₊)
    ((Set.finite_Iic ⌊π / ℓ⌋₊).subset ?_) ?_
  · rintro _ ⟨t, ⟨-, ht0, htπ⟩, rfl⟩
    exact Nat.floor_le_floor (div_le_div_of_nonneg_right htπ.le hℓ.le)
  · intro t₁ h₁ t₂ h₂ he
    simp only at he
    have a1 := Nat.floor_le (div_nonneg h₁.2.1 hℓ.le)
    have a2 := Nat.lt_floor_add_one (t₁ / ℓ)
    have b1 := Nat.floor_le (div_nonneg h₂.2.1 hℓ.le)
    have b2 := Nat.lt_floor_add_one (t₂ / ℓ)
    rw [he] at a1 a2
    have hlt : |t₁ - t₂| < ℓ := by
      have : |t₁ / ℓ - t₂ / ℓ| < 1 := abs_sub_lt_iff.2 ⟨by linarith, by linarith⟩
      rwa [← sub_div, abs_div, abs_of_pos hℓ, div_lt_one hℓ] at this
    rw [abs_sub_lt_iff] at hlt
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have := sep hr h₁.1 h₂.1 h
      linarith
    · have := sep hr h₂.1 h₁.1 h
      linarith

lemma reduce_mem_Ico (t : ℝ) : t + ((-⌊t / π⌋ : ℤ) : ℝ) * π ∈ Ico 0 π := by
  have h1 := Int.floor_le (t / π)
  have h2 := Int.lt_floor_add_one (t / π)
  rw [le_div_iff₀ pi_pos] at h1
  rw [div_lt_iff₀ pi_pos] at h2
  push_cast
  constructor <;> nlinarith

/-- **Every odd sign function with runs `≥ ℓ` is a sign sequence**, away from its sign changes. -/
theorem exists_signSeq (hℓ : 0 < ℓ) (hf : IsOddSign f) (hr : RunsGE ℓ f) :
    ∃ F : SignSeq ℓ, ∀ x, (∀ k, F.y k ≠ x) → f x = F.val x := by
  classical
  have hfin := finite_changes hr hℓ
  set s := hfin.toFinset with hs
  have hmem : ∀ t, t ∈ s ↔ ¬ LC f t ∧ t ∈ Ico 0 π := fun t => by simp [s]
  obtain ⟨t₀, ht₀⟩ := exists_not_lc hf
  have hsne : s.Nonempty :=
    ⟨_, (hmem _).2 ⟨by rwa [lc_add_int_mul_pi hf], reduce_mem_Ico t₀⟩⟩
  set c := s.card with hc
  have hc0 : 0 < c := Finset.card_pos.2 hsne
  have hcz : (0 : ℤ) < c := by exact_mod_cast hc0
  set e := s.orderEmbOfFin hc.symm with he
  have he_mem : ∀ i, e i ∈ s := fun i => Finset.orderEmbOfFin_mem s hc.symm i
  have he0 : ∀ i (hi : i < c), 0 ≤ e ⟨i, hi⟩ ∧ e ⟨i, hi⟩ < π := fun i hi =>
    ((hmem _).1 (he_mem _)).2
  -- the sign changes, listed: `y (q c + i) = e i + q π`
  let g : ℕ → ℝ := fun i => if hi : i < c then e ⟨i, hi⟩ else 0
  let y : ℤ → ℝ := fun k => g (k % (c : ℤ)).toNat + ((k / (c : ℤ) : ℤ) : ℝ) * π
  have y_spec : ∀ (q : ℤ) (i : ℕ) (hi : i < c), y (q * c + i) = e ⟨i, hi⟩ + q * π := by
    intro q i hi
    have h1 : (q * c + i) % (c : ℤ) = i := by
      rw [add_comm, Int.add_mul_emod_self_right]
      exact Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hi)
    have h2 : (q * c + i) / (c : ℤ) = q := by
      rw [add_comm, Int.add_mul_ediv_right _ _ hcz.ne',
        Int.ediv_eq_zero_of_lt (by positivity) (by exact_mod_cast hi), zero_add]
    simp only [y, g, h1, h2, Int.toNat_natCast, dif_pos hi]
  have decomp : ∀ k : ℤ, ∃ q : ℤ, ∃ i : ℕ, ∃ hi : i < c, k = q * c + i := fun k => by
    obtain ⟨q, i, hi, h⟩ := SignSeq.exists_mul_add k hc0
    exact ⟨q, i, hi, h⟩
  have hy_add : ∀ k : ℤ, y (k + c) = y k + π := by
    intro k
    obtain ⟨q, i, hi, rfl⟩ := decomp k
    rw [show q * c + i + c = (q + 1) * c + i by ring, y_spec (q + 1) i hi, y_spec q i hi]
    push_cast
    ring
  have hy_lt : ∀ k : ℤ, y k < y (k + 1) := by
    intro k
    obtain ⟨q, i, hi, rfl⟩ := decomp k
    rcases Nat.lt_or_ge (i + 1) c with h | h
    · rw [show q * c + i + 1 = q * c + ((i + 1 : ℕ) : ℤ) by push_cast; ring, y_spec q i hi,
        y_spec q (i + 1) h]
      have : e ⟨i, hi⟩ < e ⟨i + 1, h⟩ := e.strictMono (Fin.mk_lt_mk.2 (Nat.lt_succ_self i))
      linarith
    · have hic : (c : ℤ) = i + 1 := by exact_mod_cast (show c = i + 1 by omega)
      rw [show q * c + i + 1 = (q + 1) * c + ((0 : ℕ) : ℤ) by rw [hic]; push_cast; ring,
        y_spec q i hi, y_spec (q + 1) 0 hc0]
      have a := he0 i hi
      have b := he0 0 hc0
      push_cast
      linarith
  have hymono : StrictMono y := strictMono_int_of_lt_succ hy_lt
  have hyC : ∀ k, ¬ LC f (y k) := by
    intro k
    obtain ⟨q, i, hi, rfl⟩ := decomp k
    rw [y_spec q i hi, lc_add_int_mul_pi hf]
    exact ((hmem _).1 (he_mem _)).1
  have hy_onto : ∀ t, ¬ LC f t → ∃ k, y k = t := by
    intro t ht
    have h1 : t + ((-⌊t / π⌋ : ℤ) : ℝ) * π ∈ s :=
      (hmem _).2 ⟨by rwa [lc_add_int_mul_pi hf], reduce_mem_Ico t⟩
    have : t + ((-⌊t / π⌋ : ℤ) : ℝ) * π ∈ Set.range e := by
      rw [he, Finset.range_orderEmbOfFin]
      exact h1
    obtain ⟨⟨i, hi⟩, hei⟩ := this
    refine ⟨⌊t / π⌋ * c + i, ?_⟩
    rw [y_spec _ i hi, hei]
    push_cast
    ring
  have hgap : ∀ k : ℤ, y k + ℓ ≤ y (k + 1) := fun k => by
    have := sep hr (hyC k) (hyC (k + 1)) (hy_lt k)
    linarith
  -- `f` is constant between consecutive changes, and flips at each change
  have hfree : ∀ k, ∀ t ∈ Ioo (y k) (y (k + 1)), LC f t := by
    intro k t ht
    by_contra hc'
    obtain ⟨j, rfl⟩ := hy_onto t hc'
    have h1 := hymono.lt_iff_lt.1 ht.1
    have h2 := hymono.lt_iff_lt.1 ht.2
    omega
  let v : ℤ → Bool := fun k => f ((y k + y (k + 1)) / 2)
  have hv : ∀ k, ∀ x ∈ Ioo (y k) (y (k + 1)), f x = v k := by
    intro k x hx
    have hk := hy_lt k
    exact const_of_lc isPreconnected_Ioo (hfree k) hx ⟨by linarith, by linarith⟩
  have halt : ∀ k, v (k + 1) = !v k := by
    intro k
    have h1 := hy_lt k
    have h2 := hy_lt (k + 1)
    have m1 := min_le_left (y (k + 1) - y k) (y (k + 1 + 1) - y (k + 1))
    have m2 := min_le_right (y (k + 1) - y k) (y (k + 1 + 1) - y (k + 1))
    have hδ : 0 < min (y (k + 1) - y k) (y (k + 1 + 1) - y (k + 1)) := lt_min (by linarith)
      (by linarith)
    exact bool_eq_not_of_ne (flip hr hℓ hδ (hyC (k + 1))
      (fun x hx => hv k x ⟨by linarith [hx.1], hx.2⟩)
      (fun x hx => hv (k + 1) x ⟨hx.1, by linarith [hx.2]⟩))
  -- a run with value `true`
  obtain ⟨o, ho⟩ : ∃ o, v o = true := by
    by_cases h0 : v 0 = true
    · exact ⟨0, h0⟩
    · refine ⟨0 + 1, ?_⟩
      rw [halt 0]
      simpa using h0
  have hvform : ∀ k : ℤ, v (k + o) = decide (Even k) := by
    intro k
    refine Int.induction_on k ?_ ?_ ?_
    · simpa using ho
    · intro i ih
      rw [show (i : ℤ) + 1 + o = (i + o) + 1 by ring, halt, ih]
      simp [← Nat.not_even_iff_odd]
    · intro i ih
      have := halt (-(i : ℤ) - 1 + o)
      rw [show -(i : ℤ) - 1 + o + 1 = -(i : ℤ) + o by ring, ih] at this
      revert this
      generalize v (-(i : ℤ) - 1 + o) = b
      cases b <;> simp [Int.even_sub_one]
  have hodd : Odd c := by
    have x0 := (y o + y (o + 1)) / 2
    have hx0 : (y o + y (o + 1)) / 2 ∈ Ioo (y o) (y (o + 1)) := by
      have := hy_lt o
      constructor <;> linarith
    have e1 := hv o _ hx0
    have e2 := hv (o + c) ((y o + y (o + 1)) / 2 + π) (by
      rw [show o + (c : ℤ) + 1 = (o + 1) + c by ring, hy_add, hy_add]
      exact ⟨by linarith [hx0.1], by linarith [hx0.2]⟩)
    rw [hf, e1, ho, show o + (c : ℤ) = c + o by ring, hvform] at e2
    by_contra hc'
    rw [Nat.not_odd_iff_even] at hc'
    have : Even (c : ℤ) := by exact_mod_cast hc'
    simp [this] at e2
  -- the sign sequence `k ↦ y (k + o)`
  let F : SignSeq ℓ :=
    { c := c
      c_odd := hodd
      y := fun k => y (k + o)
      mono := fun a b hab => hymono (by linarith)
      y_add_c := fun k => by
        rw [show k + (c : ℤ) + o = (k + o) + c by ring]
        exact hy_add _
      gap := fun k => by
        rw [show k + 1 + o = (k + o) + 1 by ring]
        exact hgap _ }
  refine ⟨F, fun x hx => ?_⟩
  have h1 : y (F.idx x + o) ≤ x := F.y_idx_le x
  have h2 : x < y (F.idx x + 1 + o) := F.lt_y_idx_add_one x
  have h3 : y (F.idx x + o) ≠ x := hx (F.idx x)
  rw [hv (F.idx x + o) x ⟨lt_of_le_of_ne h1 h3, by
    rw [show F.idx x + o + 1 = F.idx x + 1 + o by ring]; exact h2⟩, hvform]
  rfl

/-- Compatibility passes from functions to sign sequences that represent them. -/
lemma compat_of_rep {g : ℝ → Bool} {F G : SignSeq ℓ}
    (hF : ∀ x, (∀ k, F.y k ≠ x) → f x = F.val x) (hG : ∀ x, (∀ k, G.y k ≠ x) → g x = G.val x)
    (h : Compat ℓ f g) : Compat ℓ F.val G.val := by
  obtain ⟨a, ha⟩ := h
  refine ⟨a, fun x hx => ?_⟩
  set b := min (min (F.y (F.idx x + 1)) (G.y (G.idx x + 1))) (a + ℓ) with hb
  have hb1 := min_le_left (min (F.y (F.idx x + 1)) (G.y (G.idx x + 1))) (a + ℓ)
  have hb2 := min_le_right (min (F.y (F.idx x + 1)) (G.y (G.idx x + 1))) (a + ℓ)
  have hb3 := min_le_left (F.y (F.idx x + 1)) (G.y (G.idx x + 1))
  have hb4 := min_le_right (F.y (F.idx x + 1)) (G.y (G.idx x + 1))
  have hxb : x < b :=
    lt_min (lt_min (F.lt_y_idx_add_one x) (G.lt_y_idx_add_one x)) hx.2
  set z := (x + b) / 2 with hz
  have hz1 : x < z := by rw [hz]; linarith
  have hz2 : z < b := by rw [hz]; linarith
  have eF : F.idx z = F.idx x :=
    F.idx_eq_iff.2 ⟨(F.y_idx_le x).trans hz1.le, by linarith⟩
  have eG : G.idx z = G.idx x :=
    G.idx_eq_iff.2 ⟨(G.y_idx_le x).trans hz1.le, by linarith⟩
  have nF : ∀ k, F.y k ≠ z := fun k hk => by
    have := F.idx_y k
    rw [hk, eF] at this
    subst this
    linarith [F.y_idx_le x]
  have nG : ∀ k, G.y k ≠ z := fun k hk => by
    have := G.idx_y k
    rw [hk, eG] at this
    subst this
    linarith [G.y_idx_le x]
  have := ha z ⟨hx.1.trans hz1, by linarith⟩
  rw [hF z nF, hG z nG] at this
  rw [SignSeq.val_ne_iff] at this ⊢
  rwa [eF, eG] at this

end SignBridge

open SignBridge in
/-- **(R) holds for `n ≤ 3`** (Attempt 4, §4.2 of `docs/STEP5-NOTES.md`: Theorems A and B). -/
theorem statementR_of_le_three {n : ℕ} (hn : n ≤ 3) : StatementR n := by
  intro ℓ hℓ hband S hS hcomp
  have hrep : ∀ f ∈ S, ∃ F : SignSeq ℓ, ∀ x, (∀ k, F.y k ≠ x) → f x = F.val x :=
    fun f hf => exists_signSeq hℓ (hS f hf).1 (hS f hf).2
  choose F hF using hrep
  have := SignSeq.card_le_two_pow_of_le_three S.attach (fun f => F f.1 f.2) hn hℓ hband
    (by
      rintro ⟨f, hf⟩ - ⟨g, hg⟩ - hne
      exact compat_of_rep (hF f hf) (hF g hg) (hcomp f hf g hg (fun h => hne (Subtype.ext h))))
  simpa using this

end Blumenthal
