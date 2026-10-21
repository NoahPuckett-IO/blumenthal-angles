import Blumenthal.Upper
import Blumenthal.SignBridge

/-!
# The first band from (R)

Attempt 3 of `docs/STEP5-NOTES.md`: a planar set `P` with all angles `≤ π - ℓ` gives, for each
`p ∈ P`, an odd sign function `σ_p` with runs `≥ ℓ`, and `σ_p`, `σ_q` take opposite values on an
open arc of length `ℓ` for `p ≠ q`. So `StatementR n` bounds `|P| ≤ 2^n` when `(2n+1) ℓ > 2π`
(`card_le_of_statementR`), which is the first band of `CapacityBound`
(`capacityBound_firstBand_of_statementR`).

The notes use the Voronoi sign function of `W(p) = V(p) ∪ -V(p)`. Here `σ_p(x)` is the label of the
last point of `W(p)` at or before `x + ℓ/2` (`LastPoint.lastSign`); it has the same three
properties and is easier to handle: oddness, runs `≥ ℓ`, and `σ_p = +1` on the open `ℓ/2`-arc
around each direction of `V(p)`.

With `statementR_of_le_three` this proves `CapacityBound` for `u ∈ [2, 3) ∪ [4, 5) ∪ [6, 7)`, and
`α_5 = 3π/5`, `α_9 = α_10 = 5π/7`.
-/

open EuclideanGeometry Real Set

namespace Blumenthal

namespace LastPoint

/-! ### The last-point sign function of a finite set of angles

The angles `D` stand for directions `e^{id}`; `W = D + πℤ` is the set of directions of `±V`, and a
point `d + kπ` has label `+` iff `k` is even. -/

/-- `d + lastLift d t * π` is the last lift of `d` (modulo `π`) at or before `t`. -/
noncomputable def lastLift (d t : ℝ) : ℤ := ⌊(t - d) / π⌋

lemma lastLift_le (d t : ℝ) : d + lastLift d t * π ≤ t := by
  have := Int.floor_le ((t - d) / π)
  rw [le_div_iff₀ pi_pos] at this
  unfold lastLift
  linarith

lemma le_lastLift {d t : ℝ} {k : ℤ} (h : d + k * π ≤ t) : k ≤ lastLift d t := by
  unfold lastLift
  apply Int.le_floor.2
  rw [le_div_iff₀ pi_pos]
  linarith

lemma lastLift_add_pi (d t : ℝ) : lastLift d (t + π) = lastLift d t + 1 := by
  unfold lastLift
  rw [show (t + π - d) / π = (t - d) / π + 1 by field_simp; ring]
  exact Int.floor_add_one _

/-- `D` is `ℓ`-separated from its antipode: no two directions of `D` make an angle `> π - ℓ`. -/
def AntiSep (ℓ : ℝ) (D : Finset ℝ) : Prop :=
  ∀ d ∈ D, ∀ d' ∈ D, ∀ k : ℤ, Odd k → ℓ ≤ |d - d' - k * π|

/-- The last lift of `d` at or before `t`. -/
noncomputable def pt (d t : ℝ) : ℝ := d + lastLift d t * π

/-- `d ∈ D` gives the last point of `D + πℤ` at or before `t`. -/
def IsLast (D : Finset ℝ) (t d : ℝ) : Prop := d ∈ D ∧ ∀ d' ∈ D, pt d' t ≤ pt d t

lemma exists_isLast {D : Finset ℝ} (hD : D.Nonempty) (t : ℝ) : ∃ d, IsLast D t d := by
  obtain ⟨d, hd, h⟩ := D.exists_max_image (fun d => pt d t) hD
  exact ⟨d, hd, h⟩

open scoped Classical in
/-- The sign function: the label of the last point of `D + πℤ` at or before `x + ℓ/2`. -/
noncomputable def lastSign (D : Finset ℝ) (ℓ x : ℝ) : Bool :=
  decide (∃ d, IsLast D (x + ℓ / 2) d ∧ Even (lastLift d (x + ℓ / 2)))

variable {ℓ : ℝ} {D : Finset ℝ}

/-- Points of `D + πℤ` with different labels are `ℓ` apart. -/
lemma sep_of_parity (hsep : AntiSep ℓ D) {d d' : ℝ} (hd : d ∈ D) (hd' : d' ∈ D) {k k' : ℤ}
    (h : ¬ (Even k ↔ Even k')) : ℓ ≤ |(d + k * π) - (d' + k' * π)| := by
  have hodd : Odd (k' - k) := by
    rw [← Int.not_even_iff_odd, Int.even_sub]
    tauto
  have := hsep d hd d' hd' (k' - k) hodd
  rw [show d + k * π - (d' + k' * π) = d - d' - ((k' - k : ℤ) : ℝ) * π by push_cast; ring]
  exact this

/-- A point of `D + πℤ` has a well-defined label. -/
lemma parity_eq (hℓ : 0 < ℓ) (hsep : AntiSep ℓ D) {d d' : ℝ} (hd : d ∈ D) (hd' : d' ∈ D)
    {k k' : ℤ} (h : d + k * π = d' + k' * π) : Even k ↔ Even k' := by
  by_contra hne
  have := sep_of_parity hsep hd hd' hne
  rw [h, sub_self, abs_zero] at this
  linarith

lemma lastSign_eq (hℓ : 0 < ℓ) (hsep : AntiSep ℓ D) {x d : ℝ} (hd : IsLast D (x + ℓ / 2) d) :
    lastSign D ℓ x = decide (Even (lastLift d (x + ℓ / 2))) := by
  unfold lastSign
  rw [decide_eq_decide]
  constructor
  · rintro ⟨d', hd', he⟩
    have heq : pt d' (x + ℓ / 2) = pt d (x + ℓ / 2) :=
      le_antisymm (hd.2 d' hd'.1) (hd'.2 d hd.1)
    exact (parity_eq hℓ hsep hd'.1 hd.1 heq).1 he
  · intro he
    exact ⟨d, hd, he⟩

lemma isLast_add_pi {t d : ℝ} (h : IsLast D t d) : IsLast D (t + π) d := by
  refine ⟨h.1, fun d' hd' => ?_⟩
  have := h.2 d' hd'
  unfold pt at *
  rw [lastLift_add_pi, lastLift_add_pi]
  push_cast
  linarith

/-- `lastSign` is odd. -/
lemma lastSign_odd (hℓ : 0 < ℓ) (hD : D.Nonempty) (hsep : AntiSep ℓ D) :
    IsOddSign (lastSign D ℓ) := by
  intro x
  obtain ⟨d, hd⟩ := exists_isLast hD (x + ℓ / 2)
  have hd' : IsLast D (x + π + ℓ / 2) d := by
    rw [show x + π + ℓ / 2 = x + ℓ / 2 + π by ring]
    exact isLast_add_pi hd
  rw [lastSign_eq hℓ hsep hd', lastSign_eq hℓ hsep hd,
    show x + π + ℓ / 2 = x + ℓ / 2 + π by ring, lastLift_add_pi]
  simp [← Int.not_even_iff_odd]

/-- The last point is monotone in `t`. -/
lemma pt_mono {t t' d d' : ℝ} (h : t ≤ t') (hd : IsLast D t d) (hd' : IsLast D t' d') :
    pt d t ≤ pt d' t' := by
  refine le_trans ?_ (hd'.2 d hd.1)
  unfold pt
  have : (lastLift d t : ℝ) ≤ lastLift d t' := by
    exact_mod_cast le_lastLift ((lastLift_le d t).trans h)
  nlinarith [pi_pos]

/-- If the last point before `t'` is at or before `t ≤ t'`, it is also the last point before `t`. -/
lemma pt_eq_of_le {t t' d d' : ℝ} (h : t ≤ t') (hd : IsLast D t d) (hd' : IsLast D t' d')
    (hle : pt d' t' ≤ t) : pt d' t' = pt d t := by
  refine le_antisymm ?_ (pt_mono h hd hd')
  refine le_trans ?_ (hd.2 d' hd'.1)
  unfold pt at *
  have : (lastLift d' t' : ℝ) ≤ lastLift d' t := by exact_mod_cast le_lastLift hle
  nlinarith [pi_pos]

/-- `lastSign` has all runs `≥ ℓ`. -/
lemma lastSign_runsGE (hℓ : 0 < ℓ) (hD : D.Nonempty) (hsep : AntiSep ℓ D) :
    RunsGE ℓ (lastSign D ℓ) := by
  intro x y z hxy hyz hzx hxz
  by_contra hne
  obtain ⟨dx, hdx⟩ := exists_isLast hD (x + ℓ / 2)
  obtain ⟨dy, hdy⟩ := exists_isLast hD (y + ℓ / 2)
  obtain ⟨dz, hdz⟩ := exists_isLast hD (z + ℓ / 2)
  rw [lastSign_eq hℓ hsep hdx, lastSign_eq hℓ hsep hdz, decide_eq_decide] at hxz
  rw [lastSign_eq hℓ hsep hdy, lastSign_eq hℓ hsep hdx, decide_eq_decide] at hne
  -- the last point before `y + ℓ/2` comes after `x + ℓ/2`, and similarly for `z`
  have c1 : x + ℓ / 2 < pt dy (y + ℓ / 2) := by
    by_contra h
    push_neg at h
    have := pt_eq_of_le (by linarith) hdx hdy h
    exact hne (parity_eq hℓ hsep hdy.1 hdx.1 this)
  have c2 : y + ℓ / 2 < pt dz (z + ℓ / 2) := by
    by_contra h
    push_neg at h
    have := pt_eq_of_le (by linarith) hdy hdz h
    exact hne ((parity_eq hℓ hsep hdz.1 hdy.1 this).symm.trans hxz.symm)
  have hle : pt dy (y + ℓ / 2) ≤ pt dz (z + ℓ / 2) := pt_mono (by linarith) hdy hdz
  have hs := sep_of_parity hsep hdz.1 hdy.1
    (k := lastLift dz (z + ℓ / 2)) (k' := lastLift dy (y + ℓ / 2)) (fun h => hne (h.symm.trans hxz.symm))
  have hz := lastLift_le dz (z + ℓ / 2)
  unfold pt at c1 c2 hle
  rw [abs_of_nonneg (by linarith)] at hs
  linarith

/-- `lastSign` has label `Even k` on the open `ℓ/2`-arc around `d + kπ`. -/
lemma lastSign_near (hℓ : 0 < ℓ) (hsep : AntiSep ℓ D) {d : ℝ} (hd : d ∈ D) (k : ℤ) {x : ℝ}
    (hx : |x - (d + k * π)| < ℓ / 2) : lastSign D ℓ x = decide (Even k) := by
  obtain ⟨d', hd'⟩ := exists_isLast ⟨d, hd⟩ (x + ℓ / 2)
  rw [lastSign_eq hℓ hsep hd', decide_eq_decide]
  rw [abs_lt] at hx
  have h1 : d + k * π ≤ x + ℓ / 2 := by linarith
  have h2 : (k : ℝ) ≤ lastLift d (x + ℓ / 2) := by exact_mod_cast le_lastLift h1
  have h3 : d + k * π ≤ pt d' (x + ℓ / 2) := by
    refine le_trans ?_ (hd'.2 d hd)
    unfold pt
    nlinarith [pi_pos]
  have h4 := lastLift_le d' (x + ℓ / 2)
  by_contra hpar
  have := sep_of_parity hsep hd'.1 hd hpar
  unfold pt at h3
  rw [abs_of_nonneg (by linarith)] at this
  linarith

end LastPoint

/-! ### Planar sets -/

open LastPoint

/-- The directions from `p` to the other points of `P`, as arguments. -/
noncomputable def dirs (P : Finset Plane) (p : Plane) : Finset ℝ :=
  (P.erase p).image fun q => Complex.arg (toC (q - p))

lemma toC_sub_ne_zero {p q : Plane} (h : q ≠ p) : toC (q - p) ≠ 0 := by
  rw [Ne, LinearIsometryEquiv.map_eq_zero_iff]
  exact sub_ne_zero.2 h

/-- The angle condition separates `V(p)` from `-V(p)` by `ℓ`. -/
lemma antiSep_dirs {ℓ : ℝ} (hℓπ : ℓ ≤ π) {P : Finset Plane} (hA : AnglesLE P (π - ℓ))
    {p : Plane} (hp : p ∈ P) : AntiSep ℓ (dirs P p) := by
  intro d hd d' hd' k hk
  simp only [dirs, Finset.mem_image, Finset.mem_erase] at hd hd'
  obtain ⟨q, ⟨hqp, hq⟩, rfl⟩ := hd
  obtain ⟨q', ⟨hq'p, hq'⟩, rfl⟩ := hd'
  have hz := toC_sub_ne_zero hqp
  have hw := toC_sub_ne_zero hq'p
  have hang : InnerProductGeometry.angle (toC (q - p)) (toC (q' - p)) ≤ π - ℓ := by
    by_cases hqq : q = q'
    · subst hqq
      rw [InnerProductGeometry.angle_self hz]
      linarith
    · have := hA q hq p hp q' hq' hqp (Ne.symm hq'p) hqq
      rw [EuclideanGeometry.angle, vsub_eq_sub, vsub_eq_sub, ← angle_toC] at this
      exact this
  rw [Complex.angle_eq_abs_arg hz hw] at hang
  have e := Complex.arg_div_coe_angle hz hw
  rw [← Real.Angle.coe_sub, Real.Angle.angle_eq_iff_two_pi_dvd_sub] at e
  obtain ⟨m, hm⟩ := e
  have key := pi_sub_abs_le (Complex.arg (toC (q - p) / toC (q' - p)))
    (hk.add_even (even_two_mul m))
  rw [show Complex.arg (toC (q - p)) - Complex.arg (toC (q' - p)) - k * π =
    Complex.arg (toC (q - p) / toC (q' - p)) - ((k + 2 * m : ℤ) : ℝ) * π by
      push_cast; linarith]
  linarith

/-- The direction from `q` to `p` is the direction from `p` to `q` plus an odd multiple of `π`. -/
lemma exists_odd_arg_neg {p q : Plane} (h : q ≠ p) :
    ∃ k : ℤ, Odd k ∧ Complex.arg (toC (q - p)) = Complex.arg (toC (p - q)) + k * π := by
  have hz := toC_sub_ne_zero h
  have e := Complex.arg_neg_coe_angle hz
  rw [show -toC (q - p) = toC (p - q) by rw [← map_neg, neg_sub], ← Real.Angle.coe_add,
    Real.Angle.angle_eq_iff_two_pi_dvd_sub] at e
  obtain ⟨m, hm⟩ := e
  refine ⟨-2 * m - 1, ⟨-m - 1, by ring⟩, ?_⟩
  push_cast
  linarith

/-- The sign function of `p`. -/
noncomputable def sigma (P : Finset Plane) (ℓ : ℝ) (p : Plane) : ℝ → Bool :=
  lastSign (dirs P p) ℓ

/-- **Claim 3 of Attempt 3.** For `p ≠ q`, `σ_p = +1` and `σ_q = -1` on the open arc of length `ℓ`
around the direction from `p` to `q`. -/
lemma compat_sigma {ℓ : ℝ} (hℓ : 0 < ℓ) (hℓπ : ℓ ≤ π) {P : Finset Plane}
    (hA : AnglesLE P (π - ℓ)) {p q : Plane} (hp : p ∈ P) (hq : q ∈ P) (hpq : p ≠ q) :
    Compat ℓ (sigma P ℓ p) (sigma P ℓ q) := by
  set d := Complex.arg (toC (q - p))
  have hd : d ∈ dirs P p := Finset.mem_image.2 ⟨q, Finset.mem_erase.2 ⟨Ne.symm hpq, hq⟩, rfl⟩
  have he : Complex.arg (toC (p - q)) ∈ dirs P q :=
    Finset.mem_image.2 ⟨p, Finset.mem_erase.2 ⟨hpq, hp⟩, rfl⟩
  obtain ⟨k, hk, hde⟩ := exists_odd_arg_neg (Ne.symm hpq)
  refine ⟨d - ℓ / 2, fun x hx => ?_⟩
  have h0 : |x - d| < ℓ / 2 := by
    rw [abs_lt]
    constructor <;> linarith [hx.1, hx.2]
  have h1 : |x - (d + ((0 : ℤ) : ℝ) * π)| < ℓ / 2 := by simpa using h0
  have h2 : |x - (Complex.arg (toC (p - q)) + k * π)| < ℓ / 2 := by
    rw [← hde]
    exact h0
  unfold sigma
  rw [lastSign_near hℓ (antiSep_dirs hℓπ hA hp) hd 0 h1,
    lastSign_near hℓ (antiSep_dirs hℓπ hA hq) he k h2]
  simp [Int.not_even_iff_odd.2 hk]

/-- **The reduction of Attempt 3.** If `(2n+1) ℓ > 2π` and (R) holds for `n`, a planar set with all
angles `≤ π - ℓ` has at most `2^n` points. -/
theorem card_le_of_statementR {n : ℕ} (hR : StatementR n) {ℓ : ℝ} (hℓ : 0 < ℓ) (hℓπ : ℓ ≤ π)
    (hband : 2 * π < (2 * n + 1) * ℓ) (P : Finset Plane) (hA : AnglesLE P (π - ℓ)) :
    P.card ≤ 2 ^ n := by
  classical
  rcases Nat.lt_or_ge P.card 2 with h | h
  · have := Nat.one_le_two_pow (n := n)
    omega
  have hinj : Set.InjOn (sigma P ℓ) P := by
    intro p hp q hq he
    by_contra hpq
    obtain ⟨a, ha⟩ := compat_sigma hℓ hℓπ hA hp hq hpq
    exact ha (a + ℓ / 2) ⟨by linarith, by linarith⟩ (by rw [he])
  rw [← Finset.card_image_of_injOn hinj]
  refine hR ℓ hℓ hband _ ?_ ?_
  · intro f hf
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hf
    have hne : (dirs P p).Nonempty := by
      refine Finset.Nonempty.image ?_ _
      rw [← Finset.card_pos, Finset.card_erase_of_mem hp]
      omega
    exact ⟨lastSign_odd hℓ hne (antiSep_dirs hℓπ hA hp),
      lastSign_runsGE hℓ hne (antiSep_dirs hℓπ hA hp)⟩
  · intro f hf g hg hfg
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hf
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hg
    exact compat_sigma hℓ hℓπ hA hp hq (fun h => hfg (by rw [h]))

/-! ### The first band of `CapacityBound` -/

lemma floor_half_eq {u : ℝ} {n : ℕ} (hu : 2 * n ≤ u) (hu' : u < 2 * n + 1) : ⌊u / 2⌋₊ = n := by
  rw [Nat.floor_eq_iff (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])]
  constructor <;> linarith

/-- **(R) for `n` gives the first band of `CapacityBound` for `n`**: `2n ≤ u < 2n + 1`. -/
theorem capacityBound_firstBand_of_statementR {n : ℕ} (hn : 2 ≤ n) (hR : StatementR n) {u : ℝ}
    (hu : 2 * n ≤ u) (hu' : u < 2 * n + 1) (A : Finset Plane)
    (hA : AnglesLE A ((1 - 2 / u) * π)) : A.card ≤ capacity u := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hu0 : 0 < u := by linarith
  have hfl := floor_half_eq hu hu'
  rw [capacity_of_band_one (by linarith) (by rw [hfl]; linarith), hfl]
  have hπ := pi_pos
  refine card_le_of_statementR hR (ℓ := 2 * π / u) (by positivity) ?_ ?_ A ?_
  · rw [div_le_iff₀ hu0]
    nlinarith
  · rw [mul_div_assoc', lt_div_iff₀ hu0]
    nlinarith
  · convert hA using 1
    field_simp

/-- `CapacityBound` for `2 ≤ u < 3`, from (R) for `n = 1`. -/
theorem capacityBound_two_three {u : ℝ} (hu : 2 ≤ u) (hu' : u < 3) (A : Finset Plane)
    (hA : AnglesLE A ((1 - 2 / u) * π)) : A.card ≤ capacity u := by
  have hu0 : 0 < u := by linarith
  have hπ := pi_pos
  rw [capacity_of_lt_three hu']
  have := card_le_of_statementR (statementR_of_le_three (n := 1) (by norm_num))
    (ℓ := 2 * π / u) (by positivity) (by rw [div_le_iff₀ hu0]; nlinarith)
    (by rw [mul_div_assoc', lt_div_iff₀ hu0]; push_cast; nlinarith) A
    (by convert hA using 1; field_simp)
  simpa using this

/-- `CapacityBound` for `4 ≤ u < 5`, from (R) for `n = 2`. -/
theorem capacityBound_four_five {u : ℝ} (hu : 4 ≤ u) (hu' : u < 5) (A : Finset Plane)
    (hA : AnglesLE A ((1 - 2 / u) * π)) : A.card ≤ capacity u :=
  capacityBound_firstBand_of_statementR le_rfl (statementR_of_le_three (by norm_num))
    (by push_cast; linarith) (by push_cast; linarith) A hA

/-- `CapacityBound` for `6 ≤ u < 7`, from (R) for `n = 3`. -/
theorem capacityBound_six_seven {u : ℝ} (hu : 6 ≤ u) (hu' : u < 7) (A : Finset Plane)
    (hA : AnglesLE A ((1 - 2 / u) * π)) : A.card ≤ capacity u :=
  capacityBound_firstBand_of_statementR (by norm_num) (statementR_of_le_three le_rfl)
    (by push_cast; linarith) (by push_cast; linarith) A hA

/-! ### New exact values of `α_N` -/

/-- A lower bound for `alpha N` from a size bound on `[u₁, u₀)`: if every set with all angles
`≤ (1 - 2/u) π`, `u₁ ≤ u < u₀`, has fewer than `N` points, every `N`-point set has an angle
`≥ (1 - 2/u₀) π`. -/
theorem le_alpha_of_card_lt {N : ℕ} (hN : 3 ≤ N) {u₁ u₀ : ℝ} (hu₁ : 2 ≤ u₁) (h₁₀ : u₁ < u₀)
    (h : ∀ u : ℝ, u₁ ≤ u → u < u₀ → ∀ A : Finset Plane, AnglesLE A ((1 - 2 / u) * π) →
      A.card < N) :
    (1 - 2 / u₀) * π ≤ alpha N := by
  have hπ : 0 < π := pi_pos
  have hu₀pos : 0 < u₀ := by linarith
  have h2u : 2 / u₀ ≤ 1 := (div_le_one hu₀pos).mpr (by linarith)
  have h2u0 : 0 < 2 / u₀ := by positivity
  refine le_alpha (by nlinarith) (by nlinarith) fun A hA => ?_
  obtain ⟨x, hx, y, hy, z, hz, hxy, hyz, hxz, hmax⟩ := exists_max_angle (hA ▸ hN)
  refine ⟨x, hx, y, hy, z, hz, hxy, hyz, hxz, ?_⟩
  by_contra! hlt
  have hβπ : ∠ x y z < π := by nlinarith
  have hβ0 : 0 ≤ ∠ x y z := angle_nonneg x y z
  have hden : 0 < π - ∠ x y z := by linarith
  have hv : 2 * π / (π - ∠ x y z) < u₀ := by
    rw [div_lt_iff₀ hden]
    have : 2 / u₀ * π < π - ∠ x y z := by nlinarith
    calc 2 * π = u₀ * (2 / u₀ * π) := by field_simp
      _ < u₀ * (π - ∠ x y z) := by gcongr
  have hvpos : 0 < 2 * π / (π - ∠ x y z) := by positivity
  set u := max u₁ (2 * π / (π - ∠ x y z)) with hu
  have hu1 : u₁ ≤ u := le_max_left _ _
  have hvu : 2 * π / (π - ∠ x y z) ≤ u := le_max_right _ _
  have huu : u < u₀ := max_lt h₁₀ hv
  have hupos : 0 < u := by linarith
  have hle : ∠ x y z ≤ (1 - 2 / u) * π := by
    have h1 : 2 / u ≤ 2 / (2 * π / (π - ∠ x y z)) := div_le_div_of_nonneg_left (by norm_num) hvpos hvu
    have h2 : 2 / (2 * π / (π - ∠ x y z)) * π = π - ∠ x y z := by field_simp
    nlinarith
  have := h u hu1 huu A (fun a ha b hb c hc hab hbc hac => (hmax a ha b hb c hc hab hbc hac).trans hle)
  omega

/-- **`α_5 = 3π/5`.** -/
theorem alpha_five : alpha 5 = 3 * π / 5 := by
  apply le_antisymm
  · have := sendovUpper.2.2 2 5 le_rfl (by norm_num) (by norm_num)
    rw [bandValue, if_pos (by norm_num)] at this
    convert this using 1
    push_cast
    ring
  · have := le_alpha_of_card_lt (N := 5) (by norm_num) (u₁ := 4) (u₀ := 5) (by norm_num)
      (by norm_num) (fun u hu hu' A hA => by
        have h := capacityBound_four_five hu hu' A hA
        rw [capacity_of_band_one (by linarith)
          (by rw [floor_half_eq (n := 2) (by push_cast; linarith) (by push_cast; linarith)];
              push_cast; linarith),
          floor_half_eq (n := 2) (by push_cast; linarith) (by push_cast; linarith)] at h
        omega)
    convert this using 1
    ring

lemma alpha_nine_ten_lower {N : ℕ} (hN : 9 ≤ N) : 5 * π / 7 ≤ alpha N := by
  have := le_alpha_of_card_lt (N := N) (by omega) (u₁ := 6) (u₀ := 7) (by norm_num)
    (by norm_num) (fun u hu hu' A hA => by
      have h := capacityBound_six_seven hu hu' A hA
      rw [capacity_of_band_one (by linarith)
        (by rw [floor_half_eq (n := 3) (by push_cast; linarith) (by push_cast; linarith)];
            push_cast; linarith),
        floor_half_eq (n := 3) (by push_cast; linarith) (by push_cast; linarith)] at h
      have : (2 : ℕ) ^ 3 = 8 := by norm_num
      omega)
  convert this using 1
  ring

lemma alpha_nine_ten_upper {N : ℕ} (h9 : 9 ≤ N) (h10 : N ≤ 10) : alpha N ≤ 5 * π / 7 := by
  have := sendovUpper.2.2 3 N (by norm_num) (by norm_num; omega) (by norm_num; omega)
  rw [bandValue, if_pos (by norm_num; omega)] at this
  convert this using 1
  push_cast
  ring

/-- **`α_9 = 5π/7`.** -/
theorem alpha_nine : alpha 9 = 5 * π / 7 :=
  le_antisymm (alpha_nine_ten_upper le_rfl (by norm_num)) (alpha_nine_ten_lower le_rfl)

/-- **`α_10 = 5π/7`.** -/
theorem alpha_ten : alpha 10 = 5 * π / 7 :=
  le_antisymm (alpha_nine_ten_upper (by norm_num) le_rfl) (alpha_nine_ten_lower (by norm_num))

end Blumenthal
