import Mathlib

/-!
# Step 5, first band: the one-dimensional statement (R)

`docs/STEP5-NOTES.md`, Attempt 3, reduces the first band of the lower bound to a statement about
sign functions on the circle `S¹ = ℝ/2πℤ`, which we write as functions `ℝ → Bool`:

> **(R)** Let `(2n+1) ℓ > 2π`. Let `𝒮` be a family of odd functions `S¹ → {±1}`, each with all runs
> of length `≥ ℓ`, such that any two of them take opposite values on some open arc of length `ℓ`.
> Then `|𝒮| ≤ 2^n`.

This file states (R) (`StatementR`) and develops the combinatorics of Attempt 4, §4.2 for
*sign sequences* (`SignSeq`): a sign function recorded by its increasing sequence of sign changes
`y : ℤ → ℝ`, with `c` changes per half-turn (`y (k + c) = y k + π`, `c` odd) and runs
`y (k+1) - y k ≥ ℓ`. The value on `[y k, y (k+1))` is `true` iff `k` is even. Counting sign
changes in an interval is then a difference of indices (`SignSeq.idx`), which makes the parity
arguments of Theorem B integer arithmetic.

* `SignSeq.exists_witness`: **Lemma 0** (witness arcs).
* `SignSeq.card_le_of_c_eq_one`: **Theorem A** (functions with one change per half-turn).
* `SignSeq.not_three_of_c_eq`, `SignSeq.card_le_two_of_c_eq`: **Theorem B** (functions with `n`
  changes per half-turn).
* `SignSeq.card_le_two_pow_of_le_three`: **(R) for `n ≤ 3`**, for sign sequences.

`Blumenthal.SignBridge` shows that every odd function with runs `≥ ℓ` is a sign sequence away from
its sign changes, and deduces `StatementR n` for `n ≤ 3`.
-/

open Real Set

namespace Blumenthal

/-! ### The statement (R) -/

/-- `f : ℝ → Bool` is an odd sign function on the circle: `f (x + π) = ¬ f x`. -/
def IsOddSign (f : ℝ → Bool) : Prop := ∀ x, f (x + π) = !f x

/-- All runs of `f` have length `≥ ℓ`: `f` never switches twice inside an open window of
length `ℓ`. (For a run `(a, b)` of length `< ℓ`, points just outside it on both sides would give
such a window.) -/
def RunsGE (ℓ : ℝ) (f : ℝ → Bool) : Prop :=
  ∀ x y z, x < y → y < z → z - x < ℓ → f x = f z → f y = f x

/-- `f` and `g` take opposite values on some open arc of length `ℓ`. -/
def Compat (ℓ : ℝ) (f g : ℝ → Bool) : Prop :=
  ∃ a, ∀ x ∈ Ioo a (a + ℓ), f x ≠ g x

lemma Compat.symm {ℓ : ℝ} {f g : ℝ → Bool} (h : Compat ℓ f g) : Compat ℓ g f := by
  obtain ⟨a, ha⟩ := h
  exact ⟨a, fun x hx => (ha x hx).symm⟩

/-- **(R)** for a given `n` (Attempt 3 of `docs/STEP5-NOTES.md`): a family of odd sign functions
with runs `≥ ℓ`, pairwise taking opposite values on an open arc of length `ℓ`, where
`(2n+1) ℓ > 2π`, has at most `2^n` members. -/
def StatementR (n : ℕ) : Prop :=
  ∀ ℓ : ℝ, 0 < ℓ → 2 * π < (2 * n + 1) * ℓ → ∀ S : Finset (ℝ → Bool),
    (∀ f ∈ S, IsOddSign f ∧ RunsGE ℓ f) → (∀ f ∈ S, ∀ g ∈ S, f ≠ g → Compat ℓ f g) →
      S.card ≤ 2 ^ n

/-- For an odd integer `k`, `|r - k π| ≥ π - |r|`. -/
lemma pi_sub_abs_le (r : ℝ) {k : ℤ} (hk : Odd k) : π - |r| ≤ |r - k * π| := by
  have hπ := pi_pos
  have hk0 : k ≠ 0 := by rintro rfl; exact (Int.not_odd_iff_even.2 (by decide)) hk
  rcases (show 1 ≤ k ∨ k ≤ -1 by omega) with h | h
  · have h' : (1 : ℝ) ≤ k := by exact_mod_cast h
    have : π ≤ k * π := by nlinarith
    have := neg_le_abs (r - k * π)
    have := le_abs_self r
    linarith
  · have h' : (k : ℝ) ≤ -1 := by exact_mod_cast h
    have : k * π ≤ -π := by nlinarith
    have := le_abs_self (r - k * π)
    have := neg_le_abs r
    linarith

/-! ### Sign sequences -/

/-- An odd sign function on the circle with all runs of length `≥ ℓ`, recorded by its sign
changes `y k` (in increasing order), `c` of them per half-turn. Its value (`SignSeq.val`) is
`true` on `[y k, y (k+1))` for even `k` and `false` for odd `k`. -/
structure SignSeq (ℓ : ℝ) where
  /-- The number of sign changes per half-turn. -/
  c : ℕ
  c_odd : Odd c
  /-- The sign changes, in increasing order. -/
  y : ℤ → ℝ
  mono : StrictMono y
  y_add_c : ∀ k : ℤ, y (k + c) = y k + π
  gap : ∀ k : ℤ, y k + ℓ ≤ y (k + 1)

namespace SignSeq

variable {ℓ : ℝ} (F : SignSeq ℓ)

lemma c_pos : 0 < F.c := F.c_odd.pos

lemma y_add_mul (k m : ℤ) : F.y (k + m * F.c) = F.y k + m * π := by
  refine Int.induction_on m ?_ ?_ ?_
  · simp
  · intro i ih
    have := F.y_add_c (k + i * F.c)
    rw [show k + ((i : ℤ) + 1) * F.c = k + i * F.c + F.c by ring, this, ih]
    push_cast
    ring
  · intro i ih
    have := F.y_add_c (k + (-(i : ℤ) - 1) * F.c)
    rw [show k + (-(i : ℤ) - 1) * F.c + F.c = k + -(i : ℤ) * F.c by ring, ih] at this
    push_cast at this ⊢
    linarith

/-- Iterated runs: `y k + j ℓ ≤ y (k + j)`. -/
lemma y_add_nat (k : ℤ) (j : ℕ) : F.y k + j * ℓ ≤ F.y (k + j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have := F.gap (k + j)
    push_cast
    rw [← add_assoc]
    linarith

lemma y_add_int {k k' : ℤ} (h : k ≤ k') : F.y k + ((k' : ℝ) - k) * ℓ ≤ F.y k' := by
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, k' = k + j := ⟨(k' - k).toNat, by omega⟩
  have := F.y_add_nat k j
  push_cast
  ring_nf at this ⊢
  linarith

/-- `c` runs fit in a half-turn: `c ℓ ≤ π`. -/
lemma c_mul_le : F.c * ℓ ≤ π := by
  have := F.y_add_nat 0 F.c
  rw [F.y_add_c] at this
  linarith

lemma le_pi (F : SignSeq ℓ) : ℓ ≤ π := by
  have h1 := F.c_mul_le
  have h2 : (1 : ℝ) ≤ F.c := by exact_mod_cast F.c_pos
  rcases le_or_gt ℓ 0 with h | h
  · linarith [pi_pos]
  · nlinarith

/-- In the band `(2n+1) ℓ > 2π`, a sign sequence has at most `n` changes per half-turn. -/
lemma c_le {n : ℕ} (hℓ : 0 < ℓ) (hband : 2 * π < (2 * n + 1) * ℓ) : F.c ≤ n := by
  have h := F.c_mul_le
  have : (2 * F.c : ℝ) < 2 * n + 1 := by
    by_contra hc
    push_neg at hc
    nlinarith
  have : 2 * F.c < 2 * n + 1 := by exact_mod_cast this
  omega

/-! #### The run index -/

lemma exists_y_le (x : ℝ) : ∃ k, F.y k ≤ x := by
  obtain ⟨m, hm⟩ : ∃ m : ℤ, F.y 0 - x ≤ m * π := by
    refine ⟨⌈(F.y 0 - x) / π⌉, ?_⟩
    have := Int.le_ceil ((F.y 0 - x) / π)
    rwa [div_le_iff₀ pi_pos] at this
  refine ⟨0 + (-m) * F.c, ?_⟩
  rw [F.y_add_mul]
  push_cast
  linarith

lemma bddAbove_y_le (x : ℝ) : BddAbove {k : ℤ | F.y k ≤ x} := by
  obtain ⟨m, hm⟩ : ∃ m : ℤ, x - F.y 0 < m * π := by
    refine ⟨⌊(x - F.y 0) / π⌋ + 1, ?_⟩
    have := Int.lt_floor_add_one ((x - F.y 0) / π)
    push_cast
    rwa [div_lt_iff₀ pi_pos] at this
  refine ⟨0 + m * F.c, fun k hk => ?_⟩
  by_contra h
  push_neg at h
  have := F.mono h
  rw [F.y_add_mul] at this
  simp only [Set.mem_setOf_eq] at hk
  linarith

/-- The index of the run containing `x`: `y (idx x) ≤ x < y (idx x + 1)`. So the number of sign
changes in `(x, x']` is `idx x' - idx x`. -/
noncomputable def idx (x : ℝ) : ℤ := sSup {k : ℤ | F.y k ≤ x}

lemma y_idx_le (x : ℝ) : F.y (F.idx x) ≤ x :=
  Int.csSup_mem (F.exists_y_le x) (F.bddAbove_y_le x)

lemma le_idx_iff {k : ℤ} {x : ℝ} : k ≤ F.idx x ↔ F.y k ≤ x :=
  ⟨fun h => (F.mono.monotone h).trans (F.y_idx_le x), fun h => le_csSup (F.bddAbove_y_le x) h⟩

lemma lt_y_idx_add_one (x : ℝ) : x < F.y (F.idx x + 1) := by
  by_contra h
  push_neg at h
  have := F.le_idx_iff.2 h
  omega

lemma idx_eq_iff {k : ℤ} {x : ℝ} : F.idx x = k ↔ F.y k ≤ x ∧ x < F.y (k + 1) := by
  constructor
  · rintro rfl
    exact ⟨F.y_idx_le x, F.lt_y_idx_add_one x⟩
  · rintro ⟨h1, h2⟩
    have a := F.le_idx_iff.2 h1
    have b : ¬ (k + 1 ≤ F.idx x) := fun h => by
      have := F.le_idx_iff.1 h
      linarith
    omega

lemma idx_mono : Monotone F.idx := fun x _ h => F.le_idx_iff.2 ((F.y_idx_le x).trans h)

lemma idx_y (k : ℤ) : F.idx (F.y k) = k :=
  F.idx_eq_iff.2 ⟨le_rfl, F.mono (lt_add_one k)⟩

lemma idx_add_mul_pi (x : ℝ) (m : ℤ) : F.idx (x + m * π) = F.idx x + m * F.c := by
  rw [F.idx_eq_iff, show F.idx x + m * F.c + 1 = (F.idx x + 1) + m * F.c by ring, F.y_add_mul,
    F.y_add_mul]
  exact ⟨by linarith [F.y_idx_le x], by linarith [F.lt_y_idx_add_one x]⟩

lemma idx_add_pi (x : ℝ) : F.idx (x + π) = F.idx x + F.c := by
  simpa using F.idx_add_mul_pi x 1

/-- The sign function of a sign sequence. -/
noncomputable def val (x : ℝ) : Bool := decide (Even (F.idx x))

lemma not_even_c : ¬ Even (F.c : ℤ) := by
  rw [Int.even_coe_nat]
  exact Nat.not_even_iff_odd.2 F.c_odd

/-- The sign function of a sign sequence is odd. -/
lemma isOddSign_val : IsOddSign F.val := by
  intro x
  have := F.not_even_c
  by_cases h : Even (F.idx x) <;> simp [val, F.idx_add_pi, Int.even_add, h, this]

/-- The sign function of a sign sequence has all runs `≥ ℓ`. -/
lemma runsGE_val : RunsGE ℓ F.val := by
  intro x y z hxy hyz hzx hxz
  by_contra hne
  have h1 : F.idx x ≠ F.idx y := fun h => hne (by simp [val, h])
  have h2 : F.idx y ≠ F.idx z := fun h => hne (by rw [hxz]; simp [val, h])
  have m1 := F.idx_mono hxy.le
  have m2 := F.idx_mono hyz.le
  have h3 : F.idx x + 2 ≤ F.idx z := by omega
  have a := F.lt_y_idx_add_one x
  have b := F.gap (F.idx x + 1)
  have c := F.le_idx_iff.1 h3
  rw [show F.idx x + 1 + 1 = F.idx x + 2 by ring] at b
  linarith

/-! #### Lemma 0: witness arcs -/

/-- `F` does not change sign on the open arc `(a, a + ℓ)`. -/
def NoChange (a : ℝ) : Prop := a + ℓ ≤ F.y (F.idx a + 1)

variable {F}

lemma NoChange.idx_eq {a x : ℝ} (h : F.NoChange a) (h1 : a ≤ x) (h2 : x < a + ℓ) :
    F.idx x = F.idx a :=
  F.idx_eq_iff.2 ⟨(F.y_idx_le a).trans h1, h2.trans_le h⟩

lemma NoChange.add_mul_pi {a : ℝ} (h : F.NoChange a) (m : ℤ) : F.NoChange (a + m * π) := by
  unfold NoChange at *
  rw [F.idx_add_mul_pi, show F.idx a + m * F.c + 1 = F.idx a + 1 + m * F.c by ring, F.y_add_mul]
  linarith

lemma val_ne_iff {G : SignSeq ℓ} {x : ℝ} :
    F.val x ≠ G.val x ↔ ¬ (Even (F.idx x) ↔ Even (G.idx x)) := by
  simp only [val, ne_eq, decide_eq_decide]

/-- In a witness arc `(b, b + ℓ)` of `F, G`, the first change of `F` after `b` cannot come strictly
before the first change of `G`. -/
lemma aux_first_change {G : SignSeq ℓ} {b : ℝ} (hb : ∀ x ∈ Ioo b (b + ℓ), F.val x ≠ G.val x)
    (hlt : F.y (F.idx b + 1) < G.y (G.idx b + 1)) (hin : F.y (F.idx b + 1) < b + ℓ) : False := by
  set t := F.y (F.idx b + 1) with ht
  have hbt : b < t := F.lt_y_idx_add_one b
  have e1 : F.idx t = F.idx b + 1 := F.idx_y _
  have e2 : G.idx t = G.idx b := G.idx_eq_iff.2 ⟨(G.y_idx_le b).trans hbt.le, hlt⟩
  set x := (b + t) / 2 with hx
  have hx1 : b < x := by rw [hx]; linarith
  have hx2 : x < t := by rw [hx]; linarith
  have e3 : F.idx x = F.idx b := F.idx_eq_iff.2 ⟨(F.y_idx_le b).trans hx1.le, hx2⟩
  have e4 : G.idx x = G.idx b := G.idx_eq_iff.2 ⟨(G.y_idx_le b).trans hx1.le, hx2.trans hlt⟩
  have h1 := val_ne_iff.1 (hb t ⟨hbt, hin⟩)
  have h2 := val_ne_iff.1 (hb x ⟨hx1, by linarith⟩)
  rw [e1, e2, Int.even_add_one] at h1
  rw [e3, e4] at h2
  tauto

/-- **Lemma 0 (witness arcs).** If `F` and `G` are compatible, some open arc of length `ℓ`
contains no sign change of `F` or `G`, and `F ≠ G` on it. -/
theorem exists_witness {G : SignSeq ℓ} (hℓ : 0 < ℓ) (h : Compat ℓ F.val G.val) :
    ∃ a, F.NoChange a ∧ G.NoChange a ∧ F.val a ≠ G.val a := by
  obtain ⟨b, hb⟩ := h
  have hb' : ∀ x ∈ Ioo b (b + ℓ), G.val x ≠ F.val x := fun x hx => (hb x hx).symm
  set tF := F.y (F.idx b + 1) with htF
  set tG := G.y (G.idx b + 1) with htG
  have hbF : b < tF := F.lt_y_idx_add_one b
  have hbG : b < tG := G.lt_y_idx_add_one b
  by_cases hcase : b + ℓ ≤ tF ∧ b + ℓ ≤ tG
  · refine ⟨b, hcase.1, hcase.2, ?_⟩
    have hx : b + ℓ / 2 ∈ Ioo b (b + ℓ) := ⟨by linarith, by linarith⟩
    have e1 := NoChange.idx_eq hcase.1 (by linarith : b ≤ b + ℓ / 2) hx.2
    have e2 := NoChange.idx_eq hcase.2 (by linarith : b ≤ b + ℓ / 2) hx.2
    have := val_ne_iff.1 (hb _ hx)
    rw [e1, e2] at this
    exact val_ne_iff.2 this
  · have hmin : tF < b + ℓ ∨ tG < b + ℓ := by
      by_contra hc
      push_neg at hc
      exact hcase hc
    rcases lt_trichotomy tF tG with hlt | heq | hgt
    · exact (aux_first_change hb hlt (by rcases hmin with h | h <;> linarith)).elim
    · have ht : tF < b + ℓ := by rcases hmin with h | h <;> linarith
      have gF := F.gap (F.idx b)
      have gG := G.gap (G.idx b)
      rw [← htF] at gF
      rw [← htG, ← heq] at gG
      have eF : F.idx (tF - ℓ) = F.idx b := F.idx_eq_iff.2 ⟨by linarith, by linarith⟩
      have eG : G.idx (tF - ℓ) = G.idx b := G.idx_eq_iff.2 ⟨by linarith, by linarith⟩
      refine ⟨tF - ℓ, ?_, ?_, ?_⟩
      · unfold NoChange
        rw [eF]
        linarith
      · unfold NoChange
        rw [eG, ← htG, ← heq]
        linarith
      · set x := (b + tF) / 2 with hx
        have hx1 : b < x := by rw [hx]; linarith
        have hx2 : x < tF := by rw [hx]; linarith
        have e3 : F.idx x = F.idx b := F.idx_eq_iff.2 ⟨(F.y_idx_le b).trans hx1.le, hx2⟩
        have e4 : G.idx x = G.idx b :=
          G.idx_eq_iff.2 ⟨(G.y_idx_le b).trans hx1.le, by rw [← htG, ← heq]; exact hx2⟩
        have := val_ne_iff.1 (hb x ⟨hx1, by linarith⟩)
        rw [e3, e4] at this
        rw [val_ne_iff, eF, eG]
        exact this
    · exact (aux_first_change hb' hgt (by rcases hmin with h | h <;> linarith)).elim

/-! #### Theorem A: one change per half-turn -/

lemma y_eq_of_c_eq_one (hc : F.c = 1) (k : ℤ) : F.y k = F.y 0 + k * π := by
  have := F.y_add_mul 0 k
  simpa [hc] using this

/-- Two compatible one-change functions have jumps at circular distance `≥ ℓ`. -/
lemma sep_of_compat_one {G : SignSeq ℓ} (hℓ : 0 < ℓ) (hF : F.c = 1) (hG : G.c = 1)
    (h : Compat ℓ F.val G.val) (m : ℤ) : ℓ ≤ |F.y 0 - G.y 0 - m * (2 * π)| := by
  obtain ⟨a, haF, haG, hval⟩ := exists_witness hℓ h
  have hi1 := F.y_idx_le a
  have hj1 := G.y_idx_le a
  unfold NoChange at haF haG
  rw [F.y_eq_of_c_eq_one hF] at haF hi1
  rw [G.y_eq_of_c_eq_one hG] at haG hj1
  have hpar := val_ne_iff.1 hval
  have hodd : Odd (F.idx a - G.idx a + 2 * m) := by
    have : Odd (F.idx a - G.idx a) := by
      rw [← Int.not_even_iff_odd, Int.even_sub]
      exact hpar
    exact this.add_even (even_two_mul m)
  push_cast at haF haG
  have hdiff : |(F.y 0 + F.idx a * π) - (G.y 0 + G.idx a * π)| ≤ π - ℓ :=
    abs_le.2 ⟨by linarith, by linarith⟩
  have key := pi_sub_abs_le ((F.y 0 + F.idx a * π) - (G.y 0 + G.idx a * π)) hodd
  rw [show F.y 0 + F.idx a * π - (G.y 0 + G.idx a * π) -
      ((F.idx a - G.idx a + 2 * m : ℤ) : ℝ) * π = F.y 0 - G.y 0 - m * (2 * π) by
    push_cast; ring] at key
  linarith

/-- Points of `ℝ` in `[lo, hi]` that are pairwise `ℓ` apart: at most `(hi - lo)/ℓ + 1` of them. -/
lemma card_mul_le_of_sep {ι : Type*} [DecidableEq ι] (r : ι → ℝ) {lo : ℝ} (s : Finset ι) :
    ∀ hi : ℝ, lo ≤ hi + ℓ → (∀ i ∈ s, lo ≤ r i ∧ r i ≤ hi) →
      (∀ i ∈ s, ∀ j ∈ s, i ≠ j → ℓ ≤ |r i - r j|) → (s.card : ℝ) * ℓ ≤ hi - lo + ℓ := by
  induction s using Finset.induction_on_max_value r with
  | empty =>
    intro hi h _ _
    simp only [Finset.card_empty, Nat.cast_zero, zero_mul]
    linarith
  | insert a s ha hmax ih =>
    intro hi hlohi hbd hsep
    have ha_bd := hbd a (Finset.mem_insert_self a s)
    have key : ∀ x ∈ s, r x ≤ r a - ℓ := by
      intro x hx
      have h1 := hmax x hx
      have h2 := hsep x (Finset.mem_insert_of_mem hx) a (Finset.mem_insert_self a s)
        (by rintro rfl; exact ha hx)
      rw [abs_sub_comm, abs_of_nonneg (by linarith)] at h2
      linarith
    have := ih (r a - ℓ) (by linarith [ha_bd.1])
      (fun x hx => ⟨(hbd x (Finset.mem_insert_of_mem hx)).1, key x hx⟩)
      (fun i hi j hj hij => hsep i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij)
    rw [Finset.card_insert_of_notMem ha]
    push_cast
    linarith [ha_bd.2]

/-- Points on a circle of length `T` that are pairwise `ℓ` apart: at most `T / ℓ` of them. -/
lemma card_mul_le_of_circle_sep {ι : Type*} (s : Finset ι) (r : ι → ℝ) {T : ℝ} (hℓ : 0 < ℓ)
    (hT : ℓ ≤ T) (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ m : ℤ, ℓ ≤ |r i - r j - m * T|) :
    (s.card : ℝ) * ℓ ≤ T := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | ⟨i0, hi0⟩
  · simp only [Finset.card_empty, Nat.cast_zero, zero_mul]
    linarith
  have hTpos : 0 < T := by linarith
  set r' : ι → ℝ := fun i => toIcoMod hTpos (r i0) (r i) with hr'def
  have hr' : ∀ i, r' i = r i - toIcoDiv hTpos (r i0) (r i) * T := fun i => by
    simp only [hr'def, ← self_sub_toIcoDiv_zsmul, zsmul_eq_mul]
  have hmem : ∀ i, r' i ∈ Ico (r i0) (r i0 + T) := fun i => toIcoMod_mem_Ico hTpos _ _
  have bounds : ∀ i ∈ s.erase i0, r i0 + ℓ ≤ r' i ∧ r' i ≤ r i0 + T - ℓ := by
    intro i hi
    have hne := Finset.ne_of_mem_erase hi
    have his := Finset.mem_of_mem_erase hi
    set m := toIcoDiv hTpos (r i0) (r i)
    have h0 := hsep i his i0 hi0 hne m
    have h1 := hsep i his i0 hi0 hne (m + 1)
    have hm' := hmem i
    rw [show r i - r i0 - m * T = r' i - r i0 by rw [hr' i]; ring] at h0
    rw [show r i - r i0 - ((m + 1 : ℤ) : ℝ) * T = r' i - r i0 - T by rw [hr' i]; push_cast; ring]
      at h1
    rw [abs_of_nonneg (by linarith [hm'.1])] at h0
    rw [abs_of_neg (by linarith [hm'.2])] at h1
    constructor <;> linarith
  have sep' : ∀ i ∈ s.erase i0, ∀ j ∈ s.erase i0, i ≠ j → ℓ ≤ |r' i - r' j| := by
    intro i hi j hj hij
    have := hsep i (Finset.mem_of_mem_erase hi) j (Finset.mem_of_mem_erase hj) hij
      (toIcoDiv hTpos (r i0) (r i) - toIcoDiv hTpos (r i0) (r j))
    rw [hr' i, hr' j]
    convert this using 2
    push_cast
    ring
  have := card_mul_le_of_sep r' (s.erase i0) (r i0 + T - ℓ) (by linarith) bounds sep'
  have hcard : s.card = (s.erase i0).card + 1 := (Finset.card_erase_add_one hi0).symm
  rw [hcard]
  push_cast
  linarith

/-- **Theorem A (one change per half-turn).** In the band `(2n+1) ℓ > 2π`, a compatible family of
one-change functions has at most `2n` members. -/
theorem card_le_of_c_eq_one {ι : Type*} (s : Finset ι) (F : ι → SignSeq ℓ) {n : ℕ} (hℓ : 0 < ℓ)
    (hband : 2 * π < (2 * n + 1) * ℓ) (hc : ∀ i ∈ s, (F i).c = 1)
    (hcomp : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Compat ℓ (F i).val (F j).val) : s.card ≤ 2 * n := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨i0, hi0⟩
  · simp
  have hℓπ : ℓ ≤ π := (F i0).le_pi
  have h := card_mul_le_of_circle_sep s (fun i => (F i).y 0) hℓ (by linarith [pi_pos])
    (fun i hi j hj hij m => sep_of_compat_one hℓ (hc i hi) (hc j hj) (hcomp i hi j hj hij) m)
  have : (s.card : ℝ) < 2 * n + 1 := by
    by_contra hc'
    push_neg at hc'
    nlinarith
  have : s.card < 2 * n + 1 := by exact_mod_cast this
  omega

/-! #### Theorem B: `n` changes per half-turn -/

/-- Division with remainder, in the form used below. -/
lemma exists_mul_add (d : ℤ) {n : ℕ} (hn : 0 < n) : ∃ q : ℤ, ∃ m : ℕ, m < n ∧ d = q * n + m := by
  have hn' : (0 : ℤ) < n := by exact_mod_cast hn
  have h1 := Int.emod_nonneg d hn'.ne'
  have h2 := Int.emod_lt_of_pos d hn'
  have h3 := Int.emod_add_ediv_mul d n
  refine ⟨d / n, (d % n).toNat, ?_, ?_⟩
  · have h4 := Int.toNat_of_nonneg h1
    generalize d % (n : ℤ) = r at h1 h2 h4 ⊢
    omega
  · rw [Int.toNat_of_nonneg h1]
    linarith

/-- The gaps between the slots of Theorem B: `G_m = (gapLo m, gapHi m)` for `0 ≤ m < n`, relative
to a witness arc `(a, a + l)`, where `ε = π - n l`. -/
noncomputable def gapLo (l a ε : ℝ) (m : ℕ) : ℝ := a + m * l + ε

/-- See `gapLo`. -/
noncomputable def gapHi (l a ε : ℝ) (m : ℕ) : ℝ := if m = 0 then a + l - ε else a + (m + 1) * l

variable {n : ℕ}

/-- **Slots.** If `F` has `n` changes per half-turn and none on `(a, a + ℓ)`, its `m`-th change
after `a` lies in `[a + m ℓ, a + m ℓ + ε]`, where `ε = π - n ℓ`. -/
lemma slot_le (hc : F.c = n) {a : ℝ} (ha : F.NoChange a) {m : ℕ} (hm1 : 1 ≤ m) (hmn : m ≤ n) :
    a + m * ℓ ≤ F.y (F.idx a + m) ∧ F.y (F.idx a + m) ≤ a + m * ℓ + (π - n * ℓ) := by
  constructor
  · have h1 := F.y_add_nat (F.idx a + 1) (m - 1)
    rw [show F.idx a + 1 + ((m - 1 : ℕ) : ℤ) = F.idx a + m by push_cast [Nat.cast_sub hm1]; ring]
      at h1
    unfold NoChange at ha
    rw [Nat.cast_sub hm1, Nat.cast_one] at h1
    linarith
  · have h1 := F.y_add_nat (F.idx a + m) (n - m)
    rw [show F.idx a + m + ((n - m : ℕ) : ℤ) = F.idx a + F.c by
      rw [hc]; push_cast [Nat.cast_sub hmn]; ring, F.y_add_c] at h1
    have h2 := F.y_idx_le a
    rw [Nat.cast_sub hmn] at h1
    linarith

lemma y_idx_ge (hc : F.c = n) (hn : 1 ≤ n) {a : ℝ} (ha : F.NoChange a) :
    a - (π - n * ℓ) ≤ F.y (F.idx a) := by
  have h := (slot_le hc ha hn le_rfl).1
  have e := F.y_add_c (F.idx a)
  rw [hc] at e
  linarith

/-- A witness arc of `F`, shifted by a multiple of `π`, contains one of the gaps `G_m`. -/
lemma exists_gap_sub (hc : F.c = n) (hn : 1 ≤ n) {a : ℝ} (ha : F.NoChange a) {a' : ℝ}
    (ha' : F.NoChange a') :
    ∃ j : ℤ, ∃ m : ℕ, m < n ∧ F.idx (a' + j * π) = F.idx a + m ∧
      a' + j * π ≤ gapLo ℓ a (π - n * ℓ) m ∧ gapHi ℓ a (π - n * ℓ) m ≤ a' + j * π + ℓ := by
  obtain ⟨q, m, hm, hd⟩ := exists_mul_add (F.idx a' - F.idx a) (by omega : 0 < n)
  have hidx : F.idx (a' + ((-q : ℤ) : ℝ) * π) = F.idx a + m := by
    rw [F.idx_add_mul_pi, hc]
    linarith
  refine ⟨-q, m, hm, hidx, ?_⟩
  have hnc : F.NoChange (a' + ((-q : ℤ) : ℝ) * π) := ha'.add_mul_pi _
  have hlow := F.y_idx_le (a' + ((-q : ℤ) : ℝ) * π)
  unfold NoChange at hnc
  rw [hidx] at hlow hnc
  unfold gapLo gapHi
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · rw [if_pos rfl]
    simp only [Nat.cast_zero, zero_mul, add_zero] at hlow hnc ⊢
    have s1 := (slot_le hc ha le_rfl hn).2
    have s0 := y_idx_ge hc hn ha
    push_cast at s1
    exact ⟨by linarith, by linarith⟩
  · rw [if_neg (by omega)]
    have s1 := (slot_le hc ha hm0 hm.le).1
    have s2 := (slot_le hc ha (by omega : 1 ≤ m + 1) hm).2
    push_cast at s2
    rw [show F.idx a + (m : ℤ) + 1 = F.idx a + ((m : ℤ) + 1) by ring] at hnc
    exact ⟨by linarith, by linarith⟩

/-- **Pinning.** If `F` has a witness arc `(a, a + ℓ)` and `H` is compatible with `F` (both with
`n` changes per half-turn), then on some gap `G_m`, `H` does not change and `H = ¬F`. -/
lemma exists_pin {H : SignSeq ℓ} (hℓ : 0 < ℓ) (hcF : F.c = n) (hcH : H.c = n) (hn : 1 ≤ n)
    {a : ℝ} (ha : F.NoChange a) (hFH : Compat ℓ F.val H.val) :
    ∃ m : ℕ, m < n ∧ ∃ h : ℤ,
      (∀ x, gapLo ℓ a (π - n * ℓ) m < x → x < gapHi ℓ a (π - n * ℓ) m → H.idx x = h) ∧
        (Even h ↔ ¬ Even (F.idx a + m)) := by
  obtain ⟨a', hF', hH', hval⟩ := exists_witness hℓ hFH
  obtain ⟨j, m, hm, hidx, hlo, hhi⟩ := exists_gap_sub hcF hn ha hF'
  refine ⟨m, hm, H.idx (a' + j * π), fun x h1 h2 => ?_, ?_⟩
  · exact NoChange.idx_eq (hH'.add_mul_pi j) (by linarith) (by linarith)
  · have hpar := val_ne_iff.1 hval
    rw [H.idx_add_mul_pi, ← hidx, F.idx_add_mul_pi, hcF, hcH]
    simp only [Int.even_add] at hpar ⊢
    tauto

/-- The count between two pinned gaps: `H` has `h' - h` changes between them, at most `K - 1`
when the space between them is shorter than `K ℓ` and the parity forces `h' - h ≠ K`. -/
lemma pinned_gap {H : SignSeq ℓ} (hℓ : 0 < ℓ) {lo₁ hi₁ lo₂ hi₂ : ℝ} {h h' K : ℤ}
    (h₁ : lo₁ < hi₁) (h₂ : lo₂ < hi₂) (hp₁ : ∀ x, lo₁ < x → x < hi₁ → H.idx x = h)
    (hp₂ : ∀ x, lo₂ < x → x < hi₂ → H.idx x = h') (hle : hi₁ ≤ lo₂)
    (hlen : lo₂ - hi₁ < K * ℓ) (hK : 1 ≤ K) (hpar : Odd (h' - h - K)) : h' - h ≤ K - 1 := by
  have hmono : h ≤ h' := by
    have e1 := hp₁ ((lo₁ + hi₁) / 2) (by linarith) (by linarith)
    have e2 := hp₂ ((lo₂ + hi₂) / 2) (by linarith) (by linarith)
    rw [← e1, ← e2]
    exact H.idx_mono (by linarith)
  have hA : hi₁ ≤ H.y (h + 1) := by
    by_contra hc
    push_neg at hc
    have hm1 := le_max_left (H.y (h + 1)) lo₁
    have hm2 := le_max_right (H.y (h + 1)) lo₁
    have hmax : max (H.y (h + 1)) lo₁ < hi₁ := max_lt hc h₁
    have e := hp₁ ((max (H.y (h + 1)) lo₁ + hi₁) / 2) (by linarith) (by linarith)
    have := H.le_idx_iff.2 (show H.y (h + 1) ≤ (max (H.y (h + 1)) lo₁ + hi₁) / 2 by linarith)
    omega
  have hB : H.y h' ≤ lo₂ := by
    by_contra hc
    push_neg at hc
    have hm1 := min_le_left (H.y h') hi₂
    have hm2 := min_le_right (H.y h') hi₂
    have hmin : lo₂ < min (H.y h') hi₂ := lt_min hc h₂
    have e := hp₂ ((lo₂ + min (H.y h') hi₂) / 2) (by linarith) (by linarith)
    have := H.y_idx_le ((lo₂ + min (H.y h') hi₂) / 2)
    rw [e] at this
    linarith
  have hne : h' - h ≠ K := by
    intro he
    rw [he, sub_self] at hpar
    exact (Int.not_odd_iff_even.2 (by decide)) hpar
  rcases le_or_gt h' h with hh | hh
  · omega
  · have := H.y_add_int (show h + 1 ≤ h' by omega)
    have hreal : ((h' : ℝ) - (h + 1)) * ℓ < K * ℓ := by push_cast at this ⊢; linarith
    have : (h' : ℝ) - (h + 1) < K := lt_of_mul_lt_mul_right hreal hℓ.le
    have : h' - (h + 1) < K := by exact_mod_cast this
    omega

/-- **Theorem B (`n` changes per half-turn), core.** In the band `(2n+1) ℓ > 2π`, there are no three
pairwise compatible sign sequences with `n` changes per half-turn. -/
theorem not_three_of_c_eq {G H : SignSeq ℓ} (hℓ : 0 < ℓ) (hband : 2 * π < (2 * n + 1) * ℓ)
    (hF : F.c = n) (hG : G.c = n) (hH : H.c = n) (hFG : Compat ℓ F.val G.val)
    (hFH : Compat ℓ F.val H.val) (hGH : Compat ℓ G.val H.val) : False := by
  have hn : 1 ≤ n := hF ▸ F.c_pos
  obtain ⟨ε, hεdef⟩ : ∃ ε, ε = π - n * ℓ := ⟨_, rfl⟩
  have hε0 : 0 ≤ ε := by have := F.c_mul_le; rw [hF] at this; linarith
  have hε : 2 * ε < ℓ := by linarith
  obtain ⟨a, haF, haG, hval⟩ := exists_witness hℓ hFG
  obtain ⟨m, hm, h₁, hp₁, hpar₁⟩ := exists_pin hℓ hF hH hn haF hFH
  obtain ⟨j, hj, h₂, hp₂, hpar₂⟩ := exists_pin hℓ hG hH hn haG hGH
  rw [← hεdef] at hp₁ hp₂
  have hv := val_ne_iff.1 hval
  -- `H = G` on `G_m` and `H ≠ G` on `G_j`
  have hpar : ∀ {m j : ℕ} {h₁ h₂ : ℤ}, (Even h₁ ↔ ¬ Even (F.idx a + m)) →
      (Even h₂ ↔ ¬ Even (G.idx a + j)) → Odd ((h₂ - h₁) - ((j : ℤ) - m)) := by
    intro m j h₁ h₂ e₁ e₂
    have hv' := hv
    rw [Int.odd_iff]
    rw [Int.even_iff, Int.even_iff] at e₁ e₂ hv'
    omega
  have hgap : ∀ k : ℕ, gapLo ℓ a ε k < gapHi ℓ a ε k := by
    intro k
    unfold gapLo gapHi
    split_ifs with hk
    · rw [hk]; push_cast; linarith
    · push_cast; linarith
  have hhi : ∀ k : ℕ, a + (k + 1) * ℓ - ε ≤ gapHi ℓ a ε k := by
    intro k
    unfold gapHi
    split_ifs with hk
    · rw [hk]; push_cast; linarith
    · linarith
  have hhi_le : ∀ k : ℕ, gapHi ℓ a ε k ≤ a + (k + 1) * ℓ := by
    intro k
    unfold gapHi
    split_ifs with hk
    · rw [hk]; push_cast; linarith
    · exact le_rfl
  have hhi' : ∀ k : ℕ, k ≠ 0 → gapHi ℓ a ε k = a + (k + 1) * ℓ := fun k hk => if_neg hk
  -- the counting argument, for `m < j`
  have count : ∀ {m j : ℕ} {h₁ h₂ : ℤ}, m < j → j < n →
      (∀ x, gapLo ℓ a ε m < x → x < gapHi ℓ a ε m → H.idx x = h₁) →
      (∀ x, gapLo ℓ a ε j < x → x < gapHi ℓ a ε j → H.idx x = h₂) →
      Odd ((h₂ - h₁) - ((j : ℤ) - m)) → False := by
    intro m j h₁ h₂ hmj hjn hp₁ hp₂ hodd
    have hmj' : (m : ℝ) + 1 ≤ j := by exact_mod_cast hmj
    have hjn' : (j : ℝ) + 1 ≤ n := by exact_mod_cast hjn
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have hj0 : j ≠ 0 := by omega
    have p1 := mul_le_mul_of_nonneg_right hmj' hℓ.le
    have p2 := mul_le_mul_of_nonneg_right hjn' hℓ.le
    have p3 := mul_nonneg hm0 hℓ.le
    have c1 := pinned_gap hℓ (hgap m) (hgap j) hp₁ hp₂
      (show gapHi ℓ a ε m ≤ gapLo ℓ a ε j by
        have := hhi_le m; unfold gapLo; linarith)
      (show gapLo ℓ a ε j - gapHi ℓ a ε m < (((j : ℤ) - m : ℤ) : ℝ) * ℓ by
        have := hhi m; unfold gapLo; push_cast; linarith)
      (by omega) hodd
    have hp₁' : ∀ x, gapLo ℓ a ε m + π < x → x < gapHi ℓ a ε m + π → H.idx x = h₁ + n := by
      intro x hx1 hx2
      have := H.idx_add_pi (x - π)
      rw [sub_add_cancel, hp₁ (x - π) (by linarith) (by linarith), hH] at this
      exact this
    have c2 := pinned_gap hℓ (hgap j) (by linarith [hgap m]) hp₂ hp₁'
      (show gapHi ℓ a ε j ≤ gapLo ℓ a ε m + π by
        rw [hhi' j hj0]; unfold gapLo; linarith)
      (show gapLo ℓ a ε m + π - gapHi ℓ a ε j < (((n : ℤ) + m - j : ℤ) : ℝ) * ℓ by
        rw [hhi' j hj0]; unfold gapLo; push_cast; linarith)
      (by omega)
      (by
        have : h₁ + n - h₂ - ((n : ℤ) + m - j) = -((h₂ - h₁) - ((j : ℤ) - m)) := by ring
        rw [this]
        exact hodd.neg)
    omega
  rcases lt_trichotomy m j with hmj | rfl | hjm
  · exact count hmj hj hp₁ hp₂ (hpar hpar₁ hpar₂)
  · -- the same gap: `H = G` and `H ≠ G` there
    have hx := hgap m
    have e₁ := hp₁ ((gapLo ℓ a ε m + gapHi ℓ a ε m) / 2) (by linarith) (by linarith)
    have e₂ := hp₂ ((gapLo ℓ a ε m + gapHi ℓ a ε m) / 2) (by linarith) (by linarith)
    rw [e₁] at e₂
    subst e₂
    have := hpar hpar₁ hpar₂
    simp only [sub_self] at this
    exact (Int.not_odd_iff_even.2 (by decide)) this
  · refine count hjm hm hp₂ hp₁ ?_
    have : h₁ - h₂ - ((m : ℤ) - j) = -((h₂ - h₁) - ((j : ℤ) - m)) := by ring
    rw [this]
    exact (hpar hpar₁ hpar₂).neg

/-- **Theorem B.** In the band `(2n+1) ℓ > 2π`, a compatible family of sign sequences with `n`
changes per half-turn has at most `2` members. -/
theorem card_le_two_of_c_eq {ι : Type*} (s : Finset ι) (F : ι → SignSeq ℓ) (hℓ : 0 < ℓ)
    (hband : 2 * π < (2 * n + 1) * ℓ) (hc : ∀ i ∈ s, (F i).c = n)
    (hcomp : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Compat ℓ (F i).val (F j).val) : s.card ≤ 2 := by
  by_contra h
  push_neg at h
  obtain ⟨i, hi, j, hj, k, hk, hij, hik, hjk⟩ := Finset.two_lt_card.1 h
  exact not_three_of_c_eq hℓ hband (hc i hi) (hc j hj) (hc k hk) (hcomp i hi j hj hij)
    (hcomp i hi k hk hik) (hcomp j hj k hk hjk)

/-- **(R) for `n ≤ 3`, for sign sequences.** For `n ≤ 2` every member has one change per
half-turn (Theorem A); for `n = 3` the members have one or three changes (Theorems A and B). -/
theorem card_le_two_pow_of_le_three {ι : Type*} (s : Finset ι) (F : ι → SignSeq ℓ) (hn : n ≤ 3)
    (hℓ : 0 < ℓ) (hband : 2 * π < (2 * n + 1) * ℓ)
    (hcomp : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Compat ℓ (F i).val (F j).val) : s.card ≤ 2 ^ n := by
  classical
  have hc_le : ∀ i ∈ s, (F i).c ≤ n := fun i _ => (F i).c_le hℓ hband
  have hodd : ∀ i, ∃ t, (F i).c = 2 * t + 1 := fun i => (F i).c_odd
  have hA := card_le_of_c_eq_one (s.filter fun i => (F i).c = 1) F hℓ hband
    (fun i hi => (Finset.mem_filter.1 hi).2)
    (fun i hi j hj hij => hcomp i (Finset.mem_filter.1 hi).1 j (Finset.mem_filter.1 hj).1 hij)
  have hsplit := Finset.card_filter_add_card_filter_not (s := s) (fun i => (F i).c = 1)
  have hcomp' : ∀ i ∈ s.filter (fun i => ¬ (F i).c = 1), ∀ j ∈ s.filter (fun i => ¬ (F i).c = 1),
      i ≠ j → Compat ℓ (F i).val (F j).val :=
    fun i hi j hj hij => hcomp i (Finset.mem_filter.1 hi).1 j (Finset.mem_filter.1 hj).1 hij
  have h0 : n ≠ 3 → (s.filter fun i => ¬ (F i).c = 1).card = 0 := fun h3 =>
    Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 fun i hi => by
      obtain ⟨t, ht⟩ := hodd i
      have := hc_le i hi
      omega)
  have h2 : (s.filter fun i => ¬ (F i).c = 1).card ≤ 2 := by
    by_cases h3 : n = 3
    · subst h3
      refine card_le_two_of_c_eq _ F hℓ hband (fun i hi => ?_) hcomp'
      obtain ⟨hi, hne⟩ := Finset.mem_filter.1 hi
      obtain ⟨t, ht⟩ := hodd i
      have := hc_le i hi
      omega
    · rw [h0 h3]
      omega
  interval_cases n
  · have := h0 (by norm_num); norm_num; omega
  · have := h0 (by norm_num); norm_num; omega
  · have := h0 (by norm_num); norm_num; omega
  · norm_num; omega

end SignSeq

end Blumenthal
