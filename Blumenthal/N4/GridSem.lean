import Mathlib.Data.Finset.Card
import Mathlib.Tactic.IntervalCases
import Blumenthal.N4.GridDefs

/-!
# Semantics of the (22, 5) grid model

A discrete string lives on the circle of 44 cells (a full turn; a half-turn is 22 cells). It is
antiperiodic, has exactly 3 sign changes per half-turn, and every run has length ≥ 5 cells.
We describe it by the value `s` on cell 0 and the change points `a < b < c < 22` (a change at
`p` means cells `p - 1` and `p` differ); the change points on the full circle are
`a, b, c, a + 22, b + 22, c + 22`.

Two strings are *compatible* if they differ on 5 cyclically consecutive cells.
-/

namespace Grid

/-! ## 44-bit masks and rotation -/

lemma testBit_M44 (i : ℕ) : M44.testBit i = decide (i < 44) := by
  unfold M44; exact Nat.testBit_two_pow_sub_one 44 i

lemma testBit_of_lt {x : ℕ} (hx : x < 2 ^ 44) {i : ℕ} (hi : 44 ≤ i) : x.testBit i = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) hi))

lemma lt_of_testBit {x : ℕ} (h : ∀ i, 44 ≤ i → x.testBit i = false) : x < 2 ^ 44 :=
  Nat.lt_pow_two_of_testBit x h

lemma testBit_rot1 {x : ℕ} (hx : x < 2 ^ 44) (i : ℕ) :
    (rot1 x).testBit i = (decide (i < 44) && x.testBit ((i + 43) % 44)) := by
  simp only [rot1, Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftLeft,
    Nat.testBit_shiftRight, testBit_M44]
  by_cases h0 : i = 0
  · subst h0; simp
  · by_cases h44 : i < 44
    · have h1 : 1 ≤ i := Nat.one_le_iff_ne_zero.2 h0
      have hm : (i + 43) % 44 = i - 1 := by omega
      rw [testBit_of_lt hx (by omega : 44 ≤ 43 + i), hm]
      simp [h1, h44]
    · rw [testBit_of_lt hx (by omega : 44 ≤ 43 + i)]
      simp [h44]

lemma rot1_lt {x : ℕ} (hx : x < 2 ^ 44) : rot1 x < 2 ^ 44 :=
  lt_of_testBit fun i hi => by rw [testBit_rot1 hx]; simp [show ¬ i < 44 by omega]

lemma testBit_rot1_lt {x : ℕ} (hx : x < 2 ^ 44) {i : ℕ} (hi : i < 44) :
    (rot1 x).testBit i = x.testBit ((i + 43) % 44) := by
  rw [testBit_rot1 hx]; simp [hi]

/-- the five rotated copies, bit by bit -/
lemma testBit_window {d : ℕ} (hd : d < 2 ^ 44) (i : ℕ) :
    (d &&& rot1 d &&& rot1 (rot1 d) &&& rot1 (rot1 (rot1 d)) &&&
        rot1 (rot1 (rot1 (rot1 d)))).testBit i =
      (decide (i < 44) && d.testBit i && d.testBit ((i + 43) % 44) &&
        d.testBit ((i + 42) % 44) && d.testBit ((i + 41) % 44) && d.testBit ((i + 40) % 44)) := by
  have h1 := rot1_lt hd
  have h2 := rot1_lt h1
  have h3 := rot1_lt h2
  by_cases hi : i < 44
  · have m : ∀ j, j % 44 < 44 := fun j => Nat.mod_lt _ (by norm_num)
    have k1 : (rot1 d).testBit i = d.testBit ((i + 43) % 44) := testBit_rot1_lt hd hi
    have k2 : (rot1 (rot1 d)).testBit i = d.testBit ((i + 42) % 44) := by
      rw [testBit_rot1_lt h1 hi, testBit_rot1_lt hd (m _)]; congr 1; omega
    have k3 : (rot1 (rot1 (rot1 d))).testBit i = d.testBit ((i + 41) % 44) := by
      rw [testBit_rot1_lt h2 hi, testBit_rot1_lt h1 (m _), testBit_rot1_lt hd (m _)]
      congr 1; omega
    have k4 : (rot1 (rot1 (rot1 (rot1 d)))).testBit i = d.testBit ((i + 40) % 44) := by
      rw [testBit_rot1_lt h3 hi, testBit_rot1_lt h2 (m _), testBit_rot1_lt h1 (m _),
        testBit_rot1_lt hd (m _)]
      congr 1; omega
    simp only [Nat.testBit_and, k1, k2, k3, k4, hi, decide_true, Bool.true_and]
  · have z : ∀ x, x < 2 ^ 44 → x.testBit i = false := fun x hx => testBit_of_lt hx (by omega)
    simp only [Nat.testBit_and, z d hd, hi, decide_false, Bool.false_and]

lemma hasWindow_iff {d : ℕ} (hd : d < 2 ^ 44) :
    hasWindow d = true ↔ ∃ j < 44, ∀ t < 5, d.testBit ((j + t) % 44) = true := by
  simp only [hasWindow, bne_iff_ne, ne_eq]
  constructor
  · intro h
    obtain ⟨i, hi⟩ := Nat.exists_testBit_of_ne_zero h
    rw [testBit_window hd] at hi
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hi
    obtain ⟨⟨⟨⟨⟨hi44, b0⟩, b1⟩, b2⟩, b3⟩, b4⟩ := hi
    refine ⟨(i + 40) % 44, Nat.mod_lt _ (by norm_num), fun t ht => ?_⟩
    interval_cases t
    · simpa [show ((i + 40) % 44 + 0) % 44 = (i + 40) % 44 by omega] using b4
    · simpa [show ((i + 40) % 44 + 1) % 44 = (i + 41) % 44 by omega] using b3
    · simpa [show ((i + 40) % 44 + 2) % 44 = (i + 42) % 44 by omega] using b2
    · simpa [show ((i + 40) % 44 + 3) % 44 = (i + 43) % 44 by omega] using b1
    · simpa [show ((i + 40) % 44 + 4) % 44 = i by omega] using b0
  · rintro ⟨j, hj, ht⟩ h0
    have := testBit_window hd ((j + 4) % 44)
    rw [h0, Nat.zero_testBit] at this
    have hlt : (j + 4) % 44 < 44 := Nat.mod_lt _ (by norm_num)
    have g0 := ht 4 (by norm_num)
    have g1 := ht 3 (by norm_num)
    have g2 := ht 2 (by norm_num)
    have g3 := ht 1 (by norm_num)
    have g4 : d.testBit (j % 44) = true := by simpa using ht 0 (by norm_num)
    rw [show ((j + 4) % 44 + 43) % 44 = (j + 3) % 44 by omega,
      show ((j + 4) % 44 + 42) % 44 = (j + 2) % 44 by omega,
      show ((j + 4) % 44 + 41) % 44 = (j + 1) % 44 by omega,
      show ((j + 4) % 44 + 40) % 44 = j % 44 by omega] at this
    simp [hlt, g0, g1, g2, g3, g4] at this

lemma rot1_xor {x y : ℕ} (hx : x < 2 ^ 44) (hy : y < 2 ^ 44) :
    rot1 x ^^^ rot1 y = rot1 (x ^^^ y) := by
  have hxy : x ^^^ y < 2 ^ 44 := Nat.xor_lt_two_pow hx hy
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor, testBit_rot1 hx, testBit_rot1 hy, testBit_rot1 hxy, Nat.testBit_xor]
  cases decide (i < 44) <;> simp

lemma hasWindow_rot1 {d : ℕ} (hd : d < 2 ^ 44) : hasWindow (rot1 d) = hasWindow d := by
  rw [Bool.eq_iff_iff, hasWindow_iff (rot1_lt hd), hasWindow_iff hd]
  constructor
  · rintro ⟨j, hj, ht⟩
    refine ⟨(j + 43) % 44, Nat.mod_lt _ (by norm_num), fun t htt => ?_⟩
    have := ht t htt
    rw [testBit_rot1 hd] at this
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    rw [show ((j + 43) % 44 + t) % 44 = ((j + t) % 44 + 43) % 44 by omega]
    exact this.2
  · rintro ⟨j, hj, ht⟩
    refine ⟨(j + 1) % 44, Nat.mod_lt _ (by norm_num), fun t htt => ?_⟩
    rw [testBit_rot1 hd]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨Nat.mod_lt _ (by norm_num), ?_⟩
    rw [show (((j + 1) % 44 + t) % 44 + 43) % 44 = (j + t) % 44 by omega]
    exact ht t htt

lemma compat_rot1 {x y : ℕ} (hx : x < 2 ^ 44) (hy : y < 2 ^ 44) :
    compat (rot1 x) (rot1 y) = compat x y := by
  unfold compat
  rw [rot1_xor hx hy, hasWindow_rot1 (Nat.xor_lt_two_pow hx hy)]

/-! ## Discrete strings -/

/-- a discrete 3-change string on the (22, 5) grid -/
structure DStr where
  s : Bool
  a : ℕ
  b : ℕ
  c : ℕ
  hab : a + 5 ≤ b
  hbc : b + 5 ≤ c
  hca : c + 5 ≤ a + 22
  hc : c < 22

def DStr.val (d : DStr) (i : ℕ) : Bool := valP d.s d.a d.b d.c i

/-- compatibility: opposite values on 5 cyclically consecutive cells -/
def DCompat (d e : DStr) : Prop :=
  ∃ j < 44, ∀ t < 5, d.val ((j + t) % 44) ≠ e.val ((j + t) % 44)

lemma testBit_maskUpTo (f : ℕ → Bool) (n i : ℕ) :
    (maskUpTo f n).testBit i = (decide (i < n) && f i) := by
  induction n with
  | zero => simp [maskUpTo]
  | succ n ih =>
    simp only [maskUpTo, Nat.testBit_or, ih]
    split
    · rename_i hf
      rw [Nat.testBit_two_pow]
      by_cases h : i = n
      · subst h; simp [hf]
      · have : n ≠ i := Ne.symm h
        by_cases hi : i < n
        · simp [hi, show i < n + 1 by omega, this]
        · simp [hi, show ¬ i < n + 1 by omega, this]
    · rename_i hf
      simp only [Nat.zero_testBit, Bool.or_false]
      by_cases h : i = n
      · subst h; simp [hf]
      · by_cases hi : i < n
        · simp [hi, show i < n + 1 by omega]
        · simp [hi, show ¬ i < n + 1 by omega]

def DStr.mask (d : DStr) : ℕ := maskP d.s d.a d.b d.c

lemma testBit_mask (d : DStr) (i : ℕ) : d.mask.testBit i = (decide (i < 44) && d.val i) :=
  testBit_maskUpTo _ _ _

lemma mask_lt (d : DStr) : d.mask < 2 ^ 44 :=
  lt_of_testBit fun i hi => by rw [testBit_mask]; simp [show ¬ i < 44 by omega]

/-- compatibility of strings is compatibility of their masks -/
lemma compat_mask_iff (d e : DStr) : compat d.mask e.mask = true ↔ DCompat d e := by
  unfold compat
  rw [hasWindow_iff (Nat.xor_lt_two_pow (mask_lt d) (mask_lt e))]
  unfold DCompat
  apply exists_congr; intro j
  apply and_congr_right; intro _
  apply forall_congr'; intro t
  apply imp_congr_right; intro _
  have hlt : (j + t) % 44 < 44 := Nat.mod_lt _ (by norm_num)
  rw [Nat.testBit_xor, testBit_mask, testBit_mask]
  simp only [hlt, decide_true, Bool.true_and]
  cases d.val ((j + t) % 44) <;> cases e.val ((j + t) % 44) <;> simp

lemma not_compat_self (x : ℕ) : compat x x = false := by
  simp [compat, hasWindow]

end Grid
