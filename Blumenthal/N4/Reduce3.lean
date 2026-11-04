import Blumenthal.N4.Reduce2
import Blumenthal.SignBridge

/-!
# Statement (R) for n = 4

`N4.card_le_eight`: a compatible family of sign sequences with three changes per half-turn has at
most 8 members when `2π < 9ℓ` (grid reduction + `Grid.no_nine_compatible`).
`N4.card_le_sixteen`: the whole family has at most 16 members.
`N4.statementR_four`: `StatementR 4`.
-/

open Real Blumenthal Classical

namespace N4

variable {ℓ : ℝ}

/-- a window of 5 differing cells gives `Grid.DCompat` -/
lemma dcompat_of_window {F : Fin 9 → SignSeq ℓ} (hc : ∀ i, (F i).c = 3) {P : Vx → ℤ}
    (hℓ : 0 < ℓ) (hP : ∀ v w, v ≠ w → P v + cw F v w ≤ P w) {f g : Fin 9} {df dg : Grid.DStr}
    (hdf : ∀ t : ℕ, t < 44 → df.val t = Dval F P f t)
    (hdg : ∀ t : ℕ, t < 44 → dg.val t = Dval F P g t)
    {W : ℤ} (hW : ∀ t, W ≤ t → t < W + 5 → Dval F P f t ≠ Dval F P g t) :
    Grid.DCompat df dg := by
  refine ⟨(W % 44).toNat, by omega, fun t ht => ?_⟩
  set cell := ((W % 44).toNat + t) % 44
  have hcell : cell < 44 := Nat.mod_lt _ (by norm_num)
  have hcz : ((cell : ℕ) : ℤ) = (W + t) % 44 := by
    simp only [cell]; push_cast; rw [Int.toNat_of_nonneg (by omega)]; omega
  have hWt : W + t = (cell : ℤ) + 44 * ((W + t) / 44) := by
    rw [hcz]; have := Int.emod_add_ediv_mul (W + t) 44; linarith
  rw [hdf cell hcell, hdg cell hcell]
  rw [← Dval_periodic hc hℓ hP f cell ((W + t) / 44), ← Dval_periodic hc hℓ hP g cell ((W + t) / 44),
    ← hWt]
  exact hW (W + t) (by omega) (by omega)

/-- **The three-change class.** -/
theorem card_le_eight {ι : Type*} (s : Finset ι) (G : ι → SignSeq ℓ) (hℓ : 0 < ℓ)
    (hband : 2 * π < 9 * ℓ) (hc : ∀ i ∈ s, (G i).c = 3)
    (hcomp : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Compat ℓ (G i).val (G j).val) : s.card ≤ 8 := by
  by_contra h
  push Not at h
  obtain ⟨t, hts, htc⟩ := Finset.exists_subset_card_eq (show 9 ≤ s.card by omega)
  let e9 : t ≃ Fin 9 := t.equivFin.trans (finCongr htc)
  let F : Fin 9 → SignSeq ℓ := fun i => G (e9.symm i).1
  have hcF : ∀ i, (F i).c = 3 := fun i => hc _ (hts (e9.symm i).2)
  have hcompF : ∀ i j, i ≠ j → Compat ℓ (F i).val (F j).val := by
    intro i j hij
    refine hcomp _ (hts (e9.symm i).2) _ (hts (e9.symm j).2) ?_
    intro h
    exact hij (e9.symm.injective (Subtype.ext h))
  obtain ⟨P, hP⟩ := exists_P F hcF hℓ hband
  choose d hd using fun i => exists_dstr hcF hℓ hP i
  have hL : (List.ofFn d).Pairwise Grid.DCompat := by
    rw [List.pairwise_ofFn]
    intro i j hij
    obtain ⟨W, hW⟩ := window hcF hℓ hP (hcompF i j (ne_of_lt hij))
    exact dcompat_of_window hcF hℓ hP (hd i) (hd j) hW
  have := Grid.no_nine_compatible _ hL
  simp at this

/-- **(R) for n = 4, for sign sequences.** -/
theorem card_le_sixteen {ι : Type*} (s : Finset ι) (G : ι → SignSeq ℓ) (hℓ : 0 < ℓ)
    (hband : 2 * π < (2 * (4 : ℕ) + 1) * ℓ)
    (hcomp : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Compat ℓ (G i).val (G j).val) : s.card ≤ 2 ^ 4 := by
  have hband9 : 2 * π < 9 * ℓ := by norm_num at hband ⊢; linarith
  have hc_le : ∀ i ∈ s, (G i).c ≤ 4 := fun i _ => (G i).c_le hℓ hband
  have hodd : ∀ i, ∃ t, (G i).c = 2 * t + 1 := fun i => (G i).c_odd
  have hA := SignSeq.card_le_of_c_eq_one (s.filter fun i => (G i).c = 1) G hℓ hband
    (fun i hi => (Finset.mem_filter.1 hi).2)
    (fun i hi j hj hij => hcomp i (Finset.mem_filter.1 hi).1 j (Finset.mem_filter.1 hj).1 hij)
  have hB := card_le_eight (s.filter fun i => ¬ (G i).c = 1) G hℓ hband9
    (fun i hi => by
      obtain ⟨hi, hne⟩ := Finset.mem_filter.1 hi
      obtain ⟨t, ht⟩ := hodd i
      have := hc_le i hi
      omega)
    (fun i hi j hj hij => hcomp i (Finset.mem_filter.1 hi).1 j (Finset.mem_filter.1 hj).1 hij)
  have hsplit := Finset.card_filter_add_card_filter_not (s := s) (fun i => (G i).c = 1)
  omega

/-- **Statement (R) for n = 4.** -/
theorem statementR_four : StatementR 4 := by
  intro ℓ hℓ hband S hS hcomp
  have hrep : ∀ f ∈ S, ∃ F : SignSeq ℓ, ∀ x, (∀ k, F.y k ≠ x) → f x = F.val x :=
    fun f hf => SignBridge.exists_signSeq hℓ (hS f hf).1 (hS f hf).2
  choose F hF using hrep
  have := card_le_sixteen S.attach (fun f => F f.1 f.2) hℓ hband
    (by
      rintro ⟨f, hf⟩ - ⟨g, hg⟩ - hne
      exact SignBridge.compat_of_rep (hF f hf) (hF g hg) (hcomp f hf g hg (fun h => hne (Subtype.ext h))))
  simpa using this

end N4
