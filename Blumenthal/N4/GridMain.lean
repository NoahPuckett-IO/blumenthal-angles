import Mathlib.Data.Finset.Max
import Mathlib.Data.List.GetD
import Blumenthal.N4.CertSound
import Blumenthal.N4.GridSem
import Blumenthal.N4.GridFacts
import Blumenthal.N4.CaseCert0
import Blumenthal.N4.CaseCerts

/-!
# No nine compatible strings on the (22, 5) grid

Main result: `Grid.no_nine_compatible`. A list of discrete 3-change strings on the (22, 5) grid
that are pairwise compatible has at most 8 members. This is the finite step of Theorem C
(statement (R) for n = 4) in NoahPuckett-IO/blumenthal-angles-lean, `docs/STEP5-NOTES.md` §4.4.
-/

namespace Grid

open CertSound

/-! ## Propositional forms of the kernel-checked facts -/

lemma getD_mem {l : List ℕ} {i : ℕ} (h : i < l.length) : l.getD i 0 ∈ l := by
  rw [List.getD_eq_getElem _ _ h]; exact List.getElem_mem h

lemma basic_facts :
    gridMasks.length = 528 ∧ gridOrbit.length = 528 ∧ gridRotIdx.length = 528 ∧
      gridToRep.length = 528 ∧ gridReps.length = 12 ∧ (∀ x ∈ gridMasks, x < 2 ^ 44) ∧
      (∀ x ∈ gridOrbit, x < 12) ∧ (∀ x ∈ gridReps, x < 528) ∧ (∀ x ∈ gridRotIdx, x < 528) := by
  have h := chkBasic_eq
  simp only [chkBasic, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

lemma len_masks : gridMasks.length = 528 := basic_facts.1
lemma len_orbit : gridOrbit.length = 528 := basic_facts.2.1

lemma mI_lt {i : ℕ} (hi : i < 528) : mI i < 2 ^ 44 :=
  basic_facts.2.2.2.2.2.1 _ (getD_mem (by rw [len_masks]; exact hi))

lemma orbI_lt {i : ℕ} (hi : i < 528) : orbI i < 12 :=
  basic_facts.2.2.2.2.2.2.1 _ (getD_mem (by rw [len_orbit]; exact hi))

lemma repI_lt {o : ℕ} (ho : o < 12) : repI o < 528 :=
  basic_facts.2.2.2.2.2.2.2.1 _ (getD_mem (by rw [basic_facts.2.2.2.2.1]; exact ho))

lemma rotI_lt {i : ℕ} (hi : i < 528) : rotI i < 528 :=
  basic_facts.2.2.2.2.2.2.2.2 _ (getD_mem (by rw [basic_facts.2.2.1]; exact hi))

lemma mI_inj {i j : ℕ} (hi : i < 528) (hj : j < 528) (h : mI i = mI j) : i = j := by
  unfold mI at h
  rw [List.getD_eq_getElem _ _ (by rw [len_masks]; exact hi),
    List.getD_eq_getElem _ _ (by rw [len_masks]; exact hj)] at h
  exact (masks_nodup.getElem_inj_iff).1 h

/-- every string's mask is in the list -/
lemma mask_mem (d : DStr) : d.mask ∈ gridMasks := by
  have h := chkMem_eq
  unfold chkMem at h
  rw [List.all_eq_true] at h
  have h1 := h d.s (by cases d.s <;> simp)
  rw [List.all_eq_true] at h1
  have hab := d.hab; have hbc := d.hbc; have hca := d.hca; have hc := d.hc
  have h2 := h1 d.a (List.mem_range.2 (by omega))
  rw [List.all_eq_true] at h2
  have h3 := h2 d.b (List.mem_range.2 (by omega))
  rw [List.all_eq_true] at h3
  have h4 := h3 d.c (List.mem_range.2 hc)
  have hcond : (decide (d.a + 5 ≤ d.b) && decide (d.b + 5 ≤ d.c) &&
      decide (d.c + 5 ≤ d.a + 22)) = true := by simp [hab, hbc, hca]
  rw [hcond] at h4
  simpa [DStr.mask] using h4

lemma rows {i : ℕ} (hi : i < 528) : adjTree.get (bitOf i) = packL (compat (mI i)) gridMasks 0 := by
  have key : ∀ lo, chkRows lo 66 = true → lo ≤ i → i < lo + 66 →
      adjTree.get (bitOf i) = packL (compat (mI i)) gridMasks 0 := by
    intro lo h h1 h2
    unfold chkRows at h
    rw [List.all_eq_true] at h
    have := h i (List.mem_range'_1.2 ⟨h1, h2⟩)
    simpa using this
  rcases (by omega : i < 66 ∨ (66 ≤ i ∧ i < 132) ∨ (132 ≤ i ∧ i < 198) ∨ (198 ≤ i ∧ i < 264) ∨
      (264 ≤ i ∧ i < 330) ∨ (330 ≤ i ∧ i < 396) ∨ (396 ≤ i ∧ i < 462) ∨ (462 ≤ i ∧ i < 528)) with
    h | h | h | h | h | h | h | h
  · exact key 0 chkRows0 (Nat.zero_le _) h
  · exact key 66 chkRows1 h.1 h.2
  · exact key 132 chkRows2 h.1 h.2
  · exact key 198 chkRows3 h.1 h.2
  · exact key 264 chkRows4 h.1 h.2
  · exact key 330 chkRows5 h.1 h.2
  · exact key 396 chkRows6 h.1 h.2
  · exact key 462 chkRows7 h.1 h.2

lemma rot_facts {i : ℕ} (hi : i < 528) : mI (rotI i) = rot1 (mI i) ∧ orbI (rotI i) = orbI i := by
  have h := chkRot_eq
  unfold chkRot at h
  rw [List.all_eq_true] at h
  simpa using h i (List.mem_range.2 hi)

lemma rep_spec {i : ℕ} (hi : i < 528) : iterRot (gridToRep.getD i 0) i = repI (orbI i) := by
  have h := chkRep_eq
  unfold chkRep at h
  rw [List.all_eq_true] at h
  simpa using h i (List.mem_range.2 hi)

/-! ## Bits of packed rows -/

lemma testBit_packL_low (f : ℕ → Bool) :
    ∀ (L : List ℕ) (j0 : ℕ), j0 + L.length ≤ 528 → ∀ j < j0,
      (packL f L j0).testBit (bitOf j) = false := by
  intro L
  induction L with
  | nil => intro j0 _ j _; simp [packL]
  | cons x xs ih =>
    intro j0 hlen j hj
    simp only [List.length_cons] at hlen
    simp only [packL, Nat.testBit_or, ih (j0 + 1) (by omega) j (by omega), Bool.or_false]
    split
    · rw [Nat.testBit_two_pow, decide_eq_false_iff_not]; simp only [bitOf]; omega
    · simp

lemma testBit_packL (f : ℕ → Bool) :
    ∀ (L : List ℕ) (j0 : ℕ), j0 + L.length ≤ 528 → ∀ k < L.length,
      (packL f L j0).testBit (bitOf (j0 + k)) = f (L.getD k 0) := by
  intro L
  induction L with
  | nil => intro j0 _ k hk; simp at hk
  | cons x xs ih =>
    intro j0 hlen k hk
    simp only [List.length_cons] at hlen hk
    rcases k with _ | k
    · simp only [packL, Nat.testBit_or, Nat.add_zero]
      rw [testBit_packL_low f xs (j0 + 1) (by omega) j0 (by omega), Bool.or_false]
      split
      · rename_i hf; rw [Nat.testBit_two_pow]; simp [hf]
      · rename_i hf; simp [hf]
    · simp only [packL, Nat.testBit_or, List.getD_cons_succ]
      rw [show j0 + (k + 1) = (j0 + 1) + k by omega, ih (j0 + 1) (by omega) k (by omega)]
      split
      · rw [Nat.testBit_two_pow]; simp only [bitOf]
        have : ¬ (527 - j0 = 527 - (j0 + 1 + k)) := by omega
        simp [this]
      · simp

lemma adj_bit {i j : ℕ} (hi : i < 528) (hj : j < 528) :
    (adjTree.get (bitOf i)).testBit (bitOf j) = compat (mI i) (mI j) := by
  rw [rows hi]
  have := testBit_packL (compat (mI i)) gridMasks 0 (by rw [len_masks]) j (by rw [len_masks]; exact hj)
  simpa [mI] using this

lemma caseP_bit {o j : ℕ} (ho : o < 12) (hj : j < 528) :
    (caseP o).testBit (bitOf j) = (compat (mI (repI o)) (mI j) && decide (o ≤ orbI j)) := by
  unfold caseP
  rw [Nat.testBit_and, adj_bit (repI_lt ho) hj]
  have := testBit_packL (fun x => decide (o ≤ x)) gridOrbit 0 (by rw [len_orbit]) j
    (by rw [len_orbit]; exact hj)
  simp only [Nat.zero_add] at this
  rw [this]; rfl

/-! ## Rotations -/

lemma rot1_inj {x y : ℕ} (hx : x < 2 ^ 44) (hy : y < 2 ^ 44) (h : rot1 x = rot1 y) : x = y := by
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < 44
  · have hm : (k + 1) % 44 < 44 := Nat.mod_lt _ (by norm_num)
    have ex := testBit_rot1_lt hx hm
    have ey := testBit_rot1_lt hy hm
    rw [show ((k + 1) % 44 + 43) % 44 = k by omega] at ex ey
    rw [← ex, ← ey, h]
  · rw [testBit_of_lt hx (by omega), testBit_of_lt hy (by omega)]

lemma iter_rot1_lt (n : ℕ) {x : ℕ} (hx : x < 2 ^ 44) : rot1^[n] x < 2 ^ 44 := by
  induction n generalizing x with
  | zero => exact hx
  | succ n ih => rw [Function.iterate_succ_apply]; exact ih (rot1_lt hx)

lemma iter_rot1_inj (n : ℕ) {x y : ℕ} (hx : x < 2 ^ 44) (hy : y < 2 ^ 44)
    (h : rot1^[n] x = rot1^[n] y) : x = y := by
  induction n generalizing x y with
  | zero => exact h
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply] at h
    exact rot1_inj hx hy (ih (rot1_lt hx) (rot1_lt hy) h)

lemma compat_iter (n : ℕ) {x y : ℕ} (hx : x < 2 ^ 44) (hy : y < 2 ^ 44) :
    compat (rot1^[n] x) (rot1^[n] y) = compat x y := by
  induction n generalizing x y with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih (rot1_lt hx) (rot1_lt hy),
      compat_rot1 hx hy]

lemma iterRot_spec (n : ℕ) : ∀ i, i < 528 →
    iterRot n i < 528 ∧ mI (iterRot n i) = rot1^[n] (mI i) ∧ orbI (iterRot n i) = orbI i := by
  induction n with
  | zero => intro i hi; exact ⟨hi, rfl, rfl⟩
  | succ n ih =>
    intro i hi
    obtain ⟨h1, h2, h3⟩ := ih (rotI i) (rotI_lt hi)
    obtain ⟨r1, r2⟩ := rot_facts hi
    refine ⟨h1, ?_, ?_⟩
    · rw [iterRot, h2, r1, Function.iterate_succ_apply]
    · rw [iterRot, h3, r2]

/-! ## The twelve orbit cases -/

lemma cases_noClique {o : ℕ} (ho : o < 12) : NoClique adjTree.get (caseP o) 8 := by
  interval_cases o
  · exact checkCert_sound _ _ _ _ case0
  · exact checkCert_sound _ _ _ _ case1
  · exact checkCert_sound _ _ _ _ case2
  · exact checkCert_sound _ _ _ _ case3
  · exact checkCert_sound _ _ _ _ case4
  · exact checkCert_sound _ _ _ _ case5
  · exact checkCert_sound _ _ _ _ case6
  · exact checkCert_sound _ _ _ _ case7
  · exact checkCert_sound _ _ _ _ case8
  · exact checkCert_sound _ _ _ _ case9
  · exact checkCert_sound _ _ _ _ case10
  · exact checkCert_sound _ _ _ _ case11

/-! ## Main theorem -/

/-- **No nine compatible strings.** On the (22, 5) grid, a list of pairwise compatible
3-change strings has at most 8 members. -/
theorem no_nine_compatible (F : List DStr) (hF : F.Pairwise DCompat) : F.length ≤ 8 := by
  classical
  by_contra hlen
  push Not at hlen
  have hidx : ∀ d : DStr, ∃ i, i < 528 ∧ mI i = d.mask := by
    intro d
    obtain ⟨i, hi, he⟩ := List.getElem_of_mem (mask_mem d)
    refine ⟨i, by rw [len_masks] at hi; exact hi, ?_⟩
    unfold mI; rw [List.getD_eq_getElem _ _ hi]; exact he
  choose idx hidx_lt hidx_eq using hidx
  have : Std.Symm DCompat := ⟨fun d e ⟨j, hj, ht⟩ =>
    ⟨j, hj, fun t htt => Ne.symm (ht t htt)⟩⟩
  have hnodup : (F.map idx).Nodup := by
    rw [List.Nodup, List.pairwise_map]
    refine hF.imp fun {d e} hde h => ?_
    have := (compat_mask_iff d e).2 hde
    rw [← hidx_eq d, ← hidx_eq e, h, not_compat_self] at this
    exact Bool.false_ne_true this
  set I := (F.map idx).toFinset with hI
  have hIcard : I.card = F.length := by
    rw [hI, List.toFinset_card_of_nodup hnodup, List.length_map]
  have hIlt : ∀ i ∈ I, i < 528 := by
    intro i hi
    rw [hI, List.mem_toFinset, List.mem_map] at hi
    obtain ⟨d, _, rfl⟩ := hi
    exact hidx_lt d
  have hIcomp : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → compat (mI i) (mI j) = true := by
    intro i hi j hj hij
    rw [hI, List.mem_toFinset, List.mem_map] at hi hj
    obtain ⟨d, hd, rfl⟩ := hi
    obtain ⟨e, he, rfl⟩ := hj
    have hde : d ≠ e := fun h => hij (h ▸ rfl)
    rw [hidx_eq, hidx_eq]
    exact (compat_mask_iff d e).2 (hF.forall hd he hde)
  have hIne : I.Nonempty := Finset.card_pos.1 (by omega)
  obtain ⟨i0, hi0, hmin⟩ := Finset.exists_min_image I orbI hIne
  have ho : orbI i0 < 12 := orbI_lt (hIlt i0 hi0)
  set r := gridToRep.getD i0 0
  have hg : ∀ i, i < 528 →
      iterRot r i < 528 ∧ mI (iterRot r i) = rot1^[r] (mI i) ∧ orbI (iterRot r i) = orbI i :=
    fun i hi => iterRot_spec r i hi
  have hginj : Set.InjOn (iterRot r) I := by
    intro a ha b hb hab
    apply mI_inj (hIlt a ha) (hIlt b hb)
    apply iter_rot1_inj r (mI_lt (hIlt a ha)) (mI_lt (hIlt b hb))
    rw [← (hg a (hIlt a ha)).2.1, ← (hg b (hIlt b hb)).2.1]
    exact congrArg mI hab
  have hrep : iterRot r i0 = repI (orbI i0) := rep_spec (hIlt i0 hi0)
  have hgcomp : ∀ a ∈ I, ∀ b ∈ I, a ≠ b →
      compat (mI (iterRot r a)) (mI (iterRot r b)) = true := by
    intro a ha b hb hab
    rw [(hg a (hIlt a ha)).2.1, (hg b (hIlt b hb)).2.1,
      compat_iter r (mI_lt (hIlt a ha)) (mI_lt (hIlt b hb))]
    exact hIcomp a ha b hb hab
  set J := (I.image (iterRot r)).erase (iterRot r i0) with hJdef
  have hJcard : J.card = F.length - 1 := by
    rw [hJdef, Finset.card_erase_of_mem (Finset.mem_image_of_mem _ hi0),
      Finset.card_image_of_injOn hginj, hIcard]
  have hJ : ∀ j ∈ J, ∃ i ∈ I, i ≠ i0 ∧ j = iterRot r i := by
    intro j hj
    rw [hJdef, Finset.mem_erase, Finset.mem_image] at hj
    obtain ⟨hne, i, hi, rfl⟩ := hj
    exact ⟨i, hi, fun h => hne (h ▸ rfl), rfl⟩
  have hJlt : ∀ j ∈ J, j < 528 := by
    intro j hj
    obtain ⟨i, hi, -, rfl⟩ := hJ j hj
    exact (hg i (hIlt i hi)).1
  set S := J.image bitOf with hSdef
  have hbitinj : Set.InjOn bitOf J := by
    intro a ha b hb hab
    have := hJlt a ha; have := hJlt b hb
    simp only [bitOf] at hab
    omega
  have hScard : S.card = F.length - 1 := by
    rw [hSdef, Finset.card_image_of_injOn hbitinj, hJcard]
  have hclique : Clique adjTree.get S := by
    intro u hu v hv huv
    rw [hSdef, Finset.mem_image] at hu hv
    obtain ⟨j1, hj1, rfl⟩ := hu
    obtain ⟨j2, hj2, rfl⟩ := hv
    obtain ⟨a, ha, -, rfl⟩ := hJ j1 hj1
    obtain ⟨b, hb, -, rfl⟩ := hJ j2 hj2
    have hab : a ≠ b := by rintro rfl; exact huv rfl
    rw [adj_bit (hg a (hIlt a ha)).1 (hg b (hIlt b hb)).1]
    exact hgcomp a ha b hb hab
  have hsub : ∀ s ∈ S, (caseP (orbI i0)).testBit s = true := by
    intro s hs
    rw [hSdef, Finset.mem_image] at hs
    obtain ⟨j, hj, rfl⟩ := hs
    obtain ⟨a, ha, hai0, rfl⟩ := hJ j hj
    rw [caseP_bit ho (hg a (hIlt a ha)).1, ← hrep]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨hgcomp i0 hi0 a ha (Ne.symm hai0), ?_⟩
    rw [(hg a (hIlt a ha)).2.2]
    exact hmin a ha
  have := cases_noClique ho S hclique hsub
  omega

end Grid
