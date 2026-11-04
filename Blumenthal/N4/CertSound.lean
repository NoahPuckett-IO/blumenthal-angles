import Mathlib.Data.Finset.Card
import Blumenthal.N4.Cert

/-!
Soundness of the certificate checker: if `checkCert adj c P k = true`, then the set of vertices
`P` (as bits) contains no clique of size `k` of the directed relation `u → v ⟺ bit v of adj u`.
Only the direction `u → v` for `u ≠ v` in the clique is used, so no symmetry is needed.
-/

namespace CertSound

/-- a clique: every ordered pair of distinct members is adjacent -/
def Clique (adj : ℕ → ℕ) (S : Finset ℕ) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, u ≠ v → (adj u).testBit v = true

/-- no clique of size `k` inside the vertex set `P` -/
def NoClique (adj : ℕ → ℕ) (P k : ℕ) : Prop :=
  ∀ S : Finset ℕ, Clique adj S → (∀ s ∈ S, P.testBit s = true) → S.card < k

lemma isBit_eq (Q v : ℕ) : isBit Q v = Q.testBit v := by
  unfold isBit
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.shiftRight_eq_div_pow]
  by_cases h : Q / 2 ^ v % 2 = 1 <;> simp [h]

lemma testBit_maskOf (c : List ℕ) (v : ℕ) : (maskOf c).testBit v = true ↔ v ∈ c := by
  induction c with
  | nil => simp [maskOf]
  | cons w ws ih =>
    simp only [maskOf, Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true, decide_eq_true_eq,
      ih, List.mem_cons]
    constructor
    · rintro (h | h)
      · exact Or.inl h.symm
      · exact Or.inr h
    · rintro (h | h)
      · exact Or.inl h.symm
      · exact Or.inr h

lemma and_eq_zero_testBit {a b v : ℕ} (h : a &&& b = 0) (ha : a.testBit v = true) :
    b.testBit v = false := by
  have := congrArg (fun x => x.testBit v) h
  simp only [Nat.testBit_and, Nat.zero_testBit, ha, Bool.true_and] at this
  exact this

lemma indepL_spec {adj : ℕ → ℕ} {m : ℕ} {c : List ℕ} (h : indepL adj m c = true) :
    ∀ v ∈ c, adj v &&& m = 0 := by
  induction c with
  | nil => simp
  | cons w ws ih =>
    simp only [indepL, Bool.and_eq_true, beq_iff_eq] at h
    intro v hv
    rcases List.mem_cons.1 hv with rfl | hv
    · exact h.1
    · exact ih h.2 v hv

/-- what a successful `unionL` guarantees -/
lemma unionL_spec {adj : ℕ → ℕ} {cls : List (List ℕ)} {U : ℕ} (h : unionL adj cls = some U) :
    (∀ c ∈ cls, ∀ v ∈ c, adj v &&& maskOf c = 0) ∧
      (∀ v, U.testBit v = true ↔ ∃ c ∈ cls, v ∈ c) := by
  induction cls generalizing U with
  | nil =>
    simp only [unionL, Option.some.injEq] at h
    subst h
    simp
  | cons c cs ih =>
    simp only [unionL] at h
    split at h
    · rename_i hind
      obtain ⟨U', hU', rfl⟩ := Option.map_eq_some_iff.1 h
      obtain ⟨h1, h2⟩ := ih hU'
      refine ⟨?_, ?_⟩
      · intro c' hc' v hv
        rcases List.mem_cons.1 hc' with rfl | hc'
        · exact indepL_spec hind v hv
        · exact h1 c' hc' v hv
      · intro v
        simp only [Nat.testBit_or, Bool.or_eq_true, testBit_maskOf, h2, List.mem_cons,
          exists_eq_or_imp]
    · simp at h

/-- pigeonhole: a clique covered by independent classes has at most one vertex per class -/
lemma card_le_of_cover {adj : ℕ → ℕ} {cls : List (List ℕ)}
    (hind : ∀ c ∈ cls, ∀ v ∈ c, adj v &&& maskOf c = 0)
    {S : Finset ℕ} (hS : Clique adj S) (hcov : ∀ s ∈ S, ∃ c ∈ cls, s ∈ c) :
    S.card ≤ cls.length := by
  classical
  let f : ℕ → ℕ := fun s => cls.findIdx (fun c => decide (s ∈ c))
  have hf : ∀ s ∈ S, f s < cls.length := by
    intro s hs
    obtain ⟨c, hc, hsc⟩ := hcov s hs
    exact List.findIdx_lt_length_of_exists ⟨c, hc, by simpa using hsc⟩
  have hmem : ∀ s (hs : s ∈ S), s ∈ cls[f s]'(hf s hs) := by
    intro s hs
    have := List.findIdx_getElem (p := fun c => decide (s ∈ c)) (w := hf s hs)
    simpa using this
  have hinj : Set.InjOn f S := by
    intro s hs t ht hst
    by_contra hne
    have hs' := hmem s hs
    have ht' : t ∈ cls[f s]'(hf s hs) := by
      have := hmem t ht
      simp only [hst] at this ⊢
      exact this
    have hadj := hS s hs t ht hne
    have h0 := hind _ (List.getElem_mem _) s hs'
    have := and_eq_zero_testBit h0 hadj
    rw [(testBit_maskOf _ t).2 ht'] at this
    exact Bool.noConfusion this
  calc S.card ≤ (Finset.range cls.length).card :=
        Finset.card_le_card_of_injOn f (fun s hs => by simpa using hf s hs) hinj
    _ = cls.length := Finset.card_range _

lemma testBit_xor_two_pow (a v s : ℕ) (hs : s ≠ v) : (a ^^^ 2 ^ v).testBit s = a.testBit s := by
  rw [Nat.testBit_xor, Nat.testBit_two_pow]
  simp [Ne.symm hs]

/-- the branch loop: a large clique meeting `B` is ruled out by the children -/
lemma children_sound {adj : ℕ → ℕ} {k : ℕ} :
    ∀ (B : List ℕ) (P : ℕ) (ch : List (ℕ × ℕ)), children adj k P B = some ch →
      (∀ p ∈ ch, NoClique adj p.1 p.2) →
      ∀ S : Finset ℕ, Clique adj S → (∀ s ∈ S, P.testBit s = true) → (∃ s ∈ S, s ∈ B) →
        S.card < k := by
  intro B
  induction B with
  | nil => intro P ch _ _ S _ _ hB; obtain ⟨s, _, hs⟩ := hB; simp at hs
  | cons v vs ih =>
    intro P ch hch hkids S hS hSP hB
    simp only [children] at hch
    split at hch
    · rename_i hPv
      obtain ⟨ch', hch', rfl⟩ := Option.map_eq_some_iff.1 hch
      by_cases hvS : v ∈ S
      · -- the child (P ∩ N(v), k - 1) rules out S \ {v}
        have hchild := hkids _ List.mem_cons_self
        have hS' : Clique adj (S.erase v) := fun u hu w hw huw =>
          hS u (Finset.mem_of_mem_erase hu) w (Finset.mem_of_mem_erase hw) huw
        have hsub : ∀ s ∈ S.erase v, (P &&& adj v).testBit s = true := by
          intro s hs
          have hsv := Finset.ne_of_mem_erase hs
          rw [Nat.testBit_and, hSP s (Finset.mem_of_mem_erase hs),
            hS v hvS s (Finset.mem_of_mem_erase hs) (Ne.symm hsv)]
          rfl
        have := hchild (S.erase v) hS' hsub
        rw [Finset.card_erase_of_mem hvS] at this
        have hpos : 0 < S.card := Finset.card_pos.2 ⟨v, hvS⟩
        simp only at this
        omega
      · have hsub : ∀ s ∈ S, (P ^^^ 2 ^ v).testBit s = true := by
          intro s hs
          have hsv : s ≠ v := fun h => hvS (h ▸ hs)
          rw [testBit_xor_two_pow _ _ _ hsv]
          exact hSP s hs
        obtain ⟨s, hs, hsB⟩ := hB
        have hsv : s ≠ v := fun h => hvS (h ▸ hs)
        exact ih _ ch' hch' (fun p hp => hkids p (List.mem_cons_of_mem _ hp)) S hS hsub
          ⟨s, hs, (List.mem_cons.1 hsB).resolve_left hsv⟩
    · simp at hch

/-- one node of the certificate -/
lemma step_sound {adj : ℕ → ℕ} {P k : ℕ} {cls : List (List ℕ)} {ch : List (ℕ × ℕ)}
    (h : step adj P k cls = some ch) (hkids : ∀ p ∈ ch, NoClique adj p.1 p.2) :
    NoClique adj P k := by
  intro S hS hSP
  unfold step at h
  split at h
  · simp at h
  · rename_i hk
    have hk0 : k ≠ 0 := by simpa using hk
    split at h
    · simp at h
    · rename_i U hU
      obtain ⟨hind, hcov⟩ := unionL_spec hU
      split at h
      · simp at h
      · rename_i hUP
        have hUP' : U = P := by simpa using hUP
        subst hUP'
        have hcovS : ∀ s ∈ S, ∃ c ∈ cls, s ∈ c := fun s hs => (hcov s).1 (hSP s hs)
        split at h
        · rename_i hlen
          exact lt_of_le_of_lt (card_le_of_cover hind hS hcovS) hlen
        · -- either S meets the branch set, or it is covered by the first k-1 classes
          by_cases hB : ∃ s ∈ S, s ∈ (cls.drop (k - 1)).flatten
          · exact children_sound _ _ _ h hkids S hS hSP hB
          · push Not at hB
            have hcov' : ∀ s ∈ S, ∃ c ∈ cls.take (k - 1), s ∈ c := by
              intro s hs
              obtain ⟨c, hc, hsc⟩ := hcovS s hs
              rw [← List.take_append_drop (k - 1) cls, List.mem_append] at hc
              rcases hc with hc | hc
              · exact ⟨c, hc, hsc⟩
              · exact absurd (List.mem_flatten.2 ⟨c, hc, hsc⟩) (hB s hs)
            have hind' : ∀ c ∈ cls.take (k - 1), ∀ v ∈ c, adj v &&& maskOf c = 0 :=
              fun c hc => hind c (List.mem_of_mem_take hc)
            have := card_le_of_cover hind' hS hcov'
            have hlen : (cls.take (k - 1)).length ≤ k - 1 := List.length_take_le _ _
            omega

mutual
theorem checkCert_sound (adj : ℕ → ℕ) :
    ∀ (c : Cert) (P k : ℕ), checkCert adj c P k = true → NoClique adj P k
  | .node cls kids, P, k, h => by
    simp only [checkCert] at h
    split at h
    · simp at h
    · rename_i ch hch
      exact step_sound hch (checkKids_sound adj kids ch h)
theorem checkKids_sound (adj : ℕ → ℕ) :
    ∀ (kids : List Cert) (ch : List (ℕ × ℕ)), checkKids adj kids ch = true →
      ∀ p ∈ ch, NoClique adj p.1 p.2
  | [], [], _ => by simp
  | c :: cs, (P, k) :: ps, h => by
    simp only [checkKids, Bool.and_eq_true] at h
    intro p hp
    rcases List.mem_cons.1 hp with rfl | hp
    · exact checkCert_sound adj c P k h.1
    · exact checkKids_sound adj cs ps h.2 p hp
  | [], _ :: _, h => by simp [checkKids] at h
  | _ :: _, [], h => by simp [checkKids] at h
end

end CertSound
