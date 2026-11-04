import Mathlib.Data.List.Chain
import Mathlib.Data.Fintype.List
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Integer difference constraints (Bellman–Ford potentials)

Lemma DC of `docs/N4-PLAN.md`. Let `V` be a finite vertex set, `E` an edge relation and `c` integer
edge weights. If every closed walk with at most `|V|` edges has total weight `≤ 0`, then there are
integer potentials `x` with `x v + c v w ≤ x w` on every edge `v → w`.

The potential of `v` is the maximum weight of a simple path ending at `v`.
-/

namespace DiffCons

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- weight of a walk given by its list of vertices -/
def wt (c : V → V → ℤ) : List V → ℤ
  | a :: b :: l => c a b + wt c (b :: l)
  | _ => 0

lemma wt_append_cons (c : V → V → ℤ) (w : V) :
    ∀ A B : List V, wt c (A ++ w :: B) = wt c (A ++ [w]) + wt c (w :: B)
  | [], B => by simp [wt]
  | [a], B => by simp [wt]
  | a :: b :: A, B => by
    show c a b + wt c (b :: A ++ w :: B) = c a b + wt c (b :: A ++ [w]) + wt c (w :: B)
    rw [wt_append_cons c w (b :: A) B]
    ring

lemma wt_append_single (c : V → V → ℤ) (v w : V) :
    ∀ L : List V, L.getLast? = some v → wt c (L ++ [w]) = wt c L + c v w
  | [], h => by simp at h
  | [a], h => by
    simp only [List.getLast?_singleton, Option.some.injEq] at h
    subst h
    simp [wt]
  | a :: b :: L, h => by
    show c a b + wt c (b :: L ++ [w]) = c a b + wt c (b :: L) + c v w
    rw [wt_append_single c v w (b :: L) (by simpa using h)]
    ring

variable (E : V → V → Prop) [DecidableRel E]

/-- simple paths ending at `v` -/
def paths (v : V) : Finset { l : List V // l.Nodup } :=
  Finset.univ.filter fun l => l.1.IsChain E ∧ l.1.getLast? = some v

lemma single_mem (v : V) : (⟨[v], List.nodup_singleton v⟩ : { l : List V // l.Nodup }) ∈ paths E v := by
  simp [paths]

/-- the potential: maximum weight of a simple path ending at `v` -/
def pot (c : V → V → ℤ) (v : V) : ℤ :=
  (paths E v).sup' ⟨_, single_mem E v⟩ fun l => wt c l.1

/-- **Lemma DC.** Nonpositive short closed walks give feasible integer potentials. -/
theorem pot_spec (c : V → V → ℤ)
    (hcyc : ∀ l : List V, l.IsChain E → l ≠ [] → l.head? = l.getLast? →
      l.length ≤ Fintype.card V + 1 → wt c l ≤ 0)
    {v w : V} (hE : E v w) : pot E c v + c v w ≤ pot E c w := by
  obtain ⟨l, hl, hmax⟩ := Finset.exists_mem_eq_sup' ⟨_, single_mem E v⟩ fun l => wt c l.1
  unfold pot
  rw [hmax]
  obtain ⟨hchain, hlast⟩ := (Finset.mem_filter.1 hl).2
  have hlen : l.1.length ≤ Fintype.card V := l.2.length_le_card
  by_cases hw : w ∈ l.1
  · obtain ⟨A, B, hAB⟩ := List.append_of_mem hw
    have hAB' : l.1 = (A ++ [w]) ++ B := by rw [hAB]; simp
    -- the prefix ending at `w` is a simple path to `w`
    have hpre_nodup : (A ++ [w]).Nodup := by
      have := l.2; rw [hAB'] at this; exact this.sublist (List.sublist_append_left _ _)
    have hpre_chain : (A ++ [w]).IsChain E := by
      have := hchain; rw [hAB'] at this; exact this.left_of_append
    have hpre_mem : (⟨A ++ [w], hpre_nodup⟩ : { l : List V // l.Nodup }) ∈ paths E w := by
      simp [paths, hpre_chain]
    have le1 : wt c (A ++ [w]) ≤ (paths E w).sup' ⟨_, single_mem E w⟩ fun l => wt c l.1 :=
      Finset.le_sup' (fun l : { l : List V // l.Nodup } => wt c l.1) hpre_mem
    -- the rest, closed up by the edge `v → w`, is a short closed walk
    have hsuf_chain : (w :: B).IsChain E := by
      have := hchain; rw [hAB] at this; exact this.right_of_append
    have hlastB : (w :: B).getLast? = some v := by
      rw [← hlast, hAB, List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _)]
    have hcyc_chain : ((w :: B) ++ [w]).IsChain E := by
      refine hsuf_chain.append (List.isChain_singleton w) fun x hx y hy => ?_
      rw [hlastB] at hx
      simp at hx hy
      rw [← hx, ← hy]
      exact hE
    have hlenB : (w :: B).length ≤ l.1.length := by rw [hAB]; simp
    have hhead : ((w :: B) ++ [w]).head? = ((w :: B) ++ [w]).getLast? := by
      rw [List.getLast?_append_of_ne_nil _ (by simp)]; simp
    have hc := hcyc _ hcyc_chain (by simp) hhead (by simp; simp at hlenB; omega)
    rw [wt_append_single c v w (w :: B) hlastB] at hc
    have hsplit : wt c l.1 = wt c (A ++ [w]) + wt c (w :: B) := by
      rw [hAB]; exact wt_append_cons c w A B
    linarith
  · -- otherwise extend the path by `w`
    have hext_nodup : (l.1 ++ [w]).Nodup := by
      rw [List.nodup_append]
      refine ⟨l.2, List.nodup_singleton w, ?_⟩
      intro a ha b hb
      simp only [List.mem_singleton] at hb
      rintro rfl
      exact hw (hb ▸ ha)
    have hext_chain : (l.1 ++ [w]).IsChain E := by
      refine hchain.append (List.isChain_singleton w) fun x hx y hy => ?_
      rw [hlast] at hx
      simp at hx hy
      rw [← hx, ← hy]
      exact hE
    have hext_mem : (⟨l.1 ++ [w], hext_nodup⟩ : { l : List V // l.Nodup }) ∈ paths E w := by
      simp [paths, hext_chain]
    have := Finset.le_sup' (fun l : { l : List V // l.Nodup } => wt c l.1) hext_mem
    simp only at this
    rw [wt_append_single c v w l.1 hlast] at this
    exact this

/-- Packaged form: feasible integer potentials exist. -/
theorem exists_potential (c : V → V → ℤ)
    (hcyc : ∀ l : List V, l.IsChain E → l ≠ [] → l.head? = l.getLast? →
      l.length ≤ Fintype.card V + 1 → wt c l ≤ 0) :
    ∃ x : V → ℤ, ∀ v w, E v w → x v + c v w ≤ x w :=
  ⟨pot E c, fun _ _ hE => pot_spec E c hcyc hE⟩

end DiffCons
