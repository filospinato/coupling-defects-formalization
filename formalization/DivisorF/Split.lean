import DivisorF.LinearForest
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Sum
import Mathlib.Logic.Equiv.Sum

set_option linter.style.header false

/-!
# Splitting a spanning linear forest along a vertex partition

A vertex predicate `p` cuts a finite graph `G` into the two induced subgraphs
`G[p]` and `G[¬p]`.  Linear forests of the two parts have disjoint vertex
sets, so their disjoint union is again a linear forest, and its edge count is
the sum of the two edge counts.  The resulting superadditivity

```text
λ(G[p]) + λ(G[¬p]) ≤ λ(G)
```

is the graph-theoretic content of Lemma 2.4 of the paper.

The disjoint union is built with mathlib's `SimpleGraph.sum` (`⊕g`) and then
relabelled along `Equiv.sumCompl`, so that acyclicity travels along a genuine
graph isomorphism rather than through a bespoke walk argument.
-/

namespace DivisorF

open SimpleGraph

variable {V W : Type*}

section Sum

variable {A : SimpleGraph V} {B : SimpleGraph W}

/-- A walk of a disjoint sum that starts on the left stays on the left. -/
private theorem sum_walk_left {x y : V ⊕ W} (w : (A ⊕g B).Walk x y) :
    ∀ a : V, x = Sum.inl a → ∃ b : V, y = Sum.inl b ∧ A.Reachable a b := by
  induction w with
  | nil => exact fun a ha ↦ ⟨a, ha, Reachable.refl a⟩
  | @cons u v z hadj _ ih =>
    intro a ha
    subst ha
    cases v with
    | inl b =>
      obtain ⟨c, hc, hbc⟩ := ih b rfl
      exact ⟨c, hc, ((sum_adj_inl.mp hadj).reachable).trans hbc⟩
    | inr b => exact absurd hadj (not_adj_sum_inl_inr a b)

/-- A walk of a disjoint sum that starts on the right stays on the right. -/
private theorem sum_walk_right {x y : V ⊕ W} (w : (A ⊕g B).Walk x y) :
    ∀ a : W, x = Sum.inr a → ∃ b : W, y = Sum.inr b ∧ B.Reachable a b := by
  induction w with
  | nil => exact fun a ha ↦ ⟨a, ha, Reachable.refl a⟩
  | @cons u v z hadj _ ih =>
    intro a ha
    subst ha
    cases v with
    | inl b => exact absurd hadj.symm (not_adj_sum_inl_inr b a)
    | inr b =>
      obtain ⟨c, hc, hbc⟩ := ih b rfl
      exact ⟨c, hc, ((sum_adj_inr.mp hadj).reachable).trans hbc⟩

theorem reachable_left_of_sum {a a' : V}
    (h : (A ⊕g B).Reachable (Sum.inl a) (Sum.inl a')) : A.Reachable a a' := by
  obtain ⟨w⟩ := h
  obtain ⟨b, hb, hab⟩ := sum_walk_left w a rfl
  have : a' = b := Sum.inl_injective hb
  subst this
  exact hab

theorem reachable_right_of_sum {a a' : W}
    (h : (A ⊕g B).Reachable (Sum.inr a) (Sum.inr a')) : B.Reachable a a' := by
  obtain ⟨w⟩ := h
  obtain ⟨b, hb, hab⟩ := sum_walk_right w a rfl
  have : a' = b := Sum.inr_injective hb
  subst this
  exact hab

/-- Deleting a left edge of a disjoint sum deletes it from the left summand. -/
theorem sum_deleteEdges_inl (A : SimpleGraph V) (B : SimpleGraph W) (a a' : V) :
    (A ⊕g B).deleteEdges {s(Sum.inl a, Sum.inl a')}
      = (A.deleteEdges {s(a, a')}) ⊕g B := by
  ext x y
  cases x <;> cases y <;> simp

/-- Deleting a right edge of a disjoint sum deletes it from the right summand. -/
theorem sum_deleteEdges_inr (A : SimpleGraph V) (B : SimpleGraph W) (a a' : W) :
    (A ⊕g B).deleteEdges {s(Sum.inr a, Sum.inr a')}
      = A ⊕g (B.deleteEdges {s(a, a')}) := by
  ext x y
  cases x <;> cases y <;> simp

/-- The disjoint union of two acyclic graphs is acyclic. -/
theorem isAcyclic_sum (hA : A.IsAcyclic) (hB : B.IsAcyclic) : (A ⊕g B).IsAcyclic := by
  rw [isAcyclic_iff_forall_isBridge]
  intro e he
  induction e using Sym2.ind with
  | _ x y =>
    rw [mem_edgeSet] at he
    cases x with
    | inl a =>
      cases y with
      | inl a' =>
        have hadj : A.Adj a a' := sum_adj_inl.mp he
        rw [isBridge_iff, sum_deleteEdges_inl]
        intro hre
        exact (isBridge_iff.mp
          (isAcyclic_iff_forall_isBridge.mp hA (by simpa using hadj)))
          (reachable_left_of_sum hre)
      | inr b => exact absurd he (not_adj_sum_inl_inr a b)
    | inr a =>
      cases y with
      | inl b => exact absurd he.symm (not_adj_sum_inl_inr b a)
      | inr a' =>
        have hadj : B.Adj a a' := sum_adj_inr.mp he
        rw [isBridge_iff, sum_deleteEdges_inr]
        intro hre
        exact (isBridge_iff.mp
          (isAcyclic_iff_forall_isBridge.mp hB (by simpa using hadj)))
          (reachable_right_of_sum hre)

theorem neighborSet_sum_inl (A : SimpleGraph V) (B : SimpleGraph W) (a : V) :
    (A ⊕g B).neighborSet (Sum.inl a) = Sum.inl '' (A.neighborSet a) := by
  ext x
  cases x <;> simp [SimpleGraph.mem_neighborSet]

theorem neighborSet_sum_inr (A : SimpleGraph V) (B : SimpleGraph W) (a : W) :
    (A ⊕g B).neighborSet (Sum.inr a) = Sum.inr '' (B.neighborSet a) := by
  ext x
  cases x <;> simp [SimpleGraph.mem_neighborSet]

theorem selectedDegree_sum_inl (A : SimpleGraph V) (B : SimpleGraph W) (a : V) :
    selectedDegree (A ⊕g B) (Sum.inl a) = selectedDegree A a := by
  unfold selectedDegree
  rw [neighborSet_sum_inl]
  exact Set.ncard_image_of_injective _ Sum.inl_injective

theorem selectedDegree_sum_inr (A : SimpleGraph V) (B : SimpleGraph W) (a : W) :
    selectedDegree (A ⊕g B) (Sum.inr a) = selectedDegree B a := by
  unfold selectedDegree
  rw [neighborSet_sum_inr]
  exact Set.ncard_image_of_injective _ Sum.inr_injective

/-- Edges of a disjoint union are counted exactly once on each side. -/
theorem edgeCard_sum [Finite V] [Finite W] (A : SimpleGraph V) (B : SimpleGraph W) :
    edgeCard (A ⊕g B) = edgeCard A + edgeCard B := by
  unfold edgeCard
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq,
    Nat.card_congr edgeSetSumEquiv]
  exact Nat.card_sum

/-- The disjoint union of linear forests of the two summands is a linear forest
of the disjoint union. -/
theorem isLinearForest_sum {GA : SimpleGraph V} {GB : SimpleGraph W}
    {LA : SimpleGraph V} {LB : SimpleGraph W}
    (hA : IsLinearForest GA LA) (hB : IsLinearForest GB LB) :
    IsLinearForest (GA ⊕g GB) (LA ⊕g LB) := by
  refine ⟨?_, isAcyclic_sum hA.2.1 hB.2.1, ?_⟩
  · intro x y hxy
    cases x with
    | inl a =>
      cases y with
      | inl a' => exact sum_adj_inl.mpr (hA.1 (sum_adj_inl.mp hxy))
      | inr b => exact absurd hxy (not_adj_sum_inl_inr a b)
    | inr a =>
      cases y with
      | inl b => exact absurd hxy.symm (not_adj_sum_inl_inr b a)
      | inr a' => exact sum_adj_inr.mpr (hB.1 (sum_adj_inr.mp hxy))
  · intro x
    cases x with
    | inl a => rw [selectedDegree_sum_inl]; exact hA.2.2 a
    | inr a => rw [selectedDegree_sum_inr]; exact hB.2.2 a

end Sum

section Superadditivity

variable [Fintype V] [DecidableEq V]

/--
`λ` is superadditive along any vertex partition: maximum linear forests of the
two induced parts sit inside a common spanning linear forest of `G`.
-/
theorem linearForestNumber_induce_add_induce_le
    (G : SimpleGraph V) (p : V → Prop) [DecidablePred p] :
    linearForestNumber (G.induce {v | p v}) + linearForestNumber (G.induce {v | ¬ p v})
      ≤ linearForestNumber G := by
  classical
  obtain ⟨LA, hLA, hcardA⟩ := exists_maximumLinearForest (G.induce {v | p v})
  obtain ⟨LB, hLB, hcardB⟩ := exists_maximumLinearForest (G.induce {v | ¬ p v})
  set e : ({v // p v} ⊕ {v // ¬ p v}) ≃ V := Equiv.sumCompl p with he
  set M : SimpleGraph V := relabel e (LA ⊕g LB) with hM
  have hforest : IsLinearForest G M := by
    refine IsLinearForest.of_relabel e (isAcyclic_sum hLA.2.1 hLB.2.1) ?_ ?_
    · intro x
      cases x with
      | inl a => rw [selectedDegree_sum_inl]; exact hLA.2.2 a
      | inr a => rw [selectedDegree_sum_inr]; exact hLB.2.2 a
    · intro x y hxy
      change ((LA ⊕g LB).map e).Adj x y at hxy
      rw [SimpleGraph.map_adj'] at hxy
      obtain ⟨_, u, v, huv, rfl, rfl⟩ := hxy
      cases u with
      | inl a =>
        cases v with
        | inl a' =>
          have h : G.Adj (a : V) (a' : V) := hLA.1 (sum_adj_inl.mp huv)
          simpa [he, Equiv.sumCompl_apply_inl] using h
        | inr b => exact absurd huv (not_adj_sum_inl_inr a b)
      | inr a =>
        cases v with
        | inl b => exact absurd huv.symm (not_adj_sum_inl_inr b a)
        | inr a' =>
          have h : G.Adj (a : V) (a' : V) := hLB.1 (sum_adj_inr.mp huv)
          simpa [he, Equiv.sumCompl_apply_inr] using h
  calc
    linearForestNumber (G.induce {v | p v}) + linearForestNumber (G.induce {v | ¬ p v})
        = edgeCard LA + edgeCard LB := by rw [hcardA, hcardB]
    _ = edgeCard (LA ⊕g LB) := (edgeCard_sum LA LB).symm
    _ = edgeCard M := (edgeCard_relabel e (LA ⊕g LB)).symm
    _ ≤ linearForestNumber G := edgeCard_le_linearForestNumber hforest

end Superadditivity

end DivisorF
