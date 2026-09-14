import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Maps

set_option linter.style.header false

/-!
# Spanning linear forests

The predicate `IsLinearForest G L` says that `L` is a spanning subgraph of
`G`, is acyclic, and has degree at most two at every vertex.  Since `L` and
`G` share their vertex type, spanning is built into the representation.
-/

namespace DivisorF

open SimpleGraph

variable {V : Type*}

/-- Number of selected edges in a finite simple graph. -/
noncomputable def edgeCard (L : SimpleGraph V) : ℕ :=
  L.edgeSet.ncard

/-- Number of selected edges incident to `v`. -/
noncomputable def selectedDegree (L : SimpleGraph V) (v : V) : ℕ :=
  (L.neighborSet v).ncard

/-- A spanning linear forest `L` of `G`. -/
def IsLinearForest (G L : SimpleGraph V) : Prop :=
  L ≤ G ∧ L.IsAcyclic ∧ ∀ v, selectedDegree L v ≤ 2

/-- Maximum number of edges in a spanning linear forest of a finite graph. -/
noncomputable def linearForestNumber [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : ℕ := by
  classical
  exact Finset.univ.sup fun L : SimpleGraph V ↦
    if IsLinearForest G L then edgeCard L else 0

theorem edgeCard_le_linearForestNumber [Fintype V] [DecidableEq V]
    {G L : SimpleGraph V}
    (hL : IsLinearForest G L) :
    edgeCard L ≤ linearForestNumber G := by
  classical
  unfold linearForestNumber
  simpa [hL] using
    (Finset.le_sup (s := Finset.univ)
      (f := fun K : SimpleGraph V ↦
        if IsLinearForest G K then edgeCard K else 0)
      (Finset.mem_univ L))

theorem bot_isLinearForest (G : SimpleGraph V) :
    IsLinearForest G (⊥ : SimpleGraph V) := by
  refine ⟨bot_le, SimpleGraph.isAcyclic_bot, ?_⟩
  intro v
  simp [selectedDegree]

@[simp]
theorem edgeCard_bot : edgeCard (⊥ : SimpleGraph V) = 0 := by
  simp [edgeCard]

/--
The maximum in `linearForestNumber` is attained: some spanning linear forest
really has that many edges.  Every counting argument about a *fixed* optimal
forest starts here.
-/
theorem exists_maximumLinearForest [Fintype V] [DecidableEq V] (G : SimpleGraph V) :
    ∃ L, IsLinearForest G L ∧ edgeCard L = linearForestNumber G := by
  classical
  obtain ⟨L, -, hL⟩ :=
    Finset.exists_mem_eq_sup (Finset.univ : Finset (SimpleGraph V))
      ⟨⊥, Finset.mem_univ _⟩
      (fun K : SimpleGraph V ↦ if IsLinearForest G K then edgeCard K else 0)
  by_cases h : IsLinearForest G L
  · refine ⟨L, h, ?_⟩
    unfold linearForestNumber
    rw [hL, if_pos h]
  · refine ⟨⊥, bot_isLinearForest G, ?_⟩
    have hzero : linearForestNumber G = 0 := by
      unfold linearForestNumber
      rw [hL, if_neg h]
    rw [hzero, edgeCard_bot]

section Relabel

variable {W : Type*}

/-- Relabel a graph along an equivalence of its vertex type. -/
def relabel (e : V ≃ W) (L : SimpleGraph V) : SimpleGraph W :=
  L.map e

theorem edgeCard_relabel (e : V ≃ W) (L : SimpleGraph V) :
    edgeCard (relabel e L) = edgeCard L := by
  unfold edgeCard relabel
  exact (Set.ncard_congr' (SimpleGraph.Iso.map e L).mapEdgeSet).symm

theorem selectedDegree_relabel (e : V ≃ W) (L : SimpleGraph V) (v : V) :
    selectedDegree (relabel e L) (e v) = selectedDegree L v := by
  unfold selectedDegree relabel
  exact (Set.ncard_congr' ((SimpleGraph.Iso.map e L).mapNeighborSet v)).symm

theorem IsLinearForest.relabel {G L : SimpleGraph V} {G' : SimpleGraph W}
    (f : G ≃g G') (hL : IsLinearForest G L) :
    IsLinearForest G' (DivisorF.relabel f.toEquiv L) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b hab
    change (L.map f.toEquiv).Adj a b at hab
    rw [SimpleGraph.map_adj'] at hab
    obtain ⟨_, u, v, huv, rfl, rfl⟩ := hab
    exact f.map_adj_iff.mpr (hL.1 huv)
  · exact (SimpleGraph.Iso.map f.toEquiv L).isAcyclic_iff.mp hL.2.1
  · intro w
    calc
      selectedDegree (DivisorF.relabel f.toEquiv L) w =
          selectedDegree L (f.symm w) := by
        simpa using selectedDegree_relabel f.toEquiv L (f.symm w)
      _ ≤ 2 := hL.2.2 (f.symm w)

/--
Relabelling a linear forest along an equivalence of vertex types preserves
acyclicity and the degree bound; the ambient graph only has to contain the
relabelled edges.  Unlike `IsLinearForest.relabel`, the two ambient graphs need
not be isomorphic, which is what the fibre/complement split requires.
-/
theorem IsLinearForest.of_relabel {L : SimpleGraph V} {G' : SimpleGraph W} (e : V ≃ W)
    (hacyc : L.IsAcyclic) (hdeg : ∀ v, selectedDegree L v ≤ 2)
    (hle : DivisorF.relabel e L ≤ G') :
    IsLinearForest G' (DivisorF.relabel e L) := by
  refine ⟨hle, (SimpleGraph.Iso.map e L).isAcyclic_iff.mp hacyc, ?_⟩
  intro w
  calc
    selectedDegree (DivisorF.relabel e L) w = selectedDegree L (e.symm w) := by
      simpa using selectedDegree_relabel e L (e.symm w)
    _ ≤ 2 := hdeg _

theorem linearForestNumber_le_of_iso [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] {G : SimpleGraph V} {G' : SimpleGraph W}
    (f : G ≃g G') : linearForestNumber G ≤ linearForestNumber G' := by
  classical
  unfold linearForestNumber
  apply Finset.sup_le
  intro L _
  by_cases hL : IsLinearForest G L
  · simp only [if_pos hL]
    calc
      edgeCard L = edgeCard (relabel f.toEquiv L) :=
        (edgeCard_relabel f.toEquiv L).symm
      _ ≤ Finset.univ.sup (fun K : SimpleGraph W ↦
          if IsLinearForest G' K then edgeCard K else 0) := by
        simpa [hL.relabel f] using
          (Finset.le_sup (s := Finset.univ)
            (f := fun K : SimpleGraph W ↦
              if IsLinearForest G' K then edgeCard K else 0)
            (Finset.mem_univ (relabel f.toEquiv L)))
  · simp [hL]

/-- Isomorphic finite graphs have the same maximum linear-forest size. -/
theorem linearForestNumber_iso {G : SimpleGraph V} {G' : SimpleGraph W}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (f : G ≃g G') : linearForestNumber G = linearForestNumber G' := by
  apply Nat.le_antisymm
  · exact linearForestNumber_le_of_iso f
  · exact linearForestNumber_le_of_iso f.symm

end Relabel

end DivisorF
