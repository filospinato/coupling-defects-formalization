import DivisorF.LinearForestPath
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Path partitions and Lemma 2.2

The manuscript's subject is `P(X)`, the least number of paths in a
vertex-disjoint path partition of `V(X)`, and hence `F(N) = P(G_N)`. The
`DivisorF` development works throughout with `lambda(X)` (`linearForestNumber`)
and *defines* the coupling defect by the `lambda` identity (2.6) rather than by
the manuscript's own definition (2.5). Lemma 2.2,

`P(X) = |V(X)| - lambda(X)`,

is the bridge between the two, and until it is machine-checked every downstream
theorem is a theorem about maximum spanning linear forests whose reading as a
theorem about path partitions rests on an unformalized translation.

This module defines path partitions as the manuscript does — a family of
pairwise disjoint vertex sets covering `V(X)`, each traced by an actual path of
`X` — and proves Lemma 2.2 in the equivalent subtraction-free form

`pathPartitionNumber X + linearForestNumber X = Fintype.card V`.

Nothing here is a project-original result; it is the bridge lemma that makes the
project-original results be about the manuscript's object.
-/

namespace DivisorF

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A finset of vertices is a **path block** of `X` when some path of `X`
visits exactly those vertices. -/
def IsPathBlock (X : SimpleGraph V) (s : Finset V) : Prop :=
  ∃ (u v : V) (p : X.Walk u v), p.IsPath ∧ p.support.toFinset = s

/-- The manuscript's **vertex-disjoint path partition** of `V(X)`. -/
structure IsPathPartition (X : SimpleGraph V) (P : Finset (Finset V)) : Prop where
  /-- every part is traced by an actual path of `X` -/
  isBlock : ∀ s ∈ P, IsPathBlock X s
  /-- the parts are pairwise disjoint -/
  pairwise : ∀ s ∈ P, ∀ t ∈ P, s ≠ t → Disjoint s t
  /-- the parts cover every vertex -/
  covers : P.biUnion id = Finset.univ

/-- `P(X)`: the least number of paths in a vertex-disjoint path partition. -/
noncomputable def pathPartitionNumber (X : SimpleGraph V) : ℕ :=
  sInf {c | ∃ P : Finset (Finset V), IsPathPartition X P ∧ P.card = c}

omit [Fintype V] [DecidableEq V] in
/-- The finite forest Euler identity in instance-free form, so that it can be
combined with counts formed under any `Fintype` instance on the components. -/
theorem card_connectedComponent_add_edgeCard_eq_natCard [Finite V]
    (G : SimpleGraph V) (hacyc : G.IsAcyclic) :
    Nat.card G.ConnectedComponent + edgeCard G = Nat.card V := by
  letI := Fintype.ofFinite V
  have h := card_connectedComponent_add_edgeCard_eq_fintypeCard G hacyc
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact h

section Component

variable {X L : SimpleGraph V} [DecidableRel L.Adj]

local instance connectedComponentSetLikeDecidablePred'
    (C : L.ConnectedComponent) : DecidablePred (fun v => v ∈ C) :=
  fun v => SimpleGraph.instDecidableMemSupp L C v

local instance connectedComponentToSimpleGraphDecidableRel'
    (C : L.ConnectedComponent) : DecidableRel C.toSimpleGraph.Adj :=
  fun a b => ‹DecidableRel L.Adj› a.1 b.1

/-- Inside a linear forest every component degree is at most two. -/
theorem component_degree_le_two
    (hL : IsLinearForest X L) (C : L.ConnectedComponent) (x : C) :
    C.toSimpleGraph.degree x ≤ 2 := by
  have hdeg := connectedComponent_toSimpleGraph_degree_eq L C x
  have hsel : selectedDegree L x.1 ≤ 2 := hL.2.2 x.1
  have hcard : selectedDegree L x.1 = L.degree x.1 := by
    unfold selectedDegree
    rw [Set.ncard_eq_toFinset_card', ← SimpleGraph.card_neighborFinset_eq_degree]
    congr 1
  rw [hdeg, ← hcard]
  exact hsel

/-- **Each component of a linear forest is a path block of the ambient graph.**
This is the folklore half of Lemma 2.2 that the degree condition hides. -/
theorem isPathBlock_component_supp
    (hL : IsLinearForest X L) (C : L.ConnectedComponent) :
    IsPathBlock X (C.supp.toFinset) := by
  classical
  have hconn : C.toSimpleGraph.Connected :=
    SimpleGraph.ConnectedComponent.connected_toSimpleGraph C
  obtain ⟨a, b, p, hham⟩ :=
    exists_isHamiltonian_of_connected_degree_le_two C.toSimpleGraph hconn
      (component_degree_le_two hL C)
  -- transport the component path directly into `X`
  set g : C.toSimpleGraph →g X :=
    (SimpleGraph.Hom.ofLE hL.1).comp
      (SimpleGraph.ConnectedComponent.toSimpleGraph_hom C) with hgdef
  have hginj : Function.Injective g := fun x y hxy => Subtype.ext hxy
  refine ⟨_, _, p.map g, (hham.isPath).map hginj, ?_⟩
  ext w
  rw [List.mem_toFinset, SimpleGraph.Walk.support_map, List.mem_map,
    Set.mem_toFinset]
  constructor
  · rintro ⟨z, -, rfl⟩
    exact z.2
  · intro hw
    exact ⟨⟨w, hw⟩, hham.mem_support _, rfl⟩

/-- The component supports of a linear forest form a path partition. -/
theorem isPathPartition_componentSupports
    (hL : IsLinearForest X L) :
    IsPathPartition X
      (Finset.image (fun C : L.ConnectedComponent => C.supp.toFinset)
        Finset.univ) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro s hs
    obtain ⟨C, -, rfl⟩ := Finset.mem_image.mp hs
    exact isPathBlock_component_supp hL C
  · intro s hs t ht hst
    obtain ⟨C, -, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨D, -, rfl⟩ := Finset.mem_image.mp ht
    have hCD : C ≠ D := by
      intro h
      exact hst (by rw [h])
    rw [Finset.disjoint_left]
    intro w hw hw'
    rw [Set.mem_toFinset] at hw hw'
    exact hCD (by
      rw [← SimpleGraph.ConnectedComponent.mem_supp_iff C w |>.mp hw,
        ← SimpleGraph.ConnectedComponent.mem_supp_iff D w |>.mp hw'])
  · ext w
    simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_univ,
      true_and, id_eq, iff_true]
    exact ⟨(L.connectedComponentMk w).supp.toFinset,
      ⟨L.connectedComponentMk w, rfl⟩, by
        rw [Set.mem_toFinset]
        exact SimpleGraph.ConnectedComponent.connectedComponentMk_mem⟩

end Component

/-- **Lemma 2.2, forest-to-partition half.**

Every maximum spanning linear forest yields a genuine vertex-disjoint path
partition with `|V| - lambda(X)` parts, so `P(X) + lambda(X) <= |V(X)|`. -/
theorem pathPartitionNumber_add_linearForestNumber_le (X : SimpleGraph V) :
    pathPartitionNumber X + linearForestNumber X ≤ Fintype.card V := by
  classical
  obtain ⟨L, hL, hmax⟩ := exists_maximumLinearForest X
  have hinj : Function.Injective
      (fun C : L.ConnectedComponent => C.supp.toFinset) := by
    intro C D h
    apply SimpleGraph.ConnectedComponent.supp_injective
    ext w
    have hw := congrArg (fun s : Finset V => w ∈ s) h
    simpa [Set.mem_toFinset] using hw
  have hcard :
      (Finset.image (fun C : L.ConnectedComponent => C.supp.toFinset)
        Finset.univ).card = Nat.card L.ConnectedComponent := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ,
      ← Nat.card_eq_fintype_card]
  have hle : pathPartitionNumber X ≤ Nat.card L.ConnectedComponent := by
    rw [← hcard]
    exact Nat.sInf_le ⟨_, isPathPartition_componentSupports hL, rfl⟩
  have heuler := card_connectedComponent_add_edgeCard_eq_natCard L hL.2.1
  have hV : Nat.card V = Fintype.card V := Nat.card_eq_fintype_card
  omega

end DivisorF
