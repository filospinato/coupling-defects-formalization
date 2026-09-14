import DivisorF.ExtremalIncidence
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Extremal post-crossing contraction layer

Concrete geometric preparation for the original Corollary 3.11.  After the
extremal nonbinary crossings are identified exactly, remove those crossing
edges from the fixed maximum linear forest.  The connected components of the
remaining forest are the path pieces that the paper contracts.

This module keeps the contraction faithful to one fixed maximum forest and
proves the first two structural facts needed downstream: deleting the counted
crossings preserves acyclicity, and every saturated boundary vertex becomes an
isolated component after the cut.
-/

namespace DivisorF

open SimpleGraph

/--
The selected maximum forest after deleting every crossing of the extremal
nonbinary cumulative fibres.
-/
noncomputable def extremalCutGraph
    (N K : ℕ) (L : SimpleGraph (HVertex N)) : SimpleGraph (HVertex N) :=
  L.deleteEdges (↑(nonbinaryCrossingUnion N K L) : Set (Sym2 (HVertex N)))

/-- The cut graph is a subgraph of the selected maximum forest. -/
theorem extremalCutGraph_le
    {N K : ℕ} {L : SimpleGraph (HVertex N)} :
    extremalCutGraph N K L ≤ L := by
  exact SimpleGraph.deleteEdges_le _

/-- Deleting the counted crossings preserves acyclicity. -/
theorem extremalCutGraph_isAcyclic
    {N K : ℕ} {L : SimpleGraph (HVertex N)}
    (hL : IsLinearForest (reducedDivisorGraph N) L) :
    (extremalCutGraph N K L).IsAcyclic := by
  intro v c hc
  have hcL : (c.map (SimpleGraph.Hom.ofLE extremalCutGraph_le)).IsCycle := by
    simpa using hc
  exact hL.2.1 (c.map (SimpleGraph.Hom.ofLE extremalCutGraph_le)) hcL

/-- The post-cut restriction component containing a vertex. -/
noncomputable def extremalRestrictionComponent
    {N K : ℕ} (L : SimpleGraph (HVertex N)) (v : HVertex N) :
    (extremalCutGraph N K L).ConnectedComponent :=
  (extremalCutGraph N K L).connectedComponentMk v

/-- Equality of post-cut components is exactly reachability in the cut forest. -/
theorem extremalRestrictionComponent_eq_iff_reachable
    {N K : ℕ} {L : SimpleGraph (HVertex N)} {v w : HVertex N} :
    extremalRestrictionComponent (K := K) L v =
        extremalRestrictionComponent (K := K) L w ↔
      (extremalCutGraph N K L).Reachable v w := by
  exact SimpleGraph.ConnectedComponent.eq

/-- Every deleted nonbinary crossing is absent from the post-cut graph. -/
theorem not_adj_extremalCutGraph_of_crossing
    {N K : ℕ} {L : SimpleGraph (HVertex N)} {v w : HVertex N}
    (he : s(v, w) ∈ nonbinaryCrossingUnion N K L) :
    ¬(extremalCutGraph N K L).Adj v w := by
  simp [extremalCutGraph, he]

/--
**Corollary 3.11 geometric input:** at extremality every common-boundary
vertex is isolated after the counted nonbinary crossings are removed.

This is the formal counterpart of the manuscript statement that the `K-1`
boundary vertices are singleton complement components of incidence degree two
before contraction.
-/
theorem boundary_isolated_in_extremalCutGraph
    {N K : ℕ} {L : SimpleGraph (HVertex N)}
    (hKN : K ≤ N)
    (hL : IsLinearForest (reducedDivisorGraph N) L)
    (hmax : edgeCard L = linearForestNumber (reducedDivisorGraph N))
    (hsat : cumulativeNonbinaryCount N K = K - 1)
    {c : HVertex N} (hc : c ∈ smallEndpointVertices N K) :
    (extremalCutGraph N K L).IsIsolated c := by
  intro v hadjCut
  have hadjL : L.Adj c v :=
    (SimpleGraph.deleteEdges_adj.mp hadjCut).1
  have heInc : s(c, v) ∈ incidentEdgesOn L (smallEndpointVertices N K) := by
    rw [incidentEdgesOn, Finset.mem_biUnion]
    refine ⟨c, hc, ?_⟩
    rw [SimpleGraph.mem_incidenceFinset]
    refine ⟨?_, ?_⟩
    · rw [SimpleGraph.mem_edgeSet]
      exact hadjL
    · simp
  have heCross : s(c, v) ∈ nonbinaryCrossingUnion N K L := by
    rw [← incidentEdges_eq_nonbinaryCrossingUnion_of_extremal
      hKN hL hmax hsat]
    exact heInc
  exact (SimpleGraph.deleteEdges_adj.mp hadjCut).2 heCross

/--
Distinct vertices cannot share the post-cut component of an extremal boundary
vertex.  Thus those boundary components are genuinely singletons, not merely
vertices of degree zero in the retained graph.
-/
theorem extremalRestrictionComponent_boundary_eq_iff
    {N K : ℕ} {L : SimpleGraph (HVertex N)}
    (hKN : K ≤ N)
    (hL : IsLinearForest (reducedDivisorGraph N) L)
    (hmax : edgeCard L = linearForestNumber (reducedDivisorGraph N))
    (hsat : cumulativeNonbinaryCount N K = K - 1)
    {c : HVertex N} (hc : c ∈ smallEndpointVertices N K)
    {v : HVertex N} :
    extremalRestrictionComponent (K := K) L c =
        extremalRestrictionComponent (K := K) L v ↔ c = v := by
  rw [extremalRestrictionComponent_eq_iff_reachable]
  constructor
  · intro hreach
    by_contra hne
    have hiso := boundary_isolated_in_extremalCutGraph
      hKN hL hmax hsat hc
    exact (SimpleGraph.not_reachable_of_neighborSet_left_eq_empty hne
      hiso.neighborSet_eq_empty) hreach
  · intro h
    subst v
    exact (SimpleGraph.Reachable.refl c :
      (extremalCutGraph N K L).Reachable c c)

end DivisorF
