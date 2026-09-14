import DivisorF.ExtremalContractedLeafCount
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Path-lifting geometry for the extremal contracted incidence graph

This module prepares the remaining acyclicity proof in the original
Corollary 3.11.  A contracted left-right incidence is represented by a unique
selected crossing.  When two contracted incidences meet at the same active
right component, their fibre endpoints are connected inside the post-cut
forest.  Consequently the length-two contracted segment

`boundary -- active component -- boundary`

lifts to an actual reachable segment in the original maximum linear forest,
using the two selected crossings and the surviving path inside the component.
This is the local path-lifting mechanism needed to turn a hypothetical
contracted cycle into a cycle of the original acyclic forest.
-/

namespace DivisorF

open SimpleGraph

/-- The canonical endpoints of a selected crossing are adjacent in the original forest. -/
theorem crossingOutsideEndpoint_adj_crossingFibreEndpoint
    {N K : ℕ} {q : LargePrime N} {L : SimpleGraph (HVertex N)}
    (e : FibreCrossingEdge (_K := K) q L) :
    L.Adj (crossingOutsideEndpoint (K := K) e)
      (crossingFibreEndpoint (K := K) e) := by
  rw [← SimpleGraph.mem_edgeSet,
    ← crossing_eq_outside_fibre_endpoints (K := K) e]
  exact (mem_crossingFinset.mp e.2).1

/-- The active component chosen by a crossing is the cut component of its fibre endpoint. -/
theorem crossingActiveFibreRestrictionComponent_val
    {N K : ℕ} {q : LargePrime N} {L : SimpleGraph (HVertex N)}
    (e : FibreCrossingEdge (_K := K) q L) :
    (crossingActiveFibreRestrictionComponent (K := K) e).1 =
      extremalRestrictionComponent (K := K) L
        (crossingFibreEndpoint (K := K) e) := rfl

/--
Two crossings of the same fibre that land in the same active right component
have fibre endpoints reachable in the post-cut forest.
-/
theorem crossingFibreEndpoints_reachable_cut_of_same_activeComponent
    {N K : ℕ} {q : LargePrime N} {L : SimpleGraph (HVertex N)}
    (e f : FibreCrossingEdge (_K := K) q L)
    (hcomp :
      crossingActiveFibreRestrictionComponent (K := K) e =
        crossingActiveFibreRestrictionComponent (K := K) f) :
    (extremalCutGraph N K L).Reachable
      (crossingFibreEndpoint (K := K) e)
      (crossingFibreEndpoint (K := K) f) := by
  apply extremalRestrictionComponent_eq_iff_reachable.mp
  exact congrArg Subtype.val hcomp

/--
A concrete left-right contracted adjacency exposes a crossing witness whose
canonical boundary endpoint is exactly the left node.
-/
theorem exists_crossing_witness_of_contracted_adj
    {N K : ℕ} {L : SimpleGraph (HVertex N)}
    (hKsq : K * K ≤ N)
    (hLsub : L ≤ reducedDivisorGraph N)
    (c : ExtremalBoundaryNode N K) (R : ExtremalRightNode N K L)
    (hAdj : (extremalContractedIncidenceGraph N K L).Adj
      (Sum.inl c) (Sum.inr R)) :
    ∃ e : FibreCrossingEdge (_K := K) R.1.1 L,
      c = crossingBoundaryNode (K := K) hLsub
        (mem_cumulativeLevelFibres.mp R.1.2).1 e ∧
      crossingActiveFibreRestrictionComponent (K := K) e = R.2 := by
  rw [extremalContractedIncidenceGraph_adj_left_right] at hAdj
  rcases hAdj with ⟨e, hce, heR⟩
  refine ⟨e, ?_, heR⟩
  exact boundaryNode_eq_crossingBoundaryNode_of_mem hKsq hLsub
    (mem_cumulativeLevelFibres.mp R.1.2).1 e c hce

/--
**Local contraction path lift.**  Two boundary nodes incident with the same
active right node are reachable in the original selected maximum forest.
The lifted route is

`c -- crossing e -- fibre endpoint e -- cut path -- fibre endpoint f -- crossing f -- d`.
-/
theorem original_reachable_of_common_contracted_right
    {N K : ℕ} {L : SimpleGraph (HVertex N)}
    (hKsq : K * K ≤ N)
    (hL : IsLinearForest (reducedDivisorGraph N) L)
    (c d : ExtremalBoundaryNode N K) (R : ExtremalRightNode N K L)
    (hc : (extremalContractedIncidenceGraph N K L).Adj
      (Sum.inl c) (Sum.inr R))
    (hd : (extremalContractedIncidenceGraph N K L).Adj
      (Sum.inl d) (Sum.inr R)) :
    L.Reachable c.1 d.1 := by
  obtain ⟨e, hce, heR⟩ :=
    exists_crossing_witness_of_contracted_adj hKsq hL.1 c R hc
  obtain ⟨f, hdf, hfR⟩ :=
    exists_crossing_witness_of_contracted_adj hKsq hL.1 d R hd
  have heAdj : L.Adj c.1 (crossingFibreEndpoint (K := K) e) := by
    have h := crossingOutsideEndpoint_adj_crossingFibreEndpoint (K := K) e
    simpa [hce] using h
  have hfAdj : L.Adj d.1 (crossingFibreEndpoint (K := K) f) := by
    have h := crossingOutsideEndpoint_adj_crossingFibreEndpoint (K := K) f
    simpa [hdf] using h
  have hcut :
      (extremalCutGraph N K L).Reachable
        (crossingFibreEndpoint (K := K) e)
        (crossingFibreEndpoint (K := K) f) :=
    crossingFibreEndpoints_reachable_cut_of_same_activeComponent
      e f (heR.trans hfR.symm)
  have hmiddle :
      L.Reachable (crossingFibreEndpoint (K := K) e)
        (crossingFibreEndpoint (K := K) f) :=
    hcut.mono extremalCutGraph_le
  exact heAdj.reachable.trans (hmiddle.trans hfAdj.symm.reachable)

/--
The same local lift also records the surviving middle segment explicitly; this
form is useful when proving that a lifted contracted cycle avoids one chosen
crossing edge.
-/
theorem exists_cut_reachable_endpoints_of_common_contracted_right
    {N K : ℕ} {L : SimpleGraph (HVertex N)}
    (hKsq : K * K ≤ N)
    (hLsub : L ≤ reducedDivisorGraph N)
    (c d : ExtremalBoundaryNode N K) (R : ExtremalRightNode N K L)
    (hc : (extremalContractedIncidenceGraph N K L).Adj
      (Sum.inl c) (Sum.inr R))
    (hd : (extremalContractedIncidenceGraph N K L).Adj
      (Sum.inl d) (Sum.inr R)) :
    ∃ e f : FibreCrossingEdge (_K := K) R.1.1 L,
      c = crossingBoundaryNode (K := K) hLsub
        (mem_cumulativeLevelFibres.mp R.1.2).1 e ∧
      d = crossingBoundaryNode (K := K) hLsub
        (mem_cumulativeLevelFibres.mp R.1.2).1 f ∧
      (extremalCutGraph N K L).Reachable
        (crossingFibreEndpoint (K := K) e)
        (crossingFibreEndpoint (K := K) f) := by
  obtain ⟨e, hce, heR⟩ :=
    exists_crossing_witness_of_contracted_adj hKsq hLsub c R hc
  obtain ⟨f, hdf, hfR⟩ :=
    exists_crossing_witness_of_contracted_adj hKsq hLsub d R hd
  refine ⟨e, f, hce, hdf, ?_⟩
  exact crossingFibreEndpoints_reachable_cut_of_same_activeComponent
    e f (heR.trans hfR.symm)

end DivisorF
