import DivisorF.ExtremalContractedPathLift
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Acyclicity of the extremal contracted incidence graph

This module closes the remaining contraction-geometry step in the original
Corollary 3.11.  Every retained nonbinary crossing is a bridge of the original
maximum linear forest.  Deleting one such crossing separates its canonical
outside and fibre endpoints.  We transport that separation to the concrete
contracted incidence graph: every other contracted incidence preserves the
side of this cut, while the contracted edge produced by the deleted crossing
joins opposite sides.  Hence every contracted edge is a bridge, and the
contracted graph is acyclic.

No optimal forests are mixed: all objects below come from the same selected
linear forest `L`.
-/

namespace DivisorF

open SimpleGraph

/-- A concrete representative vertex of one active right component. -/
noncomputable def extremalRightNodeRepresentative
    {N K : ℕ} {L : SimpleGraph (HVertex N)}
    (R : ExtremalRightNode N K L) : HVertex N :=
  Classical.choose R.2.2

/-- The representative really belongs to the post-cut component carried by `R`. -/
theorem extremalRightNodeRepresentative_component
    {N K : ℕ} {L : SimpleGraph (HVertex N)}
    (R : ExtremalRightNode N K L) :
    extremalRestrictionComponent (K := K) L
        (extremalRightNodeRepresentative R) = R.2.1 := by
  exact (Classical.choose_spec R.2.2).2.1

/--
The post-cut forest is contained in the graph obtained by deleting any one
retained nonbinary crossing from `L`.
-/
theorem extremalCutGraph_le_delete_one_nonbinary_crossing
    {N K : ℕ} {L : SimpleGraph (HVertex N)}
    (x : ExtremalNonbinaryCrossingEdge N K L) :
    extremalCutGraph N K L ≤ L.deleteEdges {x.2.1} := by
  intro u v huv
  have huv' :
      L.Adj u v ∧
        s(u, v) ∉ (↑(nonbinaryCrossingUnion N K L) : Set (Sym2 (HVertex N))) := by
    simpa [extremalCutGraph, SimpleGraph.deleteEdges_adj] using huv
  rw [SimpleGraph.deleteEdges_adj]
  refine ⟨huv'.1, ?_⟩
  intro hsingle
  have hedge : s(u, v) = x.2.1 := by simpa using hsingle
  apply huv'.2
  rw [hedge]
  exact Finset.mem_coe.mpr (crossing_mem_nonbinaryCrossingUnion x.1.2 x.2.2)

/-- A retained crossing of the original acyclic selected forest is a bridge. -/
theorem extremalNonbinaryCrossing_isBridge
    {N K : ℕ} {L : SimpleGraph (HVertex N)}
    (hL : IsLinearForest (reducedDivisorGraph N) L)
    (x : ExtremalNonbinaryCrossingEdge N K L) :
    L.IsBridge x.2.1 := by
  apply (SimpleGraph.isAcyclic_iff_forall_isBridge.mp hL.2.1)
  exact (mem_crossingFinset.mp x.2.2).1

/--
Deleting a retained crossing disconnects its canonical outside endpoint from
its canonical fibre endpoint.
-/
theorem not_reachable_delete_crossing_outside_fibre
    {N K : ℕ} {L : SimpleGraph (HVertex N)}
    (hL : IsLinearForest (reducedDivisorGraph N) L)
    (x : ExtremalNonbinaryCrossingEdge N K L) :
    ¬(L.deleteEdges {x.2.1}).Reachable
      (crossingOutsideEndpoint (K := K) x.2)
      (crossingFibreEndpoint (K := K) x.2) := by
  have hb := extremalNonbinaryCrossing_isBridge hL x
  have hpair := crossing_eq_outside_fibre_endpoints (K := K) x.2
  rw [hpair] at hb
  have hsep := SimpleGraph.isBridge_iff.mp hb
  rw [← hpair] at hsep
  exact hsep

/--
Two tagged retained crossings with the same underlying selected edge are the
same tagged crossing.  Distinct large-prime fibres cannot share a crossing
edge.
-/
theorem extremalNonbinaryCrossingEdge_eq_of_edge_eq
    {N K : ℕ} {L : SimpleGraph (HVertex N)}
    (hL : IsLinearForest (reducedDivisorGraph N) L)
    {x y : ExtremalNonbinaryCrossingEdge N K L}
    (hedge : x.2.1 = y.2.1) : x = y := by
  obtain ⟨qx, ex⟩ := x
  obtain ⟨qy, ey⟩ := y
  have hedge' : (ex.1 : Sym2 (HVertex N)) = (ey.1 : Sym2 (HVertex N)) := hedge
  have hq : qx = qy := by
    by_contra hqne
    have hval : (qx.1 : LargePrime N).val ≠ (qy.1 : LargePrime N).val := by
      intro hv
      refine hqne (Subtype.ext ?_)
      obtain ⟨a, ha⟩ := qx
      obtain ⟨b, hb⟩ := qy
      cases a
      cases b
      simp_all
    have hdisj := crossingFinset_disjoint_of_ne hL hval
    rw [Finset.disjoint_left] at hdisj
    refine hdisj ex.2 ?_
    rw [hedge']
    exact ey.2
  subst hq
  have hxy : ex = ey := Subtype.ext hedge'
  subst hxy
  rfl

/-- The right representative is reachable from every crossing endpoint landing in it. -/
theorem crossingFibreEndpoint_reachable_rightRepresentative
    {N K : ℕ} {L : SimpleGraph (HVertex N)}
    (R : ExtremalRightNode N K L)
    (e : FibreCrossingEdge (_K := K) R.1.1 L)
    (hcomp : crossingActiveFibreRestrictionComponent (K := K) e = R.2) :
    (extremalCutGraph N K L).Reachable
      (crossingFibreEndpoint (K := K) e)
      (extremalRightNodeRepresentative R) := by
  apply extremalRestrictionComponent_eq_iff_reachable.mp
  calc
    extremalRestrictionComponent (K := K) L
        (crossingFibreEndpoint (K := K) e)
        = (crossingActiveFibreRestrictionComponent (K := K) e).1 := rfl
    _ = R.2.1 :=
      congrArg
        (fun A : ActiveFibreRestrictionComponent (K := K) R.1.1 L => A.1) hcomp
    _ = extremalRestrictionComponent (K := K) L
        (extremalRightNodeRepresentative R) :=
      (extremalRightNodeRepresentative_component R).symm

/-- The two concrete nodes produced by one tagged crossing. -/
noncomputable def extremalCrossingBoundaryNode
    {N K : ℕ} {L : SimpleGraph (HVertex N)}
    (hLsub : L ≤ reducedDivisorGraph N)
    (x : ExtremalNonbinaryCrossingEdge N K L) : ExtremalBoundaryNode N K :=
  crossingBoundaryNode (K := K) hLsub
    (mem_cumulativeLevelFibres.mp x.1.2).1 x.2

noncomputable def extremalCrossingRightNode
    {N K : ℕ} {L : SimpleGraph (HVertex N)}
    (x : ExtremalNonbinaryCrossingEdge N K L) : ExtremalRightNode N K L :=
  ⟨x.1, crossingActiveFibreRestrictionComponent (K := K) x.2⟩

@[simp]
theorem extremalNonbinaryCrossingToContractedEdge_val
    {N K : ℕ} {L : SimpleGraph (HVertex N)}
    (hLsub : L ≤ reducedDivisorGraph N)
    (x : ExtremalNonbinaryCrossingEdge N K L) :
    (extremalNonbinaryCrossingToContractedEdge hLsub x).1 =
      s(Sum.inl (extremalCrossingBoundaryNode hLsub x),
        Sum.inr (extremalCrossingRightNode x)) := rfl

/--
The side of the original bridge cut on which a contracted node lies.  A right
node is represented by any fixed vertex in its post-cut component; the whole
component lies on one side because the cut graph removes the target crossing.
-/
noncomputable def contractedSideOfCrossing
    {N K : ℕ} {L : SimpleGraph (HVertex N)}
    (x : ExtremalNonbinaryCrossingEdge N K L)
    (z : ExtremalBoundaryNode N K ⊕ ExtremalRightNode N K L) : Prop :=
  match z with
  | Sum.inl c =>
      (L.deleteEdges {x.2.1}).Reachable
        (crossingOutsideEndpoint (K := K) x.2) c.1
  | Sum.inr R =>
      (L.deleteEdges {x.2.1}).Reachable
        (crossingOutsideEndpoint (K := K) x.2)
        (extremalRightNodeRepresentative R)

/-- The boundary endpoint of the target crossing lies on its outside side. -/
theorem contractedSideOfCrossing_boundary
    {N K : ℕ} {L : SimpleGraph (HVertex N)}
    (hLsub : L ≤ reducedDivisorGraph N)
    (x : ExtremalNonbinaryCrossingEdge N K L) :
    contractedSideOfCrossing x
      (Sum.inl (extremalCrossingBoundaryNode hLsub x)) := by
  change (L.deleteEdges {x.2.1}).Reachable
    (crossingOutsideEndpoint (K := K) x.2)
    (extremalCrossingBoundaryNode hLsub x).1
  exact SimpleGraph.Reachable.refl _

/-- The right endpoint of the target contracted edge lies on the opposite side. -/
theorem not_contractedSideOfCrossing_right
    {N K : ℕ} {L : SimpleGraph (HVertex N)}
    (hL : IsLinearForest (reducedDivisorGraph N) L)
    (x : ExtremalNonbinaryCrossingEdge N K L) :
    ¬contractedSideOfCrossing x (Sum.inr (extremalCrossingRightNode x)) := by
  intro hside
  change (L.deleteEdges {x.2.1}).Reachable
    (crossingOutsideEndpoint (K := K) x.2)
    (extremalRightNodeRepresentative (extremalCrossingRightNode x)) at hside
  have hcut :
      (extremalCutGraph N K L).Reachable
        (crossingFibreEndpoint (K := K) x.2)
        (extremalRightNodeRepresentative (extremalCrossingRightNode x)) := by
    exact crossingFibreEndpoint_reachable_rightRepresentative
      (extremalCrossingRightNode x) x.2 rfl
  have hmiddle :
      (L.deleteEdges {x.2.1}).Reachable
        (crossingFibreEndpoint (K := K) x.2)
        (extremalRightNodeRepresentative (extremalCrossingRightNode x)) :=
    hcut.mono (extremalCutGraph_le_delete_one_nonbinary_crossing x)
  exact (not_reachable_delete_crossing_outside_fibre hL x)
    (hside.trans hmiddle.symm)

/--
A contracted edge different from the target bridge preserves the target cut
side in either direction.
-/
theorem contractedSideOfCrossing_of_adj_delete_target
    {N K : ℕ} {L : SimpleGraph (HVertex N)}
    (hKsq : K * K ≤ N)
    (hL : IsLinearForest (reducedDivisorGraph N) L)
    (x : ExtremalNonbinaryCrossingEdge N K L)
    {z w : ExtremalBoundaryNode N K ⊕ ExtremalRightNode N K L}
    (hzw :
      ((extremalContractedIncidenceGraph N K L).deleteEdges
        {(extremalNonbinaryCrossingToContractedEdge hL.1 x).1}).Adj z w)
    (hz : contractedSideOfCrossing x z) :
    contractedSideOfCrossing x w := by
  have hAdj : (extremalContractedIncidenceGraph N K L).Adj z w :=
    (SimpleGraph.deleteEdges_adj.mp hzw).1
  have htarget :
      s(z, w) ≠ (extremalNonbinaryCrossingToContractedEdge hL.1 x).1 := by
    intro heq
    exact (SimpleGraph.deleteEdges_adj.mp hzw).2 (by simp [heq])
  rcases extremalContractedIncidenceGraph_adj_cases hAdj with
      ⟨c, R, rfl, rfl⟩ | ⟨R, c, rfl, rfl⟩
  · rw [extremalContractedIncidenceGraph_adj_left_right] at hAdj
    rcases hAdj with ⟨f, hcf, hfR⟩
    let y : ExtremalNonbinaryCrossingEdge N K L := ⟨R.1, f⟩
    have hc : c = crossingBoundaryNode (K := K) hL.1
        (mem_cumulativeLevelFibres.mp R.1.2).1 f :=
      boundaryNode_eq_crossingBoundaryNode_of_mem hKsq hL.1
        (mem_cumulativeLevelFibres.mp R.1.2).1 f c hcf
    have hR : R = extremalCrossingRightNode y := by
      have hpair :
          (⟨R.1, crossingActiveFibreRestrictionComponent (K := K) f⟩ :
              ExtremalRightNode N K L) = ⟨R.1, R.2⟩ := by
        rw [hfR]
      exact hpair.symm
    have hyEdge :
        (extremalNonbinaryCrossingToContractedEdge hL.1 y).1 =
          s(Sum.inl c, Sum.inr R) := by
      rw [extremalNonbinaryCrossingToContractedEdge_val hL.1]
      simp only [extremalCrossingBoundaryNode]
      rw [← hc, ← hR]
    have hfy : f.1 = y.2.1 := rfl
    have hfne : f.1 ≠ x.2.1 := by
      intro hfx
      have hyx : y = x :=
        extremalNonbinaryCrossingEdge_eq_of_edge_eq hL (hfy.symm.trans hfx)
      apply htarget
      rw [← hyEdge, hyx]
    have hfAdjL : L.Adj c.1 (crossingFibreEndpoint (K := K) f) := by
      have h := crossingOutsideEndpoint_adj_crossingFibreEndpoint (K := K) f
      simpa [hc] using h
    have hfAdjDelete :
        (L.deleteEdges {x.2.1}).Adj c.1
          (crossingFibreEndpoint (K := K) f) := by
      rw [SimpleGraph.deleteEdges_adj]
      refine ⟨hfAdjL, ?_⟩
      intro hmem
      have heq : s(c.1, crossingFibreEndpoint (K := K) f) = x.2.1 := by
        simpa using hmem
      apply hfne
      calc
        f.1 = s(crossingOutsideEndpoint (K := K) f,
            crossingFibreEndpoint (K := K) f) :=
          crossing_eq_outside_fibre_endpoints (K := K) f
        _ = s(c.1, crossingFibreEndpoint (K := K) f) := by
          rw [show (c.1 : HVertex N) = crossingOutsideEndpoint (K := K) f from
            congrArg (fun d : ExtremalBoundaryNode N K => d.1) hc]
        _ = x.2.1 := heq
    have hcut :
        (extremalCutGraph N K L).Reachable
          (crossingFibreEndpoint (K := K) f)
          (extremalRightNodeRepresentative R) :=
      crossingFibreEndpoint_reachable_rightRepresentative R f hfR
    have hmiddle :
        (L.deleteEdges {x.2.1}).Reachable
          (crossingFibreEndpoint (K := K) f)
          (extremalRightNodeRepresentative R) :=
      hcut.mono (extremalCutGraph_le_delete_one_nonbinary_crossing x)
    exact hz.trans (hfAdjDelete.reachable.trans hmiddle)
  · have hAdj' :
        (extremalContractedIncidenceGraph N K L).Adj
          (Sum.inl c) (Sum.inr R) := hAdj.symm
    rw [extremalContractedIncidenceGraph_adj_left_right] at hAdj'
    rcases hAdj' with ⟨f, hcf, hfR⟩
    let y : ExtremalNonbinaryCrossingEdge N K L := ⟨R.1, f⟩
    have hc : c = crossingBoundaryNode (K := K) hL.1
        (mem_cumulativeLevelFibres.mp R.1.2).1 f :=
      boundaryNode_eq_crossingBoundaryNode_of_mem hKsq hL.1
        (mem_cumulativeLevelFibres.mp R.1.2).1 f c hcf
    have hR : R = extremalCrossingRightNode y := by
      have hpair :
          (⟨R.1, crossingActiveFibreRestrictionComponent (K := K) f⟩ :
              ExtremalRightNode N K L) = ⟨R.1, R.2⟩ := by
        rw [hfR]
      exact hpair.symm
    have hyEdge :
        (extremalNonbinaryCrossingToContractedEdge hL.1 y).1 =
          s(Sum.inl c, Sum.inr R) := by
      rw [extremalNonbinaryCrossingToContractedEdge_val hL.1]
      simp only [extremalCrossingBoundaryNode]
      rw [← hc, ← hR]
    have hfne : f.1 ≠ x.2.1 := by
      intro hfx
      have hyx : y = x :=
        extremalNonbinaryCrossingEdge_eq_of_edge_eq hL hfx
      apply htarget
      rw [Sym2.eq_swap, ← hyEdge, hyx]
    have hfAdjL : L.Adj c.1 (crossingFibreEndpoint (K := K) f) := by
      have h := crossingOutsideEndpoint_adj_crossingFibreEndpoint (K := K) f
      simpa [hc] using h
    have hfAdjDelete :
        (L.deleteEdges {x.2.1}).Adj c.1
          (crossingFibreEndpoint (K := K) f) := by
      rw [SimpleGraph.deleteEdges_adj]
      refine ⟨hfAdjL, ?_⟩
      intro hmem
      have heq : s(c.1, crossingFibreEndpoint (K := K) f) = x.2.1 := by
        simpa using hmem
      apply hfne
      calc
        f.1 = s(crossingOutsideEndpoint (K := K) f,
            crossingFibreEndpoint (K := K) f) :=
          crossing_eq_outside_fibre_endpoints (K := K) f
        _ = s(c.1, crossingFibreEndpoint (K := K) f) := by
          rw [show (c.1 : HVertex N) = crossingOutsideEndpoint (K := K) f from
            congrArg (fun d : ExtremalBoundaryNode N K => d.1) hc]
        _ = x.2.1 := heq
    have hcut :
        (extremalCutGraph N K L).Reachable
          (crossingFibreEndpoint (K := K) f)
          (extremalRightNodeRepresentative R) :=
      crossingFibreEndpoint_reachable_rightRepresentative R f hfR
    have hmiddle :
        (L.deleteEdges {x.2.1}).Reachable
          (crossingFibreEndpoint (K := K) f)
          (extremalRightNodeRepresentative R) :=
      hcut.mono (extremalCutGraph_le_delete_one_nonbinary_crossing x)
    exact hz.trans (hmiddle.symm.trans hfAdjDelete.symm.reachable)

/-- Reachability after deleting the target contracted edge preserves the bridge side. -/
theorem contractedSideOfCrossing_of_reachable_delete_target
    {N K : ℕ} {L : SimpleGraph (HVertex N)}
    (hKsq : K * K ≤ N)
    (hL : IsLinearForest (reducedDivisorGraph N) L)
    (x : ExtremalNonbinaryCrossingEdge N K L)
    {z w : ExtremalBoundaryNode N K ⊕ ExtremalRightNode N K L}
    (hreach :
      ((extremalContractedIncidenceGraph N K L).deleteEdges
        {(extremalNonbinaryCrossingToContractedEdge hL.1 x).1}).Reachable z w)
    (hz : contractedSideOfCrossing x z) :
    contractedSideOfCrossing x w := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
  induction hreach with
  | refl => exact hz
  | tail hprev hadj ih =>
      exact contractedSideOfCrossing_of_adj_delete_target hKsq hL x hadj ih

/-- Every concrete edge produced by a retained crossing is a bridge of the contracted graph. -/
theorem extremalNonbinaryCrossingToContractedEdge_isBridge
    {N K : ℕ} {L : SimpleGraph (HVertex N)}
    (hKsq : K * K ≤ N)
    (hL : IsLinearForest (reducedDivisorGraph N) L)
    (x : ExtremalNonbinaryCrossingEdge N K L) :
    (extremalContractedIncidenceGraph N K L).IsBridge
      (extremalNonbinaryCrossingToContractedEdge hL.1 x).1 := by
  rw [extremalNonbinaryCrossingToContractedEdge_val hL.1]
  rw [SimpleGraph.isBridge_iff]
  intro hreach
  have hside := contractedSideOfCrossing_of_reachable_delete_target
    hKsq hL x hreach (contractedSideOfCrossing_boundary hL.1 x)
  exact (not_contractedSideOfCrossing_right hL x) hside

/--
**Corollary 3.11 contraction geometry.**  The concrete extremal incidence graph
is acyclic: every one of its edges is the image of a retained crossing, and
every such image is a bridge.
-/
theorem extremalContractedIncidenceGraph_isAcyclic
    {N K : ℕ} {L : SimpleGraph (HVertex N)}
    (hKsq : K * K ≤ N)
    (hL : IsLinearForest (reducedDivisorGraph N) L) :
    (extremalContractedIncidenceGraph N K L).IsAcyclic := by
  rw [SimpleGraph.isAcyclic_iff_forall_isBridge]
  intro E hE
  let Et : (extremalContractedIncidenceGraph N K L).edgeSet := ⟨E, hE⟩
  obtain ⟨x, hx⟩ :=
    extremalNonbinaryCrossingToContractedEdge_surjective hKsq hL.1 Et
  have hb := extremalNonbinaryCrossingToContractedEdge_isBridge hKsq hL x
  have hval : (extremalNonbinaryCrossingToContractedEdge hL.1 x).1 = E :=
    congrArg Subtype.val hx
  rw [← hval]
  exact hb

end DivisorF
