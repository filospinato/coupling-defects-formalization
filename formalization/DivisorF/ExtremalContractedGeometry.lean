import DivisorF.ExtremalContractedIncidence
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Canonical crossing endpoints for the extremal contracted incidence graph

This module strengthens the concrete Corollary 3.11 contraction layer.  Every
selected crossing has a canonical endpoint outside its large-prime fibre; for a
counted fibre of quotient type at most `K`, that endpoint is a boundary node.
Thus every retained nonbinary crossing produces an actual edge of the concrete
contracted incidence graph.

The uniqueness statements below are the input needed to show that contraction
does not identify two retained crossings with the same simple incidence edge.
-/

namespace DivisorF

open SimpleGraph

/-- The unique endpoint of a selected crossing that lies outside its fibre. -/
noncomputable def crossingOutsideEndpoint
    {N K : ℕ} {q : LargePrime N} {L : SimpleGraph (HVertex N)}
    (e : FibreCrossingEdge (_K := K) q L) : HVertex N :=
  Classical.choose (mem_crossingFinset.mp e.2).2.2

theorem crossingOutsideEndpoint_mem
    {N K : ℕ} {q : LargePrime N} {L : SimpleGraph (HVertex N)}
    (e : FibreCrossingEdge (_K := K) q L) :
    crossingOutsideEndpoint (K := K) e ∈ e.1 := by
  exact (Classical.choose_spec (mem_crossingFinset.mp e.2).2.2).1

theorem crossingOutsideEndpoint_not_inFibre
    {N K : ℕ} {q : LargePrime N} {L : SimpleGraph (HVertex N)}
    (e : FibreCrossingEdge (_K := K) q L) :
    ¬InFibre q (crossingOutsideEndpoint (K := K) e) := by
  exact (Classical.choose_spec (mem_crossingFinset.mp e.2).2.2).2

/-- A crossing edge has a unique endpoint outside its large-prime fibre. -/
theorem crossing_outside_endpoint_unique
    {N _K : ℕ} {q : LargePrime N} {L : SimpleGraph (HVertex N)}
    {e : Sym2 (HVertex N)} (he : e ∈ crossingFinset q L)
    {x y : HVertex N}
    (hx : x ∈ e) (hy : y ∈ e)
    (hxfibre : ¬InFibre q x) (hyfibre : ¬InFibre q y) :
    x = y := by
  have hecross := mem_crossingFinset.mp he
  rcases hecross with ⟨_, ⟨v, hv, hvfibre⟩, _⟩
  induction e using Sym2.ind with
  | _ a b =>
      simp only [Sym2.mem_iff] at hx hy hv
      rcases hx with rfl | rfl
      · rcases hy with rfl | rfl
        · rfl
        · rcases hv with hva | hvb
          · subst v
            exact (hxfibre hvfibre).elim
          · subst v
            exact (hyfibre hvfibre).elim
      · rcases hy with rfl | rfl
        · rcases hv with hva | hvb
          · subst v
            exact (hyfibre hvfibre).elim
          · subst v
            exact (hxfibre hvfibre).elim
        · rfl

/-- The chosen outside endpoint is characterized by crossing membership. -/
theorem crossingOutsideEndpoint_eq_of_mem_not_inFibre
    {N K : ℕ} {q : LargePrime N} {L : SimpleGraph (HVertex N)}
    (e : FibreCrossingEdge (_K := K) q L)
    {x : HVertex N} (hx : x ∈ e.1) (hxfibre : ¬InFibre q x) :
    x = crossingOutsideEndpoint (K := K) e := by
  exact crossing_outside_endpoint_unique (_K := K) e.2 hx
    (crossingOutsideEndpoint_mem (K := K) e) hxfibre
    (crossingOutsideEndpoint_not_inFibre (K := K) e)

/-- The canonical outside endpoint is at most the quotient type. -/
theorem crossingOutsideEndpoint_value_le_quotientType
    {N K : ℕ} {q : LargePrime N} {L : SimpleGraph (HVertex N)}
    (hLsub : L ≤ reducedDivisorGraph N)
    (e : FibreCrossingEdge (_K := K) q L) :
    (crossingOutsideEndpoint (K := K) e).value ≤ q.quotientType := by
  have hecross := mem_crossingFinset.mp e.2
  rcases hecross with ⟨heL, ⟨v, hv, hvfibre⟩, _⟩
  let x := crossingOutsideEndpoint (K := K) e
  have hxe : x ∈ e.1 := crossingOutsideEndpoint_mem (K := K) e
  have hxoutside : ¬InFibre q x :=
    crossingOutsideEndpoint_not_inFibre (K := K) e
  have hne : x ≠ v := by
    intro hxv
    exact hxoutside (hxv ▸ hvfibre)
  have hpair : e.1 = s(x, v) := (Sym2.mem_and_mem_iff hne).mp ⟨hxe, hv⟩
  have hLAdj : L.Adj x v := by
    rw [← SimpleGraph.mem_edgeSet, ← hpair]
    exact heL
  have hAdj : (reducedDivisorGraph N).Adj x v := hLsub hLAdj
  exact le_trans
    (crossing_value_le_coefficient q hvfibre hxoutside hAdj)
    (fibreCoefficient_le_quotientType q hvfibre)

/-- The canonical boundary node associated with a counted crossing. -/
noncomputable def crossingBoundaryNode
    {N K : ℕ} {q : LargePrime N} {L : SimpleGraph (HVertex N)}
    (hLsub : L ≤ reducedDivisorGraph N)
    (hq : q ∈ cumulativeFibres N K)
    (e : FibreCrossingEdge (_K := K) q L) : ExtremalBoundaryNode N K := by
  refine ⟨crossingOutsideEndpoint (K := K) e, ?_⟩
  apply (mem_smallEndpointVertices).2
  exact le_trans
    (crossingOutsideEndpoint_value_le_quotientType (K := K) hLsub e)
    (mem_cumulativeFibres.mp hq).2

@[simp]
theorem crossingBoundaryNode_val
    {N K : ℕ} {q : LargePrime N} {L : SimpleGraph (HVertex N)}
    (hLsub : L ≤ reducedDivisorGraph N)
    (hq : q ∈ cumulativeFibres N K)
    (e : FibreCrossingEdge (_K := K) q L) :
    (crossingBoundaryNode (K := K) hLsub hq e).1 =
      crossingOutsideEndpoint (K := K) e := rfl

/--
Every nonbinary crossing gives a genuine edge of the concrete contracted
incidence graph, with its canonical boundary endpoint and active right
component.
-/
theorem extremalContractedIncidenceGraph_adj_of_crossing
    {N K : ℕ} {L : SimpleGraph (HVertex N)}
    (hLsub : L ≤ reducedDivisorGraph N)
    {q : LargePrime N} (hq : q ∈ cumulativeLevelFibres N K 2)
    (e : FibreCrossingEdge (_K := K) q L) :
    (extremalContractedIncidenceGraph N K L).Adj
      (Sum.inl (crossingBoundaryNode (K := K) hLsub
        (mem_cumulativeLevelFibres.mp hq).1 e))
      (Sum.inr ⟨⟨q, hq⟩,
        crossingActiveFibreRestrictionComponent (K := K) e⟩) := by
  rw [extremalContractedIncidenceGraph_adj_left_right]
  refine ⟨e, ?_, rfl⟩
  exact crossingOutsideEndpoint_mem (K := K) e

/--
In the paper range `K^2 ≤ N`, a boundary node cannot itself lie in any
large-prime fibre.  This supplies the endpoint separation used by the
no-edge-collapse argument.
-/
theorem extremalBoundaryNode_not_inFibre_of_sq_le
    {N K : ℕ} (hKsq : K * K ≤ N)
    (c : ExtremalBoundaryNode N K) (q : LargePrime N) :
    ¬InFibre q c.1 := by
  intro hcq
  have hcpos : 0 < c.1.value :=
    lt_of_lt_of_le (by decide : 0 < 2) c.1.two_le_value
  have hqle_c : q.val ≤ c.1.value := Nat.le_of_dvd hcpos hcq
  have hcK : c.1.value ≤ K := (mem_smallEndpointVertices).mp c.2
  have hqK : q.val ≤ K := le_trans hqle_c hcK
  have hqq : q.val * q.val ≤ K * K := Nat.mul_le_mul hqK hqK
  exact (Nat.not_lt_of_ge (le_trans hqq hKsq)) q.large

/--
Hence any boundary endpoint of a counted crossing is forced to be the canonical
outside endpoint of that crossing.
-/
theorem boundaryNode_eq_crossingBoundaryNode_of_mem
    {N K : ℕ} {L : SimpleGraph (HVertex N)}
    (hKsq : K * K ≤ N)
    (hLsub : L ≤ reducedDivisorGraph N)
    {q : LargePrime N} (hq : q ∈ cumulativeFibres N K)
    (e : FibreCrossingEdge (_K := K) q L)
    (c : ExtremalBoundaryNode N K) (hc : c.1 ∈ e.1) :
    c = crossingBoundaryNode (K := K) hLsub hq e := by
  apply Subtype.ext
  exact crossingOutsideEndpoint_eq_of_mem_not_inFibre (K := K) e hc
    (extremalBoundaryNode_not_inFibre_of_sq_le hKsq c q)

/-- A crossing is exactly the unordered pair of its canonical outside and fibre endpoints. -/
theorem crossing_eq_outside_fibre_endpoints
    {N K : ℕ} {q : LargePrime N} {L : SimpleGraph (HVertex N)}
    (e : FibreCrossingEdge (_K := K) q L) :
    e.1 = s(crossingOutsideEndpoint (K := K) e,
      crossingFibreEndpoint (K := K) e) := by
  have hout := crossingOutsideEndpoint_mem (K := K) e
  have hin := crossingFibreEndpoint_mem (K := K) e
  have hne :
      crossingOutsideEndpoint (K := K) e ≠ crossingFibreEndpoint (K := K) e := by
    intro hcontra
    exact crossingOutsideEndpoint_not_inFibre (K := K) e
      (hcontra ▸ crossingFibreEndpoint_inFibre (K := K) e)
  exact (Sym2.mem_and_mem_iff hne).mp ⟨hout, hin⟩

/--
No-edge-collapse for one nonbinary fibre: if two retained crossings determine
the same boundary node and the same active post-cut restriction component,
then they are the same crossing edge.
-/
theorem fibreCrossingEdge_eq_of_same_contracted_nodes
    {N K : ℕ} {L : SimpleGraph (HVertex N)}
    (hL : IsLinearForest (reducedDivisorGraph N) L)
    {q : LargePrime N} (hq : q ∈ cumulativeLevelFibres N K 2)
    (e f : FibreCrossingEdge (_K := K) q L)
    (hboundary :
      crossingOutsideEndpoint (K := K) e =
        crossingOutsideEndpoint (K := K) f)
    (hcomponent :
      crossingActiveFibreRestrictionComponent (K := K) e =
        crossingActiveFibreRestrictionComponent (K := K) f) :
    e = f := by
  apply Subtype.ext
  have hcomp :
      extremalRestrictionComponent (K := K) L
          (crossingFibreEndpoint (K := K) e) =
        extremalRestrictionComponent (K := K) L
          (crossingFibreEndpoint (K := K) f) := by
    exact congrArg Subtype.val hcomponent
  by_cases hendpoint :
      crossingFibreEndpoint (K := K) e =
        crossingFibreEndpoint (K := K) f
  · rw [crossing_eq_outside_fibre_endpoints (K := K) e,
      crossing_eq_outside_fibre_endpoints (K := K) f,
      hboundary, hendpoint]
  · have heAdj : L.Adj
        (crossingOutsideEndpoint (K := K) e)
        (crossingFibreEndpoint (K := K) e) := by
      rw [← SimpleGraph.mem_edgeSet,
        ← crossing_eq_outside_fibre_endpoints (K := K) e]
      exact (mem_crossingFinset.mp e.2).1
    have hfAdj : L.Adj
        (crossingOutsideEndpoint (K := K) f)
        (crossingFibreEndpoint (K := K) f) := by
      rw [← SimpleGraph.mem_edgeSet,
        ← crossing_eq_outside_fibre_endpoints (K := K) f]
      exact (mem_crossingFinset.mp f.2).1
    have hnecomp := nonbinary_attachment_components_distinct
      hL hq hq heAdj (by simpa [hboundary] using hfAdj)
      (by simpa [crossing_eq_outside_fibre_endpoints (K := K) e] using e.2)
      (by simpa [hboundary, crossing_eq_outside_fibre_endpoints (K := K) f] using f.2)
      hendpoint
    exact (hnecomp hcomp).elim

end DivisorF
