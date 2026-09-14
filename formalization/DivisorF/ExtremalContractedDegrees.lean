import DivisorF.ExtremalContractedEdgeCounting
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Set.Card
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Exact right-node degrees in the extremal contracted incidence graph

This module realizes the fibre-by-fibre one-component/two-component profile as
actual graph degrees in the concrete contracted incidence graph of Corollary
3.11.

For a fixed active right node `R`, consider the selected crossings of its owning
fibre whose post-cut fibre endpoint lies in `R`. Such crossings are in
bijection with the neighbours of `R` in the contracted incidence graph: the
canonical outside endpoint supplies the boundary neighbour, while the
no-edge-collapse theorem gives injectivity. Since every extremal nonbinary
fibre has exactly two crossings, a non-split fibre gives one right node of
degree two, whereas a split fibre gives two right nodes of degree one.
-/

namespace DivisorF

open SimpleGraph

/-- Crossings of the owning fibre that land in one fixed active right node. -/
def rightNodeCrossingSet
    {N K : ℕ} {L : SimpleGraph (HVertex N)}
    (R : ExtremalRightNode N K L) :
    Set (FibreCrossingEdge (_K := K) R.1.1 L) :=
  {e | crossingActiveFibreRestrictionComponent (K := K) e = R.2}

/-- Every active right node is hit by at least one selected crossing. -/
theorem rightNodeCrossingSet_nonempty
    {N K : ℕ} {L : SimpleGraph (HVertex N)}
    (R : ExtremalRightNode N K L) :
    (rightNodeCrossingSet (K := K) R).Nonempty := by
  obtain ⟨e, he⟩ :=
    crossingActiveFibreRestrictionComponent_surjective (K := K) R.2
  exact ⟨e, he⟩

/--
The selected crossings landing in `R` are equinumerous with the neighbours of
`R` in the concrete contracted incidence graph.
-/
theorem rightNodeCrossingSet_ncard_eq_selectedDegree
    {N K : ℕ} {L : SimpleGraph (HVertex N)}
    (hKsq : K * K ≤ N)
    (hL : IsLinearForest (reducedDivisorGraph N) L)
    (R : ExtremalRightNode N K L) :
    (rightNodeCrossingSet (K := K) R).ncard =
      selectedDegree (extremalContractedIncidenceGraph N K L) (Sum.inr R) := by
  unfold selectedDegree
  apply Set.ncard_congr
    (fun e _ =>
      Sum.inl (crossingBoundaryNode (K := K) hL.1
        (mem_cumulativeLevelFibres.mp R.1.2).1 e))
  · intro e he
    rw [SimpleGraph.mem_neighborSet]
    have heR : crossingActiveFibreRestrictionComponent (K := K) e = R.2 := he
    have hadj := extremalContractedIncidenceGraph_adj_of_crossing hL.1 R.1.2 e
    rw [heR] at hadj
    exact hadj.symm
  · intro e f he hf hef
    have hboundary :
        crossingOutsideEndpoint (K := K) e =
          crossingOutsideEndpoint (K := K) f := by
      have hc := Sum.inl.inj hef
      exact congrArg (fun c : ExtremalBoundaryNode N K => c.1) hc
    exact fibreCrossingEdge_eq_of_same_contracted_nodes
      hL R.1.2 e f hboundary (he.trans hf.symm)
  · intro x hx
    rw [SimpleGraph.mem_neighborSet] at hx
    cases x with
    | inl c =>
        rw [extremalContractedIncidenceGraph_adj_right_left] at hx
        rcases hx with ⟨e, hce, heR⟩
        refine ⟨e, heR, ?_⟩
        have hc :
            c = crossingBoundaryNode (K := K) hL.1
              (mem_cumulativeLevelFibres.mp R.1.2).1 e :=
          boundaryNode_eq_crossingBoundaryNode_of_mem hKsq hL.1
            (mem_cumulativeLevelFibres.mp R.1.2).1 e c hce
        simp [hc]
    | inr S =>
        exact (extremalContractedIncidenceGraph_not_adj_right_right R S hx).elim

/-- The crossing type of an extremal nonbinary fibre has cardinality two. -/
theorem fibreCrossingEdge_card_eq_two_of_extremal
    {N K : ℕ} {L : SimpleGraph (HVertex N)}
    (hL : IsLinearForest (reducedDivisorGraph N) L)
    (hmax : edgeCard L = linearForestNumber (reducedDivisorGraph N))
    (hsat : cumulativeNonbinaryCount N K = K - 1)
    {q : LargePrime N} (hq : q ∈ cumulativeLevelFibres N K 2) :
    Fintype.card (FibreCrossingEdge (_K := K) q L) = 2 := by
  simp only [FibreCrossingEdge, Fintype.card_coe]
  exact card_crossingFinset_eq_two_of_extremal hL hmax hsat hq

/-- A one-component extremal fibre gives a right node of degree two. -/
theorem extremalRightNode_selectedDegree_eq_two_of_one_component
    {N K : ℕ} {L : SimpleGraph (HVertex N)}
    (hKsq : K * K ≤ N)
    (hL : IsLinearForest (reducedDivisorGraph N) L)
    (hmax : edgeCard L = linearForestNumber (reducedDivisorGraph N))
    (hsat : cumulativeNonbinaryCount N K = K - 1)
    (R : ExtremalRightNode N K L)
    (hone : Fintype.card
      (ActiveFibreRestrictionComponent (K := K) R.1.1 L) = 1) :
    selectedDegree (extremalContractedIncidenceGraph N K L) (Sum.inr R) = 2 := by
  rw [← rightNodeCrossingSet_ncard_eq_selectedDegree hKsq hL R]
  have hset : rightNodeCrossingSet (K := K) R = Set.univ := by
    apply Set.eq_univ_of_forall
    intro e
    change crossingActiveFibreRestrictionComponent (K := K) e = R.2
    have hcard_le :
        Fintype.card (ActiveFibreRestrictionComponent (K := K) R.1.1 L) ≤ 1 := by
      omega
    exact (Fintype.card_le_one_iff.mp hcard_le) _ _
  rw [hset, Set.ncard_univ, Nat.card_eq_fintype_card,
    fibreCrossingEdge_card_eq_two_of_extremal hL hmax hsat R.1.2]

/--
If the fibre has two active restriction components, each right node receives
exactly one of its two crossings.
-/
theorem rightNodeCrossingSet_ncard_eq_one_of_two_components
    {N K : ℕ} {L : SimpleGraph (HVertex N)}
    (hL : IsLinearForest (reducedDivisorGraph N) L)
    (hmax : edgeCard L = linearForestNumber (reducedDivisorGraph N))
    (hsat : cumulativeNonbinaryCount N K = K - 1)
    (R : ExtremalRightNode N K L)
    (htwo : Fintype.card
      (ActiveFibreRestrictionComponent (K := K) R.1.1 L) = 2) :
    (rightNodeCrossingSet (K := K) R).ncard = 1 := by
  have hpos : 0 < (rightNodeCrossingSet (K := K) R).ncard :=
    (Set.ncard_pos).2 (rightNodeCrossingSet_nonempty (K := K) R)
  have hle : (rightNodeCrossingSet (K := K) R).ncard ≤ 2 := by
    calc
      (rightNodeCrossingSet (K := K) R).ncard
          ≤ Nat.card (FibreCrossingEdge (_K := K) R.1.1 L) :=
        Set.ncard_le_card _
      _ = Fintype.card (FibreCrossingEdge (_K := K) R.1.1 L) :=
        Nat.card_eq_fintype_card
      _ = 2 := fibreCrossingEdge_card_eq_two_of_extremal
        hL hmax hsat R.1.2
  have hne_two : (rightNodeCrossingSet (K := K) R).ncard ≠ 2 := by
    intro heq
    have htotal :
        Nat.card (FibreCrossingEdge (_K := K) R.1.1 L) = 2 := by
      rw [Nat.card_eq_fintype_card,
        fibreCrossingEdge_card_eq_two_of_extremal hL hmax hsat R.1.2]
    have hset : rightNodeCrossingSet (K := K) R = Set.univ := by
      rw [Set.eq_univ_iff_ncard, htotal]
      exact heq
    have hconstant :
        ∀ e : FibreCrossingEdge (_K := K) R.1.1 L,
          crossingActiveFibreRestrictionComponent (K := K) e = R.2 := by
      intro e
      have he : e ∈ rightNodeCrossingSet (K := K) R := by
        rw [hset]
        trivial
      exact he
    have hsub :
        Subsingleton (ActiveFibreRestrictionComponent (K := K) R.1.1 L) := by
      constructor
      intro A B
      obtain ⟨e, he⟩ :=
        crossingActiveFibreRestrictionComponent_surjective (K := K) A
      obtain ⟨f, hf⟩ :=
        crossingActiveFibreRestrictionComponent_surjective (K := K) B
      calc
        A = crossingActiveFibreRestrictionComponent (K := K) e := he.symm
        _ = R.2 := hconstant e
        _ = crossingActiveFibreRestrictionComponent (K := K) f :=
          (hconstant f).symm
        _ = B := hf
    have hcard_le :
        Fintype.card (ActiveFibreRestrictionComponent (K := K) R.1.1 L) ≤ 1 :=
      Fintype.card_le_one_iff_subsingleton.mpr hsub
    omega
  omega

/-- A split extremal fibre gives degree one at each of its two right nodes. -/
theorem extremalRightNode_selectedDegree_eq_one_of_two_components
    {N K : ℕ} {L : SimpleGraph (HVertex N)}
    (hKsq : K * K ≤ N)
    (hL : IsLinearForest (reducedDivisorGraph N) L)
    (hmax : edgeCard L = linearForestNumber (reducedDivisorGraph N))
    (hsat : cumulativeNonbinaryCount N K = K - 1)
    (R : ExtremalRightNode N K L)
    (htwo : Fintype.card
      (ActiveFibreRestrictionComponent (K := K) R.1.1 L) = 2) :
    selectedDegree (extremalContractedIncidenceGraph N K L) (Sum.inr R) = 1 := by
  rw [← rightNodeCrossingSet_ncard_eq_selectedDegree hKsq hL R]
  exact rightNodeCrossingSet_ncard_eq_one_of_two_components
    hL hmax hsat R htwo

/--
**Corollary 3.11 right-degree realization.** Every active right node has
contracted degree one or two.
-/
theorem extremalRightNode_selectedDegree_eq_one_or_two
    {N K : ℕ} {L : SimpleGraph (HVertex N)}
    (hKsq : K * K ≤ N)
    (hL : IsLinearForest (reducedDivisorGraph N) L)
    (hmax : edgeCard L = linearForestNumber (reducedDivisorGraph N))
    (hsat : cumulativeNonbinaryCount N K = K - 1)
    (R : ExtremalRightNode N K L) :
    selectedDegree (extremalContractedIncidenceGraph N K L) (Sum.inr R) = 1 ∨
      selectedDegree (extremalContractedIncidenceGraph N K L) (Sum.inr R) = 2 := by
  rcases activeFibreRestrictionComponent_card_eq_one_or_two_of_extremal
    hL hmax hsat R.1.2 with hone | htwo
  · exact Or.inr
      (extremalRightNode_selectedDegree_eq_two_of_one_component
        hKsq hL hmax hsat R hone)
  · exact Or.inl
      (extremalRightNode_selectedDegree_eq_one_of_two_components
        hKsq hL hmax hsat R htwo)

/--
The actual graph-theoretic right leaves are exactly the right nodes belonging
to split nonbinary fibres.
-/
theorem extremalRightNode_selectedDegree_eq_one_iff_split
    {N K : ℕ} {L : SimpleGraph (HVertex N)}
    (hKsq : K * K ≤ N)
    (hL : IsLinearForest (reducedDivisorGraph N) L)
    (hmax : edgeCard L = linearForestNumber (reducedDivisorGraph N))
    (hsat : cumulativeNonbinaryCount N K = K - 1)
    (R : ExtremalRightNode N K L) :
    selectedDegree (extremalContractedIncidenceGraph N K L) (Sum.inr R) = 1 ↔
      R.1.1 ∈ splitNonbinaryFibres N K L := by
  constructor
  · intro hdeg
    by_contra hnot
    have hcases := activeFibreRestrictionComponent_card_eq_one_or_two_of_extremal
      hL hmax hsat R.1.2
    rcases hcases with hone | htwo
    · have htwoDeg := extremalRightNode_selectedDegree_eq_two_of_one_component
        hKsq hL hmax hsat R hone
      omega
    · exact hnot (mem_splitNonbinaryFibres.mpr
        ⟨R.1.2, by
          unfold activeFibreRestrictionComponentCount
          exact htwo⟩)
  · intro hsplit
    have htwo : Fintype.card
        (ActiveFibreRestrictionComponent (K := K) R.1.1 L) = 2 := by
      exact (mem_splitNonbinaryFibres.mp hsplit).2
    exact extremalRightNode_selectedDegree_eq_one_of_two_components
      hKsq hL hmax hsat R htwo

end DivisorF
