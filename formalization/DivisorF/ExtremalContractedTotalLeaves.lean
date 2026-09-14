import DivisorF.ExtremalContractedFinal
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Data.Set.Card
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Total leaf realization in the extremal contracted incidence graph

The previous layer counts the degree-one nodes on the right side.  The original
Corollary 3.11 says more: these are all of the leaves.  Here we transfer the
original boundary degree-two constraint through the concrete crossing
contraction, prove every left node has contracted degree exactly two, and then
identify the full graph-theoretic leaf set with the already-counted right
leaves.
-/

namespace DivisorF

open SimpleGraph

/-- Tagged nonbinary crossings incident to one fixed contracted boundary node. -/
def extremalLeftNodeCrossingSet
    {N K : ℕ} {L : SimpleGraph (HVertex N)}
    (c : ExtremalBoundaryNode N K) :
    Set (ExtremalNonbinaryCrossingEdge N K L) :=
  {x | c.1 ∈ x.2.1}

/--
Crossings incident to a boundary node are equinumerous with its neighbours in
the concrete contracted graph.  Injectivity is exactly the no-edge-collapse
geometry already proved fibre-by-fibre.
-/
theorem extremalLeftNodeCrossingSet_ncard_eq_selectedDegree
    {N K : ℕ} {L : SimpleGraph (HVertex N)}
    (hKsq : K * K ≤ N)
    (hL : IsLinearForest (reducedDivisorGraph N) L)
    (c : ExtremalBoundaryNode N K) :
    (extremalLeftNodeCrossingSet (K := K) (L := L) c).ncard =
      selectedDegree (extremalContractedIncidenceGraph N K L) (Sum.inl c) := by
  unfold selectedDegree
  apply Set.ncard_congr
    (fun x _ =>
      Sum.inr
        (⟨x.1, crossingActiveFibreRestrictionComponent (K := K) x.2⟩ :
          ExtremalRightNode N K L))
  · intro x hx
    have hqcum := (mem_cumulativeLevelFibres.mp x.1.2).1
    have hc :
        c = crossingBoundaryNode (K := K) hL.1 hqcum x.2 :=
      boundaryNode_eq_crossingBoundaryNode_of_mem
        hKsq hL.1 hqcum x.2 c hx
    have hadj := extremalContractedIncidenceGraph_adj_of_crossing hL.1 x.1.2 x.2
    rw [← hc] at hadj
    exact hadj
  · intro x y hx hy hxy
    obtain ⟨qx, ex⟩ := x
    obtain ⟨qy, ey⟩ := y
    have hright :
        (⟨qx, crossingActiveFibreRestrictionComponent (K := K) ex⟩ :
            Σ q : {q : LargePrime N // q ∈ cumulativeLevelFibres N K 2},
              ActiveFibreRestrictionComponent (K := K) q.1 L) =
          ⟨qy, crossingActiveFibreRestrictionComponent (K := K) ey⟩ :=
      Sum.inr.inj hxy
    obtain ⟨hq, hcompHEq⟩ := Sigma.mk.inj hright
    subst hq
    have hcomp :
        crossingActiveFibreRestrictionComponent (K := K) ex =
          crossingActiveFibreRestrictionComponent (K := K) ey :=
      eq_of_heq hcompHEq
    have hqcum := (mem_cumulativeLevelFibres.mp qx.2).1
    have hcx : c = crossingBoundaryNode (K := K) hL.1 hqcum ex :=
      boundaryNode_eq_crossingBoundaryNode_of_mem hKsq hL.1 hqcum ex c hx
    have hcy : c = crossingBoundaryNode (K := K) hL.1 hqcum ey :=
      boundaryNode_eq_crossingBoundaryNode_of_mem hKsq hL.1 hqcum ey c hy
    have hout :
        crossingOutsideEndpoint (K := K) ex =
          crossingOutsideEndpoint (K := K) ey :=
      congrArg (fun d : ExtremalBoundaryNode N K => d.1)
        (hcx.symm.trans hcy)
    have he := fibreCrossingEdge_eq_of_same_contracted_nodes
      hL qx.2 ex ey hout hcomp
    subst he
    rfl
  · intro z hz
    replace hz : (extremalContractedIncidenceGraph N K L).Adj (Sum.inl c) z := hz
    cases z with
    | inl d =>
        exact (extremalContractedIncidenceGraph_not_adj_left_left c d hz).elim
    | inr R =>
        rcases (extremalContractedIncidenceGraph_adj_left_right c R).mp hz with
          ⟨e, hce, heR⟩
        let x : ExtremalNonbinaryCrossingEdge N K L := ⟨R.1, e⟩
        refine ⟨x, hce, ?_⟩
        have hpair :
            (⟨R.1, crossingActiveFibreRestrictionComponent (K := K) e⟩ :
                ExtremalRightNode N K L) = ⟨R.1, R.2⟩ := by
          rw [heR]
        exact congrArg Sum.inr hpair

/-- Forgetting the fibre tag is injective on crossings through one boundary node. -/
theorem extremalLeftNodeCrossingSet_underlying_injOn
    {N K : ℕ} {L : SimpleGraph (HVertex N)}
    (hL : IsLinearForest (reducedDivisorGraph N) L)
    (c : ExtremalBoundaryNode N K) :
    Set.InjOn
      (fun x : ExtremalNonbinaryCrossingEdge N K L => x.2.1)
      (extremalLeftNodeCrossingSet (K := K) (L := L) c) := by
  intro x hx y hy hxy
  obtain ⟨qx, ex⟩ := x
  obtain ⟨qy, ey⟩ := y
  have hxy' : (ex.1 : Sym2 (HVertex N)) = (ey.1 : Sym2 (HVertex N)) := hxy
  have hq : qx = qy := by
    by_contra hne
    have hval : (qx.1 : LargePrime N).val ≠ (qy.1 : LargePrime N).val := by
      intro hv
      refine hne (Subtype.ext ?_)
      obtain ⟨a, ha⟩ := qx
      obtain ⟨b, hb⟩ := qy
      cases a
      cases b
      simp_all
    have hdisj := crossingFinset_disjoint_of_ne hL hval
    rw [Finset.disjoint_left] at hdisj
    refine hdisj ex.2 ?_
    rw [hxy']
    exact ey.2
  subst hq
  have he : ex = ey := Subtype.ext hxy'
  subst he
  rfl

/-- Contracted degree at a boundary node cannot exceed its selected degree in `L`. -/
theorem extremalBoundaryNode_contractedDegree_le_selectedDegree
    {N K : ℕ} {L : SimpleGraph (HVertex N)}
    (hKsq : K * K ≤ N)
    (hL : IsLinearForest (reducedDivisorGraph N) L)
    (c : ExtremalBoundaryNode N K) :
    selectedDegree (extremalContractedIncidenceGraph N K L) (Sum.inl c) ≤
      selectedDegree L c.1 := by
  rw [← extremalLeftNodeCrossingSet_ncard_eq_selectedDegree hKsq hL c]
  have hmap :
      ∀ x ∈ extremalLeftNodeCrossingSet (K := K) (L := L) c,
        x.2.1 ∈ L.incidenceSet c.1 := by
    intro x hx
    have hcross : x.2.1 ∈ crossSet L (InFibre x.1.1) :=
      mem_crossingFinset.mp x.2.2
    exact ⟨hcross.1, hx⟩
  calc
    (extremalLeftNodeCrossingSet (K := K) (L := L) c).ncard
        ≤ (L.incidenceSet c.1).ncard :=
      Set.ncard_le_ncard_of_injOn
        (fun x : ExtremalNonbinaryCrossingEdge N K L => x.2.1)
        hmap
        (extremalLeftNodeCrossingSet_underlying_injOn hL c)
    _ = (L.neighborSet c.1).ncard :=
      Set.ncard_congr' (SimpleGraph.incidenceSetEquivNeighborSet L c.1)
    _ = selectedDegree L c.1 := rfl

/-- The left-hand degree sum is exactly the number of concrete contracted edges. -/
theorem extremalContractedLeftPart_sum_selectedDegree_eq_edgeCard
    {N K : ℕ} {L : SimpleGraph (HVertex N)} :
    (∑ z ∈ extremalContractedLeftPart N K L,
        selectedDegree (extremalContractedIncidenceGraph N K L) z) =
      edgeCard (extremalContractedIncidenceGraph N K L) := by
  classical
  let G := extremalContractedIncidenceGraph N K L
  have hbip := extremalContractedIncidenceGraph_isBipartiteWith
    (N := N) (K := K) (L := L)
  have hsum := SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges hbip
  change (∑ z ∈ extremalContractedLeftPart N K L,
      selectedDegree G z) = edgeCard G
  calc
    (∑ z ∈ extremalContractedLeftPart N K L, selectedDegree G z)
        = ∑ z ∈ extremalContractedLeftPart N K L, G.degree z := by
            apply Finset.sum_congr rfl
            intro z _
            exact (extremalContractedGraph_degree_eq_selectedDegree
              (N := N) (K := K) (L := L) z).symm
    _ = G.edgeFinset.card := hsum
    _ = edgeCard G := by
          unfold edgeCard
          rw [← Nat.card_coe_set_eq]
          simpa using (SimpleGraph.edgeFinset_card (G := G))

/--
**Corollary 3.11 left-degree clause:** every boundary node has contracted degree
exactly two at extremality.
-/
theorem extremalBoundaryNode_contractedDegree_eq_two
    {N K : ℕ} {L : SimpleGraph (HVertex N)}
    (hK : 2 ≤ K)
    (hKsq : K * K ≤ N)
    (hL : IsLinearForest (reducedDivisorGraph N) L)
    (hmax : edgeCard L = linearForestNumber (reducedDivisorGraph N))
    (hsat : cumulativeNonbinaryCount N K = K - 1)
    (c : ExtremalBoundaryNode N K) :
    selectedDegree (extremalContractedIncidenceGraph N K L) (Sum.inl c) = 2 := by
  classical
  have hKN : K ≤ N := by
    have hKK : K ≤ K * K := by nlinarith
    exact le_trans hKK hKsq
  have hle :
      ∀ d : ExtremalBoundaryNode N K,
        selectedDegree (extremalContractedIncidenceGraph N K L) (Sum.inl d) ≤ 2 := by
    intro d
    exact le_trans
      (extremalBoundaryNode_contractedDegree_le_selectedDegree hKsq hL d)
      (hL.2.2 d.1)
  have hsum :
      (∑ z ∈ extremalContractedLeftPart N K L,
          selectedDegree (extremalContractedIncidenceGraph N K L) z) =
        2 * (K - 1) := by
    rw [extremalContractedLeftPart_sum_selectedDegree_eq_edgeCard,
      extremalContractedIncidenceGraph_edgeCard_eq hKsq hL hmax hsat]
  by_contra hne
  have hlec := hle c
  have hlt :
      selectedDegree (extremalContractedIncidenceGraph N K L) (Sum.inl c) < 2 := by
    omega
  have hcpart : Sum.inl c ∈ extremalContractedLeftPart N K L := by simp
  have hstrict :
      (∑ z ∈ extremalContractedLeftPart N K L,
          selectedDegree (extremalContractedIncidenceGraph N K L) z) <
        ∑ _z ∈ extremalContractedLeftPart N K L, 2 := by
    apply Finset.sum_lt_sum
    · intro z hz
      rcases (mem_extremalContractedLeftPart z).mp hz with ⟨d, rfl⟩
      exact hle d
    · exact ⟨Sum.inl c, hcpart, hlt⟩
  have hcard :
      (extremalContractedLeftPart N K L).card = K - 1 := by
    simp [extremalContractedLeftPart, extremalBoundaryNode_card_eq hKN]
  rw [hsum] at hstrict
  have hconst :
      (∑ _z ∈ extremalContractedLeftPart N K L, 2) = 2 * (K - 1) := by
    simp [hcard, Nat.mul_comm]
  rw [hconst] at hstrict
  omega

/-- All degree-one vertices of the concrete contracted graph. -/
noncomputable def extremalContractedLeaves
    (N K : ℕ) (L : SimpleGraph (HVertex N)) :
    Finset (ExtremalBoundaryNode N K ⊕ ExtremalRightNode N K L) := by
  classical
  exact Finset.univ.filter fun z =>
    selectedDegree (extremalContractedIncidenceGraph N K L) z = 1

/-- The full leaf set is exactly the already-defined right leaf set. -/
theorem extremalContractedLeaves_eq_rightLeaves
    {N K : ℕ} {L : SimpleGraph (HVertex N)}
    (hK : 2 ≤ K)
    (hKsq : K * K ≤ N)
    (hL : IsLinearForest (reducedDivisorGraph N) L)
    (hmax : edgeCard L = linearForestNumber (reducedDivisorGraph N))
    (hsat : cumulativeNonbinaryCount N K = K - 1) :
    extremalContractedLeaves N K L = extremalContractedRightLeaves N K L := by
  classical
  ext z
  cases z with
  | inl c =>
      have hc := extremalBoundaryNode_contractedDegree_eq_two
        hK hKsq hL hmax hsat c
      simp [extremalContractedLeaves, extremalContractedRightLeaves,
        extremalContractedRightPart, hc]
  | inr R =>
      simp [extremalContractedLeaves, extremalContractedRightLeaves,
        extremalContractedRightPart]

/--
**Corollary 3.11 total leaf count:** the concrete contracted incidence forest
has exactly `2a` leaves, not merely `2a` degree-one nodes on the right.
-/
theorem extremalContractedLeaves_card_eq_two_mul_split
    {N K : ℕ} {L : SimpleGraph (HVertex N)}
    (hK : 2 ≤ K)
    (hKsq : K * K ≤ N)
    (hL : IsLinearForest (reducedDivisorGraph N) L)
    (hmax : edgeCard L = linearForestNumber (reducedDivisorGraph N))
    (hsat : cumulativeNonbinaryCount N K = K - 1) :
    (extremalContractedLeaves N K L).card =
      2 * splitNonbinaryFibreCount N K L := by
  rw [extremalContractedLeaves_eq_rightLeaves hK hKsq hL hmax hsat]
  exact extremalContractedRightLeaves_card_eq_two_mul_split
    hKsq hL hmax hsat

end DivisorF
