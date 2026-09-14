import DivisorF.ExtremalContractedTotalLeaves
import DivisorF.FiniteForestEuler
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Exact connected-component count for the extremal contracted incidence graph

This closes the remaining numerical statement of the original Corollary 3.11.
The concrete contracted graph is already acyclic, has
`2(K-1)+a` vertices and `2(K-1)` edges.  The standard finite-forest Euler
identity therefore gives exactly `a` connected components.
-/

namespace DivisorF

open SimpleGraph

/--
**Corollary 3.11 connected-component count:** the concrete extremal incidence
forest has exactly as many connected components as split nonbinary fibres.
-/
theorem extremalContractedIncidenceGraph_connectedComponent_card_eq_split
    {N K : ℕ} {L : SimpleGraph (HVertex N)}
    (hK : 2 ≤ K)
    (hKsq : K * K ≤ N)
    (hL : IsLinearForest (reducedDivisorGraph N) L)
    (hmax : edgeCard L = linearForestNumber (reducedDivisorGraph N))
    (hsat : cumulativeNonbinaryCount N K = K - 1) :
    Fintype.card
        (extremalContractedIncidenceGraph N K L).ConnectedComponent =
      splitNonbinaryFibreCount N K L := by
  let G := extremalContractedIncidenceGraph N K L
  have hKN : K ≤ N := by
    have hKK : K ≤ K * K := by nlinarith
    exact le_trans hKK hKsq
  have hacyc : G.IsAcyclic :=
    extremalContractedIncidenceGraph_isAcyclic hKsq hL
  have heuler := card_connectedComponent_add_edgeCard_eq_fintypeCard G hacyc
  have hedge : edgeCard G = 2 * (K - 1) :=
    extremalContractedIncidenceGraph_edgeCard_eq hKsq hL hmax hsat
  have hvert :
      Fintype.card (ExtremalBoundaryNode N K ⊕ ExtremalRightNode N K L) =
        2 * (K - 1) + splitNonbinaryFibreCount N K L :=
    extremalContractedIncidenceGraph_vertex_card_eq hKN hL hmax hsat
  dsimp [G] at heuler
  rw [hedge, hvert] at heuler
  omega

/--
Literal graph-theoretic package of Corollary 3.11: acyclicity, exact component
count, exact total leaf count, and the forced existence of a split fibre.
-/
theorem extremalContractedIncidence_corollary
    {N K : ℕ} {L : SimpleGraph (HVertex N)}
    (hK : 2 ≤ K)
    (hKsq : K * K ≤ N)
    (hL : IsLinearForest (reducedDivisorGraph N) L)
    (hmax : edgeCard L = linearForestNumber (reducedDivisorGraph N))
    (hsat : cumulativeNonbinaryCount N K = K - 1) :
    (extremalContractedIncidenceGraph N K L).IsAcyclic ∧
      Fintype.card
          (extremalContractedIncidenceGraph N K L).ConnectedComponent =
        splitNonbinaryFibreCount N K L ∧
      (extremalContractedLeaves N K L).card =
        2 * splitNonbinaryFibreCount N K L ∧
      1 ≤ splitNonbinaryFibreCount N K L := by
  refine ⟨extremalContractedIncidenceGraph_isAcyclic hKsq hL, ?_, ?_, ?_⟩
  · exact extremalContractedIncidenceGraph_connectedComponent_card_eq_split
      hK hKsq hL hmax hsat
  · exact extremalContractedLeaves_card_eq_two_mul_split
      hK hKsq hL hmax hsat
  · exact one_le_splitNonbinaryFibreCount_of_extremal
      hK hKsq hL hmax hsat

/-- Wrapper exposing the manuscript range `K ≤ floor(sqrt N)`. -/
theorem extremalContractedIncidence_corollary_le_sqrt
    {N K : ℕ} {L : SimpleGraph (HVertex N)}
    (hK : 2 ≤ K)
    (hKsqrt : K ≤ Nat.sqrt N)
    (hL : IsLinearForest (reducedDivisorGraph N) L)
    (hmax : edgeCard L = linearForestNumber (reducedDivisorGraph N))
    (hsat : cumulativeNonbinaryCount N K = K - 1) :
    (extremalContractedIncidenceGraph N K L).IsAcyclic ∧
      Fintype.card
          (extremalContractedIncidenceGraph N K L).ConnectedComponent =
        splitNonbinaryFibreCount N K L ∧
      (extremalContractedLeaves N K L).card =
        2 * splitNonbinaryFibreCount N K L ∧
      1 ≤ splitNonbinaryFibreCount N K L := by
  have hKsq : K * K ≤ N := Nat.le_sqrt.mp hKsqrt
  exact extremalContractedIncidence_corollary hK hKsq hL hmax hsat

end DivisorF
