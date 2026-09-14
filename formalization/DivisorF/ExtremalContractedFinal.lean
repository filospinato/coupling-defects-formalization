import DivisorF.ExtremalContractedAcyclic
import DivisorF.ExtremalContractedLeafCount
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Final nonempty consequence of the extremal contracted incidence forest

This module packages the concrete counting and acyclicity already proved for
Corollary 3.11 and closes its qualitative conclusion: in the canonical range
`2 ≤ K ≤ floor(sqrt N)`, at least one nonbinary fibre must split its two
crossings between distinct fibre-restriction paths.

The only general graph-theoretic support needed here is the standard finite
forest inequality `|E| < |V|` for a nonempty acyclic graph.  We derive it from
mathlib's spanning-tree extension theorem rather than making it part of the
project's mathematical target.
-/

namespace DivisorF

open SimpleGraph

/--
Standard support lemma: a finite nonempty acyclic simple graph has strictly
fewer edges than vertices.
-/
theorem edgeCard_lt_fintypeCard_of_isAcyclic
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (hacyc : G.IsAcyclic) :
    edgeCard G < Fintype.card V := by
  classical
  obtain ⟨T, hGT, -, hTree⟩ :=
    (SimpleGraph.connected_top (V := V)).exists_isTree_le_of_le_of_isAcyclic
      (show G ≤ (⊤ : SimpleGraph V) from le_top) hacyc
  have hmono : G.edgeFinset.card ≤ T.edgeFinset.card :=
    Finset.card_le_card (SimpleGraph.edgeFinset_mono hGT)
  have htree : T.edgeFinset.card + 1 = Fintype.card V :=
    hTree.card_edgeFinset
  have hGcard : edgeCard G = G.edgeFinset.card := by
    unfold edgeCard
    rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
    exact SimpleGraph.card_edgeSet
  rw [hGcard]
  omega

/--
**Corollary 3.11 qualitative conclusion.**  In the extremal case, at least one
nonbinary fibre splits its two retained crossings between two distinct active
fibre-restriction components.

The hypotheses are the natural-number form of the manuscript range, with
`K*K ≤ N` used by the already-checked concrete contraction lemmas.
-/
theorem one_le_splitNonbinaryFibreCount_of_extremal
    {N K : ℕ} {L : SimpleGraph (HVertex N)}
    (hK : 2 ≤ K)
    (hKsq : K * K ≤ N)
    (hL : IsLinearForest (reducedDivisorGraph N) L)
    (hmax : edgeCard L = linearForestNumber (reducedDivisorGraph N))
    (hsat : cumulativeNonbinaryCount N K = K - 1) :
    1 ≤ splitNonbinaryFibreCount N K L := by
  let G := extremalContractedIncidenceGraph N K L
  have hKN : K ≤ N := by
    have hKK : K ≤ K * K := by nlinarith
    exact le_trans hKK hKsq
  have hVcard :
      Fintype.card (ExtremalBoundaryNode N K ⊕ ExtremalRightNode N K L) =
        2 * (K - 1) + splitNonbinaryFibreCount N K L :=
    extremalContractedIncidenceGraph_vertex_card_eq hKN hL hmax hsat
  have hVpos :
      0 < Fintype.card
        (ExtremalBoundaryNode N K ⊕ ExtremalRightNode N K L) := by
    rw [hVcard]
    omega
  letI : Nonempty (ExtremalBoundaryNode N K ⊕ ExtremalRightNode N K L) :=
    Fintype.card_pos_iff.mp hVpos
  have hlt :
      edgeCard G <
        Fintype.card (ExtremalBoundaryNode N K ⊕ ExtremalRightNode N K L) :=
    edgeCard_lt_fintypeCard_of_isAcyclic G
      (extremalContractedIncidenceGraph_isAcyclic hKsq hL)
  have hE : edgeCard G = 2 * (K - 1) := by
    exact extremalContractedIncidenceGraph_edgeCard_eq hKsq hL hmax hsat
  rw [hE, hVcard] at hlt
  omega

/--
Canonical-range wrapper for the final conclusion, exposing the manuscript's
`K ≤ floor(sqrt N)` hypothesis directly.
-/
theorem one_le_splitNonbinaryFibreCount_of_extremal_le_sqrt
    {N K : ℕ} {L : SimpleGraph (HVertex N)}
    (hK : 2 ≤ K)
    (hKsqrt : K ≤ Nat.sqrt N)
    (hL : IsLinearForest (reducedDivisorGraph N) L)
    (hmax : edgeCard L = linearForestNumber (reducedDivisorGraph N))
    (hsat : cumulativeNonbinaryCount N K = K - 1) :
    1 ≤ splitNonbinaryFibreCount N K L := by
  exact one_le_splitNonbinaryFibreCount_of_extremal
    hK (Nat.le_sqrt.mp hKsqrt) hL hmax hsat

/--
Concrete extremal data already realized by the contracted incidence graph:
acyclicity, exact vertex and edge counts, exact right-leaf count, and the
nonempty split conclusion.
-/
theorem extremalContractedIncidence_summary
    {N K : ℕ} {L : SimpleGraph (HVertex N)}
    (hK : 2 ≤ K)
    (hKsqrt : K ≤ Nat.sqrt N)
    (hL : IsLinearForest (reducedDivisorGraph N) L)
    (hmax : edgeCard L = linearForestNumber (reducedDivisorGraph N))
    (hsat : cumulativeNonbinaryCount N K = K - 1) :
    let a := splitNonbinaryFibreCount N K L
    (extremalContractedIncidenceGraph N K L).IsAcyclic ∧
      Fintype.card (ExtremalBoundaryNode N K ⊕ ExtremalRightNode N K L) =
        2 * (K - 1) + a ∧
      edgeCard (extremalContractedIncidenceGraph N K L) = 2 * (K - 1) ∧
      (extremalContractedRightLeaves N K L).card = 2 * a ∧
      1 ≤ a := by
  dsimp
  have hKsq : K * K ≤ N := Nat.le_sqrt.mp hKsqrt
  have hKN : K ≤ N := by
    have hKK : K ≤ K * K := by nlinarith
    exact le_trans hKK hKsq
  refine ⟨extremalContractedIncidenceGraph_isAcyclic hKsq hL, ?_⟩
  refine ⟨extremalContractedIncidenceGraph_vertex_card_eq hKN hL hmax hsat, ?_⟩
  refine ⟨extremalContractedIncidenceGraph_edgeCard_eq hKsq hL hmax hsat, ?_⟩
  refine ⟨extremalContractedRightLeaves_card_eq_two_mul_split hKsq hL hmax hsat, ?_⟩
  exact one_le_splitNonbinaryFibreCount_of_extremal hK hKsq hL hmax hsat

end DivisorF
