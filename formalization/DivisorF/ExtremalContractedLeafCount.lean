import DivisorF.ExtremalContractedDegrees
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Concrete right-leaf count in the extremal contracted incidence graph

This module turns the already-realized right-node degree dichotomy into the
actual graph-theoretic leaf count needed by the original Corollary 3.11.
The concrete incidence graph is bipartite by construction.  Therefore the sum
of the degrees on its right side is exactly the number of contracted edges.
Combining this with the facts that every active right node has degree one or
two, that there are `K-1+a` right nodes, and that there are `2(K-1)` edges
forces exactly `2a` degree-one right nodes.
-/

namespace DivisorF

/-- The concrete contracted incidence graph is finite but not decidable by
computation; fix one classical decision procedure for the whole module so that
`SimpleGraph.degree` and `selectedDegree` are formed with the same instance. -/
noncomputable local instance extremalContractedIncidenceGraphDecidableRel
    {N K : ℕ} {L : SimpleGraph (HVertex N)} :
    DecidableRel (extremalContractedIncidenceGraph N K L).Adj :=
  Classical.decRel _

open SimpleGraph

/-- The left part of the concrete extremal incidence graph. -/
noncomputable def extremalContractedLeftPart
    (N K : ℕ) (L : SimpleGraph (HVertex N)) :
    Finset (ExtremalBoundaryNode N K ⊕ ExtremalRightNode N K L) := by
  classical
  exact (Finset.univ : Finset (ExtremalBoundaryNode N K)).disjSum ∅

/-- The right part of the concrete extremal incidence graph. -/
noncomputable def extremalContractedRightPart
    (N K : ℕ) (L : SimpleGraph (HVertex N)) :
    Finset (ExtremalBoundaryNode N K ⊕ ExtremalRightNode N K L) := by
  classical
  exact (∅ : Finset (ExtremalBoundaryNode N K)).disjSum
    (Finset.univ : Finset (ExtremalRightNode N K L))

@[simp]
theorem mem_extremalContractedLeftPart
    {N K : ℕ} {L : SimpleGraph (HVertex N)}
    (z : ExtremalBoundaryNode N K ⊕ ExtremalRightNode N K L) :
    z ∈ extremalContractedLeftPart N K L ↔
      ∃ c : ExtremalBoundaryNode N K, z = Sum.inl c := by
  classical
  cases z <;> simp [extremalContractedLeftPart]

@[simp]
theorem mem_extremalContractedRightPart
    {N K : ℕ} {L : SimpleGraph (HVertex N)}
    (z : ExtremalBoundaryNode N K ⊕ ExtremalRightNode N K L) :
    z ∈ extremalContractedRightPart N K L ↔
      ∃ R : ExtremalRightNode N K L, z = Sum.inr R := by
  classical
  cases z <;> simp [extremalContractedRightPart]

/-- The concrete contracted graph is bipartite in its declared left/right parts. -/
theorem extremalContractedIncidenceGraph_isBipartiteWith
    {N K : ℕ} {L : SimpleGraph (HVertex N)} :
    (extremalContractedIncidenceGraph N K L).IsBipartiteWith
      (↑(extremalContractedLeftPart N K L) :
        Set (ExtremalBoundaryNode N K ⊕ ExtremalRightNode N K L))
      (↑(extremalContractedRightPart N K L) :
        Set (ExtremalBoundaryNode N K ⊕ ExtremalRightNode N K L)) := by
  classical
  refine ⟨?_, ?_⟩
  · rw [Set.disjoint_left]
    intro z hzL hzR
    rcases (mem_extremalContractedLeftPart z).mp hzL with ⟨c, rfl⟩
    simp at hzR
  · intro x y hxy
    rcases extremalContractedIncidenceGraph_adj_cases hxy with
      ⟨c, R, rfl, rfl⟩ | ⟨R, c, rfl, rfl⟩
    · exact Or.inl ⟨by simp, by simp⟩
    · exact Or.inr ⟨by simp, by simp⟩

/-- `SimpleGraph.degree` agrees with the project's `selectedDegree` here. -/
theorem extremalContractedGraph_degree_eq_selectedDegree
    {N K : ℕ} {L : SimpleGraph (HVertex N)}
    (z : ExtremalBoundaryNode N K ⊕ ExtremalRightNode N K L) :
    (extremalContractedIncidenceGraph N K L).degree z =
      selectedDegree (extremalContractedIncidenceGraph N K L) z := by
  classical
  unfold SimpleGraph.degree selectedDegree SimpleGraph.neighborFinset
  exact (Set.ncard_eq_toFinset_card' _).symm

/-- The right-hand degree sum is exactly the number of contracted edges. -/
theorem extremalContractedRightPart_sum_selectedDegree_eq_edgeCard
    {N K : ℕ} {L : SimpleGraph (HVertex N)} :
    (∑ z ∈ extremalContractedRightPart N K L,
        selectedDegree (extremalContractedIncidenceGraph N K L) z) =
      edgeCard (extremalContractedIncidenceGraph N K L) := by
  classical
  let G := extremalContractedIncidenceGraph N K L
  have hbip := extremalContractedIncidenceGraph_isBipartiteWith
    (N := N) (K := K) (L := L)
  have hsum := SimpleGraph.isBipartiteWith_sum_degrees_eq_card_edges' hbip
  change (∑ z ∈ extremalContractedRightPart N K L, selectedDegree G z) =
    edgeCard G
  calc
    (∑ z ∈ extremalContractedRightPart N K L, selectedDegree G z)
        = ∑ z ∈ extremalContractedRightPart N K L, G.degree z := by
            apply Finset.sum_congr rfl
            intro z _
            exact (extremalContractedGraph_degree_eq_selectedDegree
              (N := N) (K := K) (L := L) z).symm
    _ = G.edgeFinset.card := hsum
    _ = edgeCard G := by
          unfold edgeCard
          rw [← Nat.card_coe_set_eq]
          simpa using (SimpleGraph.edgeFinset_card (G := G))

/-- The concrete right part has exactly `K-1+a` vertices. -/
theorem extremalContractedRightPart_card_eq_boundary_add_split
    {N K : ℕ} {L : SimpleGraph (HVertex N)}
    (hL : IsLinearForest (reducedDivisorGraph N) L)
    (hmax : edgeCard L = linearForestNumber (reducedDivisorGraph N))
    (hsat : cumulativeNonbinaryCount N K = K - 1) :
    (extremalContractedRightPart N K L).card =
      (K - 1) + splitNonbinaryFibreCount N K L := by
  classical
  simp [extremalContractedRightPart,
    extremalRightNode_card_eq_boundary_add_split hL hmax hsat]

/-- Actual degree-one vertices on the right side of the concrete graph. -/
noncomputable def extremalContractedRightLeaves
    (N K : ℕ) (L : SimpleGraph (HVertex N)) :
    Finset (ExtremalBoundaryNode N K ⊕ ExtremalRightNode N K L) := by
  classical
  exact (extremalContractedRightPart N K L).filter fun z =>
    selectedDegree (extremalContractedIncidenceGraph N K L) z = 1

/-- Every non-leaf right node has degree exactly two. -/
theorem selectedDegree_eq_two_of_mem_rightPart_not_leaf
    {N K : ℕ} {L : SimpleGraph (HVertex N)}
    (hKsq : K * K ≤ N)
    (hL : IsLinearForest (reducedDivisorGraph N) L)
    (hmax : edgeCard L = linearForestNumber (reducedDivisorGraph N))
    (hsat : cumulativeNonbinaryCount N K = K - 1)
    {z : ExtremalBoundaryNode N K ⊕ ExtremalRightNode N K L}
    (hzR : z ∈ extremalContractedRightPart N K L)
    (hzNot : z ∉ extremalContractedRightLeaves N K L) :
    selectedDegree (extremalContractedIncidenceGraph N K L) z = 2 := by
  rcases (mem_extremalContractedRightPart z).mp hzR with ⟨R, rfl⟩
  have hcases := extremalRightNode_selectedDegree_eq_one_or_two
    hKsq hL hmax hsat R
  rcases hcases with hone | htwo
  · exfalso
    apply hzNot
    simp [extremalContractedRightLeaves, hone]
  · exact htwo

/--
**Corollary 3.11 concrete leaf count:** if `a` nonbinary fibres split, the
concrete contracted incidence graph has exactly `2a` degree-one right nodes.
-/
theorem extremalContractedRightLeaves_card_eq_two_mul_split
    {N K : ℕ} {L : SimpleGraph (HVertex N)}
    (hKsq : K * K ≤ N)
    (hL : IsLinearForest (reducedDivisorGraph N) L)
    (hmax : edgeCard L = linearForestNumber (reducedDivisorGraph N))
    (hsat : cumulativeNonbinaryCount N K = K - 1) :
    (extremalContractedRightLeaves N K L).card =
      2 * splitNonbinaryFibreCount N K L := by
  classical
  let G := extremalContractedIncidenceGraph N K L
  let Rpart := extremalContractedRightPart N K L
  let Leaves := extremalContractedRightLeaves N K L
  let NonLeaves := Rpart.filter fun z =>
    selectedDegree G z ≠ 1
  have hleafSum :
      (∑ z ∈ Leaves, selectedDegree G z) = Leaves.card := by
    calc
      (∑ z ∈ Leaves, selectedDegree G z) = ∑ _z ∈ Leaves, 1 := by
        apply Finset.sum_congr rfl
        intro z hz
        exact (Finset.mem_filter.mp hz).2
      _ = Leaves.card := by simp
  have hnonleafSum :
      (∑ z ∈ NonLeaves, selectedDegree G z) = 2 * NonLeaves.card := by
    calc
      (∑ z ∈ NonLeaves, selectedDegree G z) = ∑ _z ∈ NonLeaves, 2 := by
        apply Finset.sum_congr rfl
        intro z hz
        have hz' := Finset.mem_filter.mp hz
        exact selectedDegree_eq_two_of_mem_rightPart_not_leaf
          hKsq hL hmax hsat hz'.1 (by
            intro hmem
            exact hz'.2 (Finset.mem_filter.mp hmem).2)
      _ = 2 * NonLeaves.card := by simp [Nat.mul_comm]
  have hsumSplit :
      (∑ z ∈ Leaves, selectedDegree G z) +
          (∑ z ∈ NonLeaves, selectedDegree G z) =
        ∑ z ∈ Rpart, selectedDegree G z := by
    simpa [Leaves, NonLeaves, Rpart, extremalContractedRightLeaves] using
      (Finset.sum_filter_add_sum_filter_not Rpart
        (fun z => selectedDegree G z = 1)
        (fun z => selectedDegree G z))
  have hcardSplit : Leaves.card + NonLeaves.card = Rpart.card := by
    simpa [Leaves, NonLeaves, Rpart, extremalContractedRightLeaves] using
      (Finset.card_filter_add_card_filter_not (s := Rpart)
        (fun z => selectedDegree G z = 1))
  have hdegreeSum :
      (∑ z ∈ Rpart, selectedDegree G z) = 2 * (K - 1) := by
    change (∑ z ∈ extremalContractedRightPart N K L,
      selectedDegree (extremalContractedIncidenceGraph N K L) z) =
        2 * (K - 1)
    rw [extremalContractedRightPart_sum_selectedDegree_eq_edgeCard,
      extremalContractedIncidenceGraph_edgeCard_eq hKsq hL hmax hsat]
  have hrightCard :
      Rpart.card = (K - 1) + splitNonbinaryFibreCount N K L := by
    exact extremalContractedRightPart_card_eq_boundary_add_split hL hmax hsat
  rw [hleafSum, hnonleafSum] at hsumSplit
  have hgoal : Leaves.card = 2 * splitNonbinaryFibreCount N K L := by
    omega
  exact hgoal

end DivisorF
