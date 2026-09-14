import DivisorF.ExtremalLeafCounting
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Concrete extremal contracted incidence graph

This module assembles the actual bipartite incidence graph used in the original
Corollary 3.11.  Left nodes are the saturated boundary vertices.  Right nodes
are the active post-cut restriction components, tagged by their nonbinary
large-prime fibre.  An incidence edge records one selected crossing whose
boundary endpoint is the left node and whose fibre endpoint lies in the right
component.

The tagging is deliberate: it preserves the fibre ownership already proved
unique for boundary-incidence edges, while the post-cut component records the
contraction geometry.  The remaining theorem-objective after this module is to
show that this concrete graph is acyclic and that its right degrees realize the
one-node/two-node fibre profile.
-/

namespace DivisorF

open SimpleGraph

/-- Boundary singleton nodes of the extremal contracted incidence graph. -/
def ExtremalBoundaryNode (N K : ℕ) :=
  {c : HVertex N // c ∈ smallEndpointVertices N K}

/--
Right nodes are active post-cut restriction components, tagged by the
nonbinary fibre that owns their selected crossings.
-/
def ExtremalRightNode
    (N K : ℕ) (L : SimpleGraph (HVertex N)) :=
  Σ q : {q : LargePrime N // q ∈ cumulativeLevelFibres N K 2},
    ActiveFibreRestrictionComponent (K := K) q.1 L

noncomputable instance extremalBoundaryNodeFintype (N K : ℕ) :
    Fintype (ExtremalBoundaryNode N K) :=
  inferInstanceAs (Fintype {c : HVertex N // c ∈ smallEndpointVertices N K})

noncomputable instance extremalRightNodeFintype
    (N K : ℕ) (L : SimpleGraph (HVertex N)) :
    Fintype (ExtremalRightNode N K L) :=
  inferInstanceAs
    (Fintype (Σ q : {q : LargePrime N // q ∈ cumulativeLevelFibres N K 2},
      ActiveFibreRestrictionComponent (K := K) q.1 L))

/--
The concrete contracted incidence graph.  The relation is written only in the
left-to-right direction; `SimpleGraph.fromRel` supplies symmetry and removes
loops.
-/
noncomputable def extremalContractedIncidenceGraph
    (N K : ℕ) (L : SimpleGraph (HVertex N)) :
    SimpleGraph (ExtremalBoundaryNode N K ⊕ ExtremalRightNode N K L) :=
  SimpleGraph.fromRel fun x y =>
    match x, y with
    | Sum.inl c, Sum.inr R =>
        ∃ e : FibreCrossingEdge (_K := K) R.1.1 L,
          c.1 ∈ e.1 ∧
            crossingActiveFibreRestrictionComponent (K := K) e = R.2
    | _, _ => False

@[simp]
theorem extremalContractedIncidenceGraph_adj_left_right
    {N K : ℕ} {L : SimpleGraph (HVertex N)}
    (c : ExtremalBoundaryNode N K) (R : ExtremalRightNode N K L) :
    (extremalContractedIncidenceGraph N K L).Adj (Sum.inl c) (Sum.inr R) ↔
      ∃ e : FibreCrossingEdge (_K := K) R.1.1 L,
        c.1 ∈ e.1 ∧
          crossingActiveFibreRestrictionComponent (K := K) e = R.2 := by
  simp [extremalContractedIncidenceGraph]

@[simp]
theorem extremalContractedIncidenceGraph_adj_right_left
    {N K : ℕ} {L : SimpleGraph (HVertex N)}
    (R : ExtremalRightNode N K L) (c : ExtremalBoundaryNode N K) :
    (extremalContractedIncidenceGraph N K L).Adj (Sum.inr R) (Sum.inl c) ↔
      ∃ e : FibreCrossingEdge (_K := K) R.1.1 L,
        c.1 ∈ e.1 ∧
          crossingActiveFibreRestrictionComponent (K := K) e = R.2 := by
  rw [SimpleGraph.adj_comm]
  exact extremalContractedIncidenceGraph_adj_left_right c R

@[simp]
theorem extremalContractedIncidenceGraph_not_adj_left_left
    {N K : ℕ} {L : SimpleGraph (HVertex N)}
    (c d : ExtremalBoundaryNode N K) :
    ¬(extremalContractedIncidenceGraph N K L).Adj (Sum.inl c) (Sum.inl d) := by
  simp [extremalContractedIncidenceGraph]

@[simp]
theorem extremalContractedIncidenceGraph_not_adj_right_right
    {N K : ℕ} {L : SimpleGraph (HVertex N)}
    (R S : ExtremalRightNode N K L) :
    ¬(extremalContractedIncidenceGraph N K L).Adj (Sum.inr R) (Sum.inr S) := by
  simp [extremalContractedIncidenceGraph]

/-- Every contracted incidence edge is genuinely bipartite. -/
theorem extremalContractedIncidenceGraph_adj_cases
    {N K : ℕ} {L : SimpleGraph (HVertex N)}
    {x y : ExtremalBoundaryNode N K ⊕ ExtremalRightNode N K L}
    (hxy : (extremalContractedIncidenceGraph N K L).Adj x y) :
    (∃ c R, x = Sum.inl c ∧ y = Sum.inr R) ∨
      (∃ R c, x = Sum.inr R ∧ y = Sum.inl c) := by
  cases x with
  | inl c =>
      cases y with
      | inl d =>
          exact (extremalContractedIncidenceGraph_not_adj_left_left c d hxy).elim
      | inr R =>
          exact Or.inl ⟨c, R, rfl, rfl⟩
  | inr R =>
      cases y with
      | inl c =>
          exact Or.inr ⟨R, c, rfl, rfl⟩
      | inr S =>
          exact (extremalContractedIncidenceGraph_not_adj_right_right R S hxy).elim

/-- The left side has exactly `K-1` nodes in the manuscript range. -/
theorem extremalBoundaryNode_card_eq
    {N K : ℕ} (hKN : K ≤ N) :
    Fintype.card (ExtremalBoundaryNode N K) = K - 1 := by
  change Fintype.card {c : HVertex N // c ∈ smallEndpointVertices N K} = K - 1
  rw [Fintype.card_coe]
  exact smallEndpointVertices_card_eq hKN

/--
The right-node cardinality is the sum of the active-component cardinalities of
the nonbinary fibres.  This is the concrete sigma-type realization of the
count already proved fibre-by-fibre.
-/
theorem extremalRightNode_card_eq_sum
    {N K : ℕ} {L : SimpleGraph (HVertex N)} :
    Fintype.card (ExtremalRightNode N K L) =
      ∑ q ∈ cumulativeLevelFibres N K 2,
        activeFibreRestrictionComponentCount (K := K) q L := by
  classical
  have hsigma :
      Fintype.card (ExtremalRightNode N K L) =
        ∑ q : {q : LargePrime N // q ∈ cumulativeLevelFibres N K 2},
          Fintype.card (ActiveFibreRestrictionComponent (K := K) q.1 L) :=
    Fintype.card_sigma
  rw [hsigma]
  exact Finset.sum_coe_sort (cumulativeLevelFibres N K 2)
    (fun q => activeFibreRestrictionComponentCount (K := K) q L)

/-- **Corollary 3.11 concrete right-node count:** `K-1+a`. -/
theorem extremalRightNode_card_eq_boundary_add_split
    {N K : ℕ} {L : SimpleGraph (HVertex N)}
    (hL : IsLinearForest (reducedDivisorGraph N) L)
    (hmax : edgeCard L = linearForestNumber (reducedDivisorGraph N))
    (hsat : cumulativeNonbinaryCount N K = K - 1) :
    Fintype.card (ExtremalRightNode N K L) =
      (K - 1) + splitNonbinaryFibreCount N K L := by
  rw [extremalRightNode_card_eq_sum,
    sum_activeFibreRestrictionComponentCount_eq_boundary_add_split hL hmax hsat]

/--
The concrete incidence graph has the exact vertex count predicted in
Corollary 3.11 before any Euler argument is used.
-/
theorem extremalContractedIncidenceGraph_vertex_card_eq
    {N K : ℕ} {L : SimpleGraph (HVertex N)}
    (hKN : K ≤ N)
    (hL : IsLinearForest (reducedDivisorGraph N) L)
    (hmax : edgeCard L = linearForestNumber (reducedDivisorGraph N))
    (hsat : cumulativeNonbinaryCount N K = K - 1) :
    Fintype.card (ExtremalBoundaryNode N K ⊕ ExtremalRightNode N K L) =
      2 * (K - 1) + splitNonbinaryFibreCount N K L := by
  rw [Fintype.card_sum, extremalBoundaryNode_card_eq hKN,
    extremalRightNode_card_eq_boundary_add_split hL hmax hsat]
  omega

end DivisorF
