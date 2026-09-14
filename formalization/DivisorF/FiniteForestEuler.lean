import DivisorF.LinearForest
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Finite forest Euler bridge

Standard support for the project-specific extremal incidence theorem. Mathlib
already proves that every connected component of an acyclic graph is a tree and
that a finite tree satisfies `|E| + 1 = |V|`. This file packages the resulting
finite-forest identity in the exact form needed by Corollary 3.11.

Two `Fintype` instances compete on `G.ConnectedComponent`: mathlib's canonical
`Quotient.fintype` one, available exactly when `DecidableEq V` and
`DecidableRel G.Adj` are, and the noncomputable `SetLike` fallback available
from `Fintype V` alone. The componentwise degree bookkeeping needs the former,
while callers of the final identity supply only `Fintype V` and therefore see
the latter. So the argument is carried out under the decidable hypotheses and
the exported statement is transported across the two instances through
`Nat.card`, which takes no instance at all.
-/

namespace DivisorF

open SimpleGraph
open scoped BigOperators

/-- Every vertex is equivalently a vertex tagged by its connected component. -/
noncomputable def vertexConnectedComponentSigmaEquiv
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) :
    V ≃ Σ C : G.ConnectedComponent, C := by
  classical
  refine
    { toFun := fun v =>
        ⟨G.connectedComponentMk v,
          ⟨v, SimpleGraph.ConnectedComponent.connectedComponentMk_mem⟩⟩
      invFun := fun x => x.2.1
      left_inv := ?_
      right_inv := ?_ }
  · intro v
    rfl
  · rintro ⟨C, ⟨v, hv⟩⟩
    have hC : G.connectedComponentMk v = C :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff C v).mp hv
    subst C
    rfl

section Decidable

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Membership in a component through the `SetLike` coercion is the same
decision as membership in its support; naming mathlib's instance keeps the two
spellings on one decision procedure instead of two defeq ones. -/
local instance connectedComponentSetLikeDecidablePred
    (C : G.ConnectedComponent) : DecidablePred (fun v => v ∈ C) :=
  fun v => SimpleGraph.instDecidableMemSupp G C v

/-- The graph induced on one connected component inherits the ambient
adjacency decision procedure; `toSimpleGraph` is not reducible, so this is
stated rather than found by unfolding. -/
local instance connectedComponentToSimpleGraphDecidableRel
    (C : G.ConnectedComponent) : DecidableRel C.toSimpleGraph.Adj :=
  fun a b => ‹DecidableRel G.Adj› a.1 b.1

/-- The connected-component supports partition the finite vertex type. -/
theorem sum_connectedComponent_card_eq_fintypeCard
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∑ C : G.ConnectedComponent, Fintype.card C) = Fintype.card V := by
  have hcard := Fintype.card_congr (vertexConnectedComponentSigmaEquiv G)
  rw [Fintype.card_sigma] at hcard
  exact hcard.symm

/-- Inducing on a full connected component does not change degrees. -/
theorem connectedComponent_toSimpleGraph_degree_eq
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (C : G.ConnectedComponent) (v : C) :
    C.toSimpleGraph.degree v = G.degree v.1 := by
  have hsubset : G.neighborSet v.1 ⊆ C.supp := by
    intro w hw
    rw [SimpleGraph.mem_neighborSet] at hw
    exact C.mem_supp_of_adj_mem_supp v.2 hw
  have hdegree :
      (G.induce C.supp).degree ⟨v.1, v.2⟩ = G.degree v.1 :=
    SimpleGraph.degree_induce_of_neighborSet_subset hsubset
  exact hdegree

/-- Summing degrees componentwise recovers the global degree sum. -/
theorem sum_connectedComponent_sum_degree_eq
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∑ C : G.ConnectedComponent, ∑ v : C, C.toSimpleGraph.degree v) =
      ∑ v : V, G.degree v := by
  calc
    (∑ C : G.ConnectedComponent, ∑ v : C, C.toSimpleGraph.degree v)
        = ∑ C : G.ConnectedComponent, ∑ v : C, G.degree v.1 := by
            apply Fintype.sum_congr
            intro C
            apply Fintype.sum_congr
            intro v
            exact connectedComponent_toSimpleGraph_degree_eq G C v
    _ = ∑ x : (Σ C : G.ConnectedComponent, C), G.degree x.2.1 :=
          (Fintype.sum_sigma'
            (fun (C : G.ConnectedComponent) (v : C) => G.degree v.1)).symm
    _ = ∑ v : V, G.degree v := by
          exact (vertexConnectedComponentSigmaEquiv G).symm.sum_comp
            (fun v : V => G.degree v)

/-- Degree sum inside one component of a forest. -/
theorem connectedComponent_sum_degree_eq_two_mul_card_sub_one
    (hacyc : G.IsAcyclic)
    (C : G.ConnectedComponent) :
    (∑ v : C, C.toSimpleGraph.degree v) =
      2 * (Fintype.card C - 1) := by
  have htree := hacyc.isTree_connectedComponent C
  have hedge := htree.card_edgeFinset
  rw [SimpleGraph.sum_degrees_eq_twice_card_edges]
  omega

/-- Finite forest Euler identity under the decidable hypotheses that make
mathlib's canonical component `Fintype` instance available. -/
theorem card_connectedComponent_add_edgeCard_eq_fintypeCard_of_decidable
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hacyc : G.IsAcyclic) :
    Fintype.card G.ConnectedComponent + edgeCard G = Fintype.card V := by
  have hdegreeComponents := sum_connectedComponent_sum_degree_eq G
  have hedgeFinsetCard : G.edgeFinset.card = G.edgeSet.ncard := by
    rw [Set.ncard_eq_toFinset_card]
    apply congrArg Finset.card
    ext e
    simp
  have hglobalDegree :
      (∑ v : V, G.degree v) = 2 * edgeCard G := by
    calc
      (∑ v : V, G.degree v) = 2 * G.edgeFinset.card :=
        SimpleGraph.sum_degrees_eq_twice_card_edges G
      _ = 2 * edgeCard G := by
        unfold edgeCard
        rw [hedgeFinsetCard]
  have htwice :
      (∑ C : G.ConnectedComponent, 2 * (Fintype.card C - 1)) =
        2 * edgeCard G := by
    calc
      (∑ C : G.ConnectedComponent, 2 * (Fintype.card C - 1))
          = ∑ C : G.ConnectedComponent, ∑ v : C, C.toSimpleGraph.degree v := by
              apply Fintype.sum_congr
              intro C
              exact (connectedComponent_sum_degree_eq_two_mul_card_sub_one
                hacyc C).symm
      _ = ∑ v : V, G.degree v := hdegreeComponents
      _ = 2 * edgeCard G := hglobalDegree
  have hsubsum :
      (∑ C : G.ConnectedComponent, (Fintype.card C - 1)) = edgeCard G := by
    rw [← Finset.mul_sum] at htwice
    omega
  have hpositive :
      ∀ C : G.ConnectedComponent, 1 ≤ Fintype.card C := by
    intro C
    exact Fintype.card_pos_iff.mpr C.nonempty_supp.to_subtype
  have hpartition :
      (∑ C : G.ConnectedComponent, (Fintype.card C - 1)) +
          Fintype.card G.ConnectedComponent =
        ∑ C : G.ConnectedComponent, Fintype.card C := by
    rw [Fintype.card_eq_sum_ones, ← Finset.sum_add_distrib]
    apply Fintype.sum_congr
    intro C
    have hCpositive := hpositive C
    omega
  rw [hsubsum] at hpartition
  have hvertices := sum_connectedComponent_card_eq_fintypeCard G
  rw [hvertices] at hpartition
  omega

end Decidable

/-- Finite forest Euler identity: components plus edges equal vertices.

`Fintype.card` is instance-independent, so the decidable-hypothesis form above
transports to the ambient `SetLike` instance that callers see; `Nat.card`
carries the transport because it mentions no instance. -/
theorem card_connectedComponent_add_edgeCard_eq_fintypeCard
    {V : Type*} [Fintype V]
    (G : SimpleGraph V)
    (hacyc : G.IsAcyclic) :
    Fintype.card G.ConnectedComponent + edgeCard G = Fintype.card V := by
  have hcomponents :
      Fintype.card G.ConnectedComponent = Nat.card G.ConnectedComponent :=
    Nat.card_eq_fintype_card.symm
  have hvertices : Fintype.card V = Nat.card V :=
    Nat.card_eq_fintype_card.symm
  rw [hcomponents, hvertices]
  classical
  rw [Nat.card_eq_fintype_card (α := G.ConnectedComponent),
    Nat.card_eq_fintype_card (α := V)]
  exact card_connectedComponent_add_edgeCard_eq_fintypeCard_of_decidable G hacyc

end DivisorF
