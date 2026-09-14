import DivisorF.ExtremalContractedGeometry
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Exact edge correspondence for the extremal contracted incidence graph

This module turns the no-collapse geometry into the exact edge correspondence
needed by Corollary 3.11.  A retained nonbinary crossing is tagged by its fibre,
then sent to the concrete contracted edge determined by its canonical boundary
node and active post-cut restriction component.

The crucial point is injectivity: equality of contracted edges first forces the
same fibre tag and the same boundary/right nodes; the same-fibre no-collapse
theorem from `ExtremalContractedGeometry` then forces equality of the original
crossing edges.  Conversely, every concrete incidence edge contains exactly
such a crossing witness by definition of the graph.
-/

namespace DivisorF

open SimpleGraph

/-- Retained crossing edges, tagged by their nonbinary large-prime fibre. -/
def ExtremalNonbinaryCrossingEdge
    (N K : ℕ) (L : SimpleGraph (HVertex N)) :=
  Σ q : {q : LargePrime N // q ∈ cumulativeLevelFibres N K 2},
    FibreCrossingEdge (_K := K) q.1 L

noncomputable instance extremalNonbinaryCrossingEdgeFintype
    (N K : ℕ) (L : SimpleGraph (HVertex N)) :
    Fintype (ExtremalNonbinaryCrossingEdge N K L) :=
  inferInstanceAs
    (Fintype (Σ q : {q : LargePrime N // q ∈ cumulativeLevelFibres N K 2},
      FibreCrossingEdge (_K := K) q.1 L))

/-- The concrete contracted edge produced by one tagged nonbinary crossing. -/
noncomputable def extremalNonbinaryCrossingToContractedEdge
    {N K : ℕ} {L : SimpleGraph (HVertex N)}
    (hLsub : L ≤ reducedDivisorGraph N)
    (x : ExtremalNonbinaryCrossingEdge N K L) :
    (extremalContractedIncidenceGraph N K L).edgeSet := by
  let q := x.1
  let e := x.2
  let c := crossingBoundaryNode (K := K) hLsub
    (mem_cumulativeLevelFibres.mp q.2).1 e
  let R : ExtremalRightNode N K L :=
    ⟨q, crossingActiveFibreRestrictionComponent (K := K) e⟩
  refine ⟨s(Sum.inl c, Sum.inr R), ?_⟩
  rw [SimpleGraph.mem_edgeSet]
  exact extremalContractedIncidenceGraph_adj_of_crossing hLsub q.2 e

/--
A fixed left/right contracted adjacency has a unique crossing witness in its
owning fibre.  This is the local form of no edge collapse.
-/
theorem extremalContractedIncidenceGraph_crossing_witness_unique
    {N K : ℕ} {L : SimpleGraph (HVertex N)}
    (hKsq : K * K ≤ N)
    (hL : IsLinearForest (reducedDivisorGraph N) L)
    (c : ExtremalBoundaryNode N K) (R : ExtremalRightNode N K L)
    (e f : FibreCrossingEdge (_K := K) R.1.1 L)
    (hec : c.1 ∈ e.1)
    (hfc : c.1 ∈ f.1)
    (heR : crossingActiveFibreRestrictionComponent (K := K) e = R.2)
    (hfR : crossingActiveFibreRestrictionComponent (K := K) f = R.2) :
    e = f := by
  have hqcum : R.1.1 ∈ cumulativeFibres N K :=
    (mem_cumulativeLevelFibres.mp R.1.2).1
  have heBoundary :
      c = crossingBoundaryNode (K := K) hL.1 hqcum e :=
    boundaryNode_eq_crossingBoundaryNode_of_mem hKsq hL.1 hqcum e c hec
  have hfBoundary :
      c = crossingBoundaryNode (K := K) hL.1 hqcum f :=
    boundaryNode_eq_crossingBoundaryNode_of_mem hKsq hL.1 hqcum f c hfc
  apply fibreCrossingEdge_eq_of_same_contracted_nodes hL R.1.2 e f
  · have h := congrArg Subtype.val (heBoundary.symm.trans hfBoundary)
    simpa using h
  · exact heR.trans hfR.symm

/-- Distinct tagged retained crossings remain distinct contracted edges. -/
theorem extremalNonbinaryCrossingToContractedEdge_injective
    {N K : ℕ} {L : SimpleGraph (HVertex N)}
    (_hKsq : K * K ≤ N)
    (hL : IsLinearForest (reducedDivisorGraph N) L) :
    Function.Injective
      (extremalNonbinaryCrossingToContractedEdge (N := N) (K := K) (L := L)
        hL.1) := by
  intro x y hxy
  rcases x with ⟨qx, ex⟩
  rcases y with ⟨qy, ey⟩
  have hedge := congrArg Subtype.val hxy
  dsimp [extremalNonbinaryCrossingToContractedEdge] at hedge
  rcases Sym2.eq_iff.mp hedge with hsame | hswap
  · have hc := Sum.inl.inj hsame.1
    have hRpair :
        (⟨qx, crossingActiveFibreRestrictionComponent (K := K) ex⟩ :
            Σ q : {q : LargePrime N // q ∈ cumulativeLevelFibres N K 2},
              ActiveFibreRestrictionComponent (K := K) q.1 L) =
          ⟨qy, crossingActiveFibreRestrictionComponent (K := K) ey⟩ :=
      Sum.inr.inj hsame.2
    obtain ⟨hq, hcompHEq⟩ := Sigma.mk.inj hRpair
    subst hq
    have hcomp :
        crossingActiveFibreRestrictionComponent (K := K) ex =
          crossingActiveFibreRestrictionComponent (K := K) ey :=
      eq_of_heq hcompHEq
    have hout :
        crossingOutsideEndpoint (K := K) ex =
          crossingOutsideEndpoint (K := K) ey := by
      simpa using congrArg (fun c : ExtremalBoundaryNode N K => c.1) hc
    have heq := fibreCrossingEdge_eq_of_same_contracted_nodes
      hL qx.2 ex ey hout hcomp
    subst ey
    rfl
  · exact absurd hswap.1 (by simp)

/-- Every concrete contracted incidence edge comes from a retained crossing. -/
theorem extremalNonbinaryCrossingToContractedEdge_surjective
    {N K : ℕ} {L : SimpleGraph (HVertex N)}
    (hKsq : K * K ≤ N)
    (hLsub : L ≤ reducedDivisorGraph N) :
    Function.Surjective
      (extremalNonbinaryCrossingToContractedEdge (N := N) (K := K) (L := L)
        hLsub) := by
  intro E
  rcases E with ⟨edge, hedge⟩
  induction edge using Sym2.ind with
  | _ u v =>
      have huv :
          (extremalContractedIncidenceGraph N K L).Adj u v := by
        simpa [SimpleGraph.mem_edgeSet] using hedge
      rcases extremalContractedIncidenceGraph_adj_cases huv with
        ⟨c, R, rfl, rfl⟩ | ⟨R, c, rfl, rfl⟩
      · rw [extremalContractedIncidenceGraph_adj_left_right] at huv
        rcases huv with ⟨e, hce, heR⟩
        let x : ExtremalNonbinaryCrossingEdge N K L := ⟨R.1, e⟩
        refine ⟨x, Subtype.ext ?_⟩
        dsimp [extremalNonbinaryCrossingToContractedEdge, x]
        have hc :
            c = crossingBoundaryNode (K := K) hLsub
              (mem_cumulativeLevelFibres.mp R.1.2).1 e :=
          boundaryNode_eq_crossingBoundaryNode_of_mem hKsq hLsub
            (mem_cumulativeLevelFibres.mp R.1.2).1 e c hce
        have hright :
            R = ⟨R.1, crossingActiveFibreRestrictionComponent (K := K) e⟩ := by
          apply Sigma.ext
          · rfl
          · simpa using heR.symm
        rw [← hc, ← hright]
      · have hAdj :
            (extremalContractedIncidenceGraph N K L).Adj
              (Sum.inl c) (Sum.inr R) := huv.symm
        rw [extremalContractedIncidenceGraph_adj_left_right] at hAdj
        rcases hAdj with ⟨e, hce, heR⟩
        let x : ExtremalNonbinaryCrossingEdge N K L := ⟨R.1, e⟩
        refine ⟨x, Subtype.ext ?_⟩
        dsimp [extremalNonbinaryCrossingToContractedEdge, x]
        have hc :
            c = crossingBoundaryNode (K := K) hLsub
              (mem_cumulativeLevelFibres.mp R.1.2).1 e :=
          boundaryNode_eq_crossingBoundaryNode_of_mem hKsq hLsub
            (mem_cumulativeLevelFibres.mp R.1.2).1 e c hce
        have hright :
            R = ⟨R.1, crossingActiveFibreRestrictionComponent (K := K) e⟩ := by
          apply Sigma.ext
          · rfl
          · simpa using heR.symm
        rw [← hc, ← hright]
        exact Sym2.eq_swap

/-- Exact cardinality of the tagged retained crossing family at extremality. -/
theorem extremalNonbinaryCrossingEdge_card_eq
    {N K : ℕ} {L : SimpleGraph (HVertex N)}
    (hL : IsLinearForest (reducedDivisorGraph N) L)
    (hmax : edgeCard L = linearForestNumber (reducedDivisorGraph N))
    (hsat : cumulativeNonbinaryCount N K = K - 1) :
    Fintype.card (ExtremalNonbinaryCrossingEdge N K L) = 2 * (K - 1) := by
  classical
  have hsigma :
      Fintype.card (ExtremalNonbinaryCrossingEdge N K L) =
        ∑ q : {q : LargePrime N // q ∈ cumulativeLevelFibres N K 2},
          Fintype.card (FibreCrossingEdge (_K := K) q.1 L) :=
    Fintype.card_sigma
  rw [hsigma]
  calc
    (∑ q : {q : LargePrime N // q ∈ cumulativeLevelFibres N K 2},
        Fintype.card (FibreCrossingEdge (_K := K) q.1 L))
        = ∑ _q : {q : LargePrime N // q ∈ cumulativeLevelFibres N K 2}, 2 := by
            apply Finset.sum_congr rfl
            intro q _
            simp only [FibreCrossingEdge, Fintype.card_coe]
            rw [card_crossingFinset,
              crossingCount_eq_two_of_extremal hL hmax hsat q.2]
    _ = 2 * cumulativeNonbinaryCount N K := by
          unfold cumulativeNonbinaryCount
          rw [Finset.sum_const, smul_eq_mul, Finset.card_univ, Fintype.card_coe,
            Nat.mul_comm]
    _ = 2 * (K - 1) := by
          rw [hsat]

/--
**Corollary 3.11 concrete edge count.**  In the paper range, contraction keeps
all `2(K-1)` retained nonbinary crossings as distinct simple incidence edges.
-/
theorem extremalContractedIncidenceGraph_edgeCard_eq
    {N K : ℕ} {L : SimpleGraph (HVertex N)}
    (hKsq : K * K ≤ N)
    (hL : IsLinearForest (reducedDivisorGraph N) L)
    (hmax : edgeCard L = linearForestNumber (reducedDivisorGraph N))
    (hsat : cumulativeNonbinaryCount N K = K - 1) :
    edgeCard (extremalContractedIncidenceGraph N K L) = 2 * (K - 1) := by
  unfold edgeCard
  rw [← Nat.card_coe_set_eq]
  calc
    Nat.card (extremalContractedIncidenceGraph N K L).edgeSet
        = Nat.card (ExtremalNonbinaryCrossingEdge N K L) := by
            exact Nat.card_eq_of_bijective
              (extremalNonbinaryCrossingToContractedEdge hL.1)
              ⟨extremalNonbinaryCrossingToContractedEdge_injective hKsq hL,
                extremalNonbinaryCrossingToContractedEdge_surjective hKsq
                  hL.1⟩ |>.symm
    _ = Fintype.card (ExtremalNonbinaryCrossingEdge N K L) := by simp
    _ = 2 * (K - 1) :=
      extremalNonbinaryCrossingEdge_card_eq hL hmax hsat

end DivisorF
