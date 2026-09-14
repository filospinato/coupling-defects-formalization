import DivisorF.ExtremalRightComponents
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Extremal active right-node counting

This module advances the concrete contraction geometry for the original
Corollary 3.11.  Each extremal nonbinary fibre has exactly two selected
crossings.  We show that those two crossings activate exactly one or two
post-cut restriction components, define the split-fibre count `a`, and derive
the exact total number `K-1+a` of active right nodes before the incidence graph
itself is assembled.
-/

namespace DivisorF

open SimpleGraph
open scoped BigOperators

noncomputable local instance rightCountingLargePrimeDecidableEq {N : ℕ} :
    DecidableEq (LargePrime N) :=
  Classical.decEq _

/-- A crossing edge has a unique endpoint inside its large-prime fibre. -/
theorem crossing_fibre_endpoint_unique
    {N _K : ℕ} {q : LargePrime N} {L : SimpleGraph (HVertex N)}
    {e : Sym2 (HVertex N)} (he : e ∈ crossingFinset q L)
    {v w : HVertex N}
    (hv : v ∈ e) (hw : w ∈ e)
    (hvfibre : InFibre q v) (hwfibre : InFibre q w) :
    v = w := by
  have hecross := mem_crossingFinset.mp he
  rcases hecross with ⟨_, _, ⟨x, hxe, hxoutside⟩⟩
  induction e using Sym2.ind with
  | _ a b =>
      simp only [Sym2.mem_iff] at hv hw hxe
      rcases hv with rfl | rfl
      · rcases hw with rfl | rfl
        · rfl
        · rcases hxe with hxa | hxb
          · subst x
            exact (hxoutside hvfibre).elim
          · subst x
            exact (hxoutside hwfibre).elim
      · rcases hw with rfl | rfl
        · rcases hxe with hxa | hxb
          · subst x
            exact (hxoutside hwfibre).elim
          · subst x
            exact (hxoutside hvfibre).elim
        · rfl

/-- Selected crossing edges of one fibre as a finite type. -/
def FibreCrossingEdge
    {N _K : ℕ} (q : LargePrime N) (L : SimpleGraph (HVertex N)) :=
  ↥(crossingFinset q L)

noncomputable instance fibreCrossingEdgeFintype
    {N K : ℕ} (q : LargePrime N) (L : SimpleGraph (HVertex N)) :
    Fintype (FibreCrossingEdge (_K := K) q L) := by
  unfold FibreCrossingEdge
  infer_instance

/-- The unique fibre endpoint of a selected crossing. -/
noncomputable def crossingFibreEndpoint
    {N K : ℕ} {q : LargePrime N} {L : SimpleGraph (HVertex N)}
    (e : FibreCrossingEdge (_K := K) q L) : HVertex N :=
  Classical.choose (mem_crossingFinset.mp e.2).2.1

theorem crossingFibreEndpoint_mem
    {N K : ℕ} {q : LargePrime N} {L : SimpleGraph (HVertex N)}
    (e : FibreCrossingEdge (_K := K) q L) :
    crossingFibreEndpoint (K := K) e ∈ e.1 := by
  exact (Classical.choose_spec (mem_crossingFinset.mp e.2).2.1).1

theorem crossingFibreEndpoint_inFibre
    {N K : ℕ} {q : LargePrime N} {L : SimpleGraph (HVertex N)}
    (e : FibreCrossingEdge (_K := K) q L) :
    InFibre q (crossingFibreEndpoint (K := K) e) := by
  exact (Classical.choose_spec (mem_crossingFinset.mp e.2).2.1).2

noncomputable instance activeFibreRestrictionComponentFintype
    {N K : ℕ} (q : LargePrime N) (L : SimpleGraph (HVertex N)) :
    Fintype (ActiveFibreRestrictionComponent (K := K) q L) := by
  classical
  unfold ActiveFibreRestrictionComponent
  infer_instance

/-- Every crossing determines the active component of its fibre endpoint. -/
noncomputable def crossingActiveFibreRestrictionComponent
    {N K : ℕ} {q : LargePrime N} {L : SimpleGraph (HVertex N)}
    (e : FibreCrossingEdge (_K := K) q L) :
    ActiveFibreRestrictionComponent (K := K) q L := by
  let v := crossingFibreEndpoint (K := K) e
  let C := extremalRestrictionComponent (K := K) L v
  refine ⟨C, ?_⟩
  exact ⟨v, crossingFibreEndpoint_inFibre (K := K) e, rfl,
    e.1, e.2, crossingFibreEndpoint_mem (K := K) e⟩

/-- The crossing-to-active-component map is surjective. -/
theorem crossingActiveFibreRestrictionComponent_surjective
    {N K : ℕ} {q : LargePrime N} {L : SimpleGraph (HVertex N)} :
    Function.Surjective
      (@crossingActiveFibreRestrictionComponent N K q L) := by
  intro C
  rcases C.2 with ⟨v, hvfibre, hcomp, e, he, hve⟩
  let ce : FibreCrossingEdge (_K := K) q L := ⟨e, he⟩
  refine ⟨ce, Subtype.ext ?_⟩
  dsimp [crossingActiveFibreRestrictionComponent]
  have hendpoint : crossingFibreEndpoint (K := K) ce = v :=
    crossing_fibre_endpoint_unique (_K := K) he
      (crossingFibreEndpoint_mem (K := K) ce) hve
      (crossingFibreEndpoint_inFibre (K := K) ce) hvfibre
  calc
    extremalRestrictionComponent (K := K) L
        (crossingFibreEndpoint (K := K) ce)
        = extremalRestrictionComponent (K := K) L v := by rw [hendpoint]
    _ = C.1 := by simpa using hcomp

/-- Active post-cut components are no more numerous than selected crossings. -/
theorem activeFibreRestrictionComponent_card_le_crossingFinset
    {N K : ℕ} {q : LargePrime N} {L : SimpleGraph (HVertex N)} :
    Fintype.card (ActiveFibreRestrictionComponent (K := K) q L)
      ≤ (crossingFinset q L).card := by
  have hle := Fintype.card_le_of_surjective
    (@crossingActiveFibreRestrictionComponent N K q L)
    crossingActiveFibreRestrictionComponent_surjective
  simpa [FibreCrossingEdge] using hle

/-- Every extremal nonbinary fibre activates exactly one or two right nodes. -/
theorem activeFibreRestrictionComponent_card_eq_one_or_two_of_extremal
    {N K : ℕ} {L : SimpleGraph (HVertex N)}
    (hL : IsLinearForest (reducedDivisorGraph N) L)
    (hmax : edgeCard L = linearForestNumber (reducedDivisorGraph N))
    (hsat : cumulativeNonbinaryCount N K = K - 1)
    {q : LargePrime N} (hq : q ∈ cumulativeLevelFibres N K 2) :
    Fintype.card (ActiveFibreRestrictionComponent (K := K) q L) = 1 ∨
      Fintype.card (ActiveFibreRestrictionComponent (K := K) q L) = 2 := by
  have hle := activeFibreRestrictionComponent_card_le_crossingFinset
    (K := K) (q := q) (L := L)
  rw [card_crossingFinset_eq_two_of_extremal hL hmax hsat hq] at hle
  have hnonempty :=
    activeFibreRestrictionComponent_nonempty_of_extremal hL hmax hsat hq
  have hpos :
      0 < Fintype.card (ActiveFibreRestrictionComponent (K := K) q L) :=
    Fintype.card_pos_iff.mpr hnonempty
  omega

/-- Number of active post-cut restriction components of one fibre. -/
noncomputable def activeFibreRestrictionComponentCount
    {N K : ℕ} (q : LargePrime N) (L : SimpleGraph (HVertex N)) : ℕ :=
  Fintype.card (ActiveFibreRestrictionComponent (K := K) q L)

/-- Extremal nonbinary fibres whose two crossings land on distinct fibre paths. -/
noncomputable def splitNonbinaryFibres
    (N K : ℕ) (L : SimpleGraph (HVertex N)) : Finset (LargePrime N) := by
  classical
  exact (cumulativeLevelFibres N K 2).filter fun q =>
    activeFibreRestrictionComponentCount (K := K) q L = 2

@[simp]
theorem mem_splitNonbinaryFibres
    {N K : ℕ} {L : SimpleGraph (HVertex N)} {q : LargePrime N} :
    q ∈ splitNonbinaryFibres N K L ↔
      q ∈ cumulativeLevelFibres N K 2 ∧
        activeFibreRestrictionComponentCount (K := K) q L = 2 := by
  classical
  simp [splitNonbinaryFibres]

/-- The manuscript's `a`: number of nonbinary fibres that split. -/
noncomputable def splitNonbinaryFibreCount
    (N K : ℕ) (L : SimpleGraph (HVertex N)) : ℕ :=
  (splitNonbinaryFibres N K L).card

/-- One right node per nonbinary fibre, plus one extra exactly for split fibres. -/
theorem activeFibreRestrictionComponentCount_eq_one_add_indicator_of_extremal
    {N K : ℕ} {L : SimpleGraph (HVertex N)}
    (hL : IsLinearForest (reducedDivisorGraph N) L)
    (hmax : edgeCard L = linearForestNumber (reducedDivisorGraph N))
    (hsat : cumulativeNonbinaryCount N K = K - 1)
    {q : LargePrime N} (hq : q ∈ cumulativeLevelFibres N K 2) :
    activeFibreRestrictionComponentCount (K := K) q L =
      1 + if q ∈ splitNonbinaryFibres N K L then 1 else 0 := by
  classical
  have hcases :=
    activeFibreRestrictionComponent_card_eq_one_or_two_of_extremal
      hL hmax hsat hq
  rcases hcases with h1 | h2
  · have hnot : q ∉ splitNonbinaryFibres N K L := by
      intro hmem
      have htwo := (mem_splitNonbinaryFibres.mp hmem).2
      unfold activeFibreRestrictionComponentCount at htwo
      omega
    simp [activeFibreRestrictionComponentCount, h1, hnot]
  · have hmem : q ∈ splitNonbinaryFibres N K L :=
      mem_splitNonbinaryFibres.mpr ⟨hq, by
        unfold activeFibreRestrictionComponentCount
        exact h2⟩
    simp [activeFibreRestrictionComponentCount, h2, hmem]

/-- Summed right-node count is `b_K+a`. -/
theorem sum_activeFibreRestrictionComponentCount_eq_nonbinary_add_split
    {N K : ℕ} {L : SimpleGraph (HVertex N)}
    (hL : IsLinearForest (reducedDivisorGraph N) L)
    (hmax : edgeCard L = linearForestNumber (reducedDivisorGraph N))
    (hsat : cumulativeNonbinaryCount N K = K - 1) :
    (cumulativeLevelFibres N K 2).sum
        (fun q => activeFibreRestrictionComponentCount (K := K) q L)
      = cumulativeNonbinaryCount N K + splitNonbinaryFibreCount N K L := by
  classical
  calc
    (cumulativeLevelFibres N K 2).sum
        (fun q => activeFibreRestrictionComponentCount (K := K) q L)
        = (cumulativeLevelFibres N K 2).sum
            (fun q => 1 + if q ∈ splitNonbinaryFibres N K L then 1 else 0) := by
              apply Finset.sum_congr rfl
              intro q hq
              exact activeFibreRestrictionComponentCount_eq_one_add_indicator_of_extremal
                hL hmax hsat hq
    _ = (cumulativeLevelFibres N K 2).card
        + (splitNonbinaryFibres N K L).card := by
          have hsub :
              splitNonbinaryFibres N K L ⊆ cumulativeLevelFibres N K 2 := by
            intro q hq
            exact (mem_splitNonbinaryFibres.mp hq).1
          rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one,
            Finset.sum_ite_mem, Finset.inter_eq_right.mpr hsub,
            Finset.sum_const, smul_eq_mul, mul_one]
    _ = cumulativeNonbinaryCount N K + splitNonbinaryFibreCount N K L := rfl

/-- **Corollary 3.11 right-node count:** the active right side has `K-1+a` nodes. -/
theorem sum_activeFibreRestrictionComponentCount_eq_boundary_add_split
    {N K : ℕ} {L : SimpleGraph (HVertex N)}
    (hL : IsLinearForest (reducedDivisorGraph N) L)
    (hmax : edgeCard L = linearForestNumber (reducedDivisorGraph N))
    (hsat : cumulativeNonbinaryCount N K = K - 1) :
    (cumulativeLevelFibres N K 2).sum
        (fun q => activeFibreRestrictionComponentCount (K := K) q L)
      = (K - 1) + splitNonbinaryFibreCount N K L := by
  calc
    (cumulativeLevelFibres N K 2).sum
        (fun q => activeFibreRestrictionComponentCount (K := K) q L)
        = cumulativeNonbinaryCount N K + splitNonbinaryFibreCount N K L :=
      sum_activeFibreRestrictionComponentCount_eq_nonbinary_add_split
        hL hmax hsat
    _ = (K - 1) + splitNonbinaryFibreCount N K L := by rw [hsat]

end DivisorF
