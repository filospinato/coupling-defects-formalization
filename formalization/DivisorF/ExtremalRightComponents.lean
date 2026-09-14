import DivisorF.ExtremalContraction
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Extremal right-component geometry

Concrete next step toward the original Corollary 3.11.  The selected nonbinary
crossings have already been deleted from one fixed maximum linear forest and
saturated boundary vertices are singleton post-cut components.

This module proves the no-edge-collapse mechanism needed by the contraction and
introduces the actual post-cut fibre components touched by selected crossings.
-/

namespace DivisorF

open SimpleGraph

/--
If two distinct selected attachments from the same vertex are among the deleted
nonbinary crossings, their opposite endpoints cannot lie in the same post-cut
component.  Otherwise the surviving path between those endpoints, together
with the two selected attachments, would create a cycle in the original
maximum forest.
-/
theorem extremalRestrictionComponent_ne_of_two_attachments
    {N K : ℕ} {L : SimpleGraph (HVertex N)}
    (hL : IsLinearForest (reducedDivisorGraph N) L)
    {c v w : HVertex N}
    (hcv : L.Adj c v) (hcw : L.Adj c w)
    (hcvCross : s(c, v) ∈ nonbinaryCrossingUnion N K L)
    (_hcwCross : s(c, w) ∈ nonbinaryCrossingUnion N K L)
    (hvw : v ≠ w) :
    extremalRestrictionComponent (K := K) L v ≠
      extremalRestrictionComponent (K := K) L w := by
  intro hcomp
  have hreachCut : (extremalCutGraph N K L).Reachable v w :=
    extremalRestrictionComponent_eq_iff_reachable.mp hcomp
  have hcut_le_single :
      extremalCutGraph N K L ≤ L.deleteEdges {s(c, v)} := by
    intro x y hxy
    have hxy' := hxy
    rw [extremalCutGraph, SimpleGraph.deleteEdges_adj] at hxy'
    rw [SimpleGraph.deleteEdges_adj]
    refine ⟨hxy'.1, ?_⟩
    intro hsingle
    have heq : s(x, y) = s(c, v) := by simpa using hsingle
    apply hxy'.2
    rw [heq]
    exact hcvCross
  have hreachVW : (L.deleteEdges {s(c, v)}).Reachable v w :=
    hreachCut.mono hcut_le_single
  have hedge_ne : s(c, w) ≠ s(c, v) := by
    intro heq
    rcases Sym2.eq_iff.mp heq with hsame | hswap
    · exact hvw hsame.2.symm
    · exact hcv.ne hswap.1
  have hcwDelete : (L.deleteEdges {s(c, v)}).Adj w c := by
    rw [SimpleGraph.deleteEdges_adj]
    refine ⟨hcw.symm, ?_⟩
    intro hmem
    have heq : s(w, c) = s(c, v) := by simpa using hmem
    apply hedge_ne
    calc
      s(c, w) = s(w, c) := Sym2.eq_swap
      _ = s(c, v) := heq
  have hreachCV : (L.deleteEdges {s(c, v)}).Reachable c v :=
    (hreachVW.trans hcwDelete.reachable).symm
  obtain ⟨u, p, hpCycle, _⟩ :=
    SimpleGraph.adj_and_reachable_delete_edges_iff_exists_cycle.mp
      ⟨hcv, hreachCV⟩
  exact hL.2.1 p hpCycle

/-- A crossing of a nonbinary fibre belongs to the global deleted crossing union. -/
theorem crossing_mem_nonbinaryCrossingUnion
    {N K : ℕ} {q : LargePrime N} {L : SimpleGraph (HVertex N)}
    (hq : q ∈ cumulativeLevelFibres N K 2)
    {e : Sym2 (HVertex N)} (he : e ∈ crossingFinset q L) :
    e ∈ nonbinaryCrossingUnion N K L := by
  rw [nonbinaryCrossingUnion, crossingUnion, Finset.mem_biUnion]
  exact ⟨q, hq, he⟩

/--
Two distinct crossing attachments of nonbinary fibres at the same boundary
vertex survive the contraction as two distinct right nodes.
-/
theorem nonbinary_attachment_components_distinct
    {N K : ℕ} {L : SimpleGraph (HVertex N)}
    (hL : IsLinearForest (reducedDivisorGraph N) L)
    {q r : LargePrime N}
    (hq : q ∈ cumulativeLevelFibres N K 2)
    (hr : r ∈ cumulativeLevelFibres N K 2)
    {c v w : HVertex N}
    (hcv : L.Adj c v) (hcw : L.Adj c w)
    (hcvCross : s(c, v) ∈ crossingFinset q L)
    (hcwCross : s(c, w) ∈ crossingFinset r L)
    (hvw : v ≠ w) :
    extremalRestrictionComponent (K := K) L v ≠
      extremalRestrictionComponent (K := K) L w := by
  exact extremalRestrictionComponent_ne_of_two_attachments
    hL hcv hcw
      (crossing_mem_nonbinaryCrossingUnion hq hcvCross)
      (crossing_mem_nonbinaryCrossingUnion hr hcwCross)
      hvw

/--
A post-cut component is active for a fibre when it contains a fibre endpoint of
one of that fibre's selected crossing edges.
-/
def IsActiveFibreRestrictionComponent
    {N K : ℕ} (q : LargePrime N) (L : SimpleGraph (HVertex N))
    (C : (extremalCutGraph N K L).ConnectedComponent) : Prop :=
  ∃ v : HVertex N,
    InFibre q v ∧
      extremalRestrictionComponent (K := K) L v = C ∧
      ∃ e ∈ crossingFinset q L, v ∈ e

/-- The type of active post-cut restriction components of one fibre. -/
def ActiveFibreRestrictionComponent
    {N K : ℕ} (q : LargePrime N) (L : SimpleGraph (HVertex N)) :=
  {C : (extremalCutGraph N K L).ConnectedComponent //
    IsActiveFibreRestrictionComponent (K := K) q L C}

/-- Every selected crossing of a fibre exposes an active post-cut fibre component. -/
theorem exists_activeFibreRestrictionComponent_of_crossing
    {N K : ℕ} {q : LargePrime N} {L : SimpleGraph (HVertex N)}
    {e : Sym2 (HVertex N)} (he : e ∈ crossingFinset q L) :
    Nonempty (ActiveFibreRestrictionComponent (K := K) q L) := by
  have hecross := mem_crossingFinset.mp he
  rcases hecross with ⟨_, ⟨v, hve, hvfibre⟩, _⟩
  let C := extremalRestrictionComponent (K := K) L v
  refine ⟨⟨C, ?_⟩⟩
  exact ⟨v, hvfibre, rfl, e, he, hve⟩

/-- Every extremal nonbinary fibre has at least one active right component. -/
theorem activeFibreRestrictionComponent_nonempty_of_extremal
    {N K : ℕ} {L : SimpleGraph (HVertex N)}
    (hL : IsLinearForest (reducedDivisorGraph N) L)
    (hmax : edgeCard L = linearForestNumber (reducedDivisorGraph N))
    (hsat : cumulativeNonbinaryCount N K = K - 1)
    {q : LargePrime N} (hq : q ∈ cumulativeLevelFibres N K 2) :
    Nonempty (ActiveFibreRestrictionComponent (K := K) q L) := by
  have hcard := card_crossingFinset_eq_two_of_extremal hL hmax hsat hq
  have hne : (crossingFinset q L).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    rw [hempty] at hcard
    simp at hcard
  obtain ⟨e, he⟩ := hne
  exact exists_activeFibreRestrictionComponent_of_crossing he

end DivisorF
