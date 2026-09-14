import DivisorF.Crossing
import DivisorF.Split
import DivisorF.DefectPathPartition
import DivisorF.FactorizingPartition
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Lemma 5.1: vertex sensitivity of `lambda` and `P`

Deleting `|U|` vertices from a finite graph can destroy at most `2|U|` edges of
a maximum spanning linear forest, and can never create any.  Through
`P(X) = |V(X)| - lambda(X)` this becomes a genuine two-sided bound

```text
0 <= lambda(Y) - lambda(Y - U) <= 2|U|,      |P(Y) - P(Y - U)| <= |U|.
```

Both halves are already available in the development in a scattered form: the
lower half is `linearForestNumber_induce_add_induce_le` from
`DivisorF.Split`, and the degree-charging argument behind the upper half is the
one `DivisorF.CrossingPacking` runs against a fibre boundary.  What is new here
is the *general* vertex-deletion statement, with no fibre in sight, which is
what Section 5's transport argument consumes.

The last corollary is the manuscript's "in particular, `F` is `1`-Lipschitz on
the positive integers": `G_t` is the subgraph of `G_s` induced by
`{1, ..., t}`, so the two path numbers differ by at most `s - t`.

Vertex deletion is represented by a decidable predicate `p`, with `Y - U` the
subgraph induced on `{v | p v}` and `U = {v | ¬ p v}`.  Nothing here is
project-original graph theory; it is the bridge lemma Section 5 needs.
-/

namespace DivisorF

open SimpleGraph

section General

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Selected edges of `L` incident to at least one vertex of `U`. -/
noncomputable def incidentEdgeFinset (L : SimpleGraph V) (U : Finset V) :
    Finset (Sym2 V) := by
  classical
  exact U.biUnion fun v => L.incidenceFinset v

theorem card_incidentEdgeFinset_le_two_mul {L : SimpleGraph V}
    (hdeg : ∀ v, selectedDegree L v ≤ 2) (U : Finset V) :
    (incidentEdgeFinset L U).card ≤ 2 * U.card := by
  classical
  calc
    (incidentEdgeFinset L U).card
        ≤ ∑ v ∈ U, (L.incidenceFinset v).card := Finset.card_biUnion_le
    _ = ∑ v ∈ U, selectedDegree L v := by
          refine Finset.sum_congr rfl fun v _ => ?_
          rw [SimpleGraph.card_incidenceFinset_eq_degree]
          unfold SimpleGraph.degree selectedDegree SimpleGraph.neighborFinset
          simpa using
            ((L.neighborSet v).ncard_eq_toFinset_card (Set.toFinite _)).symm
    _ ≤ ∑ _v ∈ U, 2 := Finset.sum_le_sum fun v _ => hdeg v
    _ = 2 * U.card := by simp [Nat.mul_comm]

/-- Every selected edge with an endpoint outside `p` is incident to the deleted
set. -/
theorem meetingSet_subset_incidentEdgeFinset (L : SimpleGraph V) (p : V → Prop)
    [DecidablePred p] :
    internalSet L (fun v ↦ ¬ p v) ∪ crossSet L p
      ⊆ ↑(incidentEdgeFinset L (Finset.univ.filter fun v ↦ ¬ p v)) := by
  classical
  intro e he
  have hbad : e ∈ L.edgeSet ∧ ∃ x ∈ e, ¬ p x := by
    rcases he with ⟨hmem, hall⟩ | ⟨hmem, -, hex⟩
    · refine ⟨hmem, ?_⟩
      induction e using Sym2.ind with
      | _ x y => exact ⟨x, by simp, hall x (by simp)⟩
    · exact ⟨hmem, hex⟩
  obtain ⟨hmem, x, hx, hpx⟩ := hbad
  simp only [Finset.coe_biUnion, incidentEdgeFinset, Finset.coe_filter,
    Set.mem_iUnion, Finset.mem_coe]
  refine ⟨x, ?_, ?_⟩
  · simp [hpx]
  · rw [SimpleGraph.mem_incidenceFinset]
    exact ⟨hmem, hx⟩

omit [DecidableEq V] in
/-- Edges destroyed by deleting `{v | ¬ p v}` are at most twice its size. -/
theorem internalCard_add_crossingCard_le_two_mul (L : SimpleGraph V)
    (p : V → Prop) [DecidablePred p]
    (hdeg : ∀ v, selectedDegree L v ≤ 2) :
    internalCard L (fun v ↦ ¬ p v) + crossingCard L p
      ≤ 2 * Fintype.card {v // ¬ p v} := by
  classical
  have hdisj : Disjoint (internalSet L (fun v ↦ ¬ p v)) (crossSet L p) :=
    Set.disjoint_of_subset_left Set.subset_union_right (disjoint_internal_cross L p)
  have hsum : internalCard L (fun v ↦ ¬ p v) + crossingCard L p
      = (internalSet L (fun v ↦ ¬ p v) ∪ crossSet L p).ncard := by
    unfold internalCard crossingCard
    rw [Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)]
  rw [hsum]
  calc
    (internalSet L (fun v ↦ ¬ p v) ∪ crossSet L p).ncard
        ≤ (↑(incidentEdgeFinset L (Finset.univ.filter fun v ↦ ¬ p v)) :
            Set (Sym2 V)).ncard :=
          Set.ncard_le_ncard (meetingSet_subset_incidentEdgeFinset L p)
            (Set.toFinite _)
    _ = (incidentEdgeFinset L (Finset.univ.filter fun v ↦ ¬ p v)).card := by
          rw [Set.ncard_eq_toFinset_card', Finset.toFinset_coe]
    _ ≤ 2 * (Finset.univ.filter fun v ↦ ¬ p v).card :=
          card_incidentEdgeFinset_le_two_mul hdeg _
    _ = 2 * Fintype.card {v // ¬ p v} := by
          rw [Fintype.card_subtype]

/-- **Lemma 5.1, upper half.** Deleting `U` costs at most `2|U|` forest edges. -/
theorem linearForestNumber_le_induce_add_two_mul (G : SimpleGraph V)
    (p : V → Prop) [DecidablePred p] :
    linearForestNumber G
      ≤ linearForestNumber (G.induce {v | p v}) + 2 * Fintype.card {v // ¬ p v} := by
  classical
  obtain ⟨L, hL, hmax⟩ := exists_maximumLinearForest G
  have hpart := edgeCard_eq_internal_add_internal_add_crossing L p
  have hint : internalCard L p = edgeCard (L.induce {v | p v}) :=
    (edgeCard_induce_setOf L p).symm
  have hle : edgeCard (L.induce {v | p v}) ≤ linearForestNumber (G.induce {v | p v}) :=
    edgeCard_induce_le_linearForestNumber hL p
  have hmeet := internalCard_add_crossingCard_le_two_mul L p hL.2.2
  omega

/-- **Lemma 5.1, lower half.** Deleting vertices never creates forest edges. -/
theorem linearForestNumber_induce_le (G : SimpleGraph V) (p : V → Prop)
    [DecidablePred p] :
    linearForestNumber (G.induce {v | p v}) ≤ linearForestNumber G := by
  have h := linearForestNumber_induce_add_induce_le G p
  omega

/-- **Lemma 5.1, `lambda` form.**

```text
0 <= lambda(Y) - lambda(Y - U) <= 2|U|.
```
-/
theorem vertexSensitivity_linearForestNumber (G : SimpleGraph V) (p : V → Prop)
    [DecidablePred p] :
    0 ≤ (linearForestNumber G : ℤ) - linearForestNumber (G.induce {v | p v}) ∧
      (linearForestNumber G : ℤ) - linearForestNumber (G.induce {v | p v})
        ≤ 2 * Fintype.card {v // ¬ p v} := by
  have h1 := linearForestNumber_induce_le G p
  have h2 := linearForestNumber_le_induce_add_two_mul G p
  omega

omit [DecidableEq V] in
/-- The vertex count splits along the deletion. -/
theorem card_subtype_add_card_subtype_not (p : V → Prop) [DecidablePred p] :
    Fintype.card {v // p v} + Fintype.card {v // ¬ p v} = Fintype.card V := by
  classical
  have hsplit := Fintype.card_congr (Equiv.sumCompl p)
  rw [Fintype.card_sum] at hsplit
  omega

/-- **Lemma 5.1, `P` form.**

```text
|P(Y) - P(Y - U)| <= |U|.
```

This is the half Section 5 actually transports: the `lambda` bound is two-sided
with different constants, but through `P(X) = |V(X)| - lambda(X)` the deleted
vertices cancel half of the loss. -/
theorem vertexSensitivity_pathPartitionNumber (G : SimpleGraph V) (p : V → Prop)
    [DecidablePred p] :
    |(pathPartitionNumber G : ℤ) - pathPartitionNumber (G.induce {v | p v})|
      ≤ Fintype.card {v // ¬ p v} := by
  classical
  have hG := pathPartitionNumber_add_linearForestNumber G
  have hsub := pathPartitionNumber_add_linearForestNumber (G.induce {v | p v})
  have hcard := card_subtype_add_card_subtype_not p
  have hcardsub : Fintype.card ↥{v | p v} = Fintype.card {v // p v} := rfl
  have h1 := linearForestNumber_induce_le G p
  have h2 := linearForestNumber_le_induce_add_two_mul G p
  rw [abs_le]
  omega

end General

section Divisor

/-- `G_t` is the subgraph of `G_s` induced by `{1, ..., t}`. -/
def divisorGraphTruncIso {s t : ℕ} (h : t ≤ s) :
    divisorGraph t ≃g (divisorGraph s).induce {v : GVertex s | v.value ≤ t} where
  toFun a := ⟨⟨a.val, lt_of_lt_of_le a.isLt h⟩, by
    simp only [Set.mem_setOf_eq, GVertex.value]
    omega⟩
  invFun v := ⟨v.1.val, by
    have hv := v.2
    simp only [Set.mem_setOf_eq, GVertex.value] at hv
    omega⟩
  left_inv a := by apply Fin.ext; rfl
  right_inv v := by apply Subtype.ext; apply Fin.ext; rfl
  map_rel_iff' := by
    intro a b
    change (divisorGraph s).Adj ⟨a.val, _⟩ ⟨b.val, _⟩ ↔ (divisorGraph t).Adj a b
    rw [divisorGraph_adj, divisorGraph_adj]
    have hva : GVertex.value (⟨a.val, lt_of_lt_of_le a.isLt h⟩ : GVertex s)
        = GVertex.value a := rfl
    have hvb : GVertex.value (⟨b.val, lt_of_lt_of_le b.isLt h⟩ : GVertex s)
        = GVertex.value b := rfl
    rw [hva, hvb]
    constructor
    · rintro ⟨hne, hdvd⟩
      exact ⟨fun hab => hne (by rw [hab]), hdvd⟩
    · rintro ⟨hne, hdvd⟩
      refine ⟨fun hab => hne (Fin.ext ?_), hdvd⟩
      exact congrArg (fun x : Fin s => x.val) hab

/-- The truncation deletes exactly `s - t` vertices. -/
theorem card_divisorGraphTrunc_complement {s t : ℕ} (h : t ≤ s) :
    Fintype.card {v : GVertex s // ¬ (v.value ≤ t)} = s - t := by
  classical
  have hsplit :
      Fintype.card {v : GVertex s // v.value ≤ t}
        + Fintype.card {v : GVertex s // ¬ (v.value ≤ t)} = s := by
    have := card_subtype_add_card_subtype_not (fun v : GVertex s => v.value ≤ t)
    simpa [card_GVertex] using this
  have hlow : Fintype.card {v : GVertex s // v.value ≤ t} = t := by
    have hiso := Fintype.card_congr (divisorGraphTruncIso h).toEquiv
    rw [card_GVertex] at hiso
    exact hiso.symm
  omega

/-- **Lemma 5.1, final clause.**  `F` is `1`-Lipschitz on the positive
integers. -/
theorem abs_divisorPathPartitionNumber_sub_le {s t : ℕ} (h : t ≤ s) :
    |(divisorPathPartitionNumber s : ℤ) - divisorPathPartitionNumber t|
      ≤ (s : ℤ) - t := by
  classical
  have hiso : divisorPathPartitionNumber t
      = pathPartitionNumber ((divisorGraph s).induce {v : GVertex s | v.value ≤ t}) :=
    pathPartitionNumber_iso (divisorGraphTruncIso h)
  have hsens :=
    vertexSensitivity_pathPartitionNumber (divisorGraph s)
      (fun v : GVertex s => v.value ≤ t)
  rw [card_divisorGraphTrunc_complement h] at hsens
  have hst : ((s - t : ℕ) : ℤ) = (s : ℤ) - t := by omega
  rw [hst] at hsens
  rw [hiso]
  unfold divisorPathPartitionNumber
  exact hsens

end Divisor

end DivisorF
