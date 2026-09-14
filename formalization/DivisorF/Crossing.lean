import DivisorF.Split

set_option linter.style.header false

/-!
# Exact edge accounting across a vertex partition

Fix a spanning linear forest `L` and a vertex predicate `p`.  The selected
edges split into three genuinely disjoint classes: those internal to `p`, those
internal to `¬ p`, and the crossings.  Section 3 of the paper rests on this
partition being exact, with no edge counted twice.

`internalCard L p` is the number of selected edges with both endpoints in `p`;
`crossingCard L p` is the number of selected edges with one endpoint on each
side.  The bridge to the induced subgraphs is
`internalCard L p = edgeCard (L.induce {v | p v})`.
-/

namespace DivisorF

open SimpleGraph

variable {V : Type*}

/-- Selected edges with both endpoints inside `p`. -/
def internalSet (L : SimpleGraph V) (p : V → Prop) : Set (Sym2 V) :=
  {e ∈ L.edgeSet | ∀ x ∈ e, p x}

/-- Selected edges with one endpoint on each side of `p`. -/
def crossSet (L : SimpleGraph V) (p : V → Prop) : Set (Sym2 V) :=
  {e ∈ L.edgeSet | (∃ x ∈ e, p x) ∧ ∃ x ∈ e, ¬ p x}

/-- Number of selected edges internal to `p`. -/
noncomputable def internalCard (L : SimpleGraph V) (p : V → Prop) : ℕ :=
  (internalSet L p).ncard

/-- Number of selected crossings of the partition induced by `p`. -/
noncomputable def crossingCard (L : SimpleGraph V) (p : V → Prop) : ℕ :=
  (crossSet L p).ncard

section Partition

variable (L : SimpleGraph V) (p : V → Prop)

theorem edgeSet_eq_union :
    L.edgeSet = internalSet L p ∪ internalSet L (fun v ↦ ¬ p v) ∪ crossSet L p := by
  ext e
  induction e using Sym2.ind with
  | _ x y =>
    simp only [internalSet, crossSet, Set.mem_union, Set.mem_setOf_eq, Sym2.mem_iff]
    constructor
    · intro he
      by_cases hx : p x <;> by_cases hy : p y
      · exact Or.inl (Or.inl ⟨he, by rintro z (rfl | rfl) <;> assumption⟩)
      · exact Or.inr ⟨he, ⟨x, Or.inl rfl, hx⟩, ⟨y, Or.inr rfl, hy⟩⟩
      · exact Or.inr ⟨he, ⟨y, Or.inr rfl, hy⟩, ⟨x, Or.inl rfl, hx⟩⟩
      · exact Or.inl (Or.inr ⟨he, by rintro z (rfl | rfl) <;> assumption⟩)
    · rintro ((⟨he, -⟩ | ⟨he, -⟩) | ⟨he, -⟩) <;> exact he

theorem disjoint_internal :
    Disjoint (internalSet L p) (internalSet L (fun v ↦ ¬ p v)) := by
  rw [Set.disjoint_left]
  rintro e ⟨-, h1⟩ ⟨-, h2⟩
  induction e using Sym2.ind with
  | _ x y => exact h2 x (by simp) (h1 x (by simp))

theorem disjoint_internal_cross :
    Disjoint (internalSet L p ∪ internalSet L (fun v ↦ ¬ p v)) (crossSet L p) := by
  rw [Set.disjoint_left]
  rintro e (⟨-, h1⟩ | ⟨-, h1⟩) ⟨-, ⟨a, ha, hpa⟩, ⟨b, hb, hpb⟩⟩
  · exact hpb (h1 b hb)
  · exact h1 a ha hpa

/-- The exact three-way edge partition: no selected edge is counted twice. -/
theorem edgeCard_eq_internal_add_internal_add_crossing [Finite V] :
    edgeCard L = internalCard L p + internalCard L (fun v ↦ ¬ p v) + crossingCard L p := by
  classical
  unfold edgeCard internalCard crossingCard
  rw [edgeSet_eq_union L p,
    Set.ncard_union_eq (disjoint_internal_cross L p) (Set.toFinite _) (Set.toFinite _),
    Set.ncard_union_eq (disjoint_internal L p) (Set.toFinite _) (Set.toFinite _)]

end Partition

section Induce

variable (L : SimpleGraph V) (s : Set V)

theorem edgeSet_induce_map :
    Sym2.map (Subtype.val : s → V) '' (L.induce s).edgeSet = internalSet L (fun v ↦ v ∈ s) := by
  ext e
  constructor
  · rintro ⟨e', he', rfl⟩
    induction e' using Sym2.ind with
    | _ a b =>
      rw [mem_edgeSet] at he'
      refine ⟨?_, ?_⟩
      · simpa using he'
      · rintro z hz
        rw [Sym2.map_mk, Sym2.mem_iff] at hz
        rcases hz with rfl | rfl
        · exact a.2
        · exact b.2
  · rintro ⟨he, hmem⟩
    induction e using Sym2.ind with
    | _ x y =>
      have hx : x ∈ s := hmem x (by simp)
      have hy : y ∈ s := hmem y (by simp)
      refine ⟨s(⟨x, hx⟩, ⟨y, hy⟩), ?_, ?_⟩
      · rw [mem_edgeSet]
        exact he
      · simp

/-- Edges of an induced subgraph are exactly the ambient edges inside the set. -/
theorem edgeCard_induce (L : SimpleGraph V) (s : Set V) :
    edgeCard (L.induce s) = internalCard L (fun v ↦ v ∈ s) := by
  unfold edgeCard internalCard
  rw [← edgeSet_induce_map L s]
  exact (Set.ncard_image_of_injective _ (Sym2.map.injective Subtype.val_injective)).symm

theorem edgeCard_induce_setOf (L : SimpleGraph V) (p : V → Prop) :
    edgeCard (L.induce {v | p v}) = internalCard L p :=
  edgeCard_induce L {v | p v}

end Induce

section Restriction

variable {G L : SimpleGraph V}

/-- Restricting a linear forest to a vertex subset gives a linear forest of the
induced subgraph. -/
theorem IsLinearForest.induce [Finite V] (hL : IsLinearForest G L) (s : Set V) :
    IsLinearForest (G.induce s) (L.induce s) := by
  refine ⟨?_, hL.2.1.induce s, ?_⟩
  · intro a b hab
    exact hL.1 hab
  · intro v
    have hsub : (Subtype.val : s → V) '' ((L.induce s).neighborSet v)
        ⊆ L.neighborSet (v : V) := by
      rintro x ⟨w, hw, rfl⟩
      exact hw
    calc
      selectedDegree (L.induce s) v
          = ((Subtype.val : s → V) '' ((L.induce s).neighborSet v)).ncard :=
        (Set.ncard_image_of_injective _ Subtype.val_injective).symm
      _ ≤ (L.neighborSet (v : V)).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ 2 := hL.2.2 _

/-- The restriction of a spanning linear forest never beats the induced
optimum. -/
theorem edgeCard_induce_le_linearForestNumber [Fintype V] [DecidableEq V]
    (hL : IsLinearForest G L) (p : V → Prop)
    [DecidablePred p] :
    edgeCard (L.induce {v | p v}) ≤ linearForestNumber (G.induce {v | p v}) :=
  edgeCard_le_linearForestNumber (hL.induce _)

end Restriction

end DivisorF
