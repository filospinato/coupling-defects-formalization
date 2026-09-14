import DivisorF.DefectPathPartition
import Mathlib.Tactic

set_option linter.style.header false

/-!
# `q`-factorizing path partitions and the factorization penalty

Definition 3.1 calls a path partition of `H_N` *`q`-factorizing* when every path
meeting the fibre `B_q(N)` lies inside it, and Theorem 3.2 identifies the least
size of such a partition as `P(R_{N,q}) + F(s)`. Both are statements about path
partitions, so neither could be stated before `DivisorF.PathPartition` existed.

The mathematical content is the split: a `q`-factorizing partition is exactly a
path partition of the fibre together with one of its complement. Carrying that
across the induced subgraphs in both directions needs a walk lying inside a set
to lift to the subgraph induced on it, which mathlib does not provide; that is
`exists_induce_walk` below.
-/

namespace DivisorF

open SimpleGraph

section Induce

variable {V : Type*} {G : SimpleGraph V} {S : Set V}

/-- A walk whose vertices all lie in `S` lifts to the subgraph induced on `S`. -/
theorem exists_induce_walk :
    ∀ {u v : V} (p : G.Walk u v) (hu : u ∈ S),
      (∀ w ∈ p.support, w ∈ S) →
      ∃ (hv : v ∈ S) (p' : (G.induce S).Walk ⟨u, hu⟩ ⟨v, hv⟩),
        p'.support.map Subtype.val = p.support := by
  intro u v p
  induction p with
  | nil =>
      intro hu _
      exact ⟨hu, SimpleGraph.Walk.nil, by simp⟩
  | @cons a b c h q ih =>
      intro ha hsupp
      have hb : b ∈ S := hsupp b (by simp)
      obtain ⟨hc, q', hq'⟩ := ih hb (fun w hw => hsupp w (by simp [hw]))
      have hadj : (G.induce S).Adj ⟨a, ha⟩ ⟨b, hb⟩ := h
      exact ⟨hc, SimpleGraph.Walk.cons hadj q', by simp [hq']⟩

variable [DecidableEq V]

/-- The image of a path block of the induced subgraph is a path block. -/
theorem isPathBlock_image_induce {t : Finset ↥S}
    (ht : IsPathBlock (G.induce S) t) :
    IsPathBlock G (t.image Subtype.val) := by
  classical
  obtain ⟨u, v, p, hp, hsupp⟩ := ht
  have hinj : Function.Injective (SimpleGraph.Embedding.induce (G := G) S).toHom :=
    fun x y hxy => Subtype.ext hxy
  refine ⟨_, _, p.map (SimpleGraph.Embedding.induce (G := G) S).toHom,
    hp.map hinj, ?_⟩
  ext w
  rw [List.mem_toFinset, SimpleGraph.Walk.support_map, List.mem_map]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact Finset.mem_image.mpr ⟨z, by rw [← hsupp]; exact List.mem_toFinset.mpr hz, rfl⟩
  · intro hw
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
    refine ⟨z, ?_, rfl⟩
    rw [← hsupp] at hz
    exact List.mem_toFinset.mp hz

variable [DecidablePred (· ∈ S)]

/-- A path block contained in `S` pulls back to a path block of the induced
subgraph. -/
theorem isPathBlock_subtype {t : Finset V}
    (ht : IsPathBlock G t) (htS : ∀ v ∈ t, v ∈ S) :
    IsPathBlock (G.induce S) (t.subtype (· ∈ S)) := by
  classical
  obtain ⟨u, v, p, hp, hsupp⟩ := ht
  have hall : ∀ w ∈ p.support, w ∈ S := by
    intro w hw
    exact htS w (by rw [← hsupp]; exact List.mem_toFinset.mpr hw)
  have hu : u ∈ S := hall u p.start_mem_support
  obtain ⟨hv, p', hp'⟩ := exists_induce_walk p hu hall
  refine ⟨⟨u, hu⟩, ⟨v, hv⟩, p', ?_, ?_⟩
  · rw [SimpleGraph.Walk.isPath_def]
    have hnodup : (p'.support.map Subtype.val).Nodup := by
      rw [hp']
      exact hp.support_nodup
    exact List.Nodup.of_map _ hnodup
  · ext x
    rw [List.mem_toFinset, Finset.mem_subtype, ← hsupp, List.mem_toFinset]
    constructor
    · intro hx
      have : (x : V) ∈ p'.support.map Subtype.val := List.mem_map_of_mem hx
      rwa [hp'] at this
    · intro hx
      have hx' : (x : V) ∈ p'.support.map Subtype.val := by rwa [hp']
      obtain ⟨y, hy, hyx⟩ := List.mem_map.mp hx'
      exact Subtype.ext hyx ▸ hy

end Induce

section SubtypeImage

variable {V : Type*} [DecidableEq V] {S : Set V}

@[simp]
theorem mem_image_val {t : Finset ↥S} {x : ↥S} :
    (x : V) ∈ t.image Subtype.val ↔ x ∈ t := by
  constructor
  · intro h
    obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp h
    exact (Subtype.ext hyx : y = x) ▸ hy
  · intro h
    exact Finset.mem_image_of_mem _ h

theorem image_val_injective :
    Function.Injective (fun t : Finset ↥S => t.image Subtype.val) := by
  intro a b hab
  simp only at hab
  ext x
  rw [← mem_image_val (t := a), ← mem_image_val (t := b), hab]

theorem disjoint_image_val {a b : Finset ↥S} (h : Disjoint a b) :
    Disjoint (a.image Subtype.val) (b.image Subtype.val) := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
  rw [mem_image_val] at hx'
  exact (Finset.disjoint_left.mp h hy) hx'

theorem mem_of_mem_image_val {t : Finset ↥S} {x : V}
    (hx : x ∈ t.image Subtype.val) : x ∈ S := by
  obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hx
  exact y.2

end SubtypeImage

section Split

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The minimum in the definition of `P(X)` is attained. -/
theorem exists_optimal_pathPartition (X : SimpleGraph V) :
    ∃ P : Finset (Finset V), IsPathPartition X P ∧ P.card = pathPartitionNumber X := by
  have hne : {c | ∃ P : Finset (Finset V), IsPathPartition X P ∧ P.card = c}.Nonempty :=
    ⟨_, ⟨_, isPathPartition_singletons X, rfl⟩⟩
  exact Nat.sInf_mem hne

theorem pathPartitionNumber_le {X : SimpleGraph V} {P : Finset (Finset V)}
    (hP : IsPathPartition X P) : pathPartitionNumber X ≤ P.card :=
  Nat.sInf_le ⟨P, hP, rfl⟩

omit [Fintype V] in
/-- Every path block is nonempty: a path visits at least its own start. -/
theorem IsPathBlock.nonempty {X : SimpleGraph V} {t : Finset V}
    (h : IsPathBlock X t) : t.Nonempty := by
  obtain ⟨u, v, p, hp, hsupp⟩ := h
  exact ⟨u, by rw [← hsupp]; exact List.mem_toFinset.mpr p.start_mem_support⟩

/-- `P(X)` is an isomorphism invariant. Lemma 2.2 makes this immediate: both
`|V|` and `lambda` are transported by an isomorphism. -/
theorem pathPartitionNumber_iso {W : Type*} [Fintype W] [DecidableEq W]
    {X : SimpleGraph V} {Y : SimpleGraph W} (e : X ≃g Y) :
    pathPartitionNumber X = pathPartitionNumber Y := by
  have h1 := pathPartitionNumber_add_linearForestNumber X
  have h2 := pathPartitionNumber_add_linearForestNumber Y
  have h3 := linearForestNumber_iso e
  have h4 : Fintype.card V = Fintype.card W := Fintype.card_congr e.toEquiv
  omega

/-- **Definition 3.1, in general form.**

A path partition *splits along* `p` when every block meeting `{v | p v}` lies
inside it. Taking `p = InFibre q` gives the manuscript's `q`-factorizing
partitions.

The manuscript also phrases the condition on the associated spanning linear
forest ("contains no edge between `B_q(N)` and `R_{N,q}`"). That phrasing is
not formalized here, because a path partition recorded as a family of vertex
sets does not determine its forest: distinct paths can have the same support.
The vertex-set form is the one the proof of Theorem 3.2 uses. -/
def IsSplitPartition (G : SimpleGraph V) (p : V → Prop)
    (P : Finset (Finset V)) : Prop :=
  IsPathPartition G P ∧ ∀ t ∈ P, (∃ v ∈ t, p v) → ∀ v ∈ t, p v

/-- The least number of paths in a partition splitting along `p`. -/
noncomputable def splitPartitionNumber (G : SimpleGraph V) (p : V → Prop) : ℕ :=
  sInf {c | ∃ P : Finset (Finset V), IsSplitPartition G p P ∧ P.card = c}

/-- Each block of a split partition lies wholly inside `{v | p v}` or wholly
outside it. -/
theorem IsSplitPartition.all_or_none {G : SimpleGraph V} {p : V → Prop}
    {P : Finset (Finset V)} (hP : IsSplitPartition G p P) {t : Finset V}
    (ht : t ∈ P) : (∀ v ∈ t, p v) ∨ (∀ v ∈ t, ¬ p v) := by
  by_cases h : ∃ v ∈ t, p v
  · exact Or.inl (hP.2 t ht h)
  · exact Or.inr fun v hv hpv => h ⟨v, hv, hpv⟩

/-- The blocks of a path partition that lie inside `S`, pulled back to the
subgraph induced on `S`, form a path partition of it. -/
theorem isPathPartition_subtypeImage (G : SimpleGraph V) (S : Set V)
    [DecidablePred (· ∈ S)] {P : Finset (Finset V)} (hP : IsPathPartition G P)
    (hsub : ∀ t ∈ P, (∃ v ∈ t, v ∈ S) → ∀ v ∈ t, v ∈ S) :
    IsPathPartition (G.induce S)
      ((P.filter (fun t => ∀ v ∈ t, v ∈ S)).image
        (fun t => t.subtype (· ∈ S))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨htP, htS⟩ := Finset.mem_filter.mp ht
    exact isPathBlock_subtype (hP.isBlock t htP) htS
  · intro a ha b hb hab
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hb
    have htu : t ≠ u := fun h => hab (by rw [h])
    have hd := hP.pairwise t (Finset.mem_filter.mp ht).1 u (Finset.mem_filter.mp hu).1 htu
    rw [Finset.disjoint_left]
    intro x hx hx'
    rw [Finset.mem_subtype] at hx hx'
    exact (Finset.disjoint_left.mp hd hx) hx'
  · ext x
    simp only [Finset.mem_univ, iff_true]
    have hxu : (x : V) ∈ P.biUnion id := by
      rw [hP.covers]
      exact Finset.mem_univ _
    obtain ⟨t, ht, hxt⟩ := Finset.mem_biUnion.mp hxu
    refine Finset.mem_biUnion.mpr ⟨t.subtype (· ∈ S),
      Finset.mem_image.mpr ⟨t, Finset.mem_filter.mpr ⟨ht, hsub t ht ⟨(x : V), hxt, x.2⟩⟩, rfl⟩, ?_⟩
    change x ∈ t.subtype (· ∈ S)
    rw [Finset.mem_subtype]
    exact hxt

theorem pathPartitionNumber_le_filter_card (G : SimpleGraph V) (S : Set V)
    [DecidablePred (· ∈ S)] {P : Finset (Finset V)} (hP : IsPathPartition G P)
    (hsub : ∀ t ∈ P, (∃ v ∈ t, v ∈ S) → ∀ v ∈ t, v ∈ S) :
    pathPartitionNumber (G.induce S) ≤ (P.filter (fun t => ∀ v ∈ t, v ∈ S)).card :=
  le_trans (pathPartitionNumber_le (isPathPartition_subtypeImage G S hP hsub))
    Finset.card_image_le

/-- **Theorem 3.2, lower bound.** A partition splitting along `p` restricts to
a path partition on each side, so it can beat neither optimum. -/
theorem pathPartitionNumber_add_le_of_split (G : SimpleGraph V) (p : V → Prop)
    [DecidablePred p] {P : Finset (Finset V)} (hP : IsSplitPartition G p P) :
    pathPartitionNumber (G.induce {v | p v})
      + pathPartitionNumber (G.induce {v | ¬ p v}) ≤ P.card := by
  have hcompl : ∀ t ∈ P, (∃ v ∈ t, v ∈ {v | ¬ p v}) → ∀ v ∈ t, v ∈ {v | ¬ p v} := by
    rintro t ht ⟨w, hw, hpw⟩ v hv
    rcases hP.all_or_none ht with h | h
    · exact absurd (h w hw) hpw
    · exact h v hv
  have hA : pathPartitionNumber (G.induce {v | p v})
      ≤ (P.filter (fun t => ∀ v ∈ t, v ∈ ({v | p v} : Set V))).card :=
    pathPartitionNumber_le_filter_card G {v | p v} hP.1 hP.2
  have hB : pathPartitionNumber (G.induce {v | ¬ p v})
      ≤ (P.filter (fun t => ∀ v ∈ t, v ∈ ({v | ¬ p v} : Set V))).card :=
    pathPartitionNumber_le_filter_card G {v | ¬ p v} hP.1 hcompl
  have hdisj : Disjoint (P.filter (fun t => ∀ v ∈ t, v ∈ ({v | p v} : Set V)))
      (P.filter (fun t => ∀ v ∈ t, v ∈ ({v | ¬ p v} : Set V))) := by
    rw [Finset.disjoint_left]
    intro t ht ht'
    obtain ⟨htP, h1⟩ := Finset.mem_filter.mp ht
    obtain ⟨-, h2⟩ := Finset.mem_filter.mp ht'
    obtain ⟨w, hw⟩ := (hP.1.isBlock t htP).nonempty
    exact (h2 w hw) (h1 w hw)
  have hsum : (P.filter (fun t => ∀ v ∈ t, v ∈ ({v | p v} : Set V))).card
      + (P.filter (fun t => ∀ v ∈ t, v ∈ ({v | ¬ p v} : Set V))).card ≤ P.card := by
    rw [← Finset.card_union_of_disjoint hdisj]
    exact Finset.card_le_card
      (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _))
  exact le_trans (Nat.add_le_add hA hB) hsum

/-- **Theorem 3.2, upper bound.** The union of an optimal path partition of
each side is a partition splitting along `p`, of exactly the summed size. -/
theorem exists_splitPartition (G : SimpleGraph V) (p : V → Prop)
    [DecidablePred p] :
    ∃ P : Finset (Finset V), IsSplitPartition G p P ∧
      P.card = pathPartitionNumber (G.induce {v | p v})
        + pathPartitionNumber (G.induce {v | ¬ p v}) := by
  classical
  obtain ⟨A, hA, hAcard⟩ := exists_optimal_pathPartition (G.induce {v | p v})
  obtain ⟨B, hB, hBcard⟩ := exists_optimal_pathPartition (G.induce {v | ¬ p v})
  set Ai : Finset (Finset V) :=
    A.image (fun t : Finset ↥({v | p v} : Set V) => t.image Subtype.val) with hAi
  set Bi : Finset (Finset V) :=
    B.image (fun t : Finset ↥({v | ¬ p v} : Set V) => t.image Subtype.val) with hBi
  have hAin : ∀ s ∈ Ai, ∀ v ∈ s, p v := by
    intro s hs v hv
    obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hs
    exact mem_of_mem_image_val hv
  have hBin : ∀ s ∈ Bi, ∀ v ∈ s, ¬ p v := by
    intro s hs v hv
    obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hs
    exact mem_of_mem_image_val hv
  have hAblock : ∀ s ∈ Ai, IsPathBlock G s := by
    intro s hs
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hs
    exact isPathBlock_image_induce (hA.isBlock t ht)
  have hBblock : ∀ s ∈ Bi, IsPathBlock G s := by
    intro s hs
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hs
    exact isPathBlock_image_induce (hB.isBlock t ht)
  have hmixed : ∀ s ∈ Ai, ∀ t ∈ Bi, Disjoint s t := by
    intro s hs t ht
    rw [Finset.disjoint_left]
    intro v hv hv'
    exact (hBin t ht v hv') (hAin s hs v hv)
  have hABdisj : Disjoint Ai Bi := by
    rw [Finset.disjoint_left]
    intro s hs hs'
    obtain ⟨w, hw⟩ := (hAblock s hs).nonempty
    exact (hBin s hs' w hw) (hAin s hs w hw)
  refine ⟨Ai ∪ Bi, ⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_⟩
  · intro s hs
    rcases Finset.mem_union.mp hs with h | h
    · exact hAblock s h
    · exact hBblock s h
  · intro s hs t ht hst
    rcases Finset.mem_union.mp hs with hsA | hsB <;>
      rcases Finset.mem_union.mp ht with htA | htB
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hsA
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp htA
      exact disjoint_image_val
        (hA.pairwise a ha b hb fun h => hst (by rw [h]))
    · exact hmixed _ hsA _ htB
    · exact (hmixed _ htA _ hsB).symm
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hsB
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp htB
      exact disjoint_image_val
        (hB.pairwise a ha b hb fun h => hst (by rw [h]))
  · ext x
    simp only [Finset.mem_univ, iff_true]
    by_cases hx : p x
    · have hxu : (⟨x, hx⟩ : ↥({v | p v} : Set V)) ∈ A.biUnion id := by
        rw [hA.covers]
        exact Finset.mem_univ _
      obtain ⟨a, ha, hxa⟩ := Finset.mem_biUnion.mp hxu
      refine Finset.mem_biUnion.mpr ⟨a.image Subtype.val, ?_, ?_⟩
      · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ ha)
      · exact Finset.mem_image_of_mem _ hxa
    · have hxu : (⟨x, hx⟩ : ↥({v | ¬ p v} : Set V)) ∈ B.biUnion id := by
        rw [hB.covers]
        exact Finset.mem_univ _
      obtain ⟨a, ha, hxa⟩ := Finset.mem_biUnion.mp hxu
      refine Finset.mem_biUnion.mpr ⟨a.image Subtype.val, ?_, ?_⟩
      · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ ha)
      · exact Finset.mem_image_of_mem _ hxa
  · intro s hs hmeet v hv
    rcases Finset.mem_union.mp hs with h | h
    · exact hAin s h v hv
    · obtain ⟨w, hw, hpw⟩ := hmeet
      exact absurd hpw (hBin s h w hw)
  · rw [Finset.card_union_of_disjoint hABdisj, hAi, hBi,
      Finset.card_image_of_injective _ image_val_injective,
      Finset.card_image_of_injective _ image_val_injective, hAcard, hBcard]

/-- **Theorem 3.2, first statement, in general form.** -/
theorem splitPartitionNumber_eq (G : SimpleGraph V) (p : V → Prop)
    [DecidablePred p] :
    splitPartitionNumber G p
      = pathPartitionNumber (G.induce {v | p v})
        + pathPartitionNumber (G.induce {v | ¬ p v}) := by
  refine le_antisymm ?_ ?_
  · obtain ⟨P, hP, hcard⟩ := exists_splitPartition G p
    exact hcard ▸ Nat.sInf_le ⟨P, hP, rfl⟩
  · obtain ⟨P, hP, hcard⟩ :=
      Nat.sInf_mem (s := {c | ∃ P : Finset (Finset V), IsSplitPartition G p P ∧ P.card = c})
        (by
          obtain ⟨P, hP, -⟩ := exists_splitPartition G p
          exact ⟨P.card, P, hP, rfl⟩)
    calc pathPartitionNumber (G.induce {v | p v})
          + pathPartitionNumber (G.induce {v | ¬ p v})
        ≤ P.card := pathPartitionNumber_add_le_of_split G p hP
      _ = splitPartitionNumber G p := hcard

/-- Splitting can only cost paths: `P(X) ≤` the split optimum. -/
theorem pathPartitionNumber_le_splitPartitionNumber (G : SimpleGraph V)
    (p : V → Prop) :
    pathPartitionNumber G ≤ splitPartitionNumber G p := by
  classical
  obtain ⟨P, hP, hcard⟩ :=
    Nat.sInf_mem (s := {c | ∃ P : Finset (Finset V), IsSplitPartition G p P ∧ P.card = c})
      (by
        obtain ⟨P, hP, -⟩ := exists_splitPartition G p
        exact ⟨P.card, P, hP, rfl⟩)
  calc pathPartitionNumber G ≤ P.card := pathPartitionNumber_le hP.1
    _ = splitPartitionNumber G p := hcard

end Split

section Factorizing

/-- **Definition 3.1.** A path partition of `H_N` is `q`-factorizing when every
path meeting the fibre `B_q(N)` is entirely contained in it. -/
def IsFactorizingPartition {N : ℕ} (q : LargePrime N)
    (P : Finset (Finset (HVertex N))) : Prop :=
  IsSplitPartition (reducedDivisorGraph N) (InFibre q) P

theorem isFactorizingPartition_iff {N : ℕ} (q : LargePrime N)
    {P : Finset (Finset (HVertex N))} :
    IsFactorizingPartition q P ↔
      IsPathPartition (reducedDivisorGraph N) P ∧
        ∀ t ∈ P, (∃ v ∈ t, InFibre q v) → ∀ v ∈ t, InFibre q v :=
  Iff.rfl

/-- The least number of paths in a `q`-factorizing path partition of `H_N`. -/
noncomputable def factorizingPartitionNumber {N : ℕ} (q : LargePrime N) : ℕ :=
  splitPartitionNumber (reducedDivisorGraph N) (InFibre q)

theorem exists_optimal_factorizingPartition {N : ℕ} (q : LargePrime N) :
    ∃ P : Finset (Finset (HVertex N)), IsFactorizingPartition q P ∧
      P.card = factorizingPartitionNumber q := by
  have hne : {c | ∃ P : Finset (Finset (HVertex N)),
      IsSplitPartition (reducedDivisorGraph N) (InFibre q) P ∧ P.card = c}.Nonempty := by
    obtain ⟨P, hP, -⟩ := exists_splitPartition (reducedDivisorGraph N) (InFibre q)
    exact ⟨P.card, P, hP, rfl⟩
  exact Nat.sInf_mem hne

theorem pathPartitionNumber_le_factorizingPartitionNumber {N : ℕ} (q : LargePrime N) :
    pathPartitionNumber (reducedDivisorGraph N) ≤ factorizingPartitionNumber q :=
  pathPartitionNumber_le_splitPartitionNumber (reducedDivisorGraph N) (InFibre q)

/-- **Theorem 3.2, first statement.**

The minimum number of paths in a `q`-factorizing path partition of `H_N` is
`P(R_{N,q}) + F(s)`. -/
theorem factorizingPartitionNumber_eq {N : ℕ} (q : LargePrime N) :
    factorizingPartitionNumber q
      = pathPartitionNumber (fibreComplement q)
        + divisorPathPartitionNumber q.quotientType := by
  have h : factorizingPartitionNumber q
      = pathPartitionNumber (fibreGraph q) + pathPartitionNumber (fibreComplement q) :=
    splitPartitionNumber_eq (reducedDivisorGraph N) (InFibre q)
  have h2 : divisorPathPartitionNumber q.quotientType
      = pathPartitionNumber (divisorGraph q.quotientType) := rfl
  rw [h, pathPartitionNumber_iso (fibreIso q), h2]
  omega

/-- **Theorem 3.2, equation (3.2).**

`D_N(q)` is exactly the optimality penalty for imposing `q`-factorization. -/
theorem fibreDefect_eq_factorizationPenalty {N : ℕ} (q : LargePrime N) :
    fibreDefect q =
      (factorizingPartitionNumber q : ℤ)
        - (pathPartitionNumber (reducedDivisorGraph N) : ℤ) := by
  rw [fibreDefect_eq_pathPartitionForm q, factorizingPartitionNumber_eq q]
  push_cast
  ring

/-- **Theorem 3.2, equation (3.3).**

`D_N(q) = 0` exactly when `H_N` has a `q`-factorizing optimal path partition. -/
theorem fibreDefect_eq_zero_iff_exists_factorizing_optimum {N : ℕ} (q : LargePrime N) :
    fibreDefect q = 0 ↔
      ∃ P : Finset (Finset (HVertex N)), IsFactorizingPartition q P ∧
        P.card = pathPartitionNumber (reducedDivisorGraph N) := by
  rw [fibreDefect_eq_factorizationPenalty q, sub_eq_zero]
  constructor
  · intro h
    have hnat : factorizingPartitionNumber q
        = pathPartitionNumber (reducedDivisorGraph N) := by exact_mod_cast h
    obtain ⟨P, hP, hcard⟩ := exists_optimal_factorizingPartition q
    exact ⟨P, hP, by rw [hcard, hnat]⟩
  · rintro ⟨P, hP, hcard⟩
    have h1 : factorizingPartitionNumber q
        ≤ pathPartitionNumber (reducedDivisorGraph N) := by
      rw [← hcard]
      exact Nat.sInf_le ⟨P, hP, rfl⟩
    have h2 := pathPartitionNumber_le_factorizingPartitionNumber q
    exact_mod_cast le_antisymm h1 h2

/-- **The remark closing Section 3.1.** Positive defect means every optimal path
partition of `H_N` has a path crossing the fibre boundary. -/
theorem forall_optimum_not_factorizing_of_fibreDefect_pos {N : ℕ} (q : LargePrime N)
    (hpos : 0 < fibreDefect q) :
    ∀ P : Finset (Finset (HVertex N)),
      P.card = pathPartitionNumber (reducedDivisorGraph N) →
        ¬ IsFactorizingPartition q P := by
  intro P hcard hP
  exact absurd
    ((fibreDefect_eq_zero_iff_exists_factorizing_optimum q).mpr ⟨P, hP, hcard⟩)
    (by omega)

end Factorizing

end DivisorF
