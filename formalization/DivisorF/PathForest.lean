import DivisorF.PathPartition
import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Tactic

set_option linter.style.header false

/-!
# From a path partition back to a spanning linear forest

`DivisorF.PathPartition` proves the forest-to-partition half of Lemma 2.2. This
module supplies the converse ingredient: the spanning subgraph traced by a path
is a linear forest, and linear forests supported on disjoint vertex sets can be
superposed. Together with the finite forest Euler identity these give

`Fintype.card V ≤ pathPartitionNumber X + linearForestNumber X`,

completing `P(X) = |V(X)| - lambda(X)`.

Like `LinearForestPath`, none of this is a project-original result; it is the
other half of the bridge lemma.
-/

namespace DivisorF

open SimpleGraph

variable {V : Type*} {X : SimpleGraph V}

/-- The spanning subgraph of `X` traced by a walk. -/
noncomputable def walkGraph {u v : V} (p : X.Walk u v) : SimpleGraph V :=
  p.toSubgraph.spanningCoe

theorem walkGraph_le {u v : V} (p : X.Walk u v) : walkGraph p ≤ X :=
  p.toSubgraph.spanningCoe_le

theorem walkGraph_adj_iff {u v a b : V} {p : X.Walk u v} :
    (walkGraph p).Adj a b ↔ p.toSubgraph.Adj a b := Iff.rfl

/-- Only vertices on the walk carry edges of `walkGraph`. -/
theorem mem_support_of_walkGraph_adj {u v a b : V} {p : X.Walk u v}
    (h : (walkGraph p).Adj a b) : a ∈ p.support := by
  rw [← SimpleGraph.Walk.mem_verts_toSubgraph]
  exact p.toSubgraph.edge_vert (walkGraph_adj_iff.mp h)

/-- A vertex with no incident edge reaches nothing but itself. -/
theorem not_reachable_of_forall_not_adj {G : SimpleGraph V} {a c : V}
    (hiso : ∀ b, ¬ G.Adj a b) (hac : a ≠ c) : ¬ G.Reachable a c := by
  rintro ⟨w⟩
  have hnil : ¬ w.Nil := by
    intro h
    exact hac (SimpleGraph.Walk.Nil.eq h)
  exact hiso _ (SimpleGraph.Walk.adj_snd hnil)

/-- `spanningCoe` distributes over joins of subgraphs. -/
theorem spanningCoe_sup (A B : X.Subgraph) :
    (A ⊔ B).spanningCoe = A.spanningCoe ⊔ B.spanningCoe := by
  ext x y
  simp

@[simp]
theorem walkGraph_nil {a : V} :
    walkGraph (SimpleGraph.Walk.nil : X.Walk a a) = ⊥ := by
  ext x y
  simp [walkGraph]

/-- Splitting off the first edge of a walk. -/
theorem walkGraph_cons {a b c : V} (h : X.Adj a b) (q : X.Walk b c) :
    walkGraph (SimpleGraph.Walk.cons h q) = walkGraph q ⊔ SimpleGraph.edge a b := by
  unfold walkGraph
  rw [SimpleGraph.Walk.toSubgraph, spanningCoe_sup,
    SimpleGraph.Subgraph.spanningCoe_subgraphOfAdj]
  exact sup_comm _ _

/-- **The graph traced by a path is acyclic.** -/
theorem walkGraph_isAcyclic {u v : V} {p : X.Walk u v} (hp : p.IsPath) :
    (walkGraph p).IsAcyclic := by
  induction p with
  | nil => simp
  | cons h q ih =>
      rename_i a b _
      have hq : q.IsPath := hp.of_cons
      have hnot : a ∉ q.support := ((SimpleGraph.Walk.cons_isPath_iff _ _).mp hp).2
      rw [walkGraph_cons]
      refine SimpleGraph.IsAcyclic.sup_edge_of_not_reachable ?_ (ih hq)
      exact not_reachable_of_forall_not_adj
        (fun c hc => hnot (mem_support_of_walkGraph_adj hc)) h.ne

/-- **The graph traced by a path has maximum degree two.** -/
theorem walkGraph_selectedDegree_le_two {u v : V} {p : X.Walk u v}
    (hp : p.IsPath) (w : V) : selectedDegree (walkGraph p) w ≤ 2 := by
  classical
  have hnb : (walkGraph p).neighborSet w = p.toSubgraph.neighborSet w := rfl
  unfold selectedDegree
  rw [hnb]
  by_cases hw : w ∈ p.support
  · by_cases hnil : p.Nil
    · have hempty : p.toSubgraph.neighborSet w = ∅ := by
        ext c
        simp only [Set.mem_empty_iff_false, iff_false]
        intro hc
        exact SimpleGraph.Walk.not_nil_of_adj_toSubgraph hc hnil
      rw [hempty]
      simp
    · rw [SimpleGraph.Walk.mem_support_iff_exists_getVert] at hw
      obtain ⟨i, hi, hilen⟩ := hw
      by_cases hi0 : i = 0
      · subst hi0
        have hwu : w = u := by rw [← hi]; simp
        subst hwu
        rw [hp.neighborSet_toSubgraph_startpoint hnil]
        simp
      · by_cases hilast : i = p.length
        · subst hilast
          have hwv : w = v := by rw [← hi]; simp
          subst hwv
          rw [hp.neighborSet_toSubgraph_endpoint hnil]
          simp
        · rw [← hi, hp.neighborSet_toSubgraph_internal hi0 (by omega)]
          calc ({p.getVert (i - 1), p.getVert (i + 1)} : Set V).ncard
              ≤ ({p.getVert (i + 1)} : Set V).ncard + 1 := Set.ncard_insert_le _ _
            _ = 2 := by simp
  · have hempty : p.toSubgraph.neighborSet w = ∅ := by
      ext c
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hc
      exact hw (mem_support_of_walkGraph_adj (walkGraph_adj_iff.mpr hc))
    rw [hempty]
    simp

/-- Edge count of the graph traced by a path: one less than its vertex count. -/
theorem walkGraph_edgeCard_succ [DecidableEq V] {u v : V} {p : X.Walk u v} (hp : p.IsPath) :
    edgeCard (walkGraph p) + 1 = p.support.toFinset.card := by
  classical
  have hE : (walkGraph p).edgeSet = {e | e ∈ p.edges} := by
    ext e
    induction e using Sym2.ind with
    | _ a b =>
        rw [SimpleGraph.mem_edgeSet]
        exact SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges
  have htf : p.edges.finite_toSet.toFinset = p.edges.toFinset := by
    ext e
    simp
  have hcard : edgeCard (walkGraph p) = p.edges.length := by
    unfold edgeCard
    rw [hE, Set.ncard_eq_toFinset_card _ p.edges.finite_toSet, htf]
    exact List.toFinset_card_of_nodup hp.edges_nodup
  rw [hcard, SimpleGraph.Walk.length_edges,
    List.toFinset_card_of_nodup hp.support_nodup, SimpleGraph.Walk.length_support]

/-- A graph all of whose edges live inside a finite vertex set. -/
def SupportedOn (G : SimpleGraph V) (A : Finset V) : Prop :=
  ∀ a b, G.Adj a b → a ∈ A ∧ b ∈ A

theorem supportedOn_walkGraph [DecidableEq V] {u v : V} (p : X.Walk u v) :
    SupportedOn (walkGraph p) p.support.toFinset := by
  intro a b h
  exact ⟨List.mem_toFinset.mpr (mem_support_of_walkGraph_adj h),
    List.mem_toFinset.mpr (mem_support_of_walkGraph_adj h.symm)⟩

/-- A walk starting inside `A` never leaves it, so all its edges come from `G₁`. -/
theorem edges_subset_of_supported {G₁ G₂ : SimpleGraph V} {A B : Finset V}
    (h₁ : SupportedOn G₁ A) (h₂ : SupportedOn G₂ B) (hAB : Disjoint A B)
    {x y : V} (w : (G₁ ⊔ G₂).Walk x y) :
    x ∈ A → ∀ e ∈ w.edges, e ∈ G₁.edgeSet := by
  induction w with
  | nil => intro _ e he; simp at he
  | @cons a b c h w' ih =>
      intro ha e he
      have hab : G₁.Adj a b := by
        simp only [SimpleGraph.sup_adj] at h
        rcases h with h' | h'
        · exact h'
        · exact absurd (h₂ _ _ h').1 (Finset.disjoint_left.mp hAB ha)
      rcases List.mem_cons.mp he with rfl | he'
      · exact hab
      · exact ih (h₁ _ _ hab).2 e he'

/-- The mirror statement, for a walk starting inside `B`. -/
theorem edges_subset_of_supported' {G₁ G₂ : SimpleGraph V} {A B : Finset V}
    (h₁ : SupportedOn G₁ A) (h₂ : SupportedOn G₂ B) (hAB : Disjoint A B)
    {x y : V} (w : (G₁ ⊔ G₂).Walk x y) :
    x ∈ B → ∀ e ∈ w.edges, e ∈ G₂.edgeSet := by
  induction w with
  | nil => intro _ e he; simp at he
  | @cons a b c h w' ih =>
      intro ha e he
      have hab : G₂.Adj a b := by
        simp only [SimpleGraph.sup_adj] at h
        rcases h with h' | h'
        · exact absurd (h₁ _ _ h').1 (Finset.disjoint_right.mp hAB ha)
        · exact h'
      rcases List.mem_cons.mp he with rfl | he'
      · exact hab
      · exact ih (h₂ _ _ hab).2 e he'

/-- **Superposition.** Acyclic graphs on disjoint vertex supports stay acyclic. -/
theorem isAcyclic_sup_of_disjoint_support {G₁ G₂ : SimpleGraph V} {A B : Finset V}
    (h₁ : SupportedOn G₁ A) (h₂ : SupportedOn G₂ B) (hAB : Disjoint A B)
    (hac₁ : G₁.IsAcyclic) (hac₂ : G₂.IsAcyclic) : (G₁ ⊔ G₂).IsAcyclic := by
  intro x c hc
  have hadj := SimpleGraph.Walk.adj_snd hc.not_nil
  simp only [SimpleGraph.sup_adj] at hadj
  rcases hadj with h | h
  · have hsub := edges_subset_of_supported h₁ h₂ hAB c (h₁ _ _ h).1
    exact hac₁ (c.transfer G₁ hsub) (hc.transfer hsub)
  · have hsub := edges_subset_of_supported' h₁ h₂ hAB c (h₂ _ _ h).1
    exact hac₂ (c.transfer G₂ hsub) (hc.transfer hsub)

/-- Degrees do not add across disjoint supports. -/
theorem selectedDegree_sup_le_of_disjoint_support {G₁ G₂ : SimpleGraph V} {A B : Finset V}
    (h₁ : SupportedOn G₁ A) (h₂ : SupportedOn G₂ B) (hAB : Disjoint A B)
    (hd₁ : ∀ v, selectedDegree G₁ v ≤ 2) (hd₂ : ∀ v, selectedDegree G₂ v ≤ 2) (v : V) :
    selectedDegree (G₁ ⊔ G₂) v ≤ 2 := by
  classical
  by_cases hv : v ∈ A
  · have hnb : (G₁ ⊔ G₂).neighborSet v = G₁.neighborSet v := by
      ext c
      simp only [SimpleGraph.mem_neighborSet, SimpleGraph.sup_adj]
      exact ⟨fun hc => hc.elim id
        (fun h' => absurd (h₂ _ _ h').1 (Finset.disjoint_left.mp hAB hv)), Or.inl⟩
    unfold selectedDegree
    rw [hnb]
    exact hd₁ v
  · by_cases hv2 : v ∈ B
    · have hnb : (G₁ ⊔ G₂).neighborSet v = G₂.neighborSet v := by
        ext c
        simp only [SimpleGraph.mem_neighborSet, SimpleGraph.sup_adj]
        exact ⟨fun hc => hc.elim (fun h' => absurd (h₁ _ _ h').1 hv) id, Or.inr⟩
      unfold selectedDegree
      rw [hnb]
      exact hd₂ v
    · have hnb : (G₁ ⊔ G₂).neighborSet v = ∅ := by
        ext c
        simp only [SimpleGraph.mem_neighborSet, SimpleGraph.sup_adj,
          Set.mem_empty_iff_false, iff_false, not_or]
        exact ⟨fun h' => hv (h₁ _ _ h').1, fun h' => hv2 (h₂ _ _ h').1⟩
      unfold selectedDegree
      rw [hnb]
      simp

/-- Edge counts add across disjoint supports. -/
theorem edgeCard_sup_of_disjoint_support [Finite V] {G₁ G₂ : SimpleGraph V} {A B : Finset V}
    (h₁ : SupportedOn G₁ A) (h₂ : SupportedOn G₂ B) (hAB : Disjoint A B) :
    edgeCard (G₁ ⊔ G₂) = edgeCard G₁ + edgeCard G₂ := by
  classical
  have hdisjE : Disjoint G₁.edgeSet G₂.edgeSet := by
    rw [Set.disjoint_left]
    intro e he1 he2
    induction e using Sym2.ind with
    | _ a b =>
        rw [SimpleGraph.mem_edgeSet] at he1 he2
        exact Finset.disjoint_left.mp hAB (h₁ _ _ he1).1 (h₂ _ _ he2).1
  unfold edgeCard
  rw [SimpleGraph.edgeSet_sup]
  exact Set.ncard_union_eq hdisjE (Set.toFinite _) (Set.toFinite _)

/-- **Superposing the parts of a path partition.**

Pairwise disjoint path blocks assemble into a spanning linear forest whose edge
count is the total block size less the number of blocks. -/
theorem exists_linearForest_of_pathBlocks [Finite V] [DecidableEq V]
    (X : SimpleGraph V) (P : Finset (Finset V)) :
    (∀ s ∈ P, IsPathBlock X s) →
    (∀ s ∈ P, ∀ t ∈ P, s ≠ t → Disjoint s t) →
    ∃ L, IsLinearForest X L ∧ SupportedOn L (P.biUnion id) ∧
      edgeCard L + P.card = ∑ s ∈ P, s.card := by
  classical
  induction P using Finset.induction_on with
  | empty =>
      intro _ _
      refine ⟨⊥, bot_isLinearForest X, ?_, ?_⟩
      · intro a b h
        simp at h
      · simp
  | @insert s P hs ih =>
      intro hblock hdisj
      obtain ⟨L, hL, hsupp, hcount⟩ :=
        ih (fun t ht => hblock t (Finset.mem_insert_of_mem ht))
          (fun t ht t' ht' => hdisj t (Finset.mem_insert_of_mem ht) t'
            (Finset.mem_insert_of_mem ht'))
      obtain ⟨u, v, p, hp, hpsupp⟩ := hblock s (Finset.mem_insert_self s P)
      have hdisjoint : Disjoint (P.biUnion id) s := by
        rw [Finset.disjoint_biUnion_left]
        intro t ht
        exact hdisj t (Finset.mem_insert_of_mem ht) s (Finset.mem_insert_self s P)
          (fun h => hs (h ▸ ht))
      have hwsupp : SupportedOn (walkGraph p) s := by
        rw [← hpsupp]
        exact supportedOn_walkGraph p
      refine ⟨L ⊔ walkGraph p, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
      · exact sup_le hL.1 (walkGraph_le p)
      · exact isAcyclic_sup_of_disjoint_support hsupp hwsupp hdisjoint hL.2.1
          (walkGraph_isAcyclic hp)
      · exact selectedDegree_sup_le_of_disjoint_support hsupp hwsupp hdisjoint hL.2.2
          (walkGraph_selectedDegree_le_two hp)
      · intro a b hab
        simp only [SimpleGraph.sup_adj] at hab
        rw [Finset.biUnion_insert]
        rcases hab with h | h
        · exact ⟨Finset.mem_union_right _ (hsupp a b h).1,
            Finset.mem_union_right _ (hsupp a b h).2⟩
        · exact ⟨Finset.mem_union_left _ (hwsupp a b h).1,
            Finset.mem_union_left _ (hwsupp a b h).2⟩
      · have hsum := edgeCard_sup_of_disjoint_support hsupp hwsupp hdisjoint
        have hblockCard : edgeCard (walkGraph p) + 1 = s.card := by
          rw [← hpsupp]
          exact walkGraph_edgeCard_succ hp
        rw [hsum, Finset.card_insert_of_notMem hs, Finset.sum_insert hs]
        omega

variable [Fintype V] [DecidableEq V]

/-- Every vertex on its own is a path block, so path partitions exist. -/
theorem isPathPartition_singletons (X : SimpleGraph V) :
    IsPathPartition X (Finset.image (fun v : V => ({v} : Finset V)) Finset.univ) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp ht
    exact ⟨v, v, SimpleGraph.Walk.nil, SimpleGraph.Walk.IsPath.nil, by simp⟩
  · intro t ht t' ht' hne
    obtain ⟨v, -, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp ht'
    simp only [Finset.disjoint_singleton]
    exact fun h => hne (by rw [h])
  · ext w
    simp

/-- **Lemma 2.2, partition-to-forest half.**

No vertex-disjoint path partition can beat `|V| - lambda(X)` parts. -/
theorem le_pathPartitionNumber_add_linearForestNumber (X : SimpleGraph V) :
    Fintype.card V ≤ pathPartitionNumber X + linearForestNumber X := by
  classical
  have hne : {c | ∃ P : Finset (Finset V), IsPathPartition X P ∧ P.card = c}.Nonempty :=
    ⟨_, ⟨_, isPathPartition_singletons X, rfl⟩⟩
  obtain ⟨P, hP, hPcard⟩ := Nat.sInf_mem hne
  obtain ⟨L, hL, -, hcount⟩ :=
    exists_linearForest_of_pathBlocks X P hP.isBlock hP.pairwise
  have hsum : ∑ s ∈ P, s.card = Fintype.card V := by
    rw [← Finset.card_biUnion
      (t := fun s : Finset V => s)
      (fun x hx y hy hxy => hP.pairwise x hx y hy hxy)]
    have hcov : P.biUnion (fun s : Finset V => s) = Finset.univ := hP.covers
    rw [hcov, Finset.card_univ]
  have hle : edgeCard L ≤ linearForestNumber X := edgeCard_le_linearForestNumber hL
  have hPP : P.card = pathPartitionNumber X := hPcard
  rw [← hPP]
  omega

/-- **Lemma 2.2.** `P(X) + lambda(X) = |V(X)|`, so the manuscript's path
partition number and the development's linear forest number determine each
other. -/
theorem pathPartitionNumber_add_linearForestNumber (X : SimpleGraph V) :
    pathPartitionNumber X + linearForestNumber X = Fintype.card V :=
  le_antisymm (pathPartitionNumber_add_linearForestNumber_le X)
    (le_pathPartitionNumber_add_linearForestNumber X)

end DivisorF
