import DivisorF.FiniteForestEuler
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.Combinatorics.SimpleGraph.Walk.Counting
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Components of a linear forest are paths

The manuscript defines a spanning linear forest as a spanning subgraph whose
connected components are paths, and `DivisorF` represents it by the equivalent
degree/acyclicity condition `IsLinearForest`. This module proves the folklore
equivalence in the direction the path-partition bridge needs: a finite
connected acyclic graph of maximum degree at most two carries a Hamiltonian
path.

This is a support lemma, not a project-original result. It exists only so that
`DivisorF.PathPartition` can state Lemma 2.2 about genuine vertex-disjoint path
partitions rather than about linear forests by fiat.
-/

namespace DivisorF

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The greatest length of a path of `G`. -/
noncomputable def maxPathLength (G : SimpleGraph V) : ℕ := by
  classical
  exact Finset.univ.sup
    (fun x : (Σ u : V, Σ v : V, G.Path u v) => x.2.2.1.length)

/-- A path attaining `maxPathLength` exists as soon as `V` is nonempty. -/
theorem exists_maxPathLength_path (G : SimpleGraph V) [Nonempty V] :
    ∃ (u v : V) (p : G.Walk u v),
      p.IsPath ∧ p.length = maxPathLength G := by
  classical
  have hne : (Finset.univ : Finset (Σ u : V, Σ v : V, G.Path u v)).Nonempty := by
    refine ⟨⟨Classical.arbitrary V, Classical.arbitrary V,
      ⟨SimpleGraph.Walk.nil, SimpleGraph.Walk.IsPath.nil⟩⟩, Finset.mem_univ _⟩
  obtain ⟨x, -, hx⟩ :=
    Finset.exists_mem_eq_sup (Finset.univ) hne
      (fun x : (Σ u : V, Σ v : V, G.Path u v) => x.2.2.1.length)
  exact ⟨x.1, x.2.1, x.2.2.1, x.2.2.2, hx.symm⟩

/-- Every path is at most as long as `maxPathLength`. -/
theorem length_le_maxPathLength {G : SimpleGraph V} {u v : V}
    {p : G.Walk u v} (hp : p.IsPath) :
    p.length ≤ maxPathLength G := by
  classical
  exact Finset.le_sup (f := fun x : (Σ u : V, Σ v : V, G.Path u v) => x.2.2.1.length)
    (Finset.mem_univ (⟨u, v, ⟨p, hp⟩⟩ : Σ u : V, Σ v : V, G.Path u v))

/-- An interior vertex of a path has two distinct neighbours on that path. -/
theorem exists_two_path_neighbours
    {W : Type*} {G : SimpleGraph W} {u v x : W} {p : G.Walk u v}
    (hp : p.IsPath) (hx : x ∈ p.support) (hxu : x ≠ u) (hxv : x ≠ v) :
    ∃ a b : W, a ≠ b ∧ G.Adj x a ∧ G.Adj x b ∧
      a ∈ p.support ∧ b ∈ p.support := by
  classical
  set p₀ := p.takeUntil x hx with hp₀def
  set p₁ := p.dropUntil x hx with hp₁def
  have hspec : p₀.append p₁ = p := p.take_spec hx
  have hp₀ne : ¬ p₀.Nil := by
    intro hnil
    exact hxu (SimpleGraph.Walk.Nil.eq hnil).symm
  have hp₁ne : ¬ p₁.Nil := by
    intro hnil
    exact hxv (SimpleGraph.Walk.Nil.eq hnil)
  have hrevne : ¬ p₀.reverse.Nil := by simpa using hp₀ne
  refine ⟨p₀.reverse.snd, p₁.snd, ?_, ?_, ?_, ?_, ?_⟩
  · -- distinctness: the two sides of the split share only `x`
    intro hab
    have hnodup : p.support.Nodup := hp.support_nodup
    rw [← hspec, SimpleGraph.Walk.support_append] at hnodup
    have hmem₀ : p₀.reverse.snd ∈ p₀.support := by
      have h1 : p₀.reverse.snd ∈ p₀.reverse.support :=
        List.mem_of_mem_tail (SimpleGraph.Walk.snd_mem_tail_support hrevne)
      rwa [SimpleGraph.Walk.support_reverse, List.mem_reverse] at h1
    have hmem₁ : p₁.snd ∈ p₁.support.tail :=
      SimpleGraph.Walk.snd_mem_tail_support hp₁ne
    exact (List.disjoint_of_nodup_append hnodup) hmem₀ (hab ▸ hmem₁)
  · exact SimpleGraph.Walk.adj_snd hrevne
  · exact SimpleGraph.Walk.adj_snd hp₁ne
  · rw [← hspec, SimpleGraph.Walk.mem_support_append_iff]
    left
    have h1 : p₀.reverse.snd ∈ p₀.reverse.support :=
      List.mem_of_mem_tail (SimpleGraph.Walk.snd_mem_tail_support hrevne)
    rwa [SimpleGraph.Walk.support_reverse, List.mem_reverse] at h1
  · rw [← hspec, SimpleGraph.Walk.mem_support_append_iff]
    right
    exact List.mem_of_mem_tail (SimpleGraph.Walk.snd_mem_tail_support hp₁ne)

/-- **Folklore support lemma.** A finite connected graph whose degrees are all
at most two carries a Hamiltonian path.

Acyclicity is not needed: the only connected graphs of maximum degree two are
paths and cycles, and a cycle carries a Hamiltonian path as well. The linear
forests this is applied to are acyclic anyway. -/
theorem exists_isHamiltonian_of_connected_degree_le_two
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected)
    (hdeg : ∀ w : V, G.degree w ≤ 2) :
    ∃ (u v : V) (p : G.Walk u v), p.IsHamiltonian := by
  classical
  have : Nonempty V := hconn.nonempty
  obtain ⟨u, v, p, hp, hlen⟩ := exists_maxPathLength_path G
  refine ⟨u, v, p, hp.isHamiltonian_of_mem ?_⟩
  by_contra hcover
  obtain ⟨w, hw⟩ : ∃ w : V, w ∉ p.support := by
    by_contra hall
    exact hcover fun w => not_not.mp fun h => hall ⟨w, h⟩
  -- a walk from `u` into the uncovered part crosses the boundary of the support
  obtain ⟨q⟩ := hconn.preconnected u w
  obtain ⟨d, -, hfst, hsnd⟩ :=
    q.exists_boundary_dart {z | z ∈ p.support} p.start_mem_support hw
  set x := d.fst with hxdef
  set y := d.snd with hydef
  have hadj : G.Adj x y := d.adj
  have hxmem : x ∈ p.support := hfst
  have hynot : y ∉ p.support := hsnd
  -- `x` cannot be an endpoint: the path would extend, contradicting maximality
  have hxv : x ≠ v := by
    intro hxv
    subst hxv
    have hpath : (p.concat hadj).IsPath := hp.concat hynot hadj
    have := length_le_maxPathLength hpath
    rw [SimpleGraph.Walk.length_concat, hlen] at this
    omega
  have hxu : x ≠ u := by
    intro hxu
    subst hxu
    have hrev : p.reverse.IsPath := hp.reverse
    have hynot' : y ∉ p.reverse.support := by simpa using hynot
    have hpath : (p.reverse.concat hadj).IsPath := hrev.concat hynot' hadj
    have := length_le_maxPathLength hpath
    rw [SimpleGraph.Walk.length_concat, SimpleGraph.Walk.length_reverse, hlen] at this
    omega
  -- so `x` is interior and already has two neighbours on `p`, plus `y`
  obtain ⟨a, b, hab, hxa, hxb, hamem, hbmem⟩ :=
    exists_two_path_neighbours hp hxmem hxu hxv
  have hya : y ≠ a := by rintro rfl; exact hynot hamem
  have hyb : y ≠ b := by rintro rfl; exact hynot hbmem
  have hsub : ({a, b, y} : Finset V) ⊆ G.neighborFinset x := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl
    · simpa using hxa
    · simpa using hxb
    · simpa using hadj
  have hcard : ({a, b, y} : Finset V).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hab, Ne.symm hya]),
      Finset.card_insert_of_notMem (by simp [Ne.symm hyb])]
    simp
  have := Finset.card_le_card hsub
  rw [hcard, SimpleGraph.card_neighborFinset_eq_degree] at this
  exact absurd (hdeg x) (by omega)

end DivisorF
