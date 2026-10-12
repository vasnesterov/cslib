/-
Copyright (c) 2026 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/

module

public import Cslib.Init
public import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# Cycles through a given edge

`IsCycle.exists_path_of_mem_darts`: removing an edge `e` from a cycle `C` leaves a path between the
endpoints of `e` that uses only the other edges of `C`, only vertices of `C`, and has length
`|C| - 1`.
-/

@[expose] public section

namespace SimpleGraph.Walk

variable {V : Type*} {G : SimpleGraph V}

private lemma exists_path_of_mem_darts_aux {a : V} (c : G.Walk a a) (hc : c.IsCycle)
    (d : G.Dart) (hd : d ∈ c.darts) (hda : d.fst = a) :
    ∃ p : G.Walk d.snd a, p.IsPath ∧ (∀ e ∈ p.edges, e ∈ c.edges ∧ e ≠ d.edge) ∧
      (∀ x ∈ p.support, x ∈ c.support) ∧ p.length + 1 = c.length := by
  cases c with
  | nil => exact absurd hc (by simp [isCycle_def])
  | @cons _ x _ h q =>
    rw [cons_isCycle_iff] at hc
    rw [darts_cons, List.mem_cons] at hd
    rcases hd with rfl | hd
    · refine ⟨q, hc.1, fun e he => ⟨by simp [he], ?_⟩, fun y hy => by simp [hy], by simp⟩
      rintro rfl
      exact hc.2 he
    · exfalso
      have h1 : d.fst ∈ q.support.dropLast := by
        rw [← map_fst_darts]; exact List.mem_map_of_mem hd
      have h2 := hc.1.support_nodup
      rw [← dropLast_support_concat q, List.nodup_append] at h2
      exact h2.2.2 _ h1 _ (List.mem_singleton_self _) hda

/-- Removing the edge of a dart `d` from a cycle `c` leaves a path from `d.snd` to `d.fst` that uses
only the other edges and the vertices of `c`, of length `c.length - 1`. -/
theorem IsCycle.exists_path_of_mem_darts {v : V} {c : G.Walk v v} (hc : c.IsCycle)
    {d : G.Dart} (hd : d ∈ c.darts) :
    ∃ p : G.Walk d.snd d.fst, p.IsPath ∧ (∀ e ∈ p.edges, e ∈ c.edges ∧ e ≠ d.edge) ∧
      (∀ x ∈ p.support, x ∈ c.support) ∧ p.length + 1 = c.length := by
  classical
  have hmem : d.fst ∈ c.support := dart_fst_mem_support_of_mem_darts _ hd
  obtain ⟨p, hp, hpe, hps, hpl⟩ := exists_path_of_mem_darts_aux (c.rotate d.fst hmem)
    (hc.rotate hmem) d ((rotate_darts c _ hmem).mem_iff.mpr hd) rfl
  refine ⟨p, hp, fun e he => ?_, fun x hx => ?_, by simpa using hpl⟩
  · obtain ⟨h1, h2⟩ := hpe e he
    exact ⟨(rotate_edges c _ hmem).mem_iff.mp h1, h2⟩
  · exact (mem_support_rotate_iff c _ hmem).mp (hps x hx)

/-- Edge version of `IsCycle.exists_path_of_mem_darts`: for an edge `s(a, b)` of a cycle `c` there
is an `a`–`b` path using only the other edges and the vertices of `c`, of length `c.length - 1`. -/
theorem IsCycle.exists_path_of_mem_edges {v a b : V} {c : G.Walk v v} (hc : c.IsCycle)
    (he : s(a, b) ∈ c.edges) :
    ∃ p : G.Walk a b, p.IsPath ∧ (∀ e ∈ p.edges, e ∈ c.edges ∧ e ≠ s(a, b)) ∧
      (∀ x ∈ p.support, x ∈ c.support) ∧ p.length + 1 = c.length := by
  rw [edges, List.mem_map] at he
  obtain ⟨d, hd, hde⟩ := he
  obtain ⟨p, hp, hpe, hps, hpl⟩ := hc.exists_path_of_mem_darts hd
  have hde' : s(d.fst, d.snd) = s(a, b) := hde
  rw [Sym2.eq_iff] at hde'
  rcases hde' with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine ⟨(p.reverse.copy h1 h2), by simpa using hp, fun e he => ?_, fun x hx => ?_, by simpa⟩
    · simp only [edges_copy, edges_reverse, List.mem_reverse] at he
      obtain ⟨h3, h4⟩ := hpe e he
      exact ⟨h3, fun h5 => h4 (h5.trans hde.symm)⟩
    · simp only [support_copy, support_reverse, List.mem_reverse] at hx
      exact hps x hx
  · refine ⟨(p.copy h2 h1), by simpa using hp, fun e he => ?_, fun x hx => ?_, by simpa⟩
    · simp only [edges_copy] at he
      obtain ⟨h3, h4⟩ := hpe e he
      exact ⟨h3, fun h5 => h4 (h5.trans hde.symm)⟩
    · simp only [support_copy] at hx
      exact hps x hx

end SimpleGraph.Walk
