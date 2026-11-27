/-
**The peer-URL directory of a cluster of any size** (`dirN`, putgetN's, the clusterN Scope,
2026-11-15; moved here from `putgetN/Defs.lean` and `putgetN/Dir.lean` on 2026-11-27, names and namespace
`etcd_putgetN` unchanged, since the multi-machine theorem reuses them). Lean-first (no Rocq
counterpart).

`dirN ms ids`: each member's one peer URL, at its id (the members `ms` with the ids `ids`, in order);
its laws for any members and ids: well formed (`netDirOk`, `dirN_ok`), naming the peers (`dirN_host`),
each member's peer URL its entry (`dirN_of_mem`), the ids its domain (`dirN_ne_nil`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.MembersDefs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_putgetN

open go_etcd_io.etcd.server.v3.etcdserver etcdstart

section pure
variable [GooseExts]

/-- **The peer-URL directory of the cluster** (the members `ms` with the ids `ids`, in order):
each member's one peer URL. -/
def dirN (ms : List GMember) (ids : List w64) (id : w64) : List GoString :=
  match (ms.zip ids).find? (fun p => decide (p.2 = id)) with
  | some p => [go!"http://" ++ p.1.Peer']
  | none => []

/-! ## The directory, for any members and ids -/

theorem dirN_of_mem (ms : List GMember) (ids : List w64) (hnd : ids.Nodup) (m : GMember)
    (id : w64) (h : (m, id) ∈ ms.zip ids) : dirN ms ids id = [go!"http://" ++ m.Peer'] := by
  unfold dirN
  induction ms generalizing ids with
  | nil => simp at h
  | cons a ms ih =>
    cases ids with
    | nil => simp at h
    | cons b ids =>
      rw [List.zip_cons_cons, List.find?_cons]
      rw [List.zip_cons_cons] at h
      rcases List.mem_cons.1 h with h | h
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
        simp
      · have hb : b ≠ id := fun e => (List.nodup_cons.1 hnd).1 (e ▸ (List.of_mem_zip h).2)
        simp only [hb, decide_false]
        exact ih ids (List.nodup_cons.1 hnd).2 h

theorem dirN_cases (ms : List GMember) (ids : List w64) (id : w64) :
    dirN ms ids id = [] ∨
      ∃ m, (m, id) ∈ ms.zip ids ∧ dirN ms ids id = [go!"http://" ++ m.Peer'] := by
  unfold dirN
  cases h : (ms.zip ids).find? (fun p => decide (p.2 = id)) with
  | none => left; rfl
  | some p =>
    right
    have he : p.2 = id := by have := List.find?_some h; simpa using this
    refine ⟨p.1, ?_, rfl⟩
    rw [← he]
    exact List.mem_of_find?_eq_some h

theorem zip_peer_inj (ms : List GMember) (ids : List w64) (hp : (ms.map (·.Peer')).Nodup)
    (m m' : GMember) (id id' : w64) (h : (m, id) ∈ ms.zip ids) (h' : (m', id') ∈ ms.zip ids)
    (he : m.Peer' = m'.Peer') : id = id' := by
  induction ms generalizing ids with
  | nil => simp at h
  | cons a ms ih =>
    cases ids with
    | nil => simp at h
    | cons b ids =>
      rw [List.zip_cons_cons] at h h'
      simp only [List.map_cons, List.nodup_cons] at hp
      rcases List.mem_cons.1 h with h1 | h2 <;> rcases List.mem_cons.1 h' with h1' | h2'
      · obtain ⟨-, rfl⟩ := Prod.mk.inj h1
        obtain ⟨-, rfl⟩ := Prod.mk.inj h1'
        rfl
      · obtain ⟨rfl, -⟩ := Prod.mk.inj h1
        exact absurd (he ▸ List.mem_map_of_mem (f := (·.Peer')) (List.of_mem_zip h2').1) hp.1
      · obtain ⟨rfl, -⟩ := Prod.mk.inj h1'
        exact absurd (he.symm ▸ List.mem_map_of_mem (f := (·.Peer')) (List.of_mem_zip h2).1) hp.1
      · exact ih ids hp.2 h2 h2'

/-- **The directory is well formed** (`netDirOk`, `NewServer`'s premise; putget3's `dir3_ok`). -/
theorem dirN_ok (ms : List GMember) (ids : List w64) (hnd : ids.Nodup) (h0 : W64 0 ∉ ids)
    (hp : (ms.map (·.Peer')).Nodup)
    (hpl : ∀ m ∈ ms, types.plainPeerURL (go!"http://" ++ m.Peer')) :
    netDirOk (dirN ms ids) := by
  refine ⟨?_, ?_, ?_⟩
  · rcases dirN_cases ms ids 0 with h | ⟨m, hm, -⟩
    · exact h
    · exact absurd (List.of_mem_zip hm).2 h0
  · intro i j h hi hj
    rcases dirN_cases ms ids i with hd | ⟨m, hm, hd⟩
    · rw [hd] at hi; simp at hi
    rcases dirN_cases ms ids j with hd' | ⟨m', hm', hd'⟩
    · rw [hd'] at hj; simp at hj
    rw [hd, List.mem_singleton] at hi
    rw [hd', List.mem_singleton] at hj
    exact zip_peer_inj ms ids hp m m' i j hm hm'
      ((List.append_cancel_left hi).symm.trans (List.append_cancel_left hj))
  · intro i s hs
    rcases dirN_cases ms ids i with hd | ⟨m, hm, hd⟩
    · rw [hd] at hs; simp at hs
    rw [hd, List.mem_singleton] at hs
    rw [hs]
    exact hpl m (List.of_mem_zip hm).1

/-- **A host of the directory is a member's peer address** (putget3's `dir3_host`). -/
theorem dirN_host (ms : List GMember) (ids : List w64) (i : w64) (h : GoString)
    (hm : go!"http://" ++ h ∈ dirN ms ids i) : h ∈ ms.map (·.Peer') := by
  rcases dirN_cases ms ids i with hd | ⟨m, hmz, hd⟩
  · rw [hd] at hm; simp at hm
  rw [hd, List.mem_singleton] at hm
  rw [List.append_cancel_left hm]
  exact List.mem_map_of_mem (List.of_mem_zip hmz).1

/-- **The directory's members are the ids** (`rafthttp.bootCfg`'s first half). -/
theorem dirN_ne_nil (ms : List GMember) (ids : List w64) (hlen : ms.length = ids.length)
    (hnd : ids.Nodup) (f : w64) : dirN ms ids f ≠ [] ↔ f ∈ ids := by
  constructor
  · intro h
    rcases dirN_cases ms ids f with hd | ⟨m, hm, -⟩
    · exact absurd hd h
    · exact (List.of_mem_zip hm).2
  · intro hf
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hf
    have hm : (ms[i]'(by omega), ids[i]) ∈ ms.zip ids := by
      have : (ms.zip ids)[i]'(by simp; omega) = (ms[i]'(by omega), ids[i]) := by simp
      rw [← this]; exact List.getElem_mem _
    rw [dirN_of_mem ms ids hnd _ _ hm]
    simp

end pure

end etcd_putgetN
end EtcdGrove
end Perennial
