module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRest

/-! # The members' ids are their keys (the backend-auth-split stage, Q1, 2026-11-02)

The fact the strong `membership.membersDecode` needs of the rest model (`membersDecode_putMember`:
`restUpdateAttrs` saves `memberKey a.memberID ↦ memberEnc (m.withAttrs a)`, a member whose id is its
key): every member the model keeps in `mem` has its key as its id (`memIdOk`). The applied log
keeps it (`restModel_memIdOk`): `ccRest`'s `AddNode` adds `ccMemberAt m`, whose id is the change's
node by definition; `restUpdateAttrs` changes a member's name and client URLs only; deletions and
the cluster version's put leave the members. What the boot gives (`memBoot`) is not settled here:
its members are `ccMemberOf cc.context`, whose id is opaque (the context's id is `ccContextOf`'s,
which `ccApplyOk` ties to the change's node, but `ccMemberOf`'s `id` field is not tied to it), so
`memIdOk (memBoot bootLog)` is the premise; the trusted step proposes `memBoot` with `ccMemberAt`
(Go's bootstrap members are keyed by their own id). -/

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open go_etcd_io.raft.v3

/-- **Every member the model keeps has its key as its id.** -/
def memIdOk (mem : GMap w64 apply.MemberM) : Prop :=
  ∀ id m, mem.lookup id = some m → m.id = id

theorem memIdOk_empty : memIdOk ∅ := by
  intro id m h; simp at h

theorem memIdOk_insert (mem : GMap w64 apply.MemberM) (id : w64) (m : apply.MemberM)
    (h : memIdOk mem) (hm : m.id = id) : memIdOk (mem.insert id m) := by
  intro id' m' hl
  rw [GMap.lookup_insert_eq_iff] at hl
  by_cases e : id = id'
  · rw [if_pos e] at hl; cases hl; exact hm.trans e
  · rw [if_neg e] at hl; exact h id' m' hl

theorem memIdOk_delete (mem : GMap w64 apply.MemberM) (id : w64) (h : memIdOk mem) :
    memIdOk (mem.delete id) := by
  intro id' m' hl
  rw [GMap.lookup_delete_iff] at hl
  by_cases e : id = id'
  · rw [if_pos e] at hl; cases hl
  · rw [if_neg e] at hl; exact h id' m' hl

theorem restAfter_memIdOk [GooseExts] (rq : apply.IRRModel) (v3 : Bool) (r : apply.RestM)
    (h : memIdOk r.mem) : memIdOk (apply.restAfter rq v3 r).mem := by
  unfold apply.restAfter
  split
  · unfold apply.restSetVersion
    cases v3 <;> simpa [apply.RestM.putIn_mem] using h
  · split
    next a ha =>
      unfold apply.restUpdateAttrs
      split
      · exact h
      next m hl =>
        have hi : memIdOk (r.mem.insert a.memberID (m.withAttrs a)) :=
          memIdOk_insert _ _ _ h (show (m.withAttrs a).id = a.memberID from h _ m hl)
        cases v3 <;> simpa [apply.RestM.putIn_mem] using hi
    next => exact h

theorem ccRest_memIdOk [GooseExts] (v3 : Bool) (m : ConfChangeM) (r : apply.RestM)
    (h : memIdOk r.mem) : memIdOk (ccRest v3 m r).mem := by
  unfold ccRest
  split
  · split
    · rw [apply.RestM.putIn_mem]
      exact memIdOk_insert _ _ _ h rfl
    · split
      · rw [apply.RestM.putIn_mem, apply.RestM.delIn_mem]
        exact memIdOk_delete _ _ h
      · exact h
  · exact h

theorem restEntry_memIdOk [GooseExts] (c0 : w64) (e : EntryModel) (r : apply.RestM)
    (h : memIdOk r.mem) : memIdOk (restEntry c0 e r).mem := by
  unfold restEntry
  split
  · split
    · exact h
    · split
      · exact restAfter_memIdOk _ _ _ h
      · exact h
  · split
    · exact ccRest_memIdOk _ _ _ h
    · exact h

/-- **The applied log keeps the members' ids their keys**, from a boot that has them. -/
theorem restModel_memIdOk [GooseExts] (c0 : w64) (bootLog : List EntryM) (L : List EntryModel)
    (h0 : memIdOk (memBoot bootLog)) : memIdOk (restModel c0 bootLog L).mem := by
  unfold restModel
  suffices H : ∀ (r : apply.RestM), memIdOk r.mem →
      memIdOk (L.foldl (fun r m => restEntry c0 m r) r).mem from H _ h0
  induction L with
  | nil => intro r hr; exact hr
  | cons e L ih => intro r hr; exact ih _ (restEntry_memIdOk c0 e r hr)

end EtcdGrove
end Perennial
