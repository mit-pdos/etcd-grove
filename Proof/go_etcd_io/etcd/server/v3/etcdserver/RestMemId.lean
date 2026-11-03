module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRest

/-! # The members' ids are their keys (the backend-auth-split stage, Q1, 2026-11-02)

The fact the strong `membership.membersDecode` needs of the rest model (`membersDecode_putMember`:
`restUpdateAttrs` saves `memberKey a.memberID ↦ memberEnc (m.withAttrs a)`, a member whose id is its
key): every member the model keeps in `mem` has its key as its id (`memIdOk`). The applied log
keeps it (`restModel_memIdOk`): `ccRest`'s `AddNode` adds `ccMemberAt m`, whose id is the change's
node by definition; `restUpdateAttrs` changes a member's name and client URLs only; deletions and
the cluster version's put leave the members. The boot gives it too (`memIdOk_memBoot`): `memBoot`'s
members are `ccMemberAt cc`, the change's node as the id (the trusted step, 2026-11-02: Go's
bootstrap members are keyed by their own id; until then `ccMemberOf cc.context`, whose id was
opaque, and `memIdOk (memBoot bootLog)` a premise). With it the membership buckets of every
`restModel` decode (`membersDecode_restModel`). -/

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open go_etcd_io.raft.v3

/- `memIdOk` (every member the model keeps has its key as its id) is defined in `InvRest.lean`
since 2026-11-02 (the backend-auth-split stage: `srvRestOwn` holds it). -/

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

/-- **The boot's members have their keys as their ids** (2026-11-02, the backend-auth-split stage:
`memBoot`'s members are `ccMemberAt cc`, whose id is the change's node). -/
theorem memIdOk_memBoot [GooseExts] (bootLog : List EntryM) : memIdOk (memBoot bootLog) := by
  unfold memBoot
  suffices H : ∀ (l : List EntryM) (acc : GMap w64 apply.MemberM), memIdOk acc →
      memIdOk (l.foldl (fun mem e => match ccDecodeV1 e.Data' with
        | some cc => mem.insert cc.nodeId (membership.ccMemberAt cc)
        | none => mem) acc) from H bootLog ∅ memIdOk_empty
  intro l
  induction l with
  | nil => intro acc h; exact h
  | cons e l ih =>
    intro acc h
    rw [List.foldl_cons]
    apply ih
    split
    · exact memIdOk_insert _ _ _ h rfl
    · exact h

/-- **The applied log keeps the members' ids their keys** (`restModel_memIdOk` with the boot's,
`memIdOk_memBoot`). -/
theorem restModel_memIdOk' [GooseExts] (c0 : w64) (bootLog : List EntryM) (L : List EntryModel) :
    memIdOk (restModel c0 bootLog L).mem :=
  restModel_memIdOk c0 bootLog L (memIdOk_memBoot bootLog)

theorem restAfter_membersDecode [GooseExts] (rq : apply.IRRModel) (v3 : Bool) (r : apply.RestM)
    (hm : memIdOk r.mem) (h : membership.membersDecode r.bk) :
    membership.membersDecode (apply.restAfter rq v3 r).bk := by
  unfold apply.restAfter
  split
  · unfold apply.restSetVersion
    cases v3
    · exact h
    · exact membership.membersDecode_other _ _ _ _
        (by unfold membership.memberBkts; decide) h
  · split
    next a ha =>
      unfold apply.restUpdateAttrs
      split
      · exact h
      next m hl =>
        have hid : (m.withAttrs a).id = a.memberID := hm _ m hl
        cases v3
        · exact h
        · show membership.membersDecode (apply.bkPut r.bk go!"members"
            (apply.memberKey a.memberID) (apply.memberEnc (m.withAttrs a)))
          rw [← hid]
          exact membership.membersDecode_putMember _ _ h
    next => exact h

theorem ccRest_membersDecode [GooseExts] (v3 : Bool) (m : ConfChangeM) (r : apply.RestM)
    (h : membership.membersDecode r.bk) : membership.membersDecode (ccRest v3 m r).bk := by
  unfold ccRest
  split
  · split
    · exact membership.membersDecode_putMember _ (membership.ccMemberAt m) h
    · split
      · exact membership.membersDecode_putRemoved _ _ _
          (membership.membersDecode_delMember _ _ h)
      · exact h
  · exact h

theorem restEntry_membersDecode [GooseExts] (c0 : w64) (e : EntryModel) (r : apply.RestM)
    (hm : memIdOk r.mem) (h : membership.membersDecode r.bk) :
    membership.membersDecode (restEntry c0 e r).bk := by
  unfold restEntry
  split
  · split
    · exact h
    · split
      · exact restAfter_membersDecode _ _ _ hm h
      · exact h
  · split
    · exact ccRest_membersDecode _ _ _ h
    · exact h

/-- **The membership buckets of every applied log decode** (2026-11-02, the backend-auth-split
stage): by induction on the log with `memIdOk` alongside, from the boot's empty buckets. What
`EtcdServer.apply`'s proof discharges `applyConfChange.spec`'s premise `membersDecode rs.bk` with. -/
theorem membersDecode_restModel [GooseExts] (c0 : w64) (bootLog : List EntryM)
    (L : List EntryModel) : membership.membersDecode (restModel c0 bootLog L).bk := by
  unfold restModel
  suffices H : ∀ (r : apply.RestM), memIdOk r.mem → membership.membersDecode r.bk →
      membership.membersDecode (L.foldl (fun r m => restEntry c0 m r) r).bk from
    H _ (memIdOk_memBoot bootLog)
      (membership.membersDecode_empty _
        (by simp [restBoot, restBootBk, GMap.lookup_insert_ne, GMap.lookup_insert])
        (by simp [restBoot, restBootBk, GMap.lookup_insert_ne, GMap.lookup_insert]))
  induction L with
  | nil => intro r _ hr; exact hr
  | cons e L ih =>
    intro r hm hr
    exact ih _ (restEntry_memIdOk c0 e r hm) (restEntry_membersDecode c0 e r hm hr)

end EtcdGrove
end Perennial
