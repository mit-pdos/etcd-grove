/-
**The rest buckets after `applySnapshot`** (D22 receiver epochs, S8d, step 5 of
`srvSnapApplied_of_walk`, `notes/snapshot-s8-plan.md`): `srvRest` at the snapshot's environment and
entries `A'`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SnapApplyNames
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.RestMemId

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- The records keep the rest buckets present. -/
theorem restPresent_restLeasesWith (f : w64 → w64) (ids : List w64) (r : apply.RestM)
    (h : restPresent r.bk) : restPresent (apply.restLeasesWith f ids r).bk := by
  unfold apply.restLeasesWith
  induction ids generalizing r with
  | nil => exact h
  | cons id ids ih =>
    simp only [List.foldl_cons]
    exact ih _ (restPresent_putIn r _ _ _ h)

/-- **Step 5: the rest buckets at the snapshot's entries** `A'`: the image's buckets `bk` at the
cluster's and the rest part's, the rest model's after `A'` with the records of the snapshot's table
at the TTLs `f` (`srvRestAt`'s; none in a cluster that grants none); (the lease-expiry plan's
S2–S4, Probe 4, 2026-11-05) in a cluster that grants leases, with the apply thread's half of the
live set at the table's ids, the permits, the table's requests and its half of the ids the lessor
ever had (`srvRest_close`). -/
theorem snap_srvRest (E : apply.AEnv GF) (γ' : ApplyNames) (TM' : MetaCI → IProp GF) (ci : Loc)
    (p' : mvcc.PhysNames) (g : GoFunc) (γB : backend.BNames) (d' : mvcc.KBReal) (γr : ReadNames)
    (al ast lp cl : Loc) (bk : GMap GoString backend.BktData) (memI : GMap w64 apply.MemberM)
    (A' : List EntryModel) (hγB : d'.γB = γB) (f : w64 → w64)
    -- (P6.2, 2026-11-03) the rest model's buckets the image's at the cluster's and the rest
    -- part's (until then everywhere: with auth on, the rest model does not model the admin writes)
    (hbk : ∀ n, membership.clusterBkts n ∨ restSet E.authMode n →
      (apply.restLeasesWith f (srvIds E (appliedTable γr A').ids)
        (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A'))).bk.lookup n = bk.lookup n)
    (hmem : (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A')).mem = memI)
    (hf : E.lg = true → leaseTTLsGeReq (appliedTable γr A') f) :
    backend.rbOwnIn d'.γB membership.clusterBkts bk ∗
      backend.rbPart d'.γB (restSet E.authMode) bk ∗ membership.clusterMem cl memI ∗
      alarmBeOn al d'.be ∗ authBeOn ast d'.be ∗ clusterBeOn cl d'.be ∗ lease.lessorBeOn lp d'.be ∗
      apply.ltHalf E (srvIds E (appliedTable γr A').ids) ∗ srvGrantIf E ∗
      srvReqsIf E (appliedTable γr A') ∗ srvEver E A' ⊢
    srvRest (snapE E γ' TM' ci p' g γB al ast lp cl d'.be) γr A' := by
  subst hγB
  iintro ⟨H0, H1, H2, H3, H4, H5, H6, HLt, #HG, #HQ, HU⟩
  iapply srvRest_close
  iexists f
  isplitr
  · ipureintro; exact hf
  generalize hr : apply.restLeasesWith f (srvIds E (appliedTable γr A').ids)
    (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A')) = r at hbk
  have hrm : r.mem = memI := by rw [← hr, apply.restLeasesWith_mem]; exact hmem
  have hmi : memIdOk memI := hmem ▸ restModel_memIdOk' _ _ _
  have hrp : restPresent r.bk := hr ▸ restPresent_restLeasesWith _ _ _
    (restPresent_restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A'))
  rw [show srvIds (snapE E γ' TM' ci p' g d'.γB al ast lp cl d'.be) (appliedTable γr A').ids =
    srvIds E (appliedTable γr A').ids from rfl, hr, snapE_RO,
    show apply.ltHalf (snapE E γ' TM' ci p' g d'.γB al ast lp cl d'.be)
      (srvIds E (appliedTable γr A').ids) = apply.ltHalf E (srvIds E (appliedTable γr A').ids) from rfl,
    show srvGrantIf (snapE E γ' TM' ci p' g d'.γB al ast lp cl d'.be) = srvGrantIf E from rfl,
    show srvReqsIf (snapE E γ' TM' ci p' g d'.γB al ast lp cl d'.be) (appliedTable γr A') =
      srvReqsIf E (appliedTable γr A') from rfl,
    show srvEver (snapE E γ' TM' ci p' g d'.γB al ast lp cl d'.be) A' = srvEver E A' from rfl]
  iframe HLt HG HQ HU
  unfold srvRestOwnH srvRestOwn srvObjsOn
  rw [hrm]
  ihave H0 := (backend.rbOwnIn_congr (GF := GF) _ _ _ _ (fun n h => (hbk n (.inl h)).symm)).1 $$ H0
  ihave H1 := (backend.rbPart_congr (GF := GF) _ _ _ _ (fun n h => (hbk n (.inr h)).symm)).1 $$ H1
  iframe
  ipureintro; exact ⟨hmi, hrp⟩

end proof
end EtcdGrove
end Perennial
