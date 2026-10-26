/-
**The new applier's options after `applySnapshot`, piece by piece** (D22 receiver epochs, S8d,
step 3's lemmas, `SnapApplyOpts.lean`): the lenses of the server's write right and rest resource
onto each object's backend part, the stores' contracts at the snapshot's backend, the KV, the hook,
and the server's own interfaces (`isRaftStatus`, `isSnapshotServer`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SnapApplyNames
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.LessorDerive
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__MemberID
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Leader
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Term
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__ForceSnapshot
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.cindex.consistentIndex__ConsistentIndex

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-! ## The server's write right and rest resource lend each object's backend part -/

theorem srvRestRWH_lens_alarm (γB : backend.BNames) (al ast lp cl be : Loc) :
    ⊢ rwLens (GF := GF) (srvRestRWH γB (srvObjsOn al ast lp cl be))
      iprop(srvRestRW γB ∗ alarmBeOn al be) := by
  iunfold rwLens
  iintro !> Hrw
  iunfold srvRestRWH at Hrw
  iunfold srvObjsOn at Hrw
  icases Hrw with ⟨Hrw, Hal, Hau, Hle, Hcb⟩
  isplitl [Hrw Hal]
  · iframe Hrw Hal
  iintro ⟨Hrw, Hal⟩
  iunfold srvRestRWH
  iunfold srvObjsOn
  iframe Hrw Hal Hau Hle Hcb

theorem srvRestRWH_lens_auth (γB : backend.BNames) (al ast lp cl be : Loc) :
    ⊢ rwLens (GF := GF) (srvRestRWH γB (srvObjsOn al ast lp cl be))
      iprop(srvRestRW γB ∗ authBeOn ast be) := by
  iunfold rwLens
  iintro !> Hrw
  iunfold srvRestRWH at Hrw
  iunfold srvObjsOn at Hrw
  icases Hrw with ⟨Hrw, Hal, Hau, Hle, Hcb⟩
  isplitl [Hrw Hau]
  · iframe Hrw Hau
  iintro ⟨Hrw, Hau⟩
  iunfold srvRestRWH
  iunfold srvObjsOn
  iframe Hrw Hal Hau Hle Hcb

theorem srvRestRWH_lens_lessor (γB : backend.BNames) (al ast lp cl be : Loc) :
    ⊢ rwLens (GF := GF) (srvRestRWH γB (srvObjsOn al ast lp cl be))
      iprop(srvRestRW γB ∗ lease.lessorBeOn lp be) := by
  iunfold rwLens
  iintro !> Hrw
  iunfold srvRestRWH at Hrw
  iunfold srvObjsOn at Hrw
  icases Hrw with ⟨Hrw, Hal, Hau, Hle, Hcb⟩
  isplitl [Hrw Hle]
  · iframe Hrw Hle
  iintro ⟨Hrw, Hle⟩
  iunfold srvRestRWH
  iunfold srvObjsOn
  iframe Hrw Hal Hau Hle Hcb

theorem srvRestRWH_lens_cluster (γB : backend.BNames) (al ast lp cl be : Loc) :
    ⊢ rwLens (GF := GF) (srvRestRWH γB (srvObjsOn al ast lp cl be))
      iprop(srvRestRW γB ∗ clusterBeOn cl be) := by
  iunfold rwLens
  iintro !> Hrw
  iunfold srvRestRWH at Hrw
  iunfold srvObjsOn at Hrw
  icases Hrw with ⟨Hrw, Hal, Hau, Hle, Hcb⟩
  isplitl [Hrw Hcb]
  · iframe Hrw Hcb
  iintro ⟨Hrw, Hcb⟩
  iunfold srvRestRWH
  iunfold srvObjsOn
  iframe Hrw Hal Hau Hle Hcb

theorem srvRestOwnH_lens_cluster (γB : backend.BNames) (al ast lp cl be : Loc) :
    ⊢ roLens (GF := GF) (srvRestOwnH γB cl (srvObjsOn al ast lp cl be))
      (fun r => iprop(srvRestOwn γB cl r ∗ clusterBeOn cl be)) := by
  iunfold roLens
  iintro !> %r Hro
  iunfold srvRestOwnH at Hro
  iunfold srvObjsOn at Hro
  icases Hro with ⟨Hro, Hal, Hau, Hle, Hcb⟩
  dsimp only
  isplitl [Hro Hcb]
  · iframe Hro Hcb
  iintro %r' ⟨Hro, Hcb⟩
  iunfold srvRestOwnH
  iunfold srvObjsOn
  iframe Hro Hal Hau Hle Hcb

/-! ## The logger -/

/-- The new options' logger is the server's, not `nil` (`srvFieldsAt`'s). -/
theorem snap_lg_nn (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF)
    (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (lg : Loc) :
    isServer s γ ci TM E ρ γr ∗ srvLgAddr s ↦□ lg ⊢ ⌜lg ≠ null⌝ := by
  iintro ⟨#HS, #Hlg⟩
  iunfold isServer at HS
  icases HS with ⟨-, -, ⟨%v, #Hf⟩, -⟩
  iunfold srvFieldsAt at Hf
  icases Hf with ⟨#Hlg', %Hnn, -⟩
  icombine Hlg Hlg' gives %Heq
  ipureintro; rw [Heq]; exact Hnn

/-! ## The stores' contracts at the new backend -/

theorem snap_isAlarmStore (al ast lp cl : Loc) (d' : mvcc.KBReal) (γs : mvcc.StoreNames)
    (hk : γs.kb = some d') (Pk : IProp GF) (g : GoFunc) (hgnn : g ≠ func.nil) :
    alarmApplyOk al ∗ backend.isBackend d'.γB d'.P (mvcc.lateW d'.gx) Pk d'.be ∗
      backend.plHookRO d'.γB g ⊢
    apply.isAlarmStore al γs Pk #g (srvRestRWH d'.γB (srvObjsOn al ast lp cl d'.be)) := by
  iintro ⟨#HalA, #HB, #Hhook⟩
  iunfold alarmApplyOk at HalA
  iapply HalA $$ %d' %(mvcc.lateW d'.gx) %Pk %γs %g
    %(srvRestRWH d'.γB (srvObjsOn al ast lp cl d'.be)) [] HB Hhook [] []
  · ipureintro; exact hk
  · ipureintro; exact hgnn
  · iapply srvRestRWH_lens_alarm

theorem snap_isAuthStore (al ast lp cl : Loc) (RD : IProp GF) (d' : mvcc.KBReal)
    (γs : mvcc.StoreNames) (hk : γs.kb = some d') (Pk : IProp GF) (g : GoFunc)
    (hgnn : g ≠ func.nil) :
    authApplyOk ast RD ∗ backend.isBackend d'.γB d'.P (mvcc.lateW d'.gx) Pk d'.be ∗
      backend.plHookRO d'.γB g ⊢
    apply.isAuthStore (auth.authIface ast) γs Pk #g RD .off
      (srvRestRWH d'.γB (srvObjsOn al ast lp cl d'.be)) := by
  iintro ⟨#HisAuth, #HB, #Hhook⟩
  iunfold authApplyOk at HisAuth
  iapply HisAuth $$ %d' %(mvcc.lateW d'.gx) %Pk %γs %g
    %(srvRestRWH d'.γB (srvObjsOn al ast lp cl d'.be)) [] HB Hhook [] []
  · ipureintro; exact hk
  · ipureintro; exact hgnn
  · iapply srvRestRWH_lens_auth

theorem snap_isCluster (al ast lp cl : Loc) (d' : mvcc.KBReal)
    (γs : mvcc.StoreNames) (hk : γs.kb = some d') (Pk : IProp GF) (g : GoFunc)
    (hgnn : g ≠ func.nil) :
    clusterApplyOk cl ∗ backend.isBackend d'.γB d'.P (mvcc.lateW d'.gx) Pk d'.be ∗
      backend.plHookRO d'.γB g ∗ (∃ n : Loc, membership.rcVersionChangedAddr cl ↦□ n) ⊢
    apply.isCluster cl γs Pk #g (srvRestOwnH d'.γB cl (srvObjsOn al ast lp cl d'.be))
      (srvRestRWH d'.γB (srvObjsOn al ast lp cl d'.be)) := by
  iintro ⟨#Hisc, #HB, #Hhook, #Hvcn⟩
  iunfold clusterApplyOk at Hisc
  iapply Hisc $$ %d' %(mvcc.lateW d'.gx) %Pk %γs %g
    %(srvRestOwnH d'.γB cl (srvObjsOn al ast lp cl d'.be))
    %(srvRestRWH d'.γB (srvObjsOn al ast lp cl d'.be)) [] HB Hhook [] [] [] []
  · ipureintro; exact hk
  · ipureintro; exact hgnn
  · iexact Hvcn
  · iapply srvRestOwnH_lens_cluster
  · iapply srvRestRWH_lens_cluster

theorem snap_isApplyLessor
    (hGL : lease.lessor.GetLease.spec (GF := GF) (hG := hG))
    (hAt : lease.lessor.Attach.spec (GF := GF) (hG := hG))
    (hDt : lease.lessor.Detach.spec (GF := GF) (hG := hG))
    (hSRD : lease.lessor.SetRangeDeleter.spec (GF := GF) (hG := hG))
    (hLk : lease.lessor.Lookup.spec (GF := GF) (hG := hG))
    (hGrant : lease.lessor.Grant.spec (GF := GF) (hG := hG))
    (hCk : lease.lessor.Checkpoint.spec (GF := GF) (hG := hG))
    (hTTL : lease.Lease.TTL.spec (GF := GF) (hG := hG))
    (al ast lp cl sst : Loc) (d' : mvcc.KBReal)
    (γs : mvcc.StoreNames) (hk : γs.kb = some d') (Pk : IProp GF) (g : GoFunc)
    (hgnn : g ≠ func.nil) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      lessorApplyOk lp ∗ lease.lessorCfg lp ∗ lessorLookupOk lp ∗ lease.lessorInv lp γs.leases ∗
      backend.isBackend d'.γB d'.P (mvcc.lateW d'.gx) Pk d'.be ∗ backend.plHookRO d'.γB g ⊢
    apply.isApplyLessor (lease.lessorIface lp) sst γs Pk #g
      (srvRestRWH d'.γB (srvObjsOn al ast lp cl d'.be)) := by
  iintro ⟨#Hpkg, #Hlbe, #Hlcfg, #Hllk, #Hlinv, #HB, #Hhook⟩
  ihave #Hlspkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease $$ []
  · iPkgInit
  iapply apply.isApplyLessor_of_lessorInv hGL hAt hDt hSRD hLk hGrant hCk hTTL lp sst γs
  iunfold lessorLookupOk at Hllk
  iframe Hllk Hlcfg Hlinv Hlspkg
  unfold mvcc.storeWT mvcc.storeRT
  rw [hk, show mvcc.kbWT (GF := GF) (some d') = backend.wbTok d'.γB from rfl,
    show mvcc.kbRT (GF := GF) (some d') = mvcc.bkRTx d'.γB d'.P d'.be from rfl]
  iunfold lessorApplyOk at Hlbe
  iapply Hlbe $$ %d' %(mvcc.lateW d'.gx) %Pk %g
    %(srvRestRWH d'.γB (srvObjsOn al ast lp cl d'.be)) HB Hhook [] []
  · ipureintro; exact hgnn
  · iapply srvRestRWH_lens_lessor

end proof
end EtcdGrove
end Perennial
