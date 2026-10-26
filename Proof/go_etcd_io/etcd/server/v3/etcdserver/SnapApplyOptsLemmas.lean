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

/-! ## The KV and the hook -/

/-- The new options' KV: the walk's watchable store, at the store's names on the new physical
names (`isWatchableStore_withPhys`), with its inner store's `ReadView`. -/
theorem snap_isApplyKV (ws st : Loc) (γw : mvcc.WsNames) (p' : mvcc.PhysNames)
    (γ : mvcc.StoreNames) (hγw : γw.st = γ) :
    mvcc.isWatchableStore (GF := GF) ws st γw ⊢
    apply.isApplyKV
      (interface.mkOk go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore.ty.PointerType #ws)
      st (γ.withPhys p') := by
  iintro #Hws
  iunfold apply.isApplyKV
  isplitr
  · iunfold txn.isKV
    iright
    iexists ws, { γw with st := γw.st.withPhys p' }
    rw [mvcc.isWatchableStore_withPhys]
    iframe Hws
    ipureintro; exact ⟨rfl, by rw [hγw]⟩
  · iunfold mvcc.isWatchableStore at Hws
    icases Hws with ⟨%vc, %stc, %rv, %γv, Hws⟩
    iNamed Hws
    iexists rv
    iframe Hrv
    iunfold mvcc.isReadView
    iexists _
    iframe Hrvkv
    rw [mvcc.isStore_withPhys, ← hγw]
    iframe Hs
    iunfold mvcc.kvOver; iright; iexists ws; iframe Hst; ipureintro; rfl

/-- The new store's hook: the recorded invariant and the backend's frozen hook `g`. -/
theorem snap_hookOk (γ : mvcc.StoreNames) (p' : mvcc.PhysNames) (d' : mvcc.KBReal)
    (hk : p'.kb = some d') (P : IProp GF) (g : GoFunc) (hgnn : g ≠ func.nil) :
    mvcc.hookP (γ.withPhys p') P ∗ backend.plHookRO d'.γB g ⊢ mvcc.hookOk (γ.withPhys p') P #g := by
  iintro ⟨#HP, #Hg⟩
  iunfold mvcc.hookOk
  iframe HP
  unfold mvcc.hookFn
  rw [show (γ.withPhys p').kb = some d' from hk]
  unfold mvcc.kbHookIs mvcc.bkHookIs
  iexists g
  iframe Hg
  ipureintro; exact ⟨rfl, hgnn⟩

/-! ## The server's own interfaces -/

/-- The server as the new options' `RaftStatusGetter`: from `srvFieldsAt`'s `memberID` and
`srvLeadInv`, and `srvAtomics`' term invariant. -/
theorem snap_isRaftStatus
    (hMID : EtcdServer.MemberID.spec (GF := GF) (hG := hG))
    (hLead : EtcdServer.Leader.spec (GF := GF) (hG := hG))
    (hTerm : EtcdServer.Term.spec (GF := GF) (hG := hG))
    (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF) (E : apply.AEnv GF)
    (ρ : ReqNames) (γr : ReadNames) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServer s γ ci TM E ρ γr ⊢
    apply.isRaftStatus (interface.mkOk EtcdServer.ty.PointerType #s) := by
  iintro ⟨#Hpkg, #HS⟩
  iunfold isServer at HS
  icases HS with ⟨-, -, ⟨%v, #Hf⟩, #Hat, -⟩
  iunfold srvFieldsAt at Hf
  icases Hf with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hmid, #Hlead, -⟩
  iunfold srvAtomics at Hat
  icases Hat with ⟨-, #Hti, -⟩
  iunfold apply.isRaftStatus
  iexists ⟨go.GoType.PointerType EtcdServer.ty, #s⟩
  isplitr
  · ipureintro; rfl
  isplitr
  · iintro !> !> %Φ' - HΦ'
    iapply (hMID s v.memberID) $$ [] [HΦ']
    · iframe Hpkg Hmid
    inext; iintro -; iapply HΦ'; itrivial
  isplitr
  · iintro !> !> %Φ' - HΦ'
    iapply (hLead s) $$ [] [HΦ']
    · iframe Hpkg Hlead
    inext; iintro %l -; iapply HΦ'; itrivial
  · iintro !> !> %Φ' - HΦ'
    iapply (hTerm s) $$ [] [HΦ']
    · iframe Hti Hpkg
    inext; iintro %t' -; iapply HΦ'; itrivial

/-- The server as the new options' `SnapshotServer`, under the environment's `FS` (`srvEnvOk`'s
`E.FS = srvFS s`). -/
theorem snap_isSnapshotServer
    (hFS : EtcdServer.ForceSnapshot.spec (GF := GF) (hG := hG))
    (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF) (E : apply.AEnv GF)
    (ρ : ReqNames) (γr : ReadNames) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServer s γ ci TM E ρ γr ⊢
    apply.isSnapshotServer (interface.mkOk EtcdServer.ty.PointerType #s) E.FS := by
  iintro ⟨#Hpkg, #HS⟩
  iunfold isServer at HS
  icases HS with ⟨-, -, ⟨%v, #Hf⟩, -⟩
  iunfold srvFieldsAt at Hf
  icases Hf with ⟨-, -, -, -, -, %Henv, -⟩
  rw [Henv.1]
  iunfold apply.isSnapshotServer
  iexists ⟨go.GoType.PointerType EtcdServer.ty, #s⟩
  isplitr
  · ipureintro; rfl
  iintro !> !> %Φ' Hfs HΦ'
  iapply (hFS s) $$ [Hfs] [HΦ']
  · iframe Hpkg; iframe Hfs
  inext; iintro Hfs; iapply HΦ'; iexact Hfs

/-! ## The consistent indexer -/

/-- The consistent index as the new options' indexer, over `srvCiC`'s loaded states (`wp_ci_get`
returns `stLoaded γ st`, which is `st` for them; D22 receiver epochs, S8d, 2026-10-26: `srvCiC`
admitted unloaded states until then, over which the contract is false once `γ.m0.1 ≠ 0`, after a
snapshot). -/
theorem snap_isConsistentIndexer
    (hCIg : consistentIndex.ConsistentIndex.spec (GF := GF) (hG := hG))
    (s : Loc) (γ : ApplyNames) (ci : Loc) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerCI s γ ci ⊢
    apply.isConsistentIndexer (ciIface ci) (srvCiC γ ci) := by
  iintro ⟨#Hpkg, #HCI⟩
  ihave #Hcipkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.cindex
    $$ []
  · iPkgInit
  iunfold isServerCI at HCI
  icases HCI with ⟨-, #HisCI, #Hcons⟩
  iunfold apply.isConsistentIndexer
  iexists ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.cindex.consistentIndex.ty, #ci⟩
  isplitr
  · ipureintro; rfl
  iintro !> %C %HC
  obtain ⟨cst, cb, hC, hcp, hld⟩ := HC
  subst hC
  iintro %Φ' !> Hpre HΦ'
  iapply (wp_wand (Φ := fun w => iprop((∀ x : w64,
      iprop(applyThread γ cst ∗ applyBackend γ ci cb) -∗ Φ' #x) ∗
      (⌜w = #(ciEff γ cst.k)⌝ ∗ applyThread γ cst ∗ applyBackend γ ci cb))))
    $$ [Hpre HΦ']
  · iapply (wp_frame_step_l' (by rfl) Std.LawfulSet.subset_refl)
    iframe HΦ'
    icases Hpre with ⟨Hcst, Hcb⟩
    iapply (wp_ci_get hCIg γ ci cb cst hcp) $$ [Hcst Hcb]
    · iframe Hcipkg Hcons HisCI; iframe Hcst Hcb
    iintro ⟨Hcst, Hcb⟩
    rw [hld]
    iframe Hcst Hcb
    ipureintro; rfl
  · iintro %w ⟨HΦ', %Hw, HP⟩
    subst Hw
    iapply HΦ' $$ HP

end proof
end EtcdGrove
end Perennial
