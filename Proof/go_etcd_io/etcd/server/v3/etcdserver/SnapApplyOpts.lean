/-
**The new applier's options after `applySnapshot`** (D22 receiver epochs, S8d, step 3 of
`srvSnapApplied_of_walk`, `notes/snapshot-s8-plan.md`): `apply.backendOptsOk` at the snapshot's
environment, what the walk's `NewUberApplier` post (`Hube`) takes.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SnapApplyNames
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SnapApplyOptsLemmas
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

/-- **Step 3: the new applier's options' contracts** at `E' = snapE …` (persistent).

Brief for the prover: as `NewServer.lean:1040-1110` (the lessor's and the auth store's) and
`NewServer.lean:1415-1530` (`Hbo`, the rest) do at boot, with the boot's `d`, `γA`, `#hook`,
`srvRestRWH d.γB (srvObjsOn …)` replaced by `d'`, `γ'`, `#g`, `E'.RW`. Unfold
`apply.backendOptsOk`, `simp only [snapE_…]`, rewrite the options' fields (`hopts`).
- `opts'.Logger' ≠ null`: `lg` is the old `srvFieldsAt`'s `v.lg` (agreement of the two `↦□` of
  `srvLgAddr s`), `⌜v.lg ≠ null⌝`.
- `isApplyKV`: `txn.isKV` by its right disjunct at `{ γw with st := γw.st.withPhys p' }`
  (`mvcc.isWatchableStore_withPhys`, `RestorePre.lean`, rewrites the walk's `isWatchableStore ws E.s
  γw`; `hγw`); the `ReadView` field and `isReadView` from unfolding `isWatchableStore` (as
  `BuildLemmas.lean`'s `iunfold mvcc.isWatchableStore at Hws'`, `Hrv`, `Hrvkv`, `Hs`, `Hst`).
- `mvcc.hookOk E'.γ E'.P #g`: `hookP` the hypothesis (`hγw`: `E'.γ = γw.st.withPhys p'`); `hookFn`
  unfolds to `kbHookIs (some d')` (`hkb'`) `= bkHookIs d'.γB #g`: `g`, `hgnn` and `plHookRO`
  (`hγB`). (`mvcc.hookOk_of_init` is the boot's form, for the `none`-hook case.)
- `isApplyLessor`: `apply.isApplyLessor_of_lessorInv` (the eight lease specs; `iPkgInit` for the
  lease package; `lessorLookupOk lp` unfolds to its `Lookup` clause) with `lessorApplyOk lp`
  applied at `d'`, `W := mvcc.lateW d'.gx`, `Pk := E'.P`, `g`, `RW := E'.RW`, its `rwLens` as at
  boot (`srvRestRWH`, `srvObjsOn` taken apart and put back); `mvcc.storeWT`/`storeRT` of `E'.γ`
  are `backend.wbTok d'.γB`/`bkRTx d'.γB d'.P d'.be` (`hkb'`, `rfl`).
- `isAuthStore … E'.RD E'.authMode E'.RW`: `authApplyOk ast E.RD` at `d'` (mode `.off`: `hoff`).
- `isAlarmStore`, `isCluster`: `alarmApplyOk al`, `clusterApplyOk cl` at `d'` (`roLens`/`rwLens`
  as at boot; `rcVersionChangedAddr` the hypothesis).
- `isRaftStatus`, `isSnapshotServer`, `isConsistentIndexer`: as at boot, `hMID` (with the old
  `srvFieldsAt`'s `srvMemberIDAddr s ↦□ v.memberID`), `hLead` (`srvLeadInv s`), `hTerm` (the old
  `srvAtomics`' term invariant), `hFS` (`E'.FS = E.FS = srvFS s`, the old `srvEnvOk`), and
  `wp_ci_get hCIg` at `γ'` (`isServerCI s γ' ci`'s `isCI`, `consInv`; `iPkgInit` for `cindex`). -/
theorem snap_backendOptsOk
    (hGL : lease.lessor.GetLease.spec (GF := GF) (hG := hG))
    (hAt : lease.lessor.Attach.spec (GF := GF) (hG := hG))
    (hDt : lease.lessor.Detach.spec (GF := GF) (hG := hG))
    (hSRD : lease.lessor.SetRangeDeleter.spec (GF := GF) (hG := hG))
    (hLk : lease.lessor.Lookup.spec (GF := GF) (hG := hG))
    (hGrant : lease.lessor.Grant.spec (GF := GF) (hG := hG))
    (hCk : lease.lessor.Checkpoint.spec (GF := GF) (hG := hG))
    (hTTL : lease.Lease.TTL.spec (GF := GF) (hG := hG))
    (hMID : EtcdServer.MemberID.spec (GF := GF) (hG := hG))
    (hLead : EtcdServer.Leader.spec (GF := GF) (hG := hG))
    (hTerm : EtcdServer.Term.spec (GF := GF) (hG := hG))
    (hFS : EtcdServer.ForceSnapshot.spec (GF := GF) (hG := hG))
    (hCIg : consistentIndex.ConsistentIndex.spec (GF := GF) (hG := hG))
    (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF) (E : apply.AEnv GF)
    (ρ : ReqNames) (γr : ReadNames) (π0 : ApplyPhys) (γB : backend.BNames) (P : backend.BParams)
    (d' : mvcc.KBReal) (p' : mvcc.PhysNames) (γw : mvcc.WsNames) (ws : Loc) (g : GoFunc)
    (opts' : apply.ApplierOptions) (lg : Loc) (al ast lp cl : Loc)
    (hγB : d'.γB = γB) (hkb' : p'.kb = some d') (hγw : γw.st = E.γ) (hwq : E.γ.watchQ = true)
    (hgnn : g ≠ func.nil) (hoff : E.authMode = auth.AuthMode.off)
    (hopts : opts'.Logger' = lg ∧
      opts'.KV' = interface.mkOk go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore.ty.PointerType #ws ∧
      opts'.AlarmStore' = al ∧ opts'.AuthStore' = auth.authIface ast ∧
      opts'.Lessor' = lease.lessorIface lp ∧ opts'.Cluster' = cl ∧
      opts'.ConsistentIndex' = ciIface ci ∧
      opts'.RaftStatus' = interface.mkOk EtcdServer.ty.PointerType #s ∧
      opts'.SnapshotServer' = interface.mkOk EtcdServer.ty.PointerType #s) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServer s γ ci TM E ρ γr ∗ srvLgAddr s ↦□ lg ∗
      isServerCI s (snapγ γ π0 γB) ci ∗
      backend.isBackend d'.γB d'.P (mvcc.lateW d'.gx)
        (batchLockInv (snapγ γ π0 γB) (metaTM γB P)) d'.be ∗
      backend.plHookRO γB g ∗
      mvcc.hookP (γw.st.withPhys p') (batchLockInv (snapγ γ π0 γB) (metaTM γB P)) ∗
      mvcc.isWatchableStore ws E.s γw ∗
      alarmApplyOk al ∗ authApplyOk ast E.RD ∗ lessorApplyOk lp ∗ clusterApplyOk cl ∗
      lease.lessorCfg lp ∗ lessorLookupOk lp ∗ (∃ n : Loc, membership.rcVersionChangedAddr cl ↦□ n) ∗
      lease.lessorInv lp E.γ.leases ⊢
    apply.backendOptsOk (snapE E (snapγ γ π0 γB) (metaTM γB P) ci p' g γB al ast lp cl d'.be)
      opts' := by
  subst hγB
  obtain ⟨Hu1, Hu2, Hu3, Hu4, Hu5, Hu6, Hu7, Hu8, Hu9⟩ := hopts
  have hk : (E.γ.withPhys p').kb = some d' := hkb'
  iintro ⟨#Hpkg, #HS, #Hlg, #HCI, #HB, #Hhook, #HhP, #Hws, #HalA, #HauA, #HleA, #HclA, #Hlcfg,
    #Hllk, #Hvcn, #Hlinv⟩
  iunfold apply.backendOptsOk
  simp only [snapE_s, snapE_γ, snapE_P, snapE_f, snapE_RD, snapE_authMode, snapE_FS, snapE_ciC,
    snapE_RO, snapE_RW]
  rw [Hu1, Hu2, Hu3, Hu4, Hu5, Hu6, Hu7, Hu8, Hu9, hoff]
  isplitr
  · iapply snap_lg_nn s γ ci TM E ρ γr lg $$ [$HS $Hlg]
  isplitr
  · iapply snap_isApplyKV ws E.s γw p' E.γ hγw $$ Hws
  isplitr
  · rw [← hγw]
    iapply snap_hookOk γw.st p' d' hkb' _ g hgnn $$ [$HhP $Hhook]
  isplitr
  · iapply snap_isApplyLessor hGL hAt hDt hSRD hLk hGrant hCk hTTL al ast lp cl E.s d'
      (E.γ.withPhys p') hk _ g hgnn
    iframe Hpkg HleA Hlcfg Hllk HB Hhook
    rw [mvcc.StoreNames.withPhys_leases]; iexact Hlinv
  isplitr
  · iapply snap_isAuthStore al ast lp cl E.RD d' (E.γ.withPhys p') hk _ g hgnn
    iframe HauA HB Hhook
  isplitr
  · iapply snap_isAlarmStore al ast lp cl d' (E.γ.withPhys p') hk _ g hgnn
    iframe HalA HB Hhook
  isplitr
  · iapply snap_isCluster al ast lp cl d' (E.γ.withPhys p') hk _ g hgnn
    iframe HclA HB Hhook Hvcn
  isplitr
  · iapply snap_isRaftStatus hMID hLead hTerm s γ ci TM E ρ γr $$ [$Hpkg $HS]
  isplitr
  · iapply snap_isSnapshotServer hFS s γ ci TM E ρ γr $$ [$Hpkg $HS]
  · iapply snap_isConsistentIndexer hCIg s _ ci $$ [$Hpkg $HCI]

end proof
end EtcdGrove
end Perennial
