/-
**`applySnapshot`'s post assembled** (D22 receiver epochs, S8d, 2026-10-26;
`notes/snapshot-s8-plan.md`): from what its code leaves (`snapWalkPost`, `applySnapshot_walk`) and
its precondition's persistent part, `srvSnapApplied` (`applySnapshot.spec`'s second part).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SnapApplyDefs
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__applySnapshot
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.LessorDerive

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

/-- **`applySnapshot`'s post from its walk** (S8d): the server's view, the applier, the KV's
resources and closer and the rest buckets at the snapshot's backend. -/
theorem srvSnapApplied_of_walk
    (hGL : lease.lessor.GetLease.spec (GF := GF) (hG := hG))
    (hAt : lease.lessor.Attach.spec (GF := GF) (hG := hG))
    (hDt : lease.lessor.Detach.spec (GF := GF) (hG := hG))
    (hSRD : lease.lessor.SetRangeDeleter.spec (GF := GF) (hG := hG))
    (hLk : lease.lessor.Lookup.spec (GF := GF) (hG := hG))
    (hGrant : lease.lessor.Grant.spec (GF := GF) (hG := hG))
    (hCk : lease.lessor.Checkpoint.spec (GF := GF) (hG := hG))
    (hTTL : lease.Lease.TTL.spec (GF := GF) (hG := hG))
    (s ep ap sn : Loc) (sv : SnapshotM) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF)
    (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (ai at0 dsi : w64) (nc : Loc) (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (ss hk : Loc)
    (hi : uint.Z ai < uint.Z sv.Metadata'.Index')
    (d : mvcc.KBReal) (D : backend.Data) (lgh : Loc)
    (hkb : E.γ.kb = some d)
    (hdbo : storage.dbOpensOk) (hsop : storage.snapOpensOk)
    (hP : d.P.Wf ∧ d.P.limit = storage.openLimit cfg ∧ ciKeys d.P ∧ storage.hooksParams d.P)
    (hcfgl : cfg.Logger' ≠ null)
    (hmeta : metaIs D (sv.Metadata'.Index', sv.Metadata'.Term'))
    (st : ApplyState) (b : GoInterface)
    (hle : uint.Z (ciEff γ st.k) ≤ uint.Z sv.Metadata'.Index')
    (al ast lp cl : Loc) (x : apply.ApplyKV) (A : List EntryModel)
    (hRO : E.RO = srvRestOwnH d.γB cl (srvObjsOn al ast lp cl d.be))
    (hlease : ((backend.rbData d.P D).lookup go!"lease").getD ∅ = ∅)
    (hwq : E.γ.watchQ = true)
    (R : mvcc.Log) (hpre : x.log <+: [[], []] ++ R) (hRok : mvcc.restoreLogOk R)
    (hkI : mvcc.keyImage ([[], []] ++ R) D) (hbr : mvcc.bridgeParams d.P)
    (γp : GName) (hrbw : receiptBound GF ≤ backend.wbInit - 6)
    (stp : Loc) (γd γt : GName) (img : w64 → backend.Data → IProp GF) (nt : Nat)
    (hstp : storage.storageSnap stp ss) (hnt : nt ≤ uint.nat ai)
    (halarm : ((backend.rbData d.P D).lookup go!"alarm").getD ∅ = ∅)
    (hauthb : ((backend.rbData d.P D).lookup go!"auth").getD ∅ = authBoot ∧
      ((backend.rbData d.P D).lookup go!"authUsers").getD ∅ = ∅ ∧
      ((backend.rbData d.P D).lookup go!"authRoles").getD ∅ = ∅)
    (hmemb : ((backend.rbData d.P D).lookup go!"members").isSome ∧
      ((backend.rbData d.P D).lookup go!"members_removed").isSome ∧
      ((backend.rbData d.P D).lookup go!"cluster").isSome)
    (memI : GMap w64 apply.MemberM)
    (himg : membership.clusterImageOk cl (backend.rbData d.P D) memI)
    (γn : NetNames GF) (t : Loc) (c : TrN GF) (rs : trIds) (dir : w64 → List GoString)
    (ps : List w64) (idm : w64)
    (hdir : γn.dir = dir) (hdok : netDirOk dir) (hps : ∀ f, dir f ≠ [] ↔ f ∈ ps)
    (hlid : c.lid = idm)
    (msi : w64) (cs0 : Loc) (fg : GoInterface) (quota : w64) (wad : time.Duration)
    (Tal : IProp GF) (zal : Bool) (hbuq : apply.backendUnderQuota)
    (A' : List EntryModel)
    (hA' : (restModel γr.kv.c0 γr.raft.raft.reBoot (γr.raft.pre ++ A')).bk =
        <[go!"alarm" := ∅]> (<[go!"lease" := ∅]> (backend.rbData d.P D)) ∧
      (restModel γr.kv.c0 γr.raft.raft.reBoot (γr.raft.pre ++ A')).mem = memI) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServer s γ ci TM E ρ γr ∗
      alarmApplyOk al ∗ authApplyOk ast E.RD ∗ lessorApplyOk lp ∗ clusterApplyOk cl ∗
      lease.lessorCfg lp ∗ lessorLookupOk lp ∗ (∃ n : Loc, membership.rcVersionChangedAddr cl ↦□ n) ∗
      lease.lessorInv lp E.γ.leases ∗ srvLessorAddr s ↦□ lease.lessorIface lp ∗
      srvAlarmStoreAddr s ↦□ al ∗ isAlarmStore al ∗ srvAuthStoreAddr s ↦□ auth.authIface ast ∗
      srvClusterAddr s ↦□ cl ∗ membership.isRaftCluster cl ∗ mvcc.certOk E.γ ([[], []] ++ R) ∗
      srvWTPool E γp ∗
      snapWalkPost s ep sv γ ci E ρ γr d D A x R ss hk γt γn t c rs idm lp al ast cl memI
        quota wad Tal zal ⊢
    |={⊤}=> srvSnapApplied s ep sv γ ci E ρ γr d R A' ss γt γn t c rs idm lp al ast cl Tal := by
  sorry

end proof
end EtcdGrove
end Perennial
