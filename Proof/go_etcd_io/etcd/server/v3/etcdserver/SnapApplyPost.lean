/-
**`applySnapshot`'s post assembled** (D22 receiver epochs, S8d, 2026-10-26;
`notes/snapshot-s8-plan.md`): from what its code leaves (`snapWalkPost`, `applySnapshot_walk`) and
its precondition's persistent part, `srvSnapApplied` (`applySnapshot.spec`'s second part): the
walk's result taken apart, the names (`SnapApplyNames.lean`), the five step lemmas
(`SnapApply{IsServer,Opts,KV,Rest,Closer}.lean`) and the rest framed (step 7).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SnapApplyNames
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__applySnapshot
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SnapApplyIsServer
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SnapApplyOpts
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SnapApplyKV
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SnapApplyRest
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SnapApplyCloser

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
resources and closer and the rest buckets at the snapshot's backend. The names `γ'`, `TM'`, `E'`,
`st'` are `snapγ γ π0 γB`, `metaTM γB d.P`, `snapE …`, `snapSt γ' i` (`SnapApplyNames.lean`); steps
2-6 are the lemmas `snap_isServer`, `snap_backendOptsOk`, `snap_applyKV`, `snap_srvRest`,
`snap_kvCloser`; step 7 (the rest of the post) is framed here. -/
theorem srvSnapApplied_of_walk
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
      (restModel γr.kv.c0 γr.raft.raft.reBoot (γr.raft.pre ++ A')).mem = memI)
    (hoff : E.authMode = auth.AuthMode.off) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServer s γ ci TM E ρ γr ∗
      alarmApplyOk al ∗ authApplyOk ast E.RD ∗ lessorApplyOk lp ∗ clusterApplyOk cl ∗
      lease.lessorCfg lp ∗ lessorLookupOk lp ∗ (∃ n : Loc, membership.rcVersionChangedAddr cl ↦□ n) ∗
      lease.lessorInv lp E.γ.leases ∗ srvLessorAddr s ↦□ lease.lessorIface lp ∗
      srvAlarmStoreAddr s ↦□ al ∗ isAlarmStore al ∗ srvAuthStoreAddr s ↦□ auth.authIface ast ∗
      srvClusterAddr s ↦□ cl ∗ membership.isRaftCluster cl ∗ mvcc.certOk E.γ ([[], []] ++ R) ∗
      srvWTPool E γp ∗
      E.RD ∗ snapWalkPost s ep sv γ ci E ρ γr d D A x R ss hk γt γn t c rs idm lp al ast cl memI
        quota wad Tal zal ⊢
    |={⊤}=> srvSnapApplied s ep sv γ ci E ρ γr d R A' ss γt γn t c rs idm lp al ast cl Tal := by
  iintro ⟨#Hpkg, #Hsrv, #HalA, #HauA, #HleA, #HclA, #Hlcfg, #Hllk, #Hrcn, #Hlinv, #Hlpf, #Half,
    #HisAl, #Haustf, #Hclf, #Hirc, #Hcok, #HWP, HRD2, Hw⟩
  iunfold snapWalkPost at Hw
  icases Hw with ⟨%γB, %d', %gx, %π0, %p', %γw, %ws, %g, %up', %opts', %L, %spc, %Ll, %jf, %γcf,
    %w0, %RD0, %up, %lg, %wsk, %stck, %Hpure, #HB, HSC, -, -, -, -, -, #HCI', #HhkS, -, -, -,
    #Hws, -, -, #HhP, -, #Hwa, #Hlga, Hwok, HplH, Hat, Hab, Hgv, Hbmr, Hbea, Hγt, Halb, Haub, Hclb,
    Hleb, Hlo, Hlrd, Hrt, Hrb, Hcm, Hbo, Hsc, Hwf, Hww, HwOwn, Hsr, Htl, Hlgr, Hai, Hatt, Hds, Hms,
    Hcsa, Hcso, Hpath, HTal, Hube, Hua, -, Hra, Hauar, HRD0, -, #Hkvk, #Hstopc, Hstc, Hwsw⟩
  obtain ⟨hγB, hP', -, hm0, -, hkb', hγw, -, hcov, hgnn, ho1, ho2, ho3, ho4, ho5, ho6, ho7, -, -, -,
    ho11, ho12⟩ := Hpure
  subst hγB
  -- step 1: the names (`SnapApplyNames.lean`)
  ihave HplRO := backend.plHook_persist d'.γB g $$ HplH
  imod HplRO with #HplRO
  -- step 2: the server's view
  ihave #Hsrv' := snap_isServer s γ ci TM E ρ γr π0 d'.γB d.P d' p' g al ast lp cl rfl hkb' $$ []
  · iframe #
  -- step 3: the new applier's options
  ihave #Hbo' := snap_backendOptsOk hGL hAt hDt hSRD hLk hGrant hCk hTTL hMID hLead hTerm hFS hCIg
    s γ ci TM E ρ γr π0 d'.γB d.P d' p' γw ws g opts' lg al ast lp cl rfl hkb' hγw hwq hgnn hoff
    ⟨ho1, ho2, ho3, ho4, ho5, ho6, ho7, ho11, ho12⟩ $$ []
  · iframe #
  -- step 4: the applier state
  ihave HKV' := snap_applyKV s γ ci E ρ π0 d'.γB d.P d' p' γw ws g up' opts' w0 RD0 al ast lp cl x R
      zal rfl hkb' hγw hwq hpre hRok hrbw $$
      [Hube Hua Hsr Hwf Hww HwOwn Hrt Hlo Hlrd HRD2 Hbea Hgv Hra Hauar Hwok HRD0]
  · iframe #; iframe Hube Hua Hsr Hwf Hww HwOwn Hrt Hlo Hlrd HRD2 Hbea Hgv Hra Hauar Hwok HRD0
  imod HKV' with ⟨%x', %Hx', HKV'⟩
  -- step 5: the rest buckets
  ihave HRest := snap_srvRest E (snapγ γ π0 d'.γB) (metaTM d'.γB d.P) ci p' g d'.γB d' γr al ast lp
    cl _ memI A' rfl hA' $$ [Hrb Hcm Halb Haub Hclb Hleb]
  · iframe Hrb Hcm Halb Haub Hclb Hleb
  -- step 6: the KV's closer
  ihave HKC := snap_kvCloser s E (snapγ γ π0 d'.γB) (metaTM d'.γB d.P) ci p' g d'.γB al ast lp cl
    d'.be γw wsk stck hγw $$ [Hstc Hwsw Hsc]
  · iframe #; iframe Hstc Hwsw Hsc
  -- step 7: the rest, framed
  ihave Hcs := epCsOk_of_csOptA spc sv.Metadata'.ConfState' $$ Hcso
  imodintro
  iunfold srvSnapApplied
  iexists snapγ γ π0 d'.γB, metaTM d'.γB d.P,
    snapE E (snapγ γ π0 d'.γB) (metaTM d'.γB d.P) ci p' g d'.γB al ast lp cl d'.be,
    (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty)
      #d'.be : GoInterface),
    snapSt (snapγ γ π0 d'.γB) sv.Metadata'.Index', d', x', spc, L
  isplitr
  · ipureintro
    exact ⟨by apply snapE_beSucc, hkb', hP', rfl, snapSt_loopOk γ π0 d'.γB _ _ hm0, snapSt_ciEff γ π0 d'.γB _ _ hm0, Hx'.1,
      hcov⟩
  iunfold epConfState
  iframe Hsrv' Hai Hatt Hds Hms Hcsa Hcs Hat Hab Hlgr Hbmr HKV' HRest HKC HSC Hbo Hγt Hpath Htl HTal

end proof
end EtcdGrove
end Perennial
