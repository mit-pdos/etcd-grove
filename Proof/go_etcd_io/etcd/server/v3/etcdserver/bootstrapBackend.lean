/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/bootstrapBackend.lean`: `bootstrapBackend(cfg,
false)` at a first start (`bootstrap.go:259-309` at the etcd pin `edc800c6f`), over its callees'
specs. Lean-first; claim #34, stage 4 (2026-11-23), `notes/bootstrap-proof-plan.md` §7.3-7.4.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.bootstrapBackend
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SnapApplyDefs
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BootBackendLaws
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BuildLemmas
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.cindex.NewConsistentIndex
public import Spec.go_etcd_io.etcd.server.v3.storage.NewBackendHooks
public import Spec.go_etcd_io.etcd.server.v3.storage.OpenBackend
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.backend__BatchTx
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered__UnsafePut
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.batchTxBuffered__UnsafeRange
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.CreateMetaBucket
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.bucket__ID
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.bucket__Name
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.bucket__IsSafeRangeBucket
public import Spec.go_etcd_io.etcd.server.v3.config.ServerConfig__BackendPath

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

/-! ### The boot backend's parameters -/

section params
variable [GooseExts]

/-- **The server's bucket table** (`schema`'s buckets, by name and id): `Key`, `Meta`, `Lease`,
`Alarm`, `Auth`, `AuthUsers`, `AuthRoles`, `Members`, `MembersRemoved`, `Cluster`
(`server/storage/schema/bucket.go`). -/
def bootBT : GMap GoString w64 :=
  ((((((((((∅ : GMap GoString w64).insert mvcc.keyBI.name mvcc.keyBI.id).insert
    mvcc.metaBI.name mvcc.metaBI.id).insert mvcc.leaseBI.name mvcc.leaseBI.id).insert
    mvcc.alarmBI.name mvcc.alarmBI.id).insert mvcc.authBI.name mvcc.authBI.id).insert
    mvcc.authUsersBI.name mvcc.authUsersBI.id).insert mvcc.authRolesBI.name mvcc.authRolesBI.id).insert
    mvcc.membersBI.name mvcc.membersBI.id).insert mvcc.membersRemovedBI.name
    mvcc.membersRemovedBI.id).insert mvcc.clusterBI.name mvcc.clusterBI.id

/-- **The boot backend's instance** (`OpenBackend`'s names `γB`, its `*backend`, the store's
registration name `gx`), at the configuration's batch limit `lim`: the server's table, room for the
hook's four puts (the consistent index's three, keepfix (c), and the `confState`), not compacting. -/
abbrev bootKB (γB : backend.BNames) (be : Loc) (gx : GName) (lim : w64) : mvcc.KBReal :=
  ⟨γB, bootBT, 4, lim, be, gx, false⟩

/-- **The boot backend's parameters** (`bootKB`'s, whatever its names). -/
def bootP (lim : w64) : backend.BParams :=
  { BT := bootBT, HB := fun n => decide (n ≠ mvcc.keyName), SB := fun n => decide (n = mvcc.keyName),
    HK := fun n k => decide (n = go_etcd_io.etcd.server.v3.storage.schema.metaName ∧
      (k = go_etcd_io.etcd.server.v3.storage.schema.ciKeyBytes ∨
        k = go_etcd_io.etcd.server.v3.storage.schema.termKeyBytes ∨
        k = go_etcd_io.etcd.server.v3.storage.schema.raftTermKeyBytes)),
    RB := fun n => decide (n ∈ mvcc.restBuckets), hookMax := 4, limit := lim,
    FV := mvcc.metaRevVal }

theorem bootKB_P_eq (γB : backend.BNames) (be : Loc) (gx : GName) (lim : w64) :
    (bootKB γB be gx lim).P = bootP lim := rfl

theorem bootBT_lookup (n : GoString) (i : w64) (h : bootBT.lookup n = some i) :
    (n = mvcc.keyBI.name ∧ i = mvcc.keyBI.id) ∨ (n = mvcc.metaBI.name ∧ i = mvcc.metaBI.id) ∨
    (n = mvcc.leaseBI.name ∧ i = mvcc.leaseBI.id) ∨ (n = mvcc.alarmBI.name ∧ i = mvcc.alarmBI.id) ∨
    (n = mvcc.authBI.name ∧ i = mvcc.authBI.id) ∨
    (n = mvcc.authUsersBI.name ∧ i = mvcc.authUsersBI.id) ∨
    (n = mvcc.authRolesBI.name ∧ i = mvcc.authRolesBI.id) ∨
    (n = mvcc.membersBI.name ∧ i = mvcc.membersBI.id) ∨
    (n = mvcc.membersRemovedBI.name ∧ i = mvcc.membersRemovedBI.id) ∨
    (n = mvcc.clusterBI.name ∧ i = mvcc.clusterBI.id) := by
  simp only [bootBT, GMap.lookup_insert_eq_iff, GMap.lookup_empty] at h
  repeat' split at h
  all_goals (cases h <;> (subst_vars; try simp))

/-- The boot backend's parameters' facts of concrete buckets (no free variable left). -/
local macro "kbdec" : tactic =>
  `(tactic| (simp only [bootKB, mvcc.KBReal.P, backend.BParams.has, backend.BParams.hk]; decide))

variable {GF : BundledGFunctors} in
/-- **The boot backend's parameters** (`bootOk`'s `%Hbe`, `OpenBackend`'s `openPre`): sane at a
limit in range, mvcc's layout, the consistent index's keys, the hooks', the lessor's, and the
server's other buckets in the table. -/
theorem bootKB_P (γB : backend.BNames) (be : Loc) (gx : GName) (lim : w64)
    (h0 : 0 < sint.Z lim) (h1 : sint.Z lim ≤ 2 ^ 57) :
    mvcc.bridgeParams (bootKB γB be gx lim).P ∧ ciKeys (bootKB γB be gx lim).P ∧
      storage.hooksParams (bootKB γB be gx lim).P ∧ (bootKB γB be gx lim).P.Wf ∧
      (bootKB γB be gx lim).P.limit = lim ∧ mvcc.leaseParams (bootKB γB be gx lim).P ∧
      (bootKB γB be gx lim).P.has mvcc.alarmBI ∧ (bootKB γB be gx lim).P.has mvcc.authBI ∧
      (bootKB γB be gx lim).P.has mvcc.authUsersBI ∧ (bootKB γB be gx lim).P.has mvcc.authRolesBI ∧
      (bootKB γB be gx lim).P.has mvcc.membersBI ∧
      (bootKB γB be gx lim).P.has mvcc.membersRemovedBI ∧
      (bootKB γB be gx lim).P.has mvcc.clusterBI := by
  refine ⟨⟨by kbdec, by kbdec, fun _ => rfl, fun _ => rfl, by kbdec, by kbdec⟩,
    ⟨by kbdec, by kbdec, by kbdec, by kbdec, by kbdec, by kbdec, by kbdec⟩,
    ⟨by kbdec, by kbdec, by kbdec, by kbdec, by kbdec⟩, ⟨?_, h0, h1, by kbdec, ?_⟩, rfl,
    ⟨by kbdec, by kbdec, fun k => ?_⟩, by kbdec, by kbdec, by kbdec, by kbdec, by kbdec,
    by kbdec, by kbdec⟩
  · intro n1 n2 i e1 e2
    have l1 := bootBT_lookup n1 i e1
    have l2 := bootBT_lookup n2 i e2
    rcases l1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    rcases l2 with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ |
      ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ <;>
    first | rfl | (exfalso; revert h; decide)
  · intro n h
    simp only [mvcc.KBReal.P, decide_eq_true_eq] at h ⊢
    simp [h]
  · have hne : ¬ (mvcc.leaseName = go_etcd_io.etcd.server.v3.storage.schema.metaName) := by
      decide
    simp only [mvcc.KBReal.P, backend.BParams.hk, hne, false_and, decide_false,
      Bool.and_false]

end params

section files
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **A free name holds the empty database** (bbolt's `nameHolds`' second case: `Open` creates the
file, `O_CREATE`). -/
theorem fileHolds_of_fileFree (p : GoString) :
    backend.fileFree (GF := GF) p ⊢ backend.fileHolds p ∅ := by
  rcases hfs : backend.theFs GF with _ | ⟨S, ok, has, fa, fsa, ne⟩
  · simp only [backend.fileFree, backend.onFs_none hfs]
    iintro H; iexfalso; iexact H
  · simp only [backend.fileFree, backend.fileHolds, backend.onFs_some hfs]
    unfold backend.fileFreeF backend.fileHoldsF
    iintro ⟨%R, %d, %b, %dq, %j, %qc, %h, %hp, #Hinv, #Hsh, Hp, Hcp, Hnm⟩
    obtain ⟨hp, hb, hi, hf⟩ := hp
    iexists R, d, b, dq, j, qc, h
    iframe Hinv Hsh Hp Hcp Hnm
    isplitr
    · ipureintro; exact ⟨hp, hb, hf⟩
    unfold bbolt.nameHolds
    iright
    ipureintro; exact ⟨hi, rfl⟩

end files

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

set_option maxRecDepth 100000 in
theorem bootstrapBackend.wp_proof
    (hBP : config.ServerConfig.BackendPath.spec (GF := GF) (hG := hG))
    (hExF : bootstrapBackend.existFree.law (GF := GF) (hG := hG))
    (hNCI : NewConsistentIndex.spec (GF := GF) (hG := hG))
    (hNBH : storage.NewBackendHooks.spec (GF := GF) (hG := hG))
    (hOB : storage.OpenBackend.spec (GF := GF) (hG := hG))
    (hSB : consistentIndex.SetBackend.spec (GF := GF) (hG := hG))
    (hBT : backend.backend.BatchTx.spec (GF := GF) (hG := hG))
    (hCMB : schema.CreateMetaBucket.spec (GF := GF) (hG := hG))
    (hCIg : consistentIndex.ConsistentIndex.spec (GF := GF) (hG := hG))
    (hInfo : zap.Logger.Info.spec (GF := GF) (hG := hG))
    (hU64 : zap.Uint64.spec (GF := GF) (hG := hG))
    (hOn : storage.BackendHooks.OnPreCommitUnsafe.spec (GF := GF) (hG := hG))
    (hSave : consistentIndex.UnsafeSave.spec (GF := GF) (hG := hG))
    (hPut : backend.batchTxBuffered.UnsafePut.spec (GF := GF) (hG := hG))
    (hUR : backend.batchTxBuffered.UnsafeRange.spec (GF := GF) (hG := hG))
    (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG))
    (hWA : mvcc.api.mvccW_alloc.law (GF := GF))
    (hMS : bootstrapBackend.metaSnap.law (GF := GF)) :
    bootstrapBackend.spec (GF := GF) (hG := hG) := by
  intro _ _ cfg N cl hdd hcfg hN hdbo
  wp_start as ⟨#Hzlg, Hfg, #Hvoff, Hfree, #Htp⟩
  wp_auto
  wp_apply wp_with_defer as %defer defer
  ipersist cfg
  ihave #Hcf := cfg
  iStructNamedSuffix Hcf "F"
  ihave #Hcfgpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.config $$ []
  · iPkgInit
  wp_apply (hBP cfg_ptr DFrac.discard cfg.DataDir' hdd) $$ [$Hcfgpkg $DataDirF] as -
  -- `fileutil.Exist(cfg.BackendPath())`: `false`, the name free
  ihave #Hfupkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.fileutil $$ []
  · iPkgInit
  wp_apply (hExF (config.backendPathOf cfg.DataDir')) $$ [$Hfupkg $Hfree] as Hfree
  (try wp_auto)
  -- `cindex.NewConsistentIndex(nil)`
  ihave #Hcipkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.cindex $$ []
  · iPkgInit
  wp_apply (hNCI GoInterface.nil (srvCITriple0 cl)) $$ [$Hcipkg] as %cil %γci ⟨#HisCI, Hidx, Happ, Hown, Hrt⟩
  -- `storage.NewBackendHooks(cfg.Logger, ci)`
  ihave #Hspkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage $$ []
  · iPkgInit
  wp_apply (hNBH cfg.Logger' ⟨go.GoType.PointerType cindex.consistentIndex.ty, #cil⟩) $$ [$Hspkg]
    as %bh #Hbh
  (try wp_auto)
  -- the apply protocol's names: a placeholder current backend (never opened), and the boot
  -- backend's physical names `π0`, announced at the open (`snap_create`), made current by
  -- `ci.SetBackend` (`wp_ci_swap`)
  imod (ghostVar_alloc (GF := GF) (W64 0)) with ⟨%γmt0, Hmt0⟩
  icases ghostVar_halves γmt0 _ $$ Hmt0 with ⟨Hmt0a, Hmt0b⟩
  imod (dghostVar_alloc (GF := GF) false) with ⟨%γwr0, Hwr0⟩
  imod (token_alloc (GF := GF)) with ⟨%γpd0, Hpd0⟩
  imod consInv_alloc (GF := GF) γci (W64 0, W64 0) γmt0 γmt0 ⊤ $$ Hidx
    with ⟨%γ0, %Hγ0, #Hinv, Hst, -, -, -⟩
  obtain ⟨hγci, hγm0⟩ := Hγ0
  -- (keepfix (c)) a fresh backend: no raft-term key (`consInv_alloc`'s default `rk0 := none`)
  let π0 : ApplyPhys := ⟨γmt0, γwr0, γpd0, (W64 0, W64 0), γmt0, γmt0, none⟩
  imod hWA with ⟨%gx, HwReg, HlateW⟩
  have hlim0 := hcfg.2.1
  have hlim1 := hcfg.2.2.1
  obtain ⟨hbr, hciK, hhP, hWf, -, hlpP, halP, hauP, hauuP, haurP, hmbP, hmrP, hclP⟩ :=
    bootKB_P (Classical.ofNonempty) null gx (storage.openLimit cfg) hlim0 hlim1
  ihave #HmS := hMS cl γ0 $$ Hinv
  have hm0 : metaIs (∅ : backend.Data) π0.m0 := ⟨rfl, rfl⟩
  have hr0 : metaRaftTermOf (∅ : backend.Data) = π0.rk0 := rfl
  ihave #Hpr0 : iprop(⌜π0.m0.1 = W64 0⌝ ∨ □ srvCIPair (GF := GF) cl π0.m0.1 π0.m0.2) $$ []
  · ileft; ipureintro; rfl
  ihave Hcreate := snap_create (Rw := TRow.triv) cl γ0 π0 (bootP (storage.openLimit cfg)) ∅
    (mvcc.api.mvccW gx) hm0 hr0 hciK $$ HmS Hpr0 Hinv Hpd0 Hmt0a HlateW
  ihave #HisCI0 : isCI cil γ0.ci (srvCITriple0 cl) $$ []
  · rw [hγci]; iexact HisCI
  ihave Hrt0 : ciRaftTerm (GF := GF) γ0.ci (W64 0) $$ [Hrt]
  · rw [hγci]; iexact Hrt
  ihave #Hbpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend $$ []
  · iPkgInit
  ihave #Hschpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema $$ []
  · iPkgInit
  ihave #Hhooks := hooksOk_server_fut (Rw := TRow.triv) hOn hSave hPut hUR hID hName hSafe cl γ0 π0 cil
    (bootP (storage.openLimit cfg)) (fun _ => mvcc.api.mvccW gx) bh cfg.Logger' hciK hhP
    $$ [$Hspkg $Hbpkg $Hschpkg $Hcipkg $Hbh $HisCI0 $Htp $Hinv]
  -- `storage.OpenBackend(cfg, beHooks)`: the fresh file
  ihave Hfile := fileHolds_of_fileFree _ $$ Hfree
  wp_apply (hOB cfg (storage.hooksIface bh) (bootP (storage.openLimit cfg)) ∅
      (fun _ => mvcc.api.mvccW gx)
      (fun γB => batchLockInv (γ0.withPh (futPhys π0 γB))
        (metaTMR cl (futPhys π0 γB) γB (bootP (storage.openLimit cfg))))
      (snapOpenK cl γ0 π0 (bootP (storage.openLimit cfg)))) $$ [Hfile Hcreate Hfg]
    as %b %γB ⟨Hnew, #HhkAt, #Hbfile, Hpath, -⟩
  · iframe Hfile
    iunfold storage.openPre
    iframe Hfg Hhooks Hvoff Hzlg
    isplitr
    · ipureintro; exact ⟨hdbo, hcfg.1, hWf, rfl⟩
    iexact Hcreate
  (try wp_auto)
  iunfold backend.newPostK at Hnew
  icases Hnew with ⟨#HnB, #HnSC, HnK, HnV, HnH, HnRB, HnRd, HnDl, HnFk, HnSr, HnTok⟩
  iunfold snapOpenK at HnK
  icases HnK with ⟨HnCls, #HmetaN, %jf, %γcf, Htcf, #Hidxf⟩
  -- `ci.SetBackend(be)`: the protocol moves to the boot backend's names
  let π' := futPhys π0 γB
  wp_apply (wp_ci_swap hSB γ0 cil ⟨W64 0, W64 0, W64 0, false⟩ ⟨W64 0, W64 0, W64 0, false⟩ π' jf γcf
      GoInterface.nil (interface.mkOk (go.GoType.PointerType
        go_etcd_io.etcd.server.v3.storage.backend.backend.ty) #b) (W64 0) rfl rfl
      ⟨by simp [ciEff, π', π0], by simp [ciEff, π', π0]⟩ (by simp [ciEff, hγm0, π', π0]))
    $$ [Hst Hown Hrt0 Hmt0b Hwr0 Htcf] as ⟨Hst, #Hreg', Hfs, Hown, Hrt0⟩
  · iframe HisCI0 Hinv Hst Hown Hrt0 Hwr0 Htcf Hidxf
    iexact Hmt0b
  (try wp_auto)
  -- the boot backend's payment rights, back from the futures: `bootLeft N`, the session's
  -- write-back, `Finalize`'s, the open token
  iunfold futStash at Hfs
  icases Hfs with ⟨Hnwb, Hnop⟩
  ihave Hnop1 : backend.bOpen (GF := GF) γB 1 $$ [Hnop HnCls]
  · iunfold backend.bOpen; iframe Hnop HnCls
  icases bOpen_halves γB 1 $$ Hnop1 with ⟨HoA, HoB⟩
  have hwb : N + 7 + 1 + 1 ≤ backend.wbInit := by unfold bootWB at hN; omega
  icases toks_take γB.wb backend.wbInit (N + 7) (by omega) $$ Hnwb with ⟨Hnwb, HwbL⟩
  icases toks_take γB.wb _ 1 (by omega) $$ Hnwb with ⟨Hnwb, Hwb1⟩
  icases toks_take γB.wb _ 1 (by omega) $$ Hnwb with ⟨-, Hwb2⟩
  -- `schema.CreateMetaBucket(be.BatchTx())`
  wp_apply (hBT γB (bootP (storage.openLimit cfg)) _ _ b) $$ [$Hbpkg $HnB] as %t #Ht
  wp_apply (hCMB γB (bootP (storage.openLimit cfg)) _ _ b t (1 : Qp).half hciK.1 hciK.2.2.2.2.2)
    $$ [$Hschpkg $HnB $Ht $HoA Hwb1] as HoA
  · iunfold backend.wbTok; iexact Hwb1
  (try wp_auto)
  -- `if cfg.BootstrapDefragThresholdMegabytes != 0`: not taken (`bootCfgOk`)
  have hdf := hcfg.2.2.2.1
  wp_if_destruct
  rotate_left
  · exact absurd hdf Hif
  -- `cfg.Logger.Info("restore consistentIndex", zap.Uint64("index", ci.ConsistentIndex()))`: the
  -- index loaded from the fresh backend's meta reads, `0`
  ihave #HmB := HmetaN $$ HnB
  ihave Hab : applyBackend (GF := GF) (γ0.withPh π') cil (interface.mkOk (go.GoType.PointerType
      go_etcd_io.etcd.server.v3.storage.backend.backend.ty) #b) $$ [Hown]
  · iunfold applyBackend; iframe Hown HmB
  wp_apply (wp_ci_get (Rw := TRow.triv) hCIg (srvCITriple0 cl) (γ0.withPh π') cil _ (W64 0)
      ⟨W64 0, W64 0, W64 0, false⟩ rfl)
    $$ [Hst Hab Hrt0] as ⟨Hst, Hab, Hrt⟩
  · iframe Hst Hab Hrt0; isplitr; · iexact HisCI0
    isplitr
    · rw [show consInv (GF := GF) (γ0.withPh π') = consInv γ0 from rfl]; iexact Hinv
    -- (keepfix-d) the fresh backend's index is 0
    ileft; ipureintro; intro _; simp [π', π0]
  ihave #Hzpkg : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  wp_apply hU64 as %f0 -
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %fsl -
  wp_auto
  wp_apply hInfo
  · iexact Hzlg
  (try wp_auto)
  -- the post, at the names `γA := γ0.withPh π'`, the instance `bootKB γB b gx`, the data `∅`
  have hsl : stLoaded (γ0.withPh π') ⟨W64 0, W64 0, W64 0, false⟩ =
      ⟨(γ0.withPh π').m0.1, (γ0.withPh π').m0.1, W64 0, false⟩ := by
    simp [stLoaded, π', π0]
  rw [hsl]
  iunfold applyBackend at Hab
  icases Hab with ⟨Hown, -⟩
  ihave HoAB := (backend.bOpen_add (GF := GF) γB (1 : Qp).half (1 : Qp).half).2 $$ [HoA HoB]
  · iframe HoA HoB
  rw [Qp.half_add_half]
  obtain ⟨hbr', hciK', hhP', hWf', -, hlpP', halP', hauP', hauuP', haurP', hmbP', hmrP', hclP'⟩ :=
    bootKB_P γB b gx (storage.openLimit cfg) hlim0 hlim1
  iapply HΦ
  isplitr
  · ipureintro; rfl
  iexists _, γ0.withPh π', cil, bootKB γB b gx (storage.openLimit cfg), (∅ : backend.Data)
  iframe «$r0»
  isplitr
  · ipureintro
    refine ⟨rfl, ⟨rfl, rfl⟩, rfl, mvcc.keyView_of_dget hbr' (fun _ => rfl), fun _ _ => rfl, rfl⟩
  isplitl [Hst Happ Hown Hrt HwReg Hpath]
  · iunfold bootBackendRows
    iframe Hst Happ Hown Hrt HwReg Hpath HisCI0 HhkAt Hbfile HmB
    isplitr
    · ipureintro; rfl
    isplitr
    · rw [show consInv (GF := GF) (γ0.withPh π') = consInv γ0 from rfl]; iexact Hinv
    isplitr
    · iexists cfg.Logger'; iexact Hbh
    isplitr
    · iexact HmS
    ipureintro
    exact ⟨rfl, hbr', hciK', hhP', hWf', rfl, hlpP', halP', hauP', hauuP', haurP', hmbP', hmrP',
      hclP'⟩
  isplitl [HnV HnH HnRB HnRd HnDl HnFk HnSr HnTok HwbL HoAB]
  · iunfold bootBackendNew
    iunfold backend.newPostK
    -- `rw`, not `simp only`: `bootKB_P_eq` is `rfl`, so `simp` would rewrite without a proof and
    -- leave the kernel a definitional check under `[∗list] _ ∈ List.replicate rdSlotsN ()`, which it
    -- did by unfolding the `2 ^ 30`-element list (2026-11-24: a timeout, then 175 GB at no bound)
    rw [bootKB_P_eq]
    iframe HnB HnSC HnV HnH HnRB HnRd HnDl HnFk HnSr HnTok
    iunfold bootLeft
    iframe HwbL HoAB
  iunfold backend.wbTok
  iexact Hwb2

end proof

end EtcdGrove
end Perennial
