/-
**`applySnapshot`'s post assembled** (D22 receiver epochs, S8d, 2026-10-26;
`notes/snapshot-s8-plan.md`): from what its code leaves (`snapWalkPost`, `applySnapshot_walk`) and
its precondition's persistent part, `srvSnapApplied` (`applySnapshot.spec`'s second part): the
walk's result taken apart, the names (`SnapApplyNames.lean`), the four step lemmas
(`SnapApply{IsServer,Opts,KV,Rest}.lean`) and the rest framed (step 7).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SnapApplyNames
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__applySnapshot
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SnapApplyIsServer
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SnapApplyOpts
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SnapApplyKV
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SnapApplyRest

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section snapLeases
variable [GooseExts]

/-- The grant ids of a prefix of the log are the log's. -/
theorem srvGrantLog_prefix {A A' : List EntryModel} (h : A <+: A') (u : w64)
    (hu : u ∈ srvGrantLog A) : u ∈ srvGrantLog A' := by
  obtain ⟨B, rfl⟩ := h
  unfold srvGrantLog logRevGrantIds at hu ⊢
  rw [List.filter_append, List.filterMap_append]
  exact List.mem_append_left _ hu

/-- The records keep the lease bucket present. -/
theorem restLeasesWith_lease_isSome (f : w64 → w64) (ids : List w64) (r : apply.RestM)
    (h : (r.bk.lookup mvcc.leaseName).isSome) :
    ((apply.restLeasesWith f ids r).bk.lookup mvcc.leaseName).isSome := by
  unfold apply.restLeasesWith
  induction ids generalizing r with
  | nil => exact h
  | cons id ids ih =>
    rw [List.foldl_cons]
    exact ih _ (by unfold apply.restGrantT; exact putIn_present _ _ _ _ _ h)

/-- **The rest model's buckets with the records of `ids` at the ones the rest resource holds**
(`snapRestImgM_bk` with the image's lease bucket the records'): what `srvSnapApplied_of_walk`'s
`hbkG` takes. -/
theorem snap_bkG (M : auth.AuthMode) (γr : ReadNames) (P : backend.BParams) (D : backend.Data)
    (A' : List EntryModel) (hany : M ≠ .any) (h : snapRestImgM M.isOn γr P D A')
    (f : w64 → w64) (ids : List w64)
    (hl : ((backend.rbData P D).lookup go!"lease").getD ∅ =
      ((apply.restLeasesWith f ids
        (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A'))).bk.lookup go!"lease").getD ∅) :
    ∀ n, membership.clusterBkts n ∨ restSet M n →
      (apply.restLeasesWith f ids
        (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A'))).bk.lookup n =
      (<[go!"alarm" := ∅]> (<[go!"lease" := ((backend.rbData P D).lookup go!"lease").getD ∅]>
        (backend.rbData P D))).lookup n := by
  intro n hn
  have h0 := snapRestImgM_bk M γr P D A' hany h n hn
  have e : mvcc.leaseName = go!"lease" := rfl
  by_cases hnl : n = go!"lease"
  · subst hnl
    rw [GMap.lookup_insert_ne _ _ (by decide), GMap.lookup_insert, hl]
    have hs := restLeasesWith_lease_isSome f ids
      (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A'))
      (by rw [restModel_lease]; rfl)
    rw [e] at hs
    revert hs
    generalize (apply.restLeasesWith f ids
      (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A'))).bk.lookup go!"lease" = o
    intro hs
    cases o with
    | none => cases hs
    | some v => rfl
  · rw [restLeasesWith_lookup_other _ _ _ n (fun h => hnl (h.symm.trans e))]
    rw [h0]
    by_cases hna : n = go!"alarm"
    · subst hna; rw [GMap.lookup_insert, GMap.lookup_insert]
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm hna), GMap.lookup_insert_ne _ _ (Ne.symm hna),
        GMap.lookup_insert_ne _ _ (Ne.symm hnl), GMap.lookup_insert_ne _ _ (Ne.symm hnl)]

end snapLeases

section kvLeases
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

open Iris.ProofMode in
/-- With auth on, a cluster grants no lease (`srvKVInvsOn`'s). -/
theorem srvKVInvsM_lg (on : Bool) (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) :
    srvKVInvsM (GF := GF) on s E γr ⊢ ⌜on = true → γr.kv.lg = false⌝ := by
  cases on
  · iintro -; ipureintro; intro h; cases h
  · unfold srvKVInvsM srvKVInvsOn
    iintro ⟨⟨-, -, -, -, -, -, %h⟩, -⟩
    ipureintro; intro _; exact h.2

end kvLeases

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`applySnapshot`'s post from its walk** (S8d): the server's view, the applier, the KV's
resources and the rest buckets at the snapshot's backend. The names `γ'`, `TM'`, `E'`, `st'` are
`snapγ γ π0 γB`, `metaTM γB d.P`, `snapE …`, `snapSt γ' i` (`SnapApplyNames.lean`); steps 2-5 are
the lemmas `snap_isServer`, `snap_backendOptsOk`, `snap_applyKV`, `snap_srvRest`; step 7 (the rest
of the post) is framed here. (R4, 2026-11-07: over mvcc's API, the store restored in place by
`KV.Restore.contract`, its handle `E.kv` and name `E.γ` kept, the KV at the image's model by the
mode, `kvModelM E.authOn γr.kv A'`; until then the watchable store's sole writer at the restored
physical names, the restored log `[[], []] ++ R`, its records `r`, the KV's closer
(`snap_kvCloserW`, `SnapApplyCloser.lean`, deleted with the closer).) -/
theorem srvSnapApplied_of_walk [bkSem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]
    (hGL : lease.lessor.GetLease.spec (GF := GF) (hG := hG))
    (hAt : lease.lessor.Attach.spec (GF := GF) (hG := hG))
    (hDt : lease.lessor.Detach.spec (GF := GF) (hG := hG))
    (hSRD : lease.lessor.SetRangeDeleter.spec (GF := GF) (hG := hG))
    (hLk : lease.lessor.Lookup.spec (GF := GF) (hG := hG))
    (hGrant : lease.lessor.Grant.spec (GF := GF) (hG := hG))
    (hCk : lease.lessor.Checkpoint.spec (GF := GF) (hG := hG))
    (hTTL : lease.Lease.TTL.spec (GF := GF) (hG := hG))
    (hRv : lease.lessor.Revoke.spec (GF := GF) (hG := hG))
    (hMID : EtcdServer.MemberID.spec (GF := GF) (hG := hG))
    (hLead : EtcdServer.Leader.spec (GF := GF) (hG := hG))
    (hTerm : EtcdServer.Term.spec (GF := GF) (hG := hG))
    (hFS : EtcdServer.ForceSnapshot.spec (GF := GF) (hG := hG))
    (hCIg : consistentIndex.ConsistentIndex.spec (GF := GF) (hG := hG))
    (Hp : mvcc.api.persistent.law (GF := GF))
    (s ep : Loc) (sv : SnapshotM) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF)
    (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig)
    (ss hk : Loc) (d : mvcc.KBReal) (D : backend.Data)
    (hP : ciKeys d.P ∧ storage.hooksParams d.P)
    (al ast lp cl : Loc) (x : apply.ApplyKV) (A : List EntryModel)
    (hlp : mvcc.leaseParams d.P)
    (γp : WTNames) (γt : GName)
    (memI : GMap w64 apply.MemberM)
    (γn : NetNames GF) (t : Loc) (c : TrN GF) (rs : trIds) (idm : w64)
    (quota : w64) (wad : time.Duration)
    (A' : List EntryModel)
    -- (strict M1) the KV at the applied `A`'s model, the image's committed log extending it, its
    -- history attaching no lease (`specSnapM`'s `hxA`, `hAA'`, `hnl`)
    (hxA : x.log = kvModelM E.authOn γr.kv A) (hAA' : A <+: A')
    (hnl : mvcc.LogNoLease (kvModelM E.authOn γr.kv A'))
    -- (P6.2, 2026-11-03, F9) the rest model's members the image's
    (hmem : (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A')).mem = memI)
    (hany : E.authMode ≠ .any)
    -- (the lease-expiry plan's S2–S4, Probe 4, 2026-11-05) the lessor at the image's records
    -- (`snapWalkPost`'s): its live set the snapshot's table's ids, the ids it ever had good for `A'`,
    -- the records' requests the table's; the image's lease bucket the table's records at `f`
    (Lr : List w64) (recs : List (w64 × w64 × w64)) (U : List w64) (reqOf : w64 → w64)
    (f : w64 → w64)
    (hLr : Lr = srvIds E (appliedTable γr A').ids)
    (hUok : srvEverOk E A' (U ++ recs.map (·.1)))
    (hbkG : ∀ n, membership.clusterBkts n ∨ restSet E.authMode n →
      (apply.restLeasesWith f (srvIds E (appliedTable γr A').ids)
        (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A'))).bk.lookup n =
      (<[go!"alarm" := ∅]> (<[go!"lease" := ((backend.rbData d.P D).lookup go!"lease").getD ∅]>
        (backend.rbData d.P D))).lookup n)
    (hf : E.lg = true → leaseTTLsGeReq (appliedTable γr A') f)
    (hreqT : E.lg = true → ∀ p ∈ appliedTable γr A', ∃ x ∈ recs, x.1 = p.1 ∧ reqOf x.1 = p.2) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerM E.authOn s γ ci TM E ρ γr ∗
      alarmApplyOk al ∗ authApplyOkM E.authMode ast E.RD ∗ lessorApplyOk lp ∗ clusterApplyOk cl ∗
      lease.lessorCfg lp ∗ lessorLookupOk lp ∗ (∃ n : Loc, membership.rcVersionChangedAddr cl ↦□ n) ∗
      lease.lessorInv lp (mvcc.api.mvccLeases E.γ) ∗ srvLessorAddr s ↦□ lease.lessorIface lp ∗
      srvAlarmStoreAddr s ↦□ al ∗ isAlarmStore al ∗ srvAuthStoreAddr s ↦□ auth.authIface ast ∗
      srvClusterAddr s ↦□ cl ∗ membership.isRaftCluster cl ∗ srvKVAddr s ↦□ E.kv ∗
      srvWTPool E γp ∗ srvGrantIf E ∗
      snapWalkPost s ep sv γ ci E ρ γr d D A A' x ss (config.backendPathOf cfg.DataDir') hk γt γn t c rs idm lp al ast cl memI
        quota wad Lr recs U reqOf ⊢
    |={⊤}=> srvSnapAppliedG E.authOn s ep sv γ ci E ρ γr d A' ss (config.backendPathOf cfg.DataDir') γt γn t c rs idm lp al ast cl := by
  iintro ⟨#Hpkg, #Hsrv, #HalA, #HauA, #HleA, #HclA, #Hlcfg, #Hllk, #Hrcn, #Hlinv, #Hlpf, #Half,
    #HisAl, #Haustf, #Hclf, #Hirc, #Hkvf, #HWP, #HGI, Hw⟩
  subst hLr
  iunfold snapWalkPost at Hw
  icases Hw with ⟨%d', %π0, %g, %up', %opts', %L, %spc, %jf, %γcf, %w0, %RD0, %up, %lg, %ua,
    %Hpure, #HB, #HhkAt', #HbhF', #HSC, -, -, -, #HCI', #HhkS, -, -, #Hro', #Hwa, #Hlga, Hwok,
    #HplRO, Hat, Hab, Hgv, Hbmr, Hbea, Hγt, Haub, Hclb, Hleb, Hlo, Hlrd, Hlrv, HLt1, HLt2, HEv,
    #HRqs, Hrdat, #Haus, Hrt, Hrb, Hrn, Hcm, Hbo, Hpl', HmO, HmB, HwSt, HcrO, Htl, Hlgr, Hai, Hatt,
    Hds, Hms, Hcsa, Hcso, Hpath, #Hbf, Halb, HRD2, Hube, Hua, Hra, Hauar, HRD0, -⟩
  obtain ⟨hP', hcm', hm0, hbr', hcov, hgnn, ho1, ho2, ho3, ho4, ho5, ho6, ho7, -, -, -, ho11, ho12⟩ :=
    Hpure
  -- the store's handle (the server's store invariant's)
  ihave #Hsrv3 := Hsrv
  iunfold isServerM at Hsrv3
  icases Hsrv3 with ⟨-, -, -, #Hat3, -⟩
  iunfold srvAtomicsM at Hat3
  icases Hat3 with ⟨-, -, #Hkvi⟩
  ihave ⟨#HkS, -⟩ := srvKVInvsM_kvStoreInvW E.authOn s E γr $$ Hkvi
  haveI := Hp.1
  ihave #HisM' : mvcc.api.isMvcc (GF := GF) E.kv E.γ $$ []
  · iunfold srvApi.kvStoreInvG at HkS; icases HkS with ⟨#H, -⟩; iexact H
  -- step 2: the server's view
  ihave #Hsrv' := snap_isServer E.authOn s γ ci TM E ρ γr π0 d.P d' g al ast lp cl hP' hgnn
    (by rw [hP']; exact hP.1) (by rw [hP']; exact hP.2) hk $$ []
  · iframe #
  -- step 3: the new applier's options
  ihave #Hbo' := snap_backendOptsOk hGL hAt hDt hSRD hLk hGrant hCk hTTL hRv hMID hLead hTerm hFS hCIg
    s γ ci TM E ρ γr π0 d'.γB d.P d' (mvcc.api.mvccW d'.gx) g opts' lg al ast lp cl rfl hgnn
    (by rw [hP']; exact hlp)
    ⟨ho1, ho2, ho3, ho4, ho5, ho6, ho7, ho11, ho12⟩ $$ []
  · iframe #
  -- step 4: the applier state
  -- (P6.2) the new applier at `E'`, and the auth part of the row there, by the mode (`kvAuthM_snap`)
  ihave ⟨#Hub', Huo'⟩ := Hube $$
    %(snapE E (snapγ γ π0 d'.γB) (metaTM d'.γB d.P) ci d' g d'.γB al ast lp cl d'.be) Hbo'
  ihave Hauar := kvAuthM_snap s γ ci E π0 d.P d' g up' opts' al ast lp cl ua γr A' hany
    ⟨ho4, ho5⟩ $$ [Hauar]
  · iframe #; iframe Hauar
  have hxl : x.log.length ≤ (kvModelM E.authOn γr.kv A').length := by
    rw [hxA]; exact (srvApi.kvModelM_prefix E.authOn γr.kv A A' hAA').length_le
  ihave HKV' := snap_applyKV s γ ci E ρ γr π0 d.P d' g up' opts' w0 RD0 al ast lp cl x A'
      (srvIds E (appliedTable γr A').ids) E.authOn (srvAuthAtLog γr.kv srvAuthSt0 A') hxl hnl $$
      [Huo' Hua HwSt HcrO HmO HmB Hlo Hlrd Hlrv HLt1 Hrdat HRD2 Hbea Hgv Hpl' Hrt Hra Hauar
        Hwok HRD0]
  · iframe #; iframe Huo' Hua HwSt HcrO HmO HmB Hlo Hlrd Hlrv HLt1 Hrdat HRD2 Hbea Hgv Hpl'
      Hrt Hra Hauar Hwok HRD0
  imod HKV' with ⟨%x', %Hx', HKV'⟩
  -- step 5: the rest buckets
  -- (S2–S4, Probe 4) the table's requests, from the records' (`hreqT`)
  ihave #HRqT : srvReqsIf E (appliedTable γr A') $$ []
  · unfold srvReqsIf
    cases hl : E.lg
    · simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
    · simp only [↓reduceIte]
      unfold srvReqs
      iintro !> %p %hp
      obtain ⟨x, hx, h1, h2⟩ := hreqT hl p hp
      ihave #Hx := BigSepL.bigSepL_mem
        (Φ := fun x : w64 × w64 × w64 => lease.leaseReqIs (mvcc.api.mvccLeases E.γ) x.1 (reqOf x.1)) hx $$ HRqs
      rw [← h1, ← h2]
      iexact Hx
  ihave HEv : srvEver E A' $$ [HEv]
  · iunfold srvEver
    iexists _
    iframe HEv
    ipureintro; exact hUok
  ihave HRest := snap_srvRest E (snapγ γ π0 d'.γB) (metaTM d'.γB d.P) ci g d'.γB d' γr al ast lp
    cl _ memI A' rfl f hbkG hmem hf
    $$ [Hrb Hrn Hcm Halb Haub Hclb Hleb HLt2 HEv]
  · iframe Hrb Hrn Hcm Halb Haub Hclb Hleb HLt2 HGI HRqT HEv
  -- step 7: the rest, framed
  icases Hcso with #Hcso
  ihave Hcs := epCsOk_of_csOptA spc sv.Metadata'.ConfState' $$ Hcso
  -- (R2b-3d stage 3) the new backend's stop channels at the server's own resources
  ihave #HSCs : srvStopChans (GF := GF) (snapγ γ π0 d'.γB) d' $$ []
  · iunfold srvStopChans; rw [← hP']; iframe HB HSC
  imodintro
  iunfold srvSnapAppliedG
  iexists snapγ γ π0 d'.γB, metaTM d'.γB d.P,
    snapE E (snapγ γ π0 d'.γB) (metaTM d'.γB d.P) ci d' g d'.γB al ast lp cl d'.be,
    (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty)
      #d'.be : GoInterface),
    snapSt (snapγ γ π0 d'.γB) sv.Metadata'.Index', d', x', spc, L
  isplitr
  · ipureintro
    refine ⟨by apply snapE_beSucc, rfl, hP', rfl, snapSt_loopOk γ π0 d'.γB _ _ hm0,
      snapSt_ciEff γ π0 d'.γB _ _ hm0, Hx'.1, Hx'.2.2, Hx'.2.1, hcov⟩
  iunfold epConfState
  simp only [snapE_authMode]
  iframe Hsrv' Hai Hatt Hds Hms Hcsa Hcs Hcso Hat Hab Hlgr Hbmr HKV' HRest HSCs Hbo Hγt Hpath Hbf Htl
  -- the KV, the store's handle kept by the restore
  iexists E.kv
  simp only [snapE_γ, snapE_kv]
  iframe Hkvf HisM'

end proof
end EtcdGrove
end Perennial
