/-
**`run`'s snapshot-payload job in restart form** (R2d'a task 4, 2026-11-06; DRAFT: nothing here is
frozen, and no closed theorem imports this file; `notes/restart-plan.md`, "R2d'a task 4").
Lean-first (no Rocq counterpart).

`run_job_snapCR` is the frozen `run_job_snapC` (`EtcdServer__run.lean`: `run_job_snap` off,
`run_snap_jobOn` on) over `applyResR` and `applyAll.specSnapMR`, in one proof over the component `K`
(the rows through `isServerM_C`/`srvApplyKVM_C`/`kvRunM_split`, the token rights `acTok_mono`). It
covers a snapshot inside the window (the ghost log `A₀`, the ghost index `g`, the rest at the
replay's image) and past it (the ghost log Go's, the rest at the model): the rest buckets at an image
with the model's ids either way (`srvRestR_img`). Its premise `hwin`: the snapshot above the ghost
log (inside the window, A8's `rnWinInstallAbove`; past it, Go's `|A| < |A'|`). After it Go is past
the window.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__run
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.RunR
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ApplyAllSnapR

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **The rest buckets at an image of the ghost log** (DRAFT): inside the window (Go's log a prefix
of the backend's) the replay's image of `A₀`, past it the model of Go's log; either way its members
have the model's ids. -/
theorem srvRestR_img (E : apply.AEnv GF) (γr : ReadNames) (rp : RestartPt) (A : List EntryModel)
    (h : A <+: rp.A₀ ∨ rp.A₀ <+: A) :
    ∃ r0 : apply.RestM, (∀ k, (r0.mem !! k).isSome =
        ((restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ ghostOf rp A)).mem !! k).isSome) ∧
      srvRestR E γr rp A = srvRestRp E γr (ghostOf rp A) r0 := by
  by_cases hl : A.length < rp.A₀.length
  · have hp : A <+: rp.A₀ := h.resolve_right (fun h' => by have := h'.length_le; omega)
    refine ⟨restReplay γr rp A, ?_, ?_⟩
    · intro k; rw [ghostOf_in rp A hp]; exact restReplay_memKeys γr rp A k
    · rw [srvRestR_in E γr rp A hl, ghostOf_in rp A hp]
  · have hp : rp.A₀.length ≤ A.length := by omega
    refine ⟨restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ ghostOf rp A), fun _ => rfl, ?_⟩
    rw [srvRestR_past E γr rp A hp, ghostOf_past rp A hp, srvRestRp_model]

/-- **The start chain's auth layer is the component's** (`kvInv_ch0_off`/`kvInvOn_ch0` over the
server's view). -/
theorem isServerC_ch0 (K : AuthC) (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF)
    (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) :
    isServerC K s γ ci TM E ρ γr ⊢ |={⊤}=> ⌜γr.kv.ch0 = apply.alarmChain K.isOn false false⌝ := by
  iintro #H
  ihave #H' := (isServerM_C K s γ ci TM E ρ γr).2 $$ H
  iunfold isServerM at H'
  icases H' with ⟨-, -, -, #Hatm, -, -⟩
  iunfold srvAtomicsM at Hatm
  icases Hatm with ⟨-, -, #Hki⟩
  cases K with
  | off =>
    ihave #Hki := (show srvKVInvsM (GF := GF) AuthC.off.isOn s E γr ⊢ srvKVInvs E γr from .rfl) $$ Hki
    iunfold srvKVInvs at Hki
    icases Hki with ⟨#Hkv, -⟩
    imod (kvInv_ch0_off γr.raft γr.kv) $$ Hkv with %h
    imodintro; ipureintro; exact h
  | on γa =>
    ihave #Hki := (show srvKVInvsM (GF := GF) (AuthC.on γa).isOn s E γr ⊢ srvKVInvsOn E γr srvAuthSt0
      from srvKVInvsM_true s E γr) $$ Hki
    iunfold srvKVInvsOn at Hki
    icases Hki with ⟨#Hkv, -⟩
    imod (kvInvOn_ch0 γr.raft γr.kv srvAuthSt0) $$ Hkv with %h
    imodintro; ipureintro; exact h

end laws

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

set_option maxHeartbeats 1000000 in
/-- **`run`'s snapshot-payload job in restart form** (R2d'a task 4, DRAFT): `run_job_snapC` over
`applyResR` and `applyAll.specSnapMR`, inside the window or past it; Go's handed log committed
(`srvRLogLb … A`, the loop's) places it against the backend's log, and the snapshot is above the
ghost log (`hwin`). After, Go is past the window (`applyResR … A'`). -/
theorem run_job_snapCR (hAA : EtcdServer.applyAll.specSnapMR (GF := GF) (hG := hG))
    (C : ApplyCtx GF) (rp : RestartPt) (A A' : List EntryModel) (apL : Loc) (es : GoSlice) (sn : Loc)
    (sv : SnapshotM) (rac nc : GoChan) (γs : schedule.SchedNames) (γnc : NotifyNames)
    (γn : RNNames) (rt : w64) (K : AuthC) (hM : C.E.authMode = K.mode)
    (ha00 : uint.nat C.ai₀ = 0) (hc0 : uint.Z C.c₀ ≤ uint.Z C.ai₀) (hpre : γn.pre = [])
    (hγn : γn.node = C.γr.raft.raft) (hρ : C.ρ.raft = C.γr.raft)
    (hpr : C.γr.raft.pre = γn.pre) (hγs : C.γs = γn.γs) (hγw : C.γw = C.ρ.wait)
    -- (R2d'a task 4) the snapshot above the ghost log (inside the window, A8's bound)
    (hwin : (ghostOf rp A).length < A'.length)
    (hlen : (γn.pre ++ A').length = uint.nat sv.Metadata'.Index')
    (h61 : uint.Z sv.Metadata'.Index' < 2 ^ 61)
    (hboot : (γn.node.boot.length : Int) ≤ uint.Z sv.Metadata'.Index') (hrn : C.rn = γn) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerApplyAll C.s C.γr ∗ srvMemberIDAddr C.s ↦□ γn.id ∗ srvMetaSnap C.γ ∗
        taEntriesAddr apL ↦□ es ∗ es ↦*□ ([] : List Loc) ∗
        taSnapshotAddr apL ↦□ sn ∗ ownSnapM sn DFrac.discard sv ∗
        (letI := srvStor (GF := GF) γn.node; iprop(
          snapshotCert γn.node.cl srvClusterN (snapTrip sv sv.Metadata'.ConfState'.lists) ∗
          nodeSnapLocal γn.node.cl γn.id sv.Metadata'.Index')) ∗
        taNotifycAddr apL ↦□ nc ∗ isNotify2 γnc nc iprop(True) iprop(True) ∗ notifyRcvN γnc 0 ∗
        taRaftAdvancedCAddr apL ↦□ rac ∗
        rnAdvChan rac (letI := srvStor (GF := GF) γn.node
          iprop(nodeAppliedLb γn.node.cl γn.key (γn.pre ++ A').length ∗
            nodeCommitLb γn.node.cl γn.key (γn.pre ++ A').length ∗
            srvFrozenAt γn.γs (γn.pre ++ A').length ∗ srvFrozenBelow γn.γs (γn.pre ++ A').length ∗
            rnWalHanded γn (γn.pre ++ A').length)) ∗
        taRaftTermAddr apL ↦□ rt ∗ rnRtOk γn rt (rnLogOf γn A').length ∗
        schedule.schedRunning γs ∗ applyResR K C rp A ∗ srvWTPool C.E C.wt ∗ srvRLogLb C.ρ.raft A' ∗
        srvRLogLb C.ρ.raft A }}
      (App (App (Val (C.s @!! go.GoType.PointerType EtcdServer.ty @!! go!"applyAll")) (Val #C.ep))
        (Val #apL))
    {{ RET #(); schedule.schedRunning γs ∗ applyResR K C rp A' }} := by
  iintro %Φ ⟨#Hpkg, #Hsa, #Hmid, #Hmeta, #Hes, #Hesl, #Hsnf, Hsnv, #Hcl, #Hncf, #Hnc2, Hnr0,
    #Hracf, #Hracc, #Hrtf, #Hrtok, Hrun, HR, #HWc, #Hlbr, #HlbA⟩ HΦ
  iunfold applyResR at HR
  icases HR with ⟨%B, %st, %ai, %at', %a, %t, %cs, %x, %sa, %g, %HB, #Hsrv, Hai, Hat, Hcs, #Hcv, Hss,
    Hst, Hbe, Happ, Hlr, Hbr, Hwr, HKV, Hao, #Hlog, Hkr, HRS, HAR, #HlbA0, #HKVf, Hwal, ⟨%w, #HWA⟩,
    HtokR, Hso, %Hpure⟩
  ihave Hwal : rnWalTokA γn (srvRAddr C.s) (1 : Qp).half $$ [Hwal]
  · rw [← hrn]; iexact Hwal
  obtain ⟨Hloop, Hai0, HJ, Hci, Hlt, Hg0, Hb, Hty, HA0b⟩ := Hpure
  ihave Hkr : iprop(kvAppliedM K.isOn C.γr.raft C.γr.kv srvAuthSt0 (ghostOf rp A) x sa ∗
      ⌜C.γr.kv.c0 = C.c₀ ∧ C.γr.raft.ai0 = C.ai₀⌝) $$ [Hkr]
  · rw [← kvRunM_split]; iexact Hkr
  icases Hkr with ⟨Hka, %Hkc⟩
  iunfold schedule.schedRunning at Hrun
  icases Hrun with ⟨Hrt0, Htok⟩
  -- the fresh start's facts
  have hai0 : C.ai₀ = W64 0 := by have := uint_nat_eq C.ai₀; word
  have hpre' : C.γr.raft.pre = [] := by rw [hpr]; exact hpre
  have hiA : (uint.nat sv.Metadata'.Index' : Int) = A'.length := by rw [← hlen, hpre]; simp
  have hiZ := uint_nat_eq sv.Metadata'.Index'
  have hz0 : uint.Z (W64 0) = 0 := by word
  have hgl := ghostOf_length rp A
  have hAL : uint.Z g = (ghostOf rp A).length := by rw [Hg0, hai0, hz0]; simp
  have hag : uint.Z ai ≤ uint.Z g := by rw [Hai0, Hg0, hgl]; push_cast; omega
  have hgi : uint.Z g < uint.Z sv.Metadata'.Index' := by
    have : ((ghostOf rp A).length : Int) < A'.length := by exact_mod_cast hwin
    omega
  have hcia : uint.Z (ciEff B.γ st.k) ≤ uint.Z g := by
    rcases HJ with h1 | ⟨-, h2⟩
    · rw [h1]; rw [hai0] at hc0; omega
    · exact h2
  have hc00 : C.c₀ = W64 0 := by rw [hai0] at hc0; word
  have hraft : C.γr.raft = ⟨C.γr.raft.raft, [], W64 0⟩ := by
    have h1 := Hkc.2
    rw [hai0] at h1
    cases hr : C.γr.raft
    simp only [hr] at hpre' h1
    simp [hpre', h1]
  -- the mode: the current backend's the component's
  have hMB : B.E.authMode = K.mode := (beSucc_authMode HB).trans hM
  have hon : B.E.authOn = K.isOn := by
    simp only [apply.AEnv.authOn, hMB, AuthC.mode_isOn]
  have hany : B.E.authMode ≠ .any := by rw [hMB]; cases K <;> simp [AuthC.mode]
  imod isServerC_ch0 K C.s B.γ C.ci B.TM B.E C.ρ C.γr $$ Hsrv with %hch
  -- (R2d'a task 4) the rest buckets at an image of the ghost log with the model's ids
  ihave %HpA := srvRLogLb_prefix C.γr.raft A rp.A₀ $$ [HlbA HlbA0]
  · rw [← hρ]; iframe HlbA HlbA0
  obtain ⟨r0, hids, hRS⟩ := srvRestR_img B.E C.γr rp A HpA
  ihave HRS : srvRestRp B.E C.γr (ghostOf rp A) r0 $$ [HRS]
  · rw [← hRS]; iexact HRS
  ihave #Hsa' := Hsa
  iunfold isServerApplyAll at Hsa'
  icases Hsa' with ⟨%wt0, %msc, %sc, -, -, -, -, -, -, -, -, -, -, -, %Hlog0⟩
  have hn : uint.nat sv.Metadata'.Index' ≤ (rnLogOf γn A').length := by
    simp only [rnLogOf, List.length_map]; omega
  -- the job's resources at the current backend `B`
  ihave #HWc' : iprop(srvWTPool B.E C.wt) $$ []
  · rw [srvWTPool_beSucc HB]; iexact HWc
  ihave Hbr : iprop(srvBemuReaderAt C.s B.E.γbe) $$ [Hbr]
  · rw [beSucc_γbe HB]; iexact Hbr
  ihave #Hmeta' : srvMetaSnap B.γ $$ []
  · have hms : srvMetaSnap (GF := GF) B.γ = srvMetaSnap C.γ := by
      rw [HB.1]; exact srvMetaSnap_withPh _ _
    rw [hms]; iexact Hmeta
  iunfold srvMetaSnap at Hmeta'
  ihave #Hracc' : rnAdvChan rac (letI := srvStor (GF := GF) C.ρ.raft.raft
      iprop(nodeAppliedLb C.ρ.raft.raft.cl γn.key (uint.nat sv.Metadata'.Index') ∗
        nodeCommitLb C.ρ.raft.raft.cl γn.key (uint.nat sv.Metadata'.Index') ∗
        srvFrozenAt C.γs (uint.nat sv.Metadata'.Index') ∗
        srvFrozenBelow C.γs (uint.nat sv.Metadata'.Index') ∗
        rnWalHanded γn (uint.nat sv.Metadata'.Index'))) $$ []
  · rw [hρ, ← hγn, hγs, ← hlen]; iexact Hracc
  ihave #Hcl' : (letI := srvStor (GF := GF) C.γr.raft.raft; iprop(
      snapshotCert C.γr.raft.raft.cl srvClusterN (snapTrip sv sv.Metadata'.ConfState'.lists) ∗
      nodeSnapLocal C.γr.raft.raft.cl γn.id sv.Metadata'.Index')) $$ []
  · rw [← hγn]; iexact Hcl
  ihave #HsrvM : isServerM K.isOn C.s B.γ C.ci B.TM B.E C.ρ C.γr $$ []
  · iapply (isServerM_C K C.s B.γ C.ci B.TM B.E C.ρ C.γr).2 $$ Hsrv
  ihave HKV : srvApplyKVM K.isOn C.s B.E C.ρ.wait x sa $$ [HKV]
  · rw [← hγw]; iapply (srvApplyKVM_C K C.s B.E C.γw x sa).2 $$ HKV
  have hS := hAA C.s B.γ C.ci B.TM B.E C.ρ C.γr B.b C.ep apL es sn sv rac nc st ai at' a t cs x
    (ghostOf rp A) C.ms C.γs C.wt γnc w γn.id γn.key (1 : Qp).half γn rt (rnLogOf γn A').length sa
    g r0 hany hag hgi h61 (by rw [← hγn]; exact hboot) hAL hcia hids hraft (by rw [Hkc.1, hc00])
    (by rw [hon]; exact hch) Hlog0 hγn hn
  rw [hon] at hS
  iapply hS
    $$ [Hai Hat Hcs Hss Hst Hbe Happ Hlr Hwr Htok Hbr HKV Hao Hka HRS HAR Hwal Hso Hsnv Hnr0]
  · iframe #
    iframe
    iunfold srvGoRes
    iframe
  inext
  iintro ⟨%γ', %TM', %E', %b', %st', %A'', %cs', %HB', #Hsrv'', HAR, #Hlb'', Hai, Hat, Hcs,
    #Hcv', Hss, Hst, Hbe, Happ, Hlr, Hgr, Hbr, Hao, #Hal, #HWA', ⟨%x', HKV, #Hlog', Hka, HRS⟩,
    #HKVf', Hwal, Hso, %Hpost⟩
  ihave Hwal : rnWalTokA C.rn (srvRAddr C.s) (1 : Qp).half $$ [Hwal]
  · rw [hrn]; iexact Hwal
  obtain ⟨hloop', hci', -, hlen'', hlast⟩ := Hpost
  -- the image's log is raft's `A'`: both committed, of the snapshot's length
  ihave #Hlbr' : srvRLogLb C.γr.raft A' $$ []
  · rw [← hρ]; iexact Hlbr
  ihave %Hpf := srvRLogLb_prefix C.γr.raft A'' A' $$ [Hlb'' Hlbr']
  · iframe Hlb'' Hlbr'
  have hA : A'' = A' := by
    have h1 : A''.length = A'.length := by
      rw [hpre'] at hlen''; simp only [List.nil_append] at hlen''; omega
    rcases Hpf with h | h
    · exact h.eq_of_length h1
    · exact (h.eq_of_length h1.symm).symm
  subst hA
  -- Go past the window: the ghost log Go's
  have hpast : rp.A₀.length ≤ A''.length := by
    have := ghostOf_length rp A; omega
  have hgA : ghostOf rp A'' = A'' := ghostOf_past rp A'' hpast
  iunfold srvGoRes at Hgr
  icases Hgr with ⟨Hwr, Htok⟩
  have hMB' : E'.authMode = K.mode := (beSucc_authMode HB').trans hMB
  have hon' : E'.authOn = K.isOn := by
    simp only [apply.AEnv.authOn, hMB', AuthC.mode_isOn]
  ihave #Hsrv3 : isServerC K C.s γ' C.ci TM' E' C.ρ C.γr $$ []
  · iapply (isServerM_C K C.s γ' C.ci TM' E' C.ρ C.γr).1; rw [← hon]; iexact Hsrv''
  ihave HKV : srvApplyKVC K C.s E' C.γw x' (srvAuthAtLog C.γr.kv srvAuthSt0 A'') $$ [HKV]
  · iapply (srvApplyKVM_C K C.s E' C.γw x' _).1; rw [hγw, ← hon]; iexact HKV
  ihave Hkr : kvRunM K.isOn C.γr C.ai₀ C.c₀ (ghostOf rp A'') x' (srvAuthAtLog C.γr.kv srvAuthSt0 A'')
    $$ [Hka]
  · rw [kvRunM_split, hgA, ← hon]
    iframe Hka
    ipureintro; exact Hkc
  ihave HRS : srvRestR E' C.γr rp A'' $$ [HRS]
  · rw [srvRestR_past E' C.γr rp A'' hpast]; iexact HRS
  ihave HAR : srvApRes C.s C.γr (ghostOf rp A'') $$ [HAR]
  · rw [hgA]; iexact HAR
  ihave #Hcv'' : epCsAt C.ρ.raft (ghostOf rp A'') cs' $$ []
  · rw [hgA]; iexact Hcv'
  -- the token rights at the snapshot's consistent index
  ihave HtokR := acTok_mono K _ sv.Metadata'.Index' (by omega) $$ HtokR
  ihave HtokR : acTok K (ciEff γ' st'.k) $$ [HtokR]
  · rw [hci']; iexact HtokR
  iapply HΦ
  iunfold schedule.schedRunning
  iframe Hrt0 Htok
  ihave Hbr : iprop(srvBemuReaderAt C.s C.E.γbe) $$ [Hbr]
  · rw [← beSucc_γbe HB]; iexact Hbr
  iunfold applyResR
  iexists ⟨γ', TM', E', b'⟩, st', sv.Metadata'.Index', sv.Metadata'.Term', a, t, cs', x',
    srvAuthAtLog C.γr.kv srvAuthSt0 A'', sv.Metadata'.Index'
  isplitr
  · ipureintro; exact beSucc_trans HB HB'
  iframe Hsrv3 Hcv'' HKVf' Hlog' HlbA0
  iframe
  isplitr
  · iexists w; iexact HWA'
  ipureintro
  have hb' : rp.b ≤ A''.length := by have := hgl; omega
  refine ⟨hloop', ?_, ?_, by rw [hci']; exact Int.le_refl _, hlast, ?_, hb', Hty, ?_, HA0b.2⟩
  · rw [hai0, hz0]; omega
  · right; rw [hci', hc00]; simp
  · rw [hgA, hai0, hz0]; omega
  · rw [hci', hai0, hz0]; omega

end proof

end EtcdGrove
end Perennial
