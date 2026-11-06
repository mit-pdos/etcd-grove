/-
**`apply`'s restart form** (R2d' probe, A5, 2026-11-06; DRAFT: nothing here is frozen,
`notes/restart-plan.md`, "R2d' Scope (approved 2026-11-06)", its probe). Lean-first (no Rocq
counterpart). `apply.specROff`: `apply.specOff` over the restart point `rp` and Go's log `A`, the
ghost rows at `ghostOf rp A`; its proof `wp_proofROff`, `wp_proofOff`'s with the window's replays
(`applyEntryNormal.spec`'s `v3 = false` case, Q23 (a); `applyConfChange.spec`'s, swap batch 1).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__apply
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Results
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ApplyRDefs
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__apply
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SDRun
public import Spec.go_uber_org.zap.Logger__Debug
public import Spec.go_uber_org.zap.Int
public import Spec.go_uber_org.zap.Uint64
public import Spec.go_uber_org.zap.Stringer
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.cindex.consistentIndex__ConsistentIndex
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.cindex.consistentIndex__SetConsistentApplyingIndex
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.cindex.consistentIndex__SetConsistentIndex
public import Spec.go_etcd_io.raft.v3.raftpb.Entry__GetIndex
public import Spec.go_etcd_io.raft.v3.raftpb.Entry__GetTerm
public import Spec.go_etcd_io.raft.v3.raftpb.Entry__GetType
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__applyEntryNormal
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ModeSpecs
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__setAppliedIndex
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__setTerm
public import Spec.go_etcd_io.etcd.pkg.v3.pbutil.MustUnmarshalMessage
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__applyConfChange
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.RestMemId
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.RestLeased
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVApply
public import Spec.go_etcd_io.raft.v3.raftpb.ConfChange__GetId
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster__Members
public import Proof.go_etcd_io.raft.v3.FrameH

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.cindex
  go_etcd_io.etcd.server.v3.storage go_etcd_io.etcd.server.v3.etcdserver

/-- **A replayed entry keeps the KV** (`v3 = false`; `Results.lean`'s `entryStep_no_v3`). -/
theorem entryStep_false_eq [GooseExts] (m : EntryModel) (y y' : apply.ApplyKV) (out : apply.ApplyOut)
    (h : entryStep m false y y' out) : y' = y := by
  unfold entryStep at h
  split at h
  · exact h.1
  · obtain ⟨rq, -, -, -, h⟩ := h
    exact EtcdGrove.apply.apply_no_v3_no_write rq y y' out h

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`s.apply(…)` at a restart point** (R2d' probe, A5, DRAFT; auth off, `apply.specOff`'s window
form). Go's rows at Go's log `A` (the log raft handed this incarnation): the batch from `f0`, Go's
index `f0 - 1` (`kvBatchR`), `loopOk`, the returned index and term. The ghost rows at the ghost log
`ghostOf rp A`: the applied index `g` and its log, the KV model, `ep.confState`'s voters, the view,
the membership resource; the rest buckets `srvRestR` (the replay arm inside the window). At the pin
`673da07c8` (`server.go:1922-1972`) the entries at or below the effective consistent index are
replayed v2-only (`shouldApplyV3` false): the ghost rows stay (`setAppliedIndex`'s replay case), the
rest buckets' image takes the attribute writes (`restEntryV2`), and the replay closes on the model
when Go's log reaches the backend's (`restReplay_closeI`). The view's premise at the ghost index
(`dvOk … (g + 1)`, Q19). A first start (`RestartPt.first`, `g = f0 - 1`) is `specOff`'s. -/
abbrev EtcdServer.apply.specROff : Prop :=
  ∀ (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF) (E : apply.AEnv GF) (ρ : ReqNames)
    (b : GoInterface) (es : GoSlice) (ents : List Loc) (ms : List EntryModel) (f0 : w64) (ep : Loc) (cs : Loc)
    (rac : GoChan) (st : ApplyState) (a at0 : w64) (x : apply.ApplyKV) (γr : ReadNames)
    (rp : RestartPt) (A : List EntryModel) (γp : WTNames) (dv : Option Loc) (w : Nat) (g : w64),
  ms ≠ [] → entriesFrom f0 ms → loopOk γ st (f0 - 1) → logShape E.lm ms →
  dvOk ρ.raft γr.kv.c0 dv (ciEff γ st.k) (g + 1) ms →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ isServer s γ ci TM E ρ γr ∗
      batchWaitOk ρ E ms ∗ es ↦*□ ents ∗ entriesAt ents ms ∗
      applyThread γ st ∗ applyBackend γ ci b ∗ ciApplying ci a at0 ∗ epConfState ep cs ∗
      epCsAt ρ.raft (ghostOf rp A) cs ∗
      srvLgReader s ∗ srvGoRes s ∗ srvApplyKV s E ρ.wait x ∗ srvAppliedOwn γr g ∗
      appliedLogAt γr g x.log ∗ batchCommittedIdx γr ms ∗ srvWTPool E γp ∗
      srvWTTaken γp.cnt w ∗ srvFS s ∗
      kvApplied γr.raft γr.kv (ghostOf rp A) x ∗ srvRestR E γr rp A ∗
      kvBatchR γr (ciEff γ st.k) (f0 - 1) rp A ms ∗
      ⌜uint.Z g = uint.Z γr.raft.ai0 + (ghostOf rp A).length⌝ ∗
      dvView ρ.raft dv (ghostOf rp A) ∗ dvRes s ρ.raft dv (A ++ ms) ∗ srvRunH ρ.raft dv ∗
      srvApRes s γr (ghostOf rp A) }}
    (App (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"apply"))
      (Val #es)) (Val #ep)) (Val #rac))
  {{ (appliedt appliedi : w64) (shouldStop : Bool),
      RET (PairV (PairV #appliedt #appliedi) #shouldStop);
        srvFS s ∗ dvView ρ.raft dv (ghostOf rp (A ++ ms)) ∗ srvRunH ρ.raft dv ∗
        srvApRes s γr (ghostOf rp (A ++ ms)) ∗
        (∃ (st' : ApplyState) (a' at' : w64) (csl : Loc) (g' : w64),
          applyThread γ st' ∗ applyBackend γ ci b ∗ ciApplying ci a' at' ∗
          epConfState ep csl ∗ epCsAt ρ.raft (ghostOf rp (A ++ ms)) csl ∗ srvLgReader s ∗
          srvGoRes s ∗ srvAppliedOwn γr g' ∗
          srvWTTaken γp.cnt (w + ms.length) ∗
          (∃ x' : apply.ApplyKV, srvApplyKV s E ρ.wait x' ∗ ⌜entriesStep (ciEff γ st.k) ms x x'⌝ ∗
            appliedLogAt γr g' x'.log ∗ kvApplied γr.raft γr.kv (ghostOf rp (A ++ ms)) x' ∗
            srvRestR E γr rp (A ++ ms)) ∗
          ⌜uint.Z g' = uint.Z γr.raft.ai0 + (ghostOf rp (A ++ ms)).length ∧
            (ms.getLast?).map EntryModel.index = some appliedi ∧
            (ms.getLast?).map EntryModel.term = some appliedt ∧
            loopOk γ st' appliedi ∧
            uint.Z (ciEff γ st'.k) = max (uint.Z (ciEff γ st.k)) (uint.Z appliedi) ∧
            shouldStop = false⌝) }}

set_option hygiene false in
/-- A conf change, after `applyConfChange` (`xj` unchanged: no KV effect): the KV model's step,
the applied index (`setAppliedIndex`) and term (both conf-change branches: applied, or
skipped by the consistent index). -/
local macro "cc_kv_applied" : tactic => `(tactic| (
    (try wp_auto)
    wp_apply hGI $$ [He] as -
    · iframe He
    icases srvApplyKV_idxCert s E ρ.wait xj $$ HKV with ⟨HKV, #Hcert⟩
    ihave %Hlxj := idxCert_len E.γ.idx xj.log $$ Hcert
    have hcc0 : kvEntry γr.kv.c0 xj.chain (kvLeases γr.kv (A ++ ms.take (sint.nat j))) xj.log m =
        xj.log :=
      kvEntry_nonwrite _ _ _ _ m (Or.inr (Or.inl (by rw [h1]; decide)))
    imod kv_applied_step E γr (A ++ ms.take (sint.nat j)) m xj (by rw [hcc0]; exact Hlxj)
      $$ Hkvi Hka HlbJ with ⟨%Hpe, Hka⟩
    ihave ⟨Hka, #HkL⟩ := kvApplied_next γr (A ++ ms.take (sint.nat j)) m xj xj m.index hiA
      hcc0.symm Hpe.2.1
      (crevOf_batchStep γr.kv _ m xj xj Hpe.1
        (by unfold batchStep; rw [if_neg (by rw [h1]; decide)]) Hpe.2.1 Hpe.2.2.2.1) $$ Hka
    imod applied_predeposit s E γr aw m.index xj.log xj.log (by omega) (List.prefix_refl _)
      $$ Hainv Hao Hlog HkL with Hpre
    wp_apply (hSet1 s E γr aw m.index xj.log) $$ [Hpre] as ⟨Hao, -, #Hlog'⟩
    · iframe HainvM Hpre Hcert; rw [hAuthOff]; unfold appliedPubM; itrivial
    (try wp_auto)
    wp_apply hGT $$ [He] as -
    · iframe He
    wp_apply hSet2 $$ [$(frameH `HatM)]
    (try wp_auto)
  ))

set_option hygiene false in
/-- A conf change's response (both conf-change branches, either value of the loop's
`shouldStop`): `GetId`, the cluster's members, the `Trigger` of the wait (no waiter), the next
iteration up to its witnesses. -/
local macro "cc_respond" : tactic => `(tactic| (
    (try wp_auto)
    wp_apply (wp_ownCCV1_GetId hId cc_ptr DFrac.discard cm' (ccIdOf m.data)
      (by rw [hIdEq, ccIdOf_of_decode Hdec])) $$ [Hcc] as Hcc
    · iframe Hcc
    (try wp_auto)
    wp_apply (membership.RaftCluster.Members.spec_static hMem sv.cluster) $$ [] as %msl -
    · iframe #
    (try wp_auto)
    wp_alloc rsp as Hrsp
    (try wp_auto)
    ihave #Hwok2 := Hwok
    iunfold waitInv at Hwok2
    icases Hwok2 with ⟨⟨%RD0, Hwok2⟩, -⟩
    iunfold isWait at Hwok2
    icases Hwok2 with ⟨%wi, %hw, -, #Htrig, -⟩
    simp only [hw]
    (try wp_auto)
    wp_apply Htrig
    · iright; iright
      iunfold waitTrig
      iintro %Ψ HR
      iexfalso
      iapply Hccf $$ HR
    (try wp_auto)
    wp_apply hGI $$ [He] as -
    · iframe He
    wp_apply hGT $$ [He] as -
    · iframe He
    (try wp_auto)
    wp_for_post
    iframe
  ))


set_option maxHeartbeats 1600000 in
/-- **`apply.specROff`** (R2d' probe, DRAFT): over the replays' specs. -/
theorem EtcdServer.apply.wp_proofROff
    (hDebug : zap.Logger.Debug.spec (GF := GF) (hG := hG))
    (hInt : zap.Int'.spec (GF := GF) (hG := hG))
    (hU64 : zap.Uint64.spec (GF := GF) (hG := hG))
    (hStr : zap.Stringer.spec (GF := GF) (hG := hG))
    (hCI : consistentIndex.ConsistentIndex.spec (GF := GF) (hG := hG))
    (hSAI : consistentIndex.SetConsistentApplyingIndex.spec (GF := GF) (hG := hG))
    (hSCI : consistentIndex.SetConsistentIndex.spec (GF := GF) (hG := hG))
    (hGI : raftpb.Entry.GetIndex.spec (GF := GF) (hG := hG))
    (hGT : raftpb.Entry.GetTerm.spec (GF := GF) (hG := hG))
    (hGTy : raftpb.Entry.GetType.spec (GF := GF) (hG := hG))
    (hAEN : EtcdServer.applyEntryNormal.spec (GF := GF) (hG := hG))
    (hSet1 : EtcdServer.setAppliedIndex.spec (GF := GF) (hG := hG))
    (hSet2 : EtcdServer.setTerm.spec (GF := GF) (hG := hG))
    (hMU : pbutil.MustUnmarshalMessage.spec (GF := GF) (hG := hG))
    (hACC : EtcdServer.applyConfChange.spec (GF := GF) (hG := hG))
    (hId : raftpb.ConfChange.GetId.spec (GF := GF) (hG := hG))
    (hMem : membership.RaftCluster.Members.spec (GF := GF) (hG := hG)) :
    EtcdServer.apply.specROff (GF := GF) (hG := hG) := by
  -- (R2d') `setAppliedIndex`'s replay case, for the window's replays
  have hSet1R := fun s E γr v v' L => hSet1 s E γr v v' L true
  simp only [↓reduceIte] at hSet1R
  -- (R2d-4) `setAppliedIndex`'s first case: not a replay
  have hSet1 := fun s E γr v v' L => hSet1 s E γr v v' L false
  simp only [Bool.false_eq_true, ↓reduceIte] at hSet1
  have hAEN := EtcdServer.applyEntryNormal.spec_off hAEN
  -- (R2d'a, Q23 (a)) `applyEntryNormal.spec`'s two cases: the replay (`v3 = false`) inside the
  -- window, the application (`v3`) past it
  have hAENR := fun s γ ci TM E ρ b e m st x γr A₀ r h =>
    hAEN s γ ci TM E ρ b e m st false x γr none (W64 0) [] A₀ r h
  simp only [Bool.false_eq_true, ↓reduceIte] at hAENR
  have hAEN := fun s γ ci TM E ρ b e m st x γr ot v A A₀ r h =>
    hAEN s γ ci TM E ρ b e m st true x γr ot v A A₀ r h
  simp only [↓reduceIte] at hAEN
  -- (R2d'a, swap batch 1) `applyConfChange.spec`'s replay case (`v3 = false`), for the window's
  -- replayed conf changes (the binders only the `v3` case reads at placeholders)
  have hACCR := fun s cc ep m cs E γs γB cl rs d al st lp lg bh ix lgh tl lid prs lgc cid
      (e : LogEntry) (hok : ccApplyOkM γs m) hro (hp : m.nodeId ≠ lid → m.nodeId ∈ prs)
      (hsz : GMap.size (GMap.insert m.nodeId (membership.ccMemberAt m) rs.mem) ≤ 2 ^ 62) =>
    hACC s cc ep m cs false null GoInterface.nil E γs iprop(True) iprop(True) iprop(True)
      iprop(True) (W64 0) (W64 0) γB cl rs d al st lp none [] ⟨0, Membership.empty⟩ 0 Membership.empty e lg bh ix
      lgh tl lid prs lgc cid hok hro (fun _ => hp)
      (fun h => absurd (hok.1.symm.trans h) (by decide : ¬ (W32 0 : w32) = W32 1)) (fun _ => hsz)
      (fun h => absurd h Bool.false_ne_true)
  simp only [Bool.false_eq_true, ↓reduceIte] at hACCR
  -- (swap batch 1) `applyConfChange.spec`'s `v3` case
  have hACC := fun s cc ep m cs => hACC s cc ep m cs true
  simp only [↓reduceIte] at hACC
  have hGI := wp_entryAt_GetIndex hGI
  have hGT := wp_entryAt_GetTerm hGT
  have hGTy := wp_entryAt_GetType hGTy
  intro s γ ci TM E ρ b es ents ms f0 ep cs rac st a at0 x γr rp A γp dv w g hne hfrom hok hEok hdv
  wp_start as ⟨#Hsrv, #Hbw, #Hes, #Hents, Hst, Hbe, Happ, Hcs, #Hcv0, Hlr, Hgr, HKV, Hao, #Hlog0, #Hbc,
    #HWP, #HWA0, Hfs, Hka, HRS, #Hkb, %Hg0, Hdv, #Hdvr, Hrun, HAR⟩
  ihave #Hsrv0 := Hsrv
  -- (the auth-mode merge) the mode off: `setAppliedIndex`/`setTerm` are stated at `E.authOn`
  imod authOn_false_of_off s γ ci TM E ρ γr ρ.wait x (ghostOf rp A) $$ [$Hsrv0 $HKV $Hka] with
    ⟨%hAuthOff, HKV, Hka⟩
  ihave #Pmem : isPkgInit (PROP := IProp GF)
      pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership $$ []
  · iPkgInit
  iunfold isServer at Hsrv
  icases Hsrv with ⟨%Hrd, #Hsci, ⟨%sv, #Hfl⟩, #Hat, -, #Hrn, -⟩
  ihave #Hat' := Hat
  iunfold srvAtomics at Hat'
  icases Hat' with ⟨#Hainv, -, #Hkvi⟩
  ihave #HatM : srvAtomicsM E.authOn s E γr $$ []
  · rw [hAuthOff, srvAtomicsM_false]; iexact Hat
  ihave #HainvM : srvAppliedInvM E.authOn s E γr $$ []
  · rw [hAuthOff, srvAppliedInvM_false]; iexact Hainv
  ihave #Hkvi2 := Hkvi
  iunfold srvKVInvs at Hkvi2
  icases Hkvi2 with ⟨-, -, #Hrli, -⟩
  ihave %Hai0 := srvRaftLogInv_facts _ $$ Hrli
  iunfold kvBatchR at Hkb
  icases Hkb with ⟨#HlbB, #HlbA0, %HkB⟩
  iunfold batchCommittedIdx at Hbc
  ihave #Hsci' := Hsci
  iunfold isServerCI at Hsci'
  icases Hsci' with ⟨#Hcif, #Hci, #Hinv⟩
  iunfold srvFieldsAt at Hfl
  icases Hfl with ⟨#Hlg, %Hlgnn, #Hw, #Hwok, %HE, %HEo, #Hhook, #Hls, #Hlok, #Hfc, #Hals,
    #Hcl, #Hrc, #Hq, #Hlgmu, #Hmid, #Hlead, #Het, #Htm, #Hnot, #Halm⟩
  obtain ⟨γB, Hobj, HROeq, -, dB, alB, stB, lpB, hkbB, hgbB, hHB, -⟩ := HEo.2.2.2
  subst hHB
  ihave #Hzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  ihave %Hesl := ownSlice_len _ _ _ $$ Hes
  ihave #Hents2 := Hents
  iunfold entriesAt at Hents2
  icases Hents2 with ⟨%Hel, #Hent⟩
  have Hlen : ms.length = sint.nat es.len := by rw [← Hel]; exact Hesl.1
  wp_auto
  wp_apply hInt as %fl1 -
  wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [fl1]
  isplitr
  · ipureintro; rfl
  iintro %fsl1 ⟨-, -⟩
  wp_auto
  wp_apply hDebug $$ []
  · ipureintro; exact Hlgnn
  irename i => cnt
  irename i => iv
  rename_i ivp
  ipersist s
  ipersist raftAdvancedC
  ipersist ep
  ipersist es
  obtain ⟨Hf0pos, Hf0n, Hms⟩ := hfrom
  obtain ⟨Hpend, Hp0⟩ := hok
  have Hf0m1 : uint.Z (f0 - 1) = uint.Z f0 - 1 := by word
  rw [Hf0m1] at Hp0
  ihave HI : (∃ (j : w64) (st' : ApplyState) (a' t' : w64) (csl : Loc) (sb : Bool)
        (ai at' ivv : w64) (xj : apply.ApplyKV) (aw : w64) (Γ : List EntryModel),
      "cnt" ∷ i_ptr ↦ j ∗ "iv" ∷ ivp ↦ ivv ∗ "shouldStop" ∷ shouldStop_ptr ↦ sb ∗
      "appliedi" ∷ appliedi_ptr ↦ ai ∗ "appliedt" ∷ appliedt_ptr ↦ at' ∗
      "Hst" ∷ applyThread γ st' ∗ "Hbe" ∷ applyBackend γ ci b ∗ "Happ" ∷ ciApplying ci a' t' ∗
      "Hcs" ∷ epConfState ep csl ∗ "#Hcv" ∷ epCsAt ρ.raft Γ csl ∗ "Hlr" ∷ srvLgReader s ∗ "Hgr" ∷ srvGoRes s ∗ "Hfs" ∷ srvFS s ∗
      "HKV" ∷ srvApplyKV s E ρ.wait xj ∗
      "Hao" ∷ srvAppliedOwn γr aw ∗
      "#Hlog" ∷ appliedLogAt γr aw xj.log ∗
      -- (D22 J5) the write tokens taken, one per entry
      "#HWA" ∷ srvWTTaken γp.cnt (w + sint.nat j) ∗
      "Hka" ∷ kvApplied γr.raft γr.kv Γ xj ∗
      "HRS" ∷ srvRestR E γr rp (A ++ ms.take (sint.nat j)) ∗
      "HAR" ∷ srvApRes s γr Γ ∗
      "Hdv" ∷ dvView ρ.raft dv Γ ∗
      "Hrun" ∷ srvRunH ρ.raft dv ∗
      "%Hxs" ∷ ⌜entriesStep (ciEff γ st.k) (ms.take (sint.nat j)) x xj⌝ ∗
      "Hphi" ∷ (∀ (appliedt appliedi : w64) (shouldStop : Bool),
        srvFS s ∗ dvView ρ.raft dv (ghostOf rp (A ++ ms)) ∗ srvRunH ρ.raft dv ∗
        srvApRes s γr (ghostOf rp (A ++ ms)) ∗
        (∃ (st' : ApplyState) (a' at' : w64) (csl : Loc) (g' : w64),
          applyThread γ st' ∗ applyBackend γ ci b ∗ ciApplying ci a' at' ∗
          epConfState ep csl ∗ epCsAt ρ.raft (ghostOf rp (A ++ ms)) csl ∗ srvLgReader s ∗
          srvGoRes s ∗ srvAppliedOwn γr g' ∗
          srvWTTaken γp.cnt (w + ms.length) ∗
          (∃ x' : apply.ApplyKV, srvApplyKV s E ρ.wait x' ∗ ⌜entriesStep (ciEff γ st.k) ms x x'⌝ ∗
            appliedLogAt γr g' x'.log ∗ kvApplied γr.raft γr.kv (ghostOf rp (A ++ ms)) x' ∗
            srvRestR E γr rp (A ++ ms)) ∗
          ⌜uint.Z g' = uint.Z γr.raft.ai0 + (ghostOf rp (A ++ ms)).length ∧
            (ms.getLast?).map EntryModel.index = some appliedi ∧
            (ms.getLast?).map EntryModel.term = some appliedt ∧
            loopOk γ st' appliedi ∧
            uint.Z (ciEff γ st'.k) = max (uint.Z (ciEff γ st.k)) (uint.Z appliedi) ∧
            shouldStop = false⌝) -∗
        Φ (PairV (PairV #appliedt #appliedi) #shouldStop)) ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z es.len⌝ ∗
      "%Hstj" ∷ ⌜st'.pending = false ∧
        uint.Z st'.p = max (uint.Z (ciEff γ st.k)) (uint.Z f0 - 1 + sint.Z j) ∧
        uint.Z (ciEff γ st'.k) = (if sint.Z j = 0 then uint.Z (ciEff γ st.k)
          else max (uint.Z (ciEff γ st.k)) (uint.Z f0 - 1 + sint.Z j))⌝ ∗
      "%Hlast" ∷ ⌜∀ m : EntryModel, 0 < sint.nat j → ms[sint.nat j - 1]? = some m →
        m.index = ai ∧ m.term = at'⌝ ∗
      "%Haw" ∷ ⌜uint.Z aw = uint.Z γr.raft.ai0 + Γ.length⌝ ∗
      "%HΓ" ∷ ⌜Γ = ghostOf rp (A ++ ms.take (sint.nat j))⌝ ∗ "%Hsb" ∷ ⌜sb = false⌝ : IProp GF)
    $$ [cnt iv shouldStop appliedi appliedt Hst Hbe Happ Hcs Hlr Hgr Hfs HKV Hao HΦ Hka HRS Hdv Hrun HAR]
  · iexists (W64 0), st, a, at0, cs, false, (W64 0), (W64 0), (W64 0), x, g, ghostOf rp A
    simp only [named, show sint.nat (W64 0) = 0 from rfl, List.take_zero,
      List.append_nil]
    iframe
    iframe Hlog0 Hcv0
    isplitr
    · iexact HWA0
    ipureintro
    refine ⟨rfl, by word, ⟨Hpend, ?_, ?_⟩, fun m h => absurd h (by simp), Hg0, by simp, by simp⟩
    · rw [Hp0]; simp
    · simp
  wp_for HI
  wp_if_destruct
  · -- the `j`-th entry
    have hjl : sint.nat j < ms.length := by rw [Hlen]; word
    list_elem ents (sint.nat j) as e
    list_elem ms (sint.nat j) as m
    -- (S5) the first entry applied is the first boot entry
    ihave %Hfb := srv_first_entry γr.raft A ms (sint.nat j) m Hm_lookup $$ [Hrli HlbB]
    · iframe Hrli HlbB
    ihave #He := Hent $$ %(sint.nat j) %e %m %He_lookup %Hm_lookup
    obtain ⟨hmidx, hmtyp⟩ := Hms (sint.nat j) m Hm_lookup
    -- the KV model (unit T1): the entry is the next of the committed raft log
    have hmem : m ∈ ms := List.mem_of_getElem? Hm_lookup
    -- the entry's premise at the KV's log, from its shape and the log's smallness (D19c's move)
    icases srvApplyKV_small s E ρ.wait xj $$ HKV with ⟨%Hsmall, HKV⟩
    have hOk1 : m.typ = W32 0 → entryOk E.lm xj m := fun ht =>
      entryOk_of_shape E.lm xj m (hEok m hmem) ht Hsmall.1 Hsmall.2
    have hjn' : ((sint.nat j : Nat) : Int) = sint.Z j := by
      unfold sint.nat; exact Int.toNat_of_nonneg Hj.1
    have hlenA : (A ++ ms.take (sint.nat j)).length = A.length + sint.nat j := by
      rw [List.length_append, List.length_take]; omega
    have hiA : uint.Z m.index = uint.Z γr.raft.ai0 + (A ++ ms.take (sint.nat j)).length + 1 := by
      have := HkB.1; rw [hlenA]; push_cast; omega
    have htk : A ++ ms.take (sint.nat j + 1) = A ++ ms.take (sint.nat j) ++ [m] := by
      rw [List.append_assoc, List.take_add_one, Hm_lookup]; rfl
    have hpfx : A ++ ms.take (sint.nat j) ++ [m] <+: A ++ ms := by
      rw [← htk]; exact (List.prefix_append_right_inj A).mpr (List.take_prefix _ _)
    ihave #HlbJ : iprop(srvRLogLb γr.raft (A ++ ms.take (sint.nat j) ++ [m])) $$ []
    · iapply srvRLogLb_mono γr.raft _ _ hpfx $$ HlbB
    ihave #Hewo : iprop(entryWaitOk ρ E m) $$ []
    · iunfold batchWaitOk at Hbw
      iapply Hbw
      ipureintro; exact List.mem_of_getElem? Hm_lookup
    ihave #Hcm : iprop(committedAtLeast γr m.index) $$ []
    · iapply Hbc
      ipureintro; exact List.mem_of_getElem? Hm_lookup
    have hjs : sint.nat (j + W64 1) = sint.nat j + 1 := by
      show (sint.Z (j + W64 1)).toNat = (sint.Z j).toNat + 1
      have : sint.Z (j + W64 1) = sint.Z j + 1 := by word
      rw [this]; omega
    have htk2 : A ++ ms.take (sint.nat (j + W64 1)) = A ++ ms.take (sint.nat j) ++ [m] := by
      rw [hjs]; exact htk
    have hconf : m.typ ≠ W32 0 → batchStep (ciEff γ st.k) m xj xj := by
      intro hn; unfold batchStep; rw [ite_eq_right hn]
    have Hlt : sint.Z j < sint.Z es.len := by
      first | exact Hif | exact of_decide_eq_true (go.intoVal_inj Hif)
    (try wp_auto)
    simp only [show (0 ≤ sint.Z j ∧ sint.Z j < sint.Z es.len) from ⟨Hj.1, Hlt⟩, _root_.and_self,
      ↓reduceIte]
    wp_apply wp_load_slice_index es (sint.Z j) ents DFrac.discard e Hj.1 $$ [] as -
    · iframe Hes; ipureintro; exact He_lookup
    (try wp_auto)
    simp only [show (0 ≤ sint.Z j ∧ sint.Z j < sint.Z es.len) from ⟨Hj.1, Hlt⟩, _root_.and_self,
      ↓reduceIte]
    wp_apply wp_load_slice_index es (sint.Z j) ents DFrac.discard e Hj.1 $$ [] as -
    · iframe Hes; ipureintro; exact He_lookup
    (try wp_auto)
    -- `index := s.consistIndex.ConsistentIndex()`
    ihave #Hcipkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.cindex $$ []
    · iPkgInit
    ihave #Hrpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
    · iPkgInit
    wp_apply_core (wp_ci_get hCI γ ci b st' Hstj.1) $$ [Hst Hbe]
      [cnt iv shouldStop appliedi appliedt Happ Hcs Hlr Hgr Hfs HKV Hao Hphi e Hka HRS Hdv Hrun HAR]
    · iframe Hcipkg Hci Hinv Hst Hbe
    iintro ⟨Hst, Hbe⟩
    obtain ⟨hlp, hlpp, hlpe, hlc⟩ := stLoaded_facts γ st'
    wp_pure
    wp_pure
    wp_pure
    wp_alloc index_ptr as index
    wp_pure
    wp_pure
    wp_pure
    wp_store
    wp_pure
    wp_pure
    wp_pure
    wp_pure
    wp_pure
    wp_pure
    wp_pure
    wp_pure
    wp_load
    wp_pure
    wp_pure
    -- the Go step resolving `zap.Uint64` gives a time receipt (D19b), for which the budget gives
    -- the entry's write token
    wp_bind (App (Val (GoInstruction (FuncResolve _ _))) (Val _))
    iapply wp_go_step_receipt'
    case hv => exact isPanic_intoVal _
    inext
    iintro Hr Hlc
    iapply wp_value'
    -- (2026-10-19, D21 M3) the token's count, past the entry's index
    imod srvWTPool_take_n s E γp ρ.wait xj (w + sint.nat j) $$ HWP Hr Hlc HWA HKV
      with ⟨Hwt, #HWA1, HKV⟩
    ihave #HWA2 : srvWTTaken γp.cnt (w + sint.nat (j + W64 1)) $$ []
    · rw [hjs, ← Nat.add_assoc]
      iexact HWA1
    (try wp_auto)
    -- the `Debug` log
    wp_apply hU64 as %fl2 -
    wp_apply hGI $$ [He] as -
    · iframe He
    wp_apply hU64 as %fl3 -
    wp_apply hGT $$ [He] as -
    · iframe He
    wp_apply hU64 as %fl4 -
    wp_apply hGTy $$ [He] as -
    · iframe He
    (try wp_auto)
    wp_apply hStr as %fl5 -
    wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [fl2, fl3, fl4, fl5]
    isplitr
    · ipureintro; rfl
    iintro %fsl2 ⟨-, -⟩
    (try wp_auto)
    wp_apply hDebug $$ []
    · ipureintro; exact Hlgnn
    (try wp_auto)
    try simp only [api.membership.ApplyV2storeOnly, api.membership.ApplyBoth]
    (try wp_auto)
    wp_apply hGI $$ [He] as -
    · iframe He
    (try wp_auto)
    wp_if_destruct
    · -- above `ci`: `ApplyBoth`
      have hgt : uint.Z (ciEff γ st'.k) < uint.Z m.index := by
        first | exact Hif | exact of_decide_eq_true (go.intoVal_inj Hif) | word
      have hpast : rp.A₀.length ≤ (A ++ ms.take (sint.nat j)).length := by
        have hce0' : uint.Z (ciEff γ st.k) ≤ uint.Z (ciEff γ st'.k) := by
          rw [Hstj.2.2]; split <;> omega
        have := HkB.2.2.1; omega
      -- (R2d') past the window: the ghost log is Go's
      have hΓe : Γ = A ++ ms.take (sint.nat j) := by rw [HΓ]; exact ghostOf_past _ _ hpast
      subst hΓe
      ihave HRS : srvRest E γr (A ++ ms.take (sint.nat j)) $$ [HRS]
      · rw [← srvRestR_past E γr rp _ hpast]; iexact HRS
      have hawA : uint.Z aw = uint.Z γr.raft.ai0 + (A ++ ms.take (sint.nat j)).length := Haw
      have hkbm : (uint.Z (ciEff γ st.k) < uint.Z m.index ↔ uint.Z γr.kv.c0 < uint.Z m.index) :=
        HkB.2.2.2.2.2 m hmem (by omega)
      wp_apply hGI $$ [He] as -
      · iframe He
      wp_apply hGT $$ [He] as -
      · iframe He
      (try wp_auto)
      wp_apply hSAI $$ [Happ] as Happ
      · iframe Happ
      (try wp_auto)
      wp_apply hGTy $$ [He] as -
      · iframe He
      (try wp_auto)
      -- the arithmetic: the entry is the next to process
      obtain ⟨hpend', hp', hc'⟩ := Hstj
      have hjnat : (sint.nat j : Int) = sint.Z j := by
        unfold sint.nat; exact Int.toNat_of_nonneg Hj.1
      have hidxZ : uint.Z m.index = uint.Z f0 + sint.Z j := by rw [hmidx, hjnat]
      have hjlt : sint.Z j < (ms.length : Int) := by
        have := hjl; unfold sint.nat at this; omega
      have hce0 : uint.Z (ciEff γ st.k) ≤ uint.Z (ciEff γ st'.k) := by
        rw [hc']; split <;> omega
      have hpZ : uint.Z st'.p = uint.Z f0 - 1 + sint.Z j := by
        rw [hp']; omega
      have hip : m.index = st'.p + 1 := by
        apply BitVec.eq_of_toNat_eq
        have h1 := hidxZ; have h2 := hpZ
        simp only [uint.Z] at h1 h2 ⊢
        rw [BitVec.toNat_add]; simp; omega
      have hj1 : sint.Z (j + W64 1) = sint.Z j + 1 := by word
      rcases hmtyp with h0 | ⟨h1, hcc⟩
      · -- a normal entry
        simp only [h0, _root_.decide_true]
        (try wp_auto)
        -- (linkv-txn stage B1) the entry's registration, for the member's own ids
        ihave ⟨%ot, #Hreg⟩ := entryRegd_of_wait ρ E m h0 $$ [Hewo]
        · iframe Hewo; iapply isServer_waitIs $$ Hsrv0
        icases srvApRes_cover s γr (A ++ ms.take (sint.nat j)) $$ HAR with ⟨HAR, %Hmc⟩
        wp_apply (hAEN s γ ci TM E ρ b e m (stLoaded γ st') xj γr ot aw
            (A ++ ms.take (sint.nat j)) [] (restModel γr.kv.c0 γr.raft.raft.boot []) hAuthOff)
            $$ [Hst Hbe Happ Hlr Hgr Hfs HKV Hwt Hao Hka HRS]
          as ⟨Hbe, Hlr, Hgr, Hfs, ⟨%x1, %out1, HKV, %Hstep1, -, Hpre, Hka, HRS⟩, Hpost⟩
        · (try rw [ite_eq_left rfl])
          iframe Hsrv0 Hewo He Hst Hbe Happ Hlr Hgr Hfs HKV Hwt Hao Hlog Hcm Hka HRS %Hmc HlbJ
          isplitr
          · iexact Hreg
          isplitr
          · ipureintro
            exact ⟨hawA, hkbm.1 (by omega)⟩
          isplitr
          · ipureintro; omega
          ipureintro
          refine ⟨⟨hlp ▸ hpend', hOk1 h0, h0⟩, ?_⟩
          rw [hlpp, hlc]
          refine ⟨hip, by omega, hgt, stLoaded_idem γ st'⟩
        have hb1 : batchStep (ciEff γ st.k) m xj x1 := by
          unfold batchStep; rw [ite_eq_left h0]
          refine ⟨out1, ?_⟩
          rw [decide_eq_true (show uint.Z (ciEff γ st.k) < uint.Z m.index by omega)]
          exact Hstep1
        (try rw [ite_eq_left rfl])
        icases Hpost with ⟨Happ, %eff', Hst⟩
        (try wp_auto)
        wp_apply hGI $$ [He] as -
        · iframe He
        icases srvApplyKV_idxCert s E ρ.wait x1 $$ HKV with ⟨HKV, #Hcert⟩
        wp_apply (hSet1 s E γr aw m.index x1.log) $$ [Hpre] as ⟨Hao, -, #Hlog'⟩
        · iframe HainvM Hpre Hcert; rw [hAuthOff]; unfold appliedPubM; itrivial
        (try wp_auto)
        wp_apply hGT $$ [He] as -
        · iframe He
        wp_apply hSet2 $$ [$HatM]
        (try wp_auto)
        wp_apply hGI $$ [He] as -
        · iframe He
        wp_apply hGT $$ [He] as -
        · iframe He
        (try wp_auto)
        ihave Hdv := dvView_normal ρ.raft dv _ m h0 $$ Hdv
        ihave HAR := srvApRes_normal s γr _ m h0 $$ HAR
        ihave #Hcv1 : epCsAt ρ.raft (A ++ ms.take (sint.nat j) ++ [m]) csl $$ []
        · iapply epCsAt_voters
          iapply epCsAt_ne ρ.raft (A ++ ms.take (sint.nat j)) csl
            (fun hA0 => absurd (Hfb hA0).2.1 (by rw [h0]; decide))
          iexact Hcv
        ihave HRS : srvRestR E γr rp (A ++ ms.take (sint.nat j) ++ [m]) $$ [HRS]
        · rw [srvRestR_past E γr rp _ (by have := hpast; simp only [List.length_append, List.length_singleton] at this ⊢; omega)]
          iexact HRS
        wp_for_post
        iframe
        iexists j + W64 1, ⟨m.index, m.index, eff', false⟩, m.index, m.term, csl, sb,
          m.index, m.term, j, x1, m.index, A ++ ms.take (sint.nat j) ++ [m]
        simp only [named]
        rw [htk2]
        iframe
        iframe Hcv1
        isplitr
        · iexact Hlog'
        isplitr
        · iexact HWA2
        ipureintro
        have hidx0 : m.index ≠ W64 0 := by
          intro h
          have h' : uint.Z m.index = 0 := by rw [h]; rfl
          omega
        refine ⟨by rw [hjs]; exact entriesStep_take_succ _ ms _ m x xj x1 Hm_lookup Hxs hb1,
          by omega, ⟨by simp, ?_, ?_⟩, ?_, by have := hiA; simp only [List.length_append, List.length_singleton] at this ⊢; omega,
          (ghostOf_past _ _ (by have := hpast; simp only [List.length_append, List.length_singleton] at this ⊢; omega)).symm,
          by first | exact Hsb | simp⟩
        · rw [hj1]; omega
        · rw [ite_eq_right (by omega), hj1]
          have hce : ciEff γ m.index = m.index := by unfold ciEff; rw [ite_eq_right hidx0]
          rw [hce]; omega
        · intro m' _ hm'
          have : sint.nat (j + W64 1) - 1 = sint.nat j := by
            show (sint.Z (j + W64 1)).toNat - 1 = (sint.Z j).toNat
            rw [hj1]; omega
          rw [this, Hm_lookup] at hm'
          cases hm'
          exact ⟨rfl, rfl⟩
      · -- a conf change
        have hne0 : decide (m.typ = W32 0) = false := by rw [h1]; decide
        simp only [h1]
        ihave ⟨%Hnn, %d, #Hd, #Hds⟩ := entryAt_fields _ _ $$ He
        (try wp_auto)
        wp_apply (hMU.1 cc_ptr _ d m.data DFrac.discard hcc) $$ [cc] as ⟨⟨%cm, Hcc, %Hdec⟩, -⟩
        · iframe cc Hds
        ihave #Hccw : iprop((□ ∀ Ψ, reqWaitR ρ E (ccIdOf m.data) Ψ -∗ False) ∗
            ⌜ccPolOk ρ.raft.raft m.data⌝) $$ []
        · have he : entryWaitOk ρ E m =
              iprop(reqWaitNone ρ (ccIdOf m.data) ∗
                ⌜ccPolOk ρ.raft.raft m.data⌝) := by
            unfold entryWaitOk; rw [ite_eq_right (by rw [h1]; decide)]
          rw [he]
          icases Hewo with ⟨#Hn, %Hp⟩
          iframe %Hp
          iapply reqWaitNone_none $$ Hn
        icases Hccw with ⟨#Hccf, %Hcb⟩
        (try wp_auto)
        have hpre : (stLoaded γ st').pending = false ∧ m.index = (stLoaded γ st').p + 1 ∧
            uint.Z (stLoaded γ st').p < uint.Z m.index ∧
            uint.Z (ciEff γ (stLoaded γ st').k) < uint.Z m.index := by
          rw [hlp, hlpp, hlc]; exact ⟨hpend', hip, by omega, hgt⟩
        ihave #Hhook2 := Hhook
        iunfold hookSpec at Hhook2
        ihave #Hh := Hhook2 $$ %(stLoaded γ st') %m.index %m.term %b
        obtain ⟨HEP, HEf⟩ := HE
        icases srvApplyKV_ua_rt_pool s E ρ.wait xj $$ HKV with ⟨%ua, %dP, %HdP, Hua, #Happlier, Hrt, HplP, #HbeRO, HKVk⟩
        -- (2026-11-02, the backend-auth-split stage) the current backend's reader pool, for
        -- `applyConfChange`, and the apply thread's token (`srvGoRes`'s)
        have hPB : dB = dP := Option.some.inj (hkbB.symm.trans HdP)
        subst dP
        iunfold srvGoRes at Hgr
        icases Hgr with ⟨HgrW, HthT⟩
        -- (D43 M3) the driver's view: the entry is the next conf entry of the batch's log
        have hrest : A ++ ms = A ++ ms.take (sint.nat j) ++ m :: ms.drop (sint.nat j + 1) := by
          have hdj : ms.drop (sint.nat j) = m :: ms.drop (sint.nat j + 1) := by
            rw [List.drop_eq_getElem_cons hjl]
            obtain ⟨_, hm⟩ := List.getElem?_eq_some_iff.1 Hm_lookup
            rw [hm]
          rw [List.append_assoc, ← hdj, List.take_append_drop]
        ihave #Hdvr' : iprop(dvRes s ρ.raft dv ((A ++ ms.take (sint.nat j)) ++
            m :: ms.drop (sint.nat j + 1))) $$ []
        · rw [List.append_assoc, ← hrest]; iexact Hdvr
        ihave %HidxJ := srvRLogLb_idx _ _ $$ HlbJ
        -- (D43 M5e) the apply thread's membership resource around the conf change
        have hidxA : uint.Z m.index = (γr.raft.pre ++ (A ++ ms.take (sint.nat j))).length + 1 := by
          rw [hiA, Hai0]; simp
        have hρr : ρ.raft = γr.raft := by rw [← Hrd]
        icases srvApRes_cc s γr (A ++ ms.take (sint.nat j)) m cm ρ.raft hρr (by rw [h1]; decide) Hdec
          (by rw [← hρr]; exact Hcb cm Hdec) hidxA $$ [HAR HlbJ] with
          ⟨%bh, %ix, %lgh, %tl, %lid, %cl', %lgc, %cid, %prs, #Hbh, #Hbhi, #Htr, #Hmid, #Hcl', #Hclg,
            %Hlgcnn, #Hcid, Hmr, %Hprem, HARk⟩
        · iframe HAR HlbJ
        ihave %Hcleq := typedPointsto_agree_wand _ _ _ _ _ $$ Hcl' Hcl
        subst Hcleq
        obtain ⟨Hpeer, Hloc, Hsz, Hlid⟩ := Hprem
        -- (2026-10-30, the repair) no `RemoveNode` committed before the entry (static membership)
        ihave #HlbL : iprop(srvRLogLb γr.raft (A ++ ms.take (sint.nat j))) $$ []
        · iapply srvRLogLb_mono γr.raft _ _ (List.prefix_append _ _) $$ HlbJ
        iunfold srvRLogLb at HlbL
        icases HlbL with ⟨#HlbL, -⟩
        imod srv_noRemovedIn γr.raft (A ++ ms.take (sint.nat j)) ⊤ CoPset.subseteq_top
          $$ [$Hrli $HlbL] with %Hnr
        icases dvView_ccR s ρ.raft dv γr.kv.c0 lid (A ++ ms.take (sint.nat j)) (ms.drop (sint.nat j + 1))
          m cm h1 Hdec (fun γn h => by
            obtain ⟨-, -, hpre, hai⟩ := hdv.2 γn h
            refine ⟨Hcb cm Hdec, by rw [hρr]; exact Hlid, ?_, by rw [hρr]; exact Hnr⟩
            · apply withIdx_toLE
              rw [hpre, List.nil_append]
              have := srvIdxOkW_prefix _ _ _ HidxJ (List.prefix_append _ _)
              rw [← hρr, hai] at this
              exact this) $$ [Hdv Hrun] with
          ⟨%v, %m', Hdvp, %Hdvf, Hdvc⟩
        · iframe Hdv Hdvr' Hrun
        ihave ⟨%f, %Hfbt, HRS, HLt, #HGI, #HRq, HEv⟩ := srvRest_open E γr (A ++ ms.take (sint.nat j)) $$ HRS
        have hmm := restModel_members γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ (A ++ ms.take (sint.nat j)))
        wp_apply (hACC s cc_ptr ep cm csl ci ua E ρ.raft
          iprop(applyThread γ (stLoaded γ st') ∗ ciApplying ci m.index m.term ∗
            applyBackend γ ci b ∗
            ⌜(stLoaded γ st').pending = false ∧ m.index = (stLoaded γ st').p + 1 ∧
              uint.Z (stLoaded γ st').p < uint.Z m.index ∧
              uint.Z (ciEff γ (stLoaded γ st').k) < uint.Z m.index⌝)
          iprop(hookDone γ TM ∗ applyThread γ { stLoaded γ st' with k := m.index, pending := true } ∗
            ciApplying ci m.index m.term ∗ applyBackend γ ci b)
          iprop(applyThread γ ⟨m.index, m.index, m.index, false⟩ ∗ ciApplying ci m.index m.term ∗
            applyBackend γ ci b)
          iprop(applyThread γ { { stLoaded γ st' with p := m.index } with k := m.index } ∗
            ciApplying ci m.index m.term ∗ applyBackend γ ci b)
          m.index m.term γB sv.cluster
          (apply.restLeasesWith f (srvIds E (appliedTable γr (A ++ ms.take (sint.nat j))).ids)
            (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ (A ++ ms.take (sint.nat j)))))
          dB alB stB lpB dv
          (srvLE ρ.raft ((A ++ ms.take (sint.nat j)) ++ m :: ms.drop (sint.nat j + 1))) v
          (ρ.raft.pre ++ (A ++ ms.take (sint.nat j))).length m' m.toLE
          sv.lg bh ix lgh tl lid prs lgc cid
          (Hcb cm Hdec) HROeq Hpeer Hloc (by rw [apply.restLeasesWith_mem]; exact Hsz)
          (fun _ => ⟨hkbB, hgbB, fun h => hdv.1 h m hmem h1,
            fun γn h => (by
              obtain ⟨-, hrule, -, -⟩ := hdv.2 γn h
              have := Hdvf γn h
              rw [ccRaftEff_restLeasesWith, hrule]
              simp only [hρr] at this ⊢
              exact this),
            (by rw [restLeasesWith_lookup_other _ _ _ _ (by decide)]; exact hmm.1),
            (by rw [restLeasesWith_lookup_other _ _ _ _ (by decide)]; exact hmm.2)⟩))
          $$ [Hcc Hcs Hst Happ Hbe HRS Hua Hdvp Hlr Hmr Hrt HplP HthT Hwt]
          as %removed %err ⟨%Hrem, Hlr, Hua, ⟨%cm', %cs', Hcc, %hIdEq, Hcs, Hcsv⟩, HRS, Hpost, Hdvq, Hmr,
            Hrt, HplP, HthT⟩
        · rw [HEP, HEf]
          iframe Hcif Hua Happlier Hrn Hcc Hcs Hcl HRS Hdvp Hlg Hlr Hbh Hbhi Htr Hmid Hmr Hrt Hclg Hcid
            HplP HthT HbeRO
          isplitr
          · ipureintro; exact Hlgnn
          isplitr
          · ipureintro; exact Hlgcnn
          isplitr
          · ipureintro
            refine membersDecode_restLeasesWith _ _ _ ?_
            exact membersDecode_restModel γr.kv.c0 γr.raft.raft.boot
              (γr.raft.pre ++ (A ++ ms.take (sint.nat j)))
          iframe Hwt
          isplitr
          · first | iexact Hh | (imodintro; iexact Hh) | (imodintro; imodintro; iexact Hh)
          isplitr
          · iintro ⟨Hhd, Hst, Happ, Hbe⟩
            imod (writes_done γ { stLoaded γ st' with k := m.index, pending := true } rfl) $$ Hinv Hst
              with ⟨Hst, Htok⟩
            iunfold hookDone at Hhd
            icases Hhd with ⟨%mm, Hmt, HTM, #Hreg⟩
            imodintro
            iframe Hst Happ Hbe
            iunfold batchLockInv
            iexists mm
            iframe
            iexact Hreg
          isplitr
          · iintro ⟨Hst, Happ, Hbe, %Hp⟩
            iframe Happ
            iintro Happ
            iframe Hst Hbe Happ
            ipureintro; exact Hp
          isplitr
          · iintro ⟨Hst, Happ, Hbe, -⟩
            imod (skip_done γ (stLoaded γ st') m.index hpre.1 hpre.2.1 hpre.2.2.1) $$ Hinv Hst with Hst
            wp_apply_core (wp_ci_advance hSCI γ ci { stLoaded γ st' with p := m.index } m.index m.term
              hpre.1 (Int.le_refl _) hpre.2.2.2) $$ [Hst] [Happ Hbe]
            · iframe Hcipkg Hci Hinv Hst
            iintro Hst
            iframe
            ipureintro; rfl
          iframe Hst Happ Hbe
          ipureintro; exact hpre
        have hpa : ∀ (g : w64 → w64) (T : List w64) (r : apply.RestM),
            ccPeersAfter true cm (apply.restLeasesWith g T r).bk prs = ccPeersAfter true cm r.bk prs :=
          fun g T r => by unfold ccPeersAfter; rw [ccValidOn_restLeasesWith]
        rw [hpa]
        ihave HAR := HARk $$ %true Hmr
        -- (S5) `ep.confState` after the change: raft's answer, or, on a failed validation, as
        -- before, which reports the voters (the first entry validates on a fresh backend)
        ihave #Hcv1 : epCsAt ρ.raft (A ++ ms.take (sint.nat j) ++ [m]) cs' $$ [Hcsv]
        · iapply epCsAt_voters
          icases Hcsv with (#Hv | %Hf)
          · iexact Hv
          · obtain ⟨hf, rfl⟩ := Hf
            have hA : A ++ ms.take (sint.nat j) ≠ [] := by
              intro hA0
              obtain ⟨hpre0, -, cm0, hcm0, hct0⟩ := Hfb hA0
              obtain rfl : cm0 = cm := Option.some.inj (hcm0.symm.trans Hdec)
              have hbk : (restModel γr.kv.c0 γr.raft.raft.boot
                  (γr.raft.pre ++ (A ++ ms.take (sint.nat j)))).bk = restBootBk := by
                rw [hA0, hpre0]; rfl
              rw [ccValidOn_restLeasesWith, hbk, ccValidOn_boot cm0 hct0] at hf
              cases hf
            iapply epCsAt_ne ρ.raft (A ++ ms.take (sint.nat j)) _ hA
            iexact Hcv
        ihave HKV := HKVk $$ Hua Hrt HplP
        ihave Hgr : srvGoRes s $$ [HgrW HthT]
        · iunfold srvGoRes; iframe HgrW HthT
        icases Hdvc $$ Hdvq with ⟨Hdv, Hrun⟩
        (try rw [ite_eq_left rfl])
        ihave Hpost' : iprop(∃ eff : w64, applyThread γ ⟨m.index, m.index, eff, false⟩ ∗
            ciApplying ci m.index m.term ∗ applyBackend γ ci b) $$ [Hpost]
        · icases Hpost with (⟨Hst, Happ, Hbe⟩ | ⟨Hst, Happ, Hbe⟩)
          · iexists m.index; iframe
          · iexists (stLoaded γ st').eff
            have hrec : ({ { stLoaded γ st' with p := m.index } with k := m.index } : ApplyState) =
                ⟨m.index, m.index, (stLoaded γ st').eff, false⟩ := by
              rw [← hpre.1]
            rw [hrec]
            iframe
        icases Hpost' with ⟨%eff', Hst, Happ, Hbe⟩
        -- (D22, 2026-10-23) the rest buckets: the conf change's effect, `v3` the entry's
        ihave HRS : iprop(srvRest E γr (A ++ ms.take (sint.nat j) ++ [m])) $$ [HRS HLt HEv]
        · iapply srvRest_snoc _ _ _ _ (appliedTable_cc _ _ _ (by rw [h1]; decide))
          iframe HEv
          rw [restEntry_cc _ _ cm _ (by rw [h1]; decide) Hdec,
            decide_eq_true (hkbm.1 (by omega))]
          iapply (srvRestAt_open E _ _).2
          iexists f
          rw [← ccRest_restLeasesWith]
          iframe HRS HLt HGI HRq
          ipureintro; exact Hfbt
        ihave HRS : srvRestR E γr rp (A ++ ms.take (sint.nat j) ++ [m]) $$ [HRS]
        · rw [srvRestR_past E γr rp _ (by have := hpast; simp only [List.length_append, List.length_singleton] at this ⊢; omega)]
          iexact HRS
        cc_kv_applied
        subst Hsb Hrem
        (
        cc_respond
        iexists j + W64 1, ⟨m.index, m.index, eff', false⟩, m.index, m.term, cs', _,
          m.index, m.term, j, xj, m.index, A ++ ms.take (sint.nat j) ++ [m]
        simp only [named]
        rw [htk2]
        iframe
        iframe Hcv1
        isplitr
        · iexact Hlog'
        isplitr
        · iexact HWA2
        ipureintro
        have hidx0 : m.index ≠ W64 0 := by
          intro h
          have h' : uint.Z m.index = 0 := by rw [h]; rfl
          omega
        have hb1 := hconf (by rw [h1]; decide)
        refine ⟨by rw [hjs]; exact entriesStep_take_succ _ ms _ m x xj xj Hm_lookup Hxs hb1,
          by omega, ⟨by simp, ?_, ?_⟩, ?_, by have := hiA; simp only [List.length_append, List.length_singleton] at this ⊢; omega,
          (ghostOf_past _ _ (by have := hpast; simp only [List.length_append, List.length_singleton] at this ⊢; omega)).symm,
          by first | exact Hsb | simp⟩
        · rw [hj1]; omega
        · rw [ite_eq_right (by omega), hj1]
          have hce : ciEff γ m.index = m.index := by unfold ciEff; rw [ite_eq_right hidx0]
          rw [hce]; omega
        · intro m' _ hm'
          have : sint.nat (j + W64 1) - 1 = sint.nat j := by
            show (sint.Z (j + W64 1)).toNat - 1 = (sint.Z j).toNat
            rw [hj1]; omega
          rw [this, Hm_lookup] at hm'
          cases hm'
          exact ⟨rfl, rfl⟩)
    · -- at or below `ci`: `ApplyV2storeOnly`
      have hle : uint.Z m.index ≤ uint.Z (ciEff γ st'.k) := by
        first | omega | exact Int.not_lt.mp Hif | word
      obtain ⟨hpend', hp', hc'⟩ := Hstj
      have hjnat : (sint.nat j : Int) = sint.Z j := by
        unfold sint.nat; exact Int.toNat_of_nonneg Hj.1
      have hidxZ : uint.Z m.index = uint.Z f0 + sint.Z j := by rw [hmidx, hjnat]
      have hj1 : sint.Z (j + W64 1) = sint.Z j + 1 := by word
      have hc0 : uint.Z f0 + sint.Z j ≤ uint.Z (ciEff γ st.k) ∧
          uint.Z (ciEff γ st'.k) = uint.Z (ciEff γ st.k) := by
        by_cases hj0 : sint.Z j = 0
        · rw [ite_eq_left hj0] at hc'; omega
        · rw [ite_eq_right hj0] at hc'; omega
      have hpend'' : (stLoaded γ st').pending = false := by rw [hlp]; exact hpend'
      have hidx0 : m.index ≠ W64 0 := by
        intro h
        have h' : uint.Z m.index = 0 := by rw [h]; rfl
        omega
      have hlast' : ∀ (m' : EntryModel), 0 < sint.nat (j + W64 1) →
          ms[sint.nat (j + W64 1) - 1]? = some m' → m'.index = m.index ∧ m'.term = m.term := by
        intro m' _ hm'
        have : sint.nat (j + W64 1) - 1 = sint.nat j := by
          show (sint.Z (j + W64 1)).toNat - 1 = (sint.Z j).toNat
          rw [hj1]; omega
        rw [this, Hm_lookup] at hm'
        cases hm'
        exact ⟨rfl, rfl⟩
      have hstj' : uint.Z (stLoaded γ st').p = max (uint.Z (ciEff γ st.k)) (uint.Z f0 - 1 + sint.Z (j + W64 1)) ∧
          uint.Z (ciEff γ (stLoaded γ st').k) = (if sint.Z (j + W64 1) = 0 then uint.Z (ciEff γ st.k)
            else max (uint.Z (ciEff γ st.k)) (uint.Z f0 - 1 + sint.Z (j + W64 1))) := by
        rw [hlpp, hlc, ite_eq_right (by omega), hj1]; omega
      (try wp_auto)
      wp_apply hGTy $$ [He] as -
      · iframe He
      (try wp_auto)
      by_cases hW : (A ++ ms.take (sint.nat j)).length < rp.A₀.length
      · -- (R2d') a replay: Go's log inside the window, the entry the backend's next
        ihave %HpA := srvRLogLb_prefix γr.raft (A ++ ms.take (sint.nat j) ++ [m]) rp.A₀ $$ [HlbJ HlbA0]
        · iframe HlbJ HlbA0
        have hpA : A ++ ms.take (sint.nat j) ++ [m] <+: rp.A₀ := by
          rcases HpA with h | h
          · exact h
          · rw [h.eq_of_length (by
              have := h.length_le
              have hW' := hW
              simp only [List.length_append, List.length_singleton] at this hW' ⊢; omega)]
            exact List.prefix_refl _
        have hpA0 : A ++ ms.take (sint.nat j) <+: rp.A₀ := (List.prefix_append _ _).trans hpA
        have hΓe : Γ = rp.A₀ := by rw [HΓ]; exact ghostOf_in _ _ hpA0
        subst hΓe
        have hmA : uint.Z m.index ≤ uint.Z aw := by omega
        have hbG : rp.b ≤ (A ++ ms.take (sint.nat j)).length := by
          have := HkB.2.1; rw [hlenA]; omega
        ihave HRS : srvRestRp E γr rp.A₀ (restReplay γr rp (A ++ ms.take (sint.nat j))) $$ [HRS]
        · rw [← srvRestR_in E γr rp _ hW]; iexact HRS
        imod restReplay_closeI γr rp ⊤ CoPset.subseteq_top HkB.2.2.2.1 HkB.2.2.2.2.1 $$ [$Hrli $HlbA0]
          with %Hclose
        -- the rest buckets after the replay: inside the window, or closed (`restReplay_close`)
        have hRS : srvRestRp (GF := GF) E γr rp.A₀
            (restEntryV2 m (restReplay γr rp (A ++ ms.take (sint.nat j)))) =
            srvRestR E γr rp (A ++ ms.take (sint.nat j) ++ [m]) := by
          by_cases hlt : (A ++ ms.take (sint.nat j) ++ [m]).length < rp.A₀.length
          · rw [srvRestR_in _ _ _ _ hlt, restReplay_snoc _ _ _ _ hbG]
          · have heq : A ++ ms.take (sint.nat j) ++ [m] = rp.A₀ :=
              hpA.eq_of_length (by have := hpA.length_le; omega)
            have hR : restEntryV2 m (restReplay γr rp (A ++ ms.take (sint.nat j))) =
                restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ rp.A₀) := by
              rw [← restReplay_snoc _ _ _ _ hbG, heq, Hclose]
            rw [srvRestR_past _ _ _ _ (Nat.le_of_eq (by rw [heq])), heq, ← srvRestRp_model, hR]
        have hΓ' : rp.A₀ = ghostOf rp (A ++ ms.take (sint.nat j) ++ [m]) := (ghostOf_in _ _ hpA).symm
        rcases hmtyp with h0 | ⟨h1, hcc⟩
        · -- a normal entry, replayed (`applyEntryNormal(e, false)`)
          (try simp only [h0, _root_.decide_true])
          (try wp_auto)
          icases srvApRes_cover s γr rp.A₀ $$ HAR with ⟨HAR, %Hmc⟩
          wp_apply (hAENR s γ ci TM E ρ b e m (stLoaded γ st') xj γr rp.A₀
              (restReplay γr rp (A ++ ms.take (sint.nat j))) hAuthOff)
              $$ [Hst Hbe Hlr Hgr Hfs HKV Hwt HRS]
            as ⟨Hbe, Hlr, Hgr, Hfs, ⟨%x1, %out1, HKV, %Hstep1⟩, HRS, Hst⟩
          · iframe Hsrv0 Hewo He Hst Hbe Hlr Hgr Hfs HKV Hwt Hcm HRS HlbA0
            isplitr
            · ipureintro; exact hpA.subset (List.mem_append_right _ (List.mem_singleton_self m))
            ipureintro
            refine ⟨hpend'', hOk1 h0, h0, by rw [hlc]; omega, fun k hk => ?_⟩
            rw [restReplay_memKeys]; exact Hmc k hk
          have hx1 : x1 = xj := entryStep_false_eq m xj x1 out1 Hstep1
          have hS : entryStep m false xj xj out1 := hx1 ▸ Hstep1
          ihave HKV : srvApplyKV s E ρ.wait xj $$ [HKV]
          · rw [← hx1]; iexact HKV
          have hb1 : batchStep (ciEff γ st.k) m xj xj := by
            unfold batchStep; rw [ite_eq_left h0]
            refine ⟨out1, ?_⟩
            rw [decide_eq_false (show ¬ uint.Z (ciEff γ st.k) < uint.Z m.index by omega)]
            exact hS
          (try simp only [Bool.false_eq_true, ↓reduceIte])
          (try wp_auto)
          wp_apply hGI $$ [He] as -
          · iframe He
          wp_apply (hSet1R s E γr aw m.index xj.log) $$ [Hao] as Hao
          · iframe HainvM Hao; ipureintro; exact hmA
          (try wp_auto)
          wp_apply hGT $$ [He] as -
          · iframe He
          wp_apply hSet2 $$ [$HatM]
          (try wp_auto)
          wp_apply hGI $$ [He] as -
          · iframe He
          wp_apply hGT $$ [He] as -
          · iframe He
          (try wp_auto)
          ihave HRS : srvRestR E γr rp (A ++ ms.take (sint.nat j) ++ [m]) $$ [HRS]
          · rw [← hRS]; iexact HRS
          wp_for_post
          iframe
          iexists j + W64 1, stLoaded γ st', a', t', csl, sb, m.index, m.term, j, xj, aw, rp.A₀
          simp only [named]
          rw [htk2]
          iframe
          iframe Hcv Hlog HWA2
          ipureintro
          exact ⟨by rw [hjs]; exact entriesStep_take_succ _ ms _ m x xj xj Hm_lookup Hxs hb1,
            by omega, ⟨hpend'', hstj'.1, hstj'.2⟩, hlast', Haw, hΓ', by first | exact Hsb | simp⟩
        · -- a conf change, replayed (`applyConfChange(cc, ep, false)`): no raft call, the ghost
          -- rows kept
          (try simp only [h1])
          ihave ⟨%Hnn, %d, #Hd, #Hds⟩ := entryAt_fields _ _ $$ He
          (try wp_auto)
          wp_apply (hMU.1 cc_ptr _ d m.data DFrac.discard hcc) $$ [cc] as ⟨⟨%cm, Hcc, %Hdec⟩, -⟩
          · iframe cc Hds
          ihave #Hccw : iprop((□ ∀ Ψ, reqWaitR ρ E (ccIdOf m.data) Ψ -∗ False) ∗
              ⌜ccPolOk ρ.raft.raft m.data⌝) $$ []
          · have he : entryWaitOk ρ E m =
                iprop(reqWaitNone ρ (ccIdOf m.data) ∗
                  ⌜ccPolOk ρ.raft.raft m.data⌝) := by
              unfold entryWaitOk; rw [ite_eq_right (by rw [h1]; decide)]
            rw [he]
            icases Hewo with ⟨#Hn, %Hp⟩
            iframe %Hp
            iapply reqWaitNone_none $$ Hn
          icases Hccw with ⟨#Hccf, %Hcb⟩
          (try wp_auto)
          have hρr : ρ.raft = γr.raft := by rw [← Hrd]
          have hokc : ccApplyOkM γr.raft cm := by rw [← hρr]; exact Hcb cm Hdec
          icases srvApRes_ccRep s γr rp.A₀ cm hokc $$ HAR with
            ⟨%bh, %ix, %lgh, %tl, %lid, %cl', %lgc, %cid, %prs, #Hbh, #Hbhi, #Htr, #Hmid, #Hcl', #Hclg,
              %Hlgcnn, #Hcid, Hmr, %Hpeer, HARk⟩
          obtain ⟨Hpeer, Hszk⟩ := Hpeer
          ihave %Hcleq := typedPointsto_agree_wand _ _ _ _ _ $$ Hcl' Hcl
          subst Hcleq
          -- (A4's DRAFT fix) the rest resource, at the replayed image's members
          icases srvRestRp_ro E γr rp.A₀ (restReplay γr rp (A ++ ms.take (sint.nat j))) $$ HRS with
            ⟨%rsR, HRO, %HrsR, HRSk⟩
          wp_apply (hACCR s cc_ptr ep cm csl E γr.raft γB sv.cluster rsR dB alB stB lpB
              sv.lg bh ix lgh tl lid prs lgc cid m.toLE hokc HROeq Hpeer
              (Hszk rsR.mem (fun k => by rw [HrsR]; exact restReplay_memKeys γr rp _ k)))
              $$ [Hcc Hcs Hlr Hmr HRO]
            as %removed %err ⟨%Hrem, Hlr, ⟨%cm', Hcc, %hIdEq⟩, Hcs, Hmr, HRO⟩
          · iframe Hlg Hlr Hcl Hclg Hcid Hcc Hcs Hbh Hbhi Htr Hmid Hmr HRO
            isplitr
            · ipureintro; exact Hlgnn
            ipureintro; exact Hlgcnn
          ihave HRS := HRSk $$ HRO
          ihave HAR := HARk $$ Hmr
          (try wp_auto)
          wp_apply hGI $$ [He] as -
          · iframe He
          wp_apply (hSet1R s E γr aw m.index xj.log) $$ [Hao] as Hao
          · iframe HainvM Hao; ipureintro; exact hmA
          (try wp_auto)
          wp_apply hGT $$ [He] as -
          · iframe He
          wp_apply hSet2 $$ [$HatM]
          (try wp_auto)
          ihave HRS : srvRestR E γr rp (A ++ ms.take (sint.nat j) ++ [m]) $$ [HRS]
          · rw [← hRS, restEntryV2_conf m _ (by rw [h1]; decide)]; iexact HRS
          subst Hsb Hrem
          (
          cc_respond
          iexists j + W64 1, stLoaded γ st', a', t', csl, _, m.index, m.term, j, xj, aw, rp.A₀
          simp only [named]
          rw [htk2]
          iframe
          iframe Hcv Hlog HWA2
          ipureintro
          have hb1 := hconf (by rw [h1]; decide)
          exact ⟨by rw [hjs]; exact entriesStep_take_succ _ ms _ m x xj xj Hm_lookup Hxs hb1,
            by omega, ⟨hpend'', hstj'.1, hstj'.2⟩, hlast', Haw, hΓ', by first | exact Hsb | simp⟩)
      have hpast : rp.A₀.length ≤ (A ++ ms.take (sint.nat j)).length := Nat.le_of_not_lt hW
      -- (R2d') past the window (`hW` false): the ghost log is Go's
      have hΓe : Γ = A ++ ms.take (sint.nat j) := by rw [HΓ]; exact ghostOf_past _ _ hpast
      subst hΓe
      ihave HRS : srvRest E γr (A ++ ms.take (sint.nat j)) $$ [HRS]
      · rw [← srvRestR_past E γr rp _ hpast]; iexact HRS
      have hawA : uint.Z aw = uint.Z γr.raft.ai0 + (A ++ ms.take (sint.nat j)).length := Haw
      have hkbm : (uint.Z (ciEff γ st.k) < uint.Z m.index ↔ uint.Z γr.kv.c0 < uint.Z m.index) :=
        HkB.2.2.2.2.2 m hmem (by omega)
      -- (R2d'a, Q23 (a)) dead: past the window the entry is above `ai0 ≥ c0` (`kvBatchR`), so
      -- above the consistent index
      exfalso
      have hlt := hkbm.2 (by have := HkB.2.2.2.1; omega)
      omega
  · -- the loop is done
    have hjn : sint.nat j = ms.length := by rw [Hlen]; word
    have hjZ : sint.Z j = (ms.length : Int) := by
      rw [← hjn]; unfold sint.nat; rw [Int.toNat_of_nonneg Hj.1]
    have hnpos : 0 < ms.length := List.length_pos_iff.mpr hne
    obtain ⟨mlast, hml⟩ : ∃ m, ms[ms.length - 1]? = some m :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have hgl : ms.getLast? = some mlast := by
      rw [List.getLast?_eq_getElem?]; exact hml
    obtain ⟨hmi, hmt⟩ := Hlast mlast (by omega) (by rw [hjn]; exact hml)
    have hidx := (Hms (ms.length - 1) mlast hml).1
    ihave #Hlogf := Hlog
    have htkF : ms.take (sint.nat j) = ms := by rw [hjn, List.take_of_length_le (Nat.le_refl _)]
    have hΓF : Γ = ghostOf rp (A ++ ms) := by rw [HΓ, htkF]
    subst hΓF
    ihave HRS : srvRestR E γr rp (A ++ ms) $$ [HRS]
    · rw [show A ++ ms = A ++ ms.take (sint.nat j) by rw [htkF]]; iexact HRS
    iapply Hphi
    iframe Hfs
    isplitl [Hdv]
    · iexact Hdv
    isplitl [Hrun]
    · iexact Hrun
    isplitl [HAR]
    · iexact HAR
    iexists st', a', t', csl, aw
    rw [hjn, List.take_of_length_le (Nat.le_refl _)] at Hxs
    iframe Hst Hbe Happ Hcs Hcv Hlr Hgr Hao
    isplitr
    · rw [← hjn]; iexact HWA
    isplitl [HKV Hka HRS]
    · iexists xj; iframe HKV Hlogf Hka HRS
      ipureintro; exact Hxs
    ipureintro
    have hne0 : sint.Z j ≠ 0 := by omega
    rw [ite_eq_right hne0] at Hstj
    obtain ⟨hpend', hp', hc'⟩ := Hstj
    refine ⟨Haw, by rw [hgl]; simp [hmi], by rw [hgl]; simp [hmt], ⟨hpend', ?_⟩, ?_, Hsb⟩
    · rw [hp', hc', ← hmi, hidx, hjZ]; omega
    · rw [hc', ← hmi, hidx, hjZ]; omega


end proof

end EtcdGrove
end Perennial
