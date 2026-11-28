/-
(hraft_robust R4a: over the crash views.) Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/Raft__processLogs.lean (241f27e).
-/
/-
The proof of `raft.(*Raft).processLogs`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.Raft__processLogs
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__prepareLog
public import Dsverify.Spec.github_com.hashicorp.raft.raftState__getLastApplied
public import Dsverify.Spec.github_com.hashicorp.raft.raftState__setLastApplied
public import Dsverify.Proof.github_com.hashicorp.raft.InstallBase
public import Dsverify.Proof.github_com.hashicorp.raft.DurHelpers
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__config
public import Dsverify.Spec.github_com.hashicorp.raft.deferError__respond
public import Dsverify.Proof.github_com.hashicorp.raft.DeferRespond
public import Dsverify.Proof.github_com.hashicorp.raft.FsmBase

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]
variable [hRB : ReceiptBoundLe GF (2 ^ 62)]

open github_com.hashicorp.raft proto gprot


open github_com.hashicorp.raft.fsmProof in
theorem github_com.hashicorp.raft.Raft.processLogs.wp_proof
    (wp_getLastApplied : github_com.hashicorp.raft.raftState.getLastApplied.spec (GF := GF) (hG := hG))
    (wp_setLastApplied : github_com.hashicorp.raft.raftState.setLastApplied.spec (GF := GF) (hG := hG))
    (wp_config : github_com.hashicorp.raft.Raft.config.spec (GF := GF) (hG := hG))
    (wp_prepareLog : github_com.hashicorp.raft.Raft.prepareLog.spec (GF := GF) (hG := hG))
    (wp_respond : github_com.hashicorp.raft.deferError.respond.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.Raft.processLogs.spec (GF := GF) (hG := hG) :=
  fun r γ rc i idx fm M s a cm tid => by
  wp_start as ⟨#Hr, Hsrv, %Hidx, Hprod, Hap, Hcomp, %Hca, Htok, Hfm, HM⟩
  ihave #Hcells := isRaft_cells r γ rc i $$ Hr
  unfold raftCells
  icases Hcells with ⟨#HtermC, #HcidxC, #Hdurv, #HstateC, #HappC, -, -, -⟩
  wp_auto
  wp_apply wp_getLastApplied $$ [$HappC $Hap] as %la ⟨%Hla, Hap⟩
  wp_if_destruct
  · -- nothing to apply
    have hmax : Max.max a (uint.nat idx) = a := by
      apply Nat.max_eq_left; subst Hla; word
    rw [hmax]
    iapply HΦ
    iframe
    icases Hfm with (⟨%Hn, -⟩ | Hfm)
    · ileft; ipureintro; exact Hn
    · iright; iexact Hfm
  ipersist r
  wp_apply wp_config $$ [$Hr] as %c %Hc
  ihave #Hchans := isRaft_fsmCh r γ rc i $$ Hr
  icases Hchans with ⟨%fch, #Hfch, #Hspsc⟩
  ihave #Hsd := isRaft_shutdownCh r γ rc i $$ Hr
  unfold deadField deadChan
  icases Hsd with ⟨%sch, #Hsch, %γs, #Hsbag⟩
  ihave ⟨%abf, applyBatch, #HAB⟩ : (∃ fv : GoFunc, applyBatch_ptr ↦ fv ∗
      □ (∀ (sl : GoSlice) (e k1 : Nat) (Ψ : val → IProp GF),
          prodS rc e -∗ fsmBatchP γ rc i e k1 (batchV sl) -∗ ▷ (prodS rc k1 -∗ Ψ #()) -∗
          WP (App (Val #fv) (Val #sl)) {{ Ψ }}) : IProp GF) $$ [applyBatch]
  · iexists _
    isplitl [applyBatch]
    · iexact applyBatch
    imodintro
    iintro %sl %e %k1 %Ψ Hps Hb HΨ
    wp_auto_lc 3
    imod prodS_send γ rc i e k1 sl $$ [$Hps $Hb] with ⟨%sent, Hp, HP, Hk⟩
    wp_apply_core chan.wp_select_blocking
    iapply BigAndL.bigAndL_cons.2
    isplit
    · dsimp only [chan.blockingClausePre]
      iexists GoInterface, inferInstance, inferInstance, inferInstance, inferInstance, fch,
        rc.names.fsmCh.chanName, batchV sl
      isplitr
      · ipureintro
        exact ⟨rfl, rfl⟩
      ihave #Hch : isChan fch rc.names.fsmCh.chanName GoInterface $$ [Hspsc]
      · unfold isSpsc; icases Hspsc with ⟨$, -⟩
      iframe Hch
      iapply spsc_send_au $$ Hspsc [$Hlc1 $Hlc2 $Hlc3] [$Hp $HP]
      inext
      iintro Hp
      wp_auto
      iapply HΨ
      iapply Hk $$ Hp
    iapply BigAndL.bigAndL_cons.2
    isplit
    · dsimp only [chan.blockingClausePre]
      iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, sch, γs
      isplitr
      · ipureintro; rfl
      ihave #Hsc := is_bag_is_chan _ _ _ $$ Hsbag
      iframe Hsc
      iapply bag_recv_au $$ [$Hlc1 $Hlc2] Hsbag
      inext
      iintro %v HF
      iexfalso; iexact HF
    · iapply BigAndL.bigAndL_nil.2
      itrivial
  ihave #Himm := isRaft_imm r γ rc i $$ Hr
  unfold raftImm
  icases Himm with ⟨#Hpv, -⟩
  ihave #Hproto := isRaft_proto r γ rc i $$ Hr
  icases Hproto with ⟨#Hinv, #Hvoter⟩
  iapply wp_ncfupd _ _ rfl
  iintro Hnc
  ihave H1 := srvOwn_facts_R γ rc i gd_top s $$ [$Hinv $Hdurv $Hsrv]
  imod H1 $$ Hnc with ⟨Hnc, Hsrv, -, %Hfacts⟩
  ihave H2 := srvOwn_durLb_R γ rc i gd_top s $$ [$Hinv $Hdurv $Hsrv]
  imod H2 $$ Hnc with ⟨Hnc, Hsrv, #Hdur⟩
  iframe Hnc
  imodintro
  icases fsmProd_open γ rc a $$ Hprod with ⟨%e0, Hps, %He0, Htail⟩
  obtain ⟨-, Hdl, -, -, -, -, Hlen, -, Hkinds⟩ := Hfacts
  have Hmae := Hc
  obtain ⟨-, -, -, -, -, -, -, -, -, Hmae1, Hmae2, -⟩ := Hmae
  wp_apply (wp_slice_make3 (V := Loc) (W64 0) c.MaxAppendEntries' (by word)) as %sl0 ⟨Hsl0, Hcap0, %Hsl0c⟩
  have Hla1 : uint.nat (la + W64 1) = a + 1 := by
    have : uint.nat la < uint.nat idx := by word
    subst Hla; word
  ihave HI : (∃ (x : w64) (e lk : Nat) (its : List BatchItem) (sl : GoSlice) (Mr : GMap w64 Loc),
      "idx" ∷ idx_ptr ↦ x ∗ "batch" ∷ batch_ptr ↦ sl ∗ "Hcomp" ∷ monoNatAuthOwn rc.dur.comp (1 : Qp).half cm ∗
      "Hsl" ∷ sl ↦* its.map BatchItem.tp ∗ "Hcap" ∷ ownSliceCap Loc sl (DFrac.own 1) ∗
      "Hps" ∷ prodS rc e ∗ "Hits" ∷ ([∗list] it ∈ its, itemRes γ rc i it) ∗
      "Hcov" ∷ cover γ e lk (its.map BatchItem.k) ∗ "Htail" ∷ noCmdBetween γ lk (uint.nat x) ∗
      "HM" ∷ ([∗map] k ↦ f ∈ Mr,
        ∃ e : Entry, futResp γ rc i f (uint.nat k) e ∗ ⌜ent s.log (uint.nat k) = some e⌝) ∗
      "%Hx" ∷ ⌜a < uint.nat x ∧ uint.nat x ≤ uint.nat idx + 1 ∧ e ≤ lk ∧ lk < uint.nat x ∧
        its.length < uint.nat c.MaxAppendEntries' ∧ batchOk e lk its ∧
        (∀ k f, M !! k = some f → uint.nat x ≤ uint.nat k → Mr !! k = some f)⌝ : IProp GF)
      $$ [idx batch Hsl0 Hcap0 Hps Htail HM Hcomp]
  · iexists la + W64 1, e0, e0, [], sl0, M
    rw [Hla1]
    iframe
    isplitl []
    · iapply BigSepL.bigSepL_nil.2; itrivial
    isplitl []
    · unfold cover; simp only [Nat.sub_self, List.range'_zero, List.map_nil]
      iapply BigSepL.bigSepL_nil.2; itrivial
    · ipureintro
      refine ⟨by omega, ?_, Nat.le_refl _, by omega, by simp; omega, ?_, fun k f h _ => h⟩
      · have : uint.nat la < uint.nat idx := by word
        omega
      · refine ⟨List.Pairwise.nil, by simp, Or.inr ⟨rfl, rfl⟩⟩
  wp_for HI
  obtain ⟨Hx1, Hx2, Hel, Hlkx, Hilen, Hbok, HMr⟩ := Hx
  wp_if_destruct
  · -- an iteration: index `x`
    have Hxi : uint.nat x ≤ uint.nat idx := by word
    obtain ⟨ev, Hev⟩ := ent_isSome s.log (uint.nat x) (by omega) (by omega)
    iapply wp_ncfupd _ _ rfl
    iintro Hnc
    ihave H3 := applied_C_R γ rc i gd_top s (uint.nat x) ev ⟨by omega, by omega⟩ Hev $$ [$Hinv $Hdurv $Hsrv]
    imod H3 $$ Hnc with ⟨Hnc, Hsrv, #HC⟩
    iframe Hnc
    imodintro
    ihave #Hdx := durLb_mono γ i s.dur.1 (uint.nat x) (by omega) $$ Hdur
    have Hkx := Hkinds _ _ Hev
    wp_apply wp_lookup_futs fm M x $$ [$Hfm] as Hfm
    wp_join iprop(∃ (tp : Loc) (Mr' : GMap w64 Loc),
        "preparedLog" ∷ preparedLog_ptr ↦ tp ∗ "future" ∷ future_ptr ↦ (M !! x).getD null ∗
        "Hsrv" ∷ srvV rc s ∗ "Htok" ∷ rtok tid ∗ "idx" ∷ idx_ptr ↦ x ∗
        "Hcomp" ∷ monoNatAuthOwn rc.dur.comp (1 : Qp).half cm ∗
        "HM" ∷ ([∗map] k ↦ f ∈ Mr',
          ∃ e : Entry, futResp γ rc i f (uint.nat k) e ∗ ⌜ent s.log (uint.nat k) = some e⌝) ∗
        "%HMr'" ∷ ⌜∀ k f, M !! k = some f → uint.nat x + 1 ≤ uint.nat k → Mr' !! k = some f⌝ ∗
        "Hcase" ∷ ((⌜ev.kind = kNoop ∧ tp = null⌝ ∗
              (⌜(M !! x).isSome = false⌝ ∨
                deferResp (((M !! x).getD null).[logFuture, go!"deferError"]) (fun _ => iprop(True)))) ∨
           (∃ lp fp : Loc, ⌜ev.kind = kCommand ∨ ev.kind = kConfig ∨ ev.kind = kBarrier⌝ ∗ tp ↦ commitTuple.mk lp fp ∗
              logPtr lp (uint.nat x) ev ∗
              (⌜fp = null⌝ ∨ (⌜lp = (fp.[logFuture, go!"log"])⌝ ∗ futResp γ rc i fp (uint.nat x) ev)))))
      with [preparedLog future Hsrv Htok idx HM Hcomp]
      as ⟨%tp, %Mr', preparedLog, future, Hsrv, Htok, idx, Hcomp, HM, %HMr', Hcase⟩
    · -- the entry comes from the leader's future
      obtain ⟨f, hf⟩ := Option.isSome_iff_exists.mp Hif
      have hfr : Mr !! x = some f := HMr x f hf (Nat.le_refl _)
      ihave ⟨Hfx, HM⟩ := (BigSepM.bigSepM_delete hfr).1 $$ HM
      icases Hfx with ⟨%e', Hfr, %He'⟩
      rw [Hev] at He'
      cases He'
      simp only [hf, Option.getD_some]
      iunfold futResp at Hfr
      icases Hfr with ⟨#Hlp, Hresp, Hdr⟩
      wp_apply wp_prepareLog r (f.[logFuture, go!"log"]) f (uint.nat x) ev $$ [$Hpv $Hlp]
        as %tp Htp
      · ipureintro; rcases Hkx with h | h | h | h <;> simp only [h, _root_.true_or, _root_.or_true]
      have HMr' : ∀ k f', M !! k = some f' → uint.nat x + 1 ≤ uint.nat k →
          (PartialMap.delete Mr x) !! k = some f' := by
        intro k f' h hk
        have hne : x ≠ k := by intro h'; subst h'; omega
        rw [show (PartialMap.delete Mr x) = GMap.delete x Mr from rfl, GMap.lookup_delete_ne _ hne]
        exact HMr k f' h (by omega)
      icases Htp with (⟨%Hk, %Htp⟩ | ⟨%Hk, Htp⟩)
      · -- a no-op: answered below
        subst Htp
        isplitr
        · ipureintro; rfl
        iexists null, _
        iframe
        isplitr
        · ipureintro; exact HMr'
        ileft
        isplitr
        · ipureintro; exact ⟨Hk, rfl⟩
        iright
        icases Hdr with (⟨-, Hd⟩ | ⟨%d, %n, %Hc, -⟩ | ⟨%sc, %Hc, -⟩ | ⟨%Hc, -⟩)
        · iexact Hd
        · exfalso; rw [Hc.1] at Hk; exact absurd Hk (by decide)
        · exfalso; rw [Hc] at Hk; exact absurd Hk (by decide)
        · exfalso; rw [Hc] at Hk; exact absurd Hk (by decide)
      · isplitr
        · ipureintro; rfl
        iexists tp, _
        iframe
        isplitr
        · ipureintro; exact HMr'
        iright
        iexists (f.[logFuture, go!"log"]), f
        iframe # 
        isplitr
        · ipureintro; exact Hk
        iframe Htp
        iright
        isplitr
        · ipureintro; rfl
        iunfold futResp
        iframe #
        iframe
    · -- the entry comes from the log store
      have hMx : M !! x = none := by
        cases h : M !! x
        · rfl
        · rw [h] at Hif; simp at Hif
      simp only [hMx, Option.getD_none, Option.isSome_none]
      ihave #Hls := isRaft_logStore r γ rc i $$ Hr
      icases Hls with ⟨%lsx, #Hlsp, #Hls, -⟩
      iunfold isLogStore at Hls
      icases Hls with ⟨-, -, #HGet, -⟩
      wp_auto
      wp_bind
      iapply HGet $$ «$r0» Htok
      iapply (logRead_main_k γ rc i s (1 : Qp).half cm (uint.nat x) (by omega) _) $$ Hdurv Hsrv Hcomp
      iintro %LA %Hm Hsrv Hcomp %err Hpost Htok
      have hxl := (proto.ent_le_length Hev).2
      have hLA : LA.m.lookup (uint.nat x) = some ev := by rw [Hm.2 hxl]; exact Hev
      unfold getLogPost
      rw [hLA]
      icases Hpost with ⟨%Herr, %lv, Hlv, #Hlogis⟩
      subst Herr
      wp_auto
      ipersist Hlv
      wp_apply wp_prepareLog r «$r0_ptr» null (uint.nat x) ev $$ [$Hpv] as %tp Htp
      · isplitl []
        · iunfold logPtr; iexists lv; iframe #
        · ipureintro; rcases Hkx with h | h | h | h <;> simp only [h, _root_.true_or, _root_.or_true]
      icases Htp with (⟨%Hk, %Htp⟩ | ⟨%Hk, Htp⟩)
      · subst Htp
        isplitr
        · ipureintro; rfl
        iexists null, Mr
        iframe
        isplitr
        · ipureintro; intro k f h hk; exact HMr k f h (by omega)
        ileft
        isplitr
        · ipureintro; exact ⟨Hk, rfl⟩
        ileft; ipureintro; simp
      · isplitr
        · ipureintro; rfl
        iexists tp, Mr
        iframe
        isplitr
        · ipureintro; intro k f h hk; exact HMr k f h (by omega)
        iright
        iexists «$r0_ptr», null
        iframe Htp
        isplitr
        · ipureintro; exact Hk
        isplitl []
        · iunfold logPtr; iexists lv; iframe #
        ileft; ipureintro; rfl
    have Hx1' : uint.nat (x + W64 1) = uint.nat x + 1 := by word
    icases Hcase with (⟨⟨%Hk, %Htp⟩, Hdr⟩ | ⟨%lp, %fp, %Hk, Htp, #Hlp, Hfp⟩)
    · -- a no-op entry: no tuple; answer its future if any
      subst Htp
      ihave Htail : noCmdBetween γ lk (uint.nat x + 1) $$ [Htail]
      · iapply noCmdBetween_snoc γ lk (uint.nat x) Hlkx
        iframe Htail
        iexists ev
        iframe HC
        ipureintro; rw [Hk]; decide
      wp_auto
      cases hS : (M !! x).isSome
      · wp_auto
        wp_for_post
        iframe
        iexists x + W64 1, e, lk, its, sl, Mr'
        rw [Hx1']
        iframe
        ipureintro
        refine ⟨by omega, by omega, Hel, by omega, Hilen, Hbok, HMr'⟩
      · icases Hdr with (%Hf | Hdr)
        · exfalso; revert Hf; simp
        wp_auto
        wp_apply (deferError.respond_logFuture wp_respond) ((M !! x).getD null) (fun _ => iprop(True)) interface.nil $$ [Hdr] as -
        · ileft; iframe
        wp_for_post
        iframe
        iexists x + W64 1, e, lk, its, sl, Mr'
        rw [Hx1']
        iframe
        ipureintro
        refine ⟨by omega, by omega, Hel, by omega, Hilen, Hbok, HMr'⟩
    · -- a tuple: append it to the batch
      ipersist Htp
      ihave %Htpn := typedPointsto_not_null tp _ _ $$ Htp
      simp only [decide_eq_false Htpn]
      wp_auto
      wp_apply (wp_slice_literal (V := Loc) [tp])
      isplitr
      · ipureintro; rfl
      iintro %sl2 ⟨Hsl2, -⟩
      wp_apply (wp_slice_append (V := Loc)) $$ [Hsl Hcap Hsl2] as %sl1 ⟨Hsl, Hcap, -⟩
      · iframe
      have hmap : its.map BatchItem.tp ++ [tp] =
          (its ++ [(BatchItem.mk (uint.nat x) ev tp lp fp)]).map BatchItem.tp := by simp
      rw [hmap]
      ihave %Hsl1 := ownSlice_len _ _ _ $$ Hsl
      ihave Hits : [∗list] it ∈ its ++ [(BatchItem.mk (uint.nat x) ev tp lp fp)], itemRes γ rc i it
        $$ [Hits Hfp]
      · iapply BigSepL.bigSepL_snoc.2
        iframe Hits
        simp only [itemRes]
        iframe #
        iframe Hfp
        ipureintro; exact Hk
      ihave Hcov := cover_extend γ e lk (uint.nat x) _ Hel Hlkx $$ [$Hcov $Htail]
      have hks : its.map BatchItem.k ++ [uint.nat x] =
          (its ++ [(BatchItem.mk (uint.nat x) ev tp lp fp)]).map BatchItem.k := by simp
      rw [hks]
      have Hbok' := batchOk_snoc e lk (uint.nat x) its (BatchItem.mk (uint.nat x) ev tp lp fp) Hbok Hel Hlkx rfl
      ihave Htail := noCmdBetween_self (GF := GF) γ (uint.nat x)
      simp only [List.length_append, List.length_map, List.length_singleton] at Hsl1
      wp_if_destruct
      · -- the batch is full: send it
        ipersist Hsl
        wp_apply HAB $$ %sl1 %e %(uint.nat x) Hps [Hsl Hits Hcov]
        · iapply fsmBatchP_intro γ rc i e (uint.nat x) sl1 _ Hbok' (by simp)
          iframe #
          iframe
        iintro Hps
        wp_auto
        wp_apply (wp_slice_make3 (V := Loc) (W64 0) c.MaxAppendEntries' (by word))
          as %sl3 ⟨Hsl3, Hcap3, -⟩
        wp_for_post
        iframe
        iexists x + W64 1, uint.nat x, uint.nat x, [], sl3, Mr'
        rw [Hx1']
        iframe
        iframe #
        isplitl []
        · iapply BigSepL.bigSepL_nil.2; itrivial
        isplitl []
        · unfold cover; simp only [Nat.sub_self, List.range'_zero, List.map_nil]
          iapply BigSepL.bigSepL_nil.2; itrivial
        ipureintro
        refine ⟨by omega, by omega, Nat.le_refl _, by omega, by simp; omega,
          ⟨List.Pairwise.nil, by simp, Or.inr ⟨rfl, rfl⟩⟩, HMr'⟩
      · -- not full yet
        wp_for_post
        iframe
        iexists x + W64 1, e, uint.nat x, its ++ [(BatchItem.mk (uint.nat x) ev tp lp fp)], sl1, Mr'
        rw [Hx1']
        iframe
        iframe #
        ipureintro
        refine ⟨by omega, by omega, by omega, by omega, ?_, Hbok', HMr'⟩
        simp only [List.length_append, List.length_singleton]
        word
  · -- the loop is done: `x = idx + 1`
    have Hxe : uint.nat x = uint.nat idx + 1 := by word
    rw [Hxe]
    ihave %Hsll := ownSlice_len _ _ _ $$ Hsl
    wp_join iprop(∃ e' : Nat, prodS rc e' ∗ noCmdBetween γ e' (uint.nat idx + 1) ∗
        ⌜e' ≤ uint.nat idx⌝ ∗ applyBatch_ptr ↦ abf) with [Hps Hsl Hits Hcov Htail batch Hcap applyBatch]
      as ⟨%e', Hps, Htail, %He', applyBatch⟩
    · -- no pending batch
      have hnil : its = [] := by
        cases its with
        | nil => rfl
        | cons _ _ => simp at Hsll; word
      have hlk : lk = e := by
        rcases Hbok.2.2 with h | ⟨-, h⟩
        · rw [hnil] at h; simp at h
        · exact h
      subst hlk
      iexists lk
      iframe
      ipureintro; omega
    · -- the last batch
      have hne : its ≠ [] := by
        intro h; subst h; simp at Hsll; word
      ipersist Hsl
      wp_apply HAB $$ %sl %e %lk Hps [Hsl Hits Hcov]
      · iapply fsmBatchP_intro γ rc i e lk sl _ Hbok hne
        iframe #
        iframe
      iintro Hps
      wp_auto
      isplitr
      · ipureintro; rfl
      iexists lk
      iframe
      ipureintro; omega
    wp_bind
    iapply (wp_setLastApplied r rc idx) $$ [$Hpkg $HappC]
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hmask
    inext
    iexists a
    iframe Hap
    isplitr
    · ipureintro; omega
    iintro Hap
    imod Hmask with -
    imodintro
    have hmax : Max.max a (uint.nat idx) = uint.nat idx := by
      apply Nat.max_eq_right; omega
    rw [hmax]
    wp_auto
    iapply HΦ
    iframe
    isplitl [Hps Htail]
    · iapply fsmProd_close γ rc e' (uint.nat idx) He'
      iframe
    · icases Hfm with (⟨%Hn, -⟩ | Hfm)
      · ileft; ipureintro; exact Hn
      · iright; iexact Hfm

end proof

end Perennial
