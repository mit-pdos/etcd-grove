/- Lean-first (no Rocq counterpart). The proof of `writer.put`: as `deleteRange`'s (`begin`, the
store's `Write`, the read in the transaction checked by `checkRange`, `end` with `tw.End`), with the
transaction's revision checked (`Txn.Rev`) and a put in place of the delete: the model's
(`pending.put`, `stMatch_put`) and the store's (`Txn.Put`: its revision the pending one; the lease
none or a live one, `genLease`). -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.writer__put
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.writer__begin
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.writer__checkHook
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.writer__view
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.writer__end
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.rng__genKey
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.writer__newVal
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.writer__genLease
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.pending__put
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.checkRange
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.check
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.TODO
public import Spec.context.TODO
public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccrand.TxnEnd
public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccrand.WriteLemmas

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccrand

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.mvccrand mvcc mvcc.api

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccrand.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem writer.put.wp_proof
    (hsh : mvcc.api.shapes.law (GF := GF) (hG := hG))
    (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG))
    (wp_check : check.spec (GF := GF) (hG := hG))
    (wp_begin : writer.begin.spec (GF := GF) (hG := hG))
    (wp_checkHook : writer.checkHook.spec (GF := GF) (hG := hG))
    (wp_view : writer.view.spec (GF := GF) (hG := hG))
    (wp_end : writer.end.spec (GF := GF) (hG := hG))
    (wp_genKey : rng.genKey.spec (GF := GF) (hG := hG))
    (wp_newVal : writer.newVal.spec (GF := GF) (hG := hG))
    (wp_genLease : writer.genLease.spec (GF := GF) (hG := hG))
    (wp_put : pending.put.spec (GF := GF) (hG := hG))
    (wp_checkRange : checkRange.spec (GF := GF) (hG := hG))
    (wp_trTODO : traceutil.TODO.spec (GF := GF) (hG := hG))
    (wp_ctxTODO : context.TODO.spec (GF := GF) (hG := hG)) :
    writer.put.spec (GF := GF) (hG := hG) := by
  intro w wv γ B f q σ Hs L i s n hn0 hn1
  haveI := hpers.1 wv.kv' γ.kv
  haveI := fun σ => hpers.2.2.2.2.2.1 γ.kv σ
  haveI := fun S => hpers.2.2.2.2.2.2.1 γ.ws S
  haveI : Timeless (worldInv (GF := GF) wv.h' γ) := by unfold worldInv; infer_instance
  have hdisj : (↑worldN : CoPset) ⊆ ⊤ \ ↑mvccN :=
    nclose_subseteq' "world" (mask_ndot_ne' nroot "mvccrand" "mvcc" (by decide))
  wp_start as ⟨Hctx, Hown, Hpre, Hvals⟩
  iunfold writerCtx at Hctx
  icases Hctx with ⟨#Hpkg, #Hmv, #Htu, #Hw, #Hinv, #Hhist, #Hkv, #Hhook, Hhok⟩
  iunfold hookOk at Hhok
  icases Hhok with #Hhok
  iunfold writerOwn at Hown
  icases Hown with ⟨Htt, Hbk, Hrd, Hidle, ⟨%g, Hg⟩, Hlm, Hlo⟩
  ihave #Hw2 := Hw
  iunfold writerRO at Hw2
  icases Hw2 with ⟨#kvW, #leW, #hW, #rW, #leasesW, #applyingW, #savedW, #ticksW⟩
  wp_auto
  wp_apply wp_begin w wv γ σ Hs $$ [$Hpkg $Hw $Hrd $Hinv $Hidle] as %p ⟨Hrd, Hidle, Hp⟩
  (try wp_auto)
  wp_apply wp_trTODO $$ [$Htu] as %trace ⟨%Htr, Htrc⟩
  (try wp_auto)
  -- `w.kv.Write(trace)`: the update at the writer's `σ`
  icases (persistent_entails_right (hsh.1 wv.kv' γ.kv)) $$ Hkv with ⟨%Hsh, #Hkv⟩
  obtain ⟨kty, kvv, Hkveq, -, hWriteC, -⟩ := Hsh
  iunfold writerIdle at Hidle
  icases Hidle with ⟨Hgσ, HW, Hpv, %Hid⟩
  obtain ⟨Hpn, Hlen, Hbound, Hmatch⟩ := Hid
  rw [Hkveq]
  (try wp_auto)
  wp_apply (hWriteC γ.kv trace true q B iprop(True) (hookPre wv i s) iprop(True ∗ hookPost wv i) f
      (fun σ' => iprop(⌜σ' = σ ∧ σ.crev = -1 ∧ 1 ≤ σ.rev⌝ ∗ ghostVar γ.σ (1 : Qp).half σ)))
    $$ [$Hmv $Hkv $Htt $Htrc $Hbk $Hhook $Hpre Hgσ]
    as %tw ⟨Htrc, Hbk, ⟨%σ0, Htx, ⟨%Heq, Hgσ⟩⟩, ⟨-, Hpost⟩⟩
  · isplitr
    · ipureintro; exact Htr
    isplitr
    · iapply Hhok
    iauintro
    unfold atomic_acc
    iinv Hinv with >Hi Hclose
    iunfold worldInv at Hi
    icases Hi with ⟨%σ1, %S, %p', %Hl, %W, Hst, Hgσ', HS, Hreg, Hpub, Hpv', Hpm, Hlb0, %Hok⟩
    ihave %Hag := ghostVar_agree γ.σ _ _ _ _ $$ Hgσ' Hgσ
    subst Hag
    iapply fupd_mask_intro (show (∅ : CoPset) ⊆ (⊤ \ ↑mvccN) \ ↑worldN from
      Std.LawfulSet.empty_subset)
    iintro Hclose2
    isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
    iexists σ1
    iframe Hst
    isplit
    · iintro Hst
      imod Hclose2 with -
      imod Hclose $$ [Hst Hgσ' HS Hreg Hpub Hpv' Hpm Hlb0] with -
      · inext; iunfold worldInv; iexists σ1, S, p', Hl, W; iframe; ipureintro; exact Hok
      imodintro
      iframe Hgσ
    · iintro ⟨-, Hst⟩
      imod Hclose2 with -
      imod Hclose $$ [Hst Hgσ' HS Hreg Hpub Hpv' Hpm Hlb0] with -
      · inext; iunfold worldInv; iexists σ1, S, p', Hl, W; iframe; ipureintro; exact Hok
      imodintro
      iframe Hgσ
      ipureintro
      obtain ⟨h1, h2, h3, -⟩ := Hok
      refine ⟨rfl, h1, ?_⟩
      have : sint.nat p' = (sint.Z p').toNat := rfl
      omega
  have Heq0 := Heq.1.symm
  subst Heq0
  obtain ⟨-, Hcrev, Hrev1⟩ := Heq
  icases (persistent_entails_right (hsh.2.2.1 tw γ.kv trace (.write σ []))) $$ Htx with ⟨%Hsht, Htx⟩
  obtain ⟨tty, tv, rfl, hRevC, -, hRangeC, hPutC, -, -, hEndC⟩ := Hsht
  ihave Hidle : writerIdle γ σ Hs $$ [Hgσ HW Hpv]
  · iunfold writerIdle; iframe; ipureintro; exact ⟨Hpn, Hlen, Hbound, Hmatch⟩
  (try wp_auto)

  -- `w.checkHook(i)`
  iunfold hookPost at Hpost
  icases Hpost with ⟨Happ, Hsav⟩
  wp_apply wp_checkHook w wv i $$ [$Hpkg $Hw $Hsav] as Hsav
  (try wp_auto)
  -- `tw.Rev() == p.rev-1`
  wp_apply (hRevC γ.kv trace (.write σ [])) $$ [$Hmv $Htx] as Htx
  have hl2 : 2 ≤ σ.log.length := by unfold MvccState.rev at Hrev1; omega
  have hne : σ.log ≠ [] := by intro h0; rw [h0] at hl2; simp at hl2
  iunfold ownPending at Hp
  icases Hp with ⟨%pv, Hpv, %Hprev, Hpst, Hpch, Hpcap⟩
  (try wp_auto)
  wp_apply wp_check
  · ipureintro
    simp only [decide_eq_true_eq, Hprev, MTxn.state, MvccState.rev]
    rw [Hlen, w64_pred _ (by omega) (by omega)]
  ihave Hp : ownPending p ⟨W64 (Hs.length : Int), lastSt Hs, []⟩ $$ [Hpv Hpst Hpch Hpcap]
  · iunfold ownPending; iexists pv; iframe; ipureintro; exact Hprev
  (try wp_auto)
  wp_apply wp_genKey wv.r' g $$ [$Hpkg $Hg] as %ks ⟨⟨%g1, Hg⟩, %kk, Hks, -, %Hkk⟩
  (try wp_auto)
  wp_apply wp_view w wv γ σ Hs p ⟨W64 (Hs.length : Int), lastSt Hs, []⟩ rfl
    $$ [$Hpkg $Hw $Hrd $Hidle $Hp] as %sts %cur ⟨Hrd, Hidle, %Hcur, %dsl, %ms, Hsts, HstAt, Hback⟩
  (try wp_auto)
  -- the read: `tw.Range(context.TODO(), k, nil, {})`
  wp_apply wp_ctxTODO
  (try wp_auto)
  imod ownSlice_persist _ _ _ $$ Hks with #Hks
  ihave #Hnil : (slice.nil ↦*□ ([] : List w8) : IProp GF) $$ []
  · iapply ownSlice_nil
  ihave #Hctxr : mvcc.rangeCtx true todoCtxVal
      ({ Values := GMap.empty, Deadline := none, Done_gn := ⟨0, 0⟩, PDone := iprop(True) } :
        context.ContextDesc (IProp GF)) $$ []
  · simp only [mvcc.rangeCtx, ↓reduceIte]; ileft; iapply mvcc.doneNil_todo
  wp_apply (hRangeC γ.kv trace true (.write σ []) todoCtxVal _ true ks slice.nil kk []
      (zero_val go_etcd_io.etcd.server.v3.storage.mvcc.RangeOptions)) $$ [$Hmv $Htx $Htrc $Hctxr $Hks $Hnil]
    as %rr %err ⟨%Hrn, Htx, Htrc, Hout, -, %Hlwf⟩
  -- the read's outcome at the read log `σ.log ++ [[]]`, revision `cur`, never compacted
  have hcurv : cur = W64 ((Hs.length - 1 : Nat) : Int) := by
    rw [Hcur, w64_pred _ (by omega) (by omega)]; simp [viewRev]
  have hcurZ : sint.Z cur = ((Hs.length - 1 : Nat) : Int) := by
    have : Hs.length - 1 < 2 ^ 63 := by omega
    rw [hcurv]; word
  have hrr : (MTxn.write σ []).readRev = cur := by
    rw [hcurv]; simp [MTxn.readRev, writeRev, Hlen]
  have hrl : (MTxn.write σ []).readLog = σ.log ++ [[]] := rfl
  have hcr : (MTxn.write σ []).state.crev = -1 := Hcrev
  rw [hrl] at Hlwf
  have hLok : txn.LogOk (σ.log ++ [[]]) :=
    txn.LogOk.of_cert ⟨Hlwf.1, by simp; omega, Hlwf.2⟩ (by simp)
  rw [hrr, hrl, hcr]
  ihave Hout := mvcc.rangeOutcomeC_neg _ _ _ _ _ _ _ _ (by omega) $$ Hout
  ihave Hout : rangeOutcome rr err (σ.log ++ [[]]) cur (decide ((slice.nil : GoSlice) = slice.nil)) kk []
      (zero_val go_etcd_io.etcd.server.v3.storage.mvcc.RangeOptions) $$ [Hout]
  · simp only [decide_true]; iexact Hout
  iunfold statesAt at HstAt
  icases HstAt with ⟨%Hml, HstAt⟩
  have hvl := viewSt_length_nil Hs ⟨W64 (Hs.length : Int), lastSt Hs, []⟩ rfl
  wp_apply (wp_checkRange sts dsl ms (viewSt Hs ⟨W64 (Hs.length : Int), lastSt Hs, []⟩)
      (viewDq Hs ⟨W64 (Hs.length : Int), lastSt Hs, []⟩) cur
      { key' := ks, end' := slice.nil, ro' := zeroValDef }
      kk [] DFrac.discard DFrac.discard rr err
      (σ.log ++ [[]]) hLok (by omega) (by have : sint.nat cur = (sint.Z cur).toNat := rfl; omega)
      (fun r hr => viewSt_match_nil σ Hs _ rfl Hlen Hmatch r
        (by have : sint.nat cur = (sint.Z cur).toNat := rfl; omega)))
    $$ [$Hpkg $Hmv $Hsts HstAt $Hks $Hnil $Hout] as ⟨Hsts, HstAt, -, -⟩
  · iunfold statesAt; iframe HstAt
    ipureintro; exact ⟨Hml, Hrn rfl⟩
  ihave Hp := Hback $$ HstAt
  -- the put: a value, a lease, the model's (`p.put`), then the store's
  wp_apply wp_newVal w n hn0 hn1 $$ [$Hpkg $Hvals] as Hvals
  (try wp_auto)
  icases Hlm with ⟨%Lm, Hlm, %HLm⟩
  wp_apply wp_genLease w wv Lm g1 $$ [$Hpkg $Hw $Hlm $Hg] as %l ⟨Hlm, ⟨%g2, Hg⟩, %Hl⟩
  (try wp_auto)
  wp_apply wp_bytes_to_string ks kk DFrac.discard $$ [$Hks] as -
  (try wp_auto)
  wp_apply wp_put p ⟨W64 (Hs.length : Int), lastSt Hs, []⟩ kk _ l $$ [$Hpkg $Hp] as Hp
  (try wp_auto)
  wp_apply wp_string_to_bytes as %vs ⟨Hvs, -⟩
  imod ownSlice_persist _ _ _ $$ Hvs with #Hvs
  (try wp_auto)
  have hkl := keyList_short kk Hkk
  wp_apply (hPutC γ.kv trace true σ [] ks vs kk _ l L) $$ [$Hmv $Htx $Htrc $Hks $Hvs $Hlo]
    as ⟨Htx, Htrc, Hlo⟩
  · iframe
    ipureintro
    refine ⟨by omega, ?_⟩
    rcases Hl with h | h
    · exact Or.inl h
    · exact Or.inr ((HLm l).1 h)
  simp only [List.nil_append]
  iunfold ownPending at Hp
  icases Hp with ⟨%pv, Hpv, %Hprev, Hpst, Hpch, Hpcap⟩
  simp only [PendM.put] at Hprev
  (try wp_auto)
  wp_apply wp_check
  · ipureintro; simp only [decide_eq_true_eq, Hprev, Hlen]
  (try wp_auto)
  -- `w.end(p, tw.End)`
  have hM := stMatch_lastSt σ Hs Hlen (by omega) Hmatch
  have hok := pendOk_put σ Hs Hlen hM kk (go!"v" ++ itoaM (sint.nat (n + W64 1))) l Hkk
  ihave Hp : ownPending p ((⟨W64 (Hs.length : Int), lastSt Hs, []⟩ : PendM).put kk
      (go!"v" ++ itoaM (sint.nat (n + W64 1))) l) $$ [Hpv Hpst Hpch Hpcap]
  · iunfold ownPending; iexists pv; iframe; ipureintro; exact Hprev
  ihave #Hkv0 : isMvcc wv.kv' γ.kv $$ []
  · rw [Hkveq]; iexact Hkv
  ihave Hcb := endCb_txnEnd hpers hEndC wv.h' γ σ Hs _ _ trace q B hok Hpn Hlen Hmatch
  wp_apply (wp_end w wv γ σ Hs p _ _ (methods tty go!"End" tv)
      iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
        inv worldN (worldInv wv.h' γ) ∗
        mvccTxn (interface.mkOk tty tv) γ.kv trace
          (.write σ [.put kk (go!"v" ++ itoaM (sint.nat (n + W64 1))) l]) ∗
        mvccBackend γ.kv q B iprop(True))
      (mvccBackend γ.kv q B iprop(True)) hok)
    $$ [$Hpkg $Hmv $Hw $Hrd $Hinv $Hkv0 $Hidle $Hp $Hcb $Htx $Hbk] as ⟨Hrd, Htt, Hbk, Hidle⟩
  iapply HΦ
  iframe Hvals
  isplitr [Happ Hsav]
  · iexists _, _
    iunfold writerOwn
    iframe Htt Hbk Hrd Hidle
    isplitl [Hg]
    · iexists g2; iexact Hg
    isplitl [Hlm]
    · iexists Lm; iframe Hlm; ipureintro; exact HLm
    rw [pendItems_commit]; iexact Hlo
  · iunfold hookPost; iframe

end proof

end mvccrand
end EtcdGrove
end Perennial
