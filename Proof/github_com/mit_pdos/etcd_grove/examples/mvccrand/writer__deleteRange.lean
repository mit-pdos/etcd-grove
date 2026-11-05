/- Lean-first (no Rocq counterpart). The proof of `writer.deleteRange`: `begin`; the store's `Write`
(its update at the writer's `σ`, by its half of `γ.σ`; the hook's triple from `hookOk`); the read
in the transaction (`Txn.Range` at `.write σ []`, `checkRange` against `view`'s states); the delete
(`pending.del`'s keys are `Txn.DeleteRange`'s, `delKeys_eq_match`); `end` with `tw.End`
(`endCb_txnEnd`). -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.writer__deleteRange
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.writer__begin
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.writer__checkHook
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.writer__view
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.writer__end
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.rng__genKey
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.rng__genEnd
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.pending__del
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

theorem writer.deleteRange.wp_proof
    (hsh : mvcc.api.shapes.law (GF := GF) (hG := hG))
    (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG))
    (wp_check : check.spec (GF := GF) (hG := hG))
    (wp_begin : writer.begin.spec (GF := GF) (hG := hG))
    (wp_checkHook : writer.checkHook.spec (GF := GF) (hG := hG))
    (wp_view : writer.view.spec (GF := GF) (hG := hG))
    (wp_end : writer.end.spec (GF := GF) (hG := hG))
    (wp_genKey : rng.genKey.spec (GF := GF) (hG := hG))
    (wp_genEnd : rng.genEnd.spec (GF := GF) (hG := hG))
    (wp_del : pending.del.spec (GF := GF) (hG := hG))
    (wp_checkRange : checkRange.spec (GF := GF) (hG := hG))
    (wp_trTODO : traceutil.TODO.spec (GF := GF) (hG := hG))
    (wp_ctxTODO : context.TODO.spec (GF := GF) (hG := hG)) :
    writer.deleteRange.spec (GF := GF) (hG := hG) := by
  intro w wv γ B f q σ Hs L i s
  haveI := hpers.1 wv.kv' γ.kv
  haveI := fun σ => hpers.2.2.2.2.1 γ.kv σ
  haveI := fun S => hpers.2.2.2.2.2.1 γ.ws S
  haveI : Timeless (worldInv (GF := GF) wv.h' γ) := by unfold worldInv; infer_instance
  have hdisj : (↑worldN : CoPset) ⊆ ⊤ \ ↑mvccN :=
    nclose_subseteq' "world" (mask_ndot_ne' nroot "mvccrand" "mvcc" (by decide))
  wp_start as ⟨Hctx, Hown, Hpre⟩
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
  obtain ⟨tty, tv, rfl, -, -, hRangeC, -, hDelC, -, hEndC⟩ := Hsht
  ihave Hidle : writerIdle γ σ Hs $$ [Hgσ HW Hpv]
  · iunfold writerIdle; iframe; ipureintro; exact ⟨Hpn, Hlen, Hbound, Hmatch⟩
  (try wp_auto)
  -- `w.checkHook(i)`
  iunfold hookPost at Hpost
  icases Hpost with ⟨Happ, Hsav⟩
  wp_apply wp_checkHook w wv i $$ [$Hpkg $Hw $Hsav] as Hsav
  (try wp_auto)
  wp_apply wp_genKey wv.r' g $$ [$Hpkg $Hg] as %ks ⟨⟨%g1, Hg⟩, %kk, Hks, -, %Hkk⟩
  wp_apply wp_genEnd wv.r' g1 $$ [$Hpkg $Hg] as %es ⟨⟨%g2, Hg⟩, %e, Hes, -, %He⟩
  (try wp_auto)
  wp_apply wp_view w wv γ σ Hs p ⟨W64 (Hs.length : Int), lastSt Hs, []⟩ rfl
    $$ [$Hpkg $Hw $Hrd $Hidle $Hp] as %sts %cur ⟨Hrd, Hidle, %Hcur, %dsl, %ms, Hsts, HstAt, Hback⟩
  (try wp_auto)
  -- the read: `tw.Range(context.TODO(), key, end, {})`
  wp_apply wp_ctxTODO
  (try wp_auto)
  imod ownSlice_persist _ _ _ $$ Hks with #Hks
  imod ownSlice_persist _ _ _ $$ Hes with #Hes
  ihave #Hctxr : mvcc.rangeCtx true todoCtxVal
      ({ Values := GMap.empty, Deadline := none, Done_gn := ⟨0, 0⟩, PDone := iprop(True) } :
        context.ContextDesc (IProp GF)) $$ []
  · simp only [mvcc.rangeCtx, ↓reduceIte]; ileft; iapply mvcc.doneNil_todo
  wp_apply (hRangeC γ.kv trace true (.write σ []) todoCtxVal _ true ks es kk e
      (zero_val go_etcd_io.etcd.server.v3.storage.mvcc.RangeOptions)) $$ [$Hmv $Htx $Htrc $Hctxr $Hks $Hes]
    as %rr %err ⟨%Hrn, Htx, Htrc, Hout, -, %Hlwf⟩
  -- the read's outcome at the read log `σ.log ++ [[]]`, revision `cur`, never compacted
  have hl2 : 2 ≤ σ.log.length := by unfold MvccState.rev at Hrev1; omega
  have hne : σ.log ≠ [] := by intro h0; rw [h0] at hl2; simp at hl2
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
  iunfold statesAt at HstAt
  icases HstAt with ⟨%Hml, HstAt⟩
  have hvl := viewSt_length_nil Hs ⟨W64 (Hs.length : Int), lastSt Hs, []⟩ rfl
  wp_apply (wp_checkRange sts dsl ms (viewSt Hs ⟨W64 (Hs.length : Int), lastSt Hs, []⟩)
      (viewDq Hs ⟨W64 (Hs.length : Int), lastSt Hs, []⟩) cur { key' := ks, end' := es, ro' := zeroValDef }
      kk e DFrac.discard DFrac.discard rr err
      (σ.log ++ [[]]) hLok (by omega) (by have : sint.nat cur = (sint.Z cur).toNat := rfl; omega)
      (fun r hr => viewSt_match_nil σ Hs _ rfl Hlen Hmatch r
        (by have : sint.nat cur = (sint.Z cur).toNat := rfl; omega)))
    $$ [$Hpkg $Hmv $Hsts HstAt $Hks $Hes $Hout] as ⟨Hsts, HstAt, -, -⟩
  · iunfold statesAt; iframe HstAt
    ipureintro; exact ⟨Hml, Hrn rfl⟩
  ihave Hp := Hback $$ HstAt
  -- the delete: the model's (`p.del`), then the store's
  wp_apply wp_del p ⟨W64 (Hs.length : Int), lastSt Hs, []⟩ ks es kk e DFrac.discard DFrac.discard
    $$ [$Hpkg $Hp $Hks $Hes] as ⟨Hp, -, -⟩
  (try wp_auto)
  wp_apply (hDelC γ.kv trace σ [] ks es kk e L) $$ [$Hmv $Htx $Hks $Hes $Hlo]
    as %n %rev ⟨Htx, Hlo, %Hnr, -⟩
  have hM := stMatch_lastSt σ Hs Hlen (by omega) Hmatch
  have hks := delKeys_eq_match σ.log [] hne hLok (decide (es = slice.nil)) kk e (lastSt Hs) hM
  have hdl : (matchKeys (lastSt Hs) (decide (es = slice.nil)) kk e).length ≤ 6 := by
    unfold matchKeys; exact Nat.le_trans (List.length_filter_le _ _) (by decide)
  simp only [List.nil_append] at Hnr ⊢
  obtain ⟨rfl, rfl⟩ := Hnr
  (try wp_auto)
  rw [hks]
  wp_apply wp_check
  · ipureintro; simp
  (try wp_auto)
  -- the revision's checks: the pending one if a key was deleted, else the last
  have hc1 : sint.Z (W64 0) <
      sint.Z (W64 ((matchKeys (lastSt Hs) (decide (es = slice.nil)) kk e).length : Int)) →
      W64 ((writeRev σ.log ((matchKeys (lastSt Hs) (decide (es = slice.nil)) kk e).map Change.del) : Nat) : Int) =
        W64 (Hs.length : Int) := by
    intro h
    have hD : matchKeys (lastSt Hs) (decide (es = slice.nil)) kk e ≠ [] := by
      intro h0; rw [h0] at h; exact absurd h (by decide)
    simp [writeRev, hD, Hlen]
  have hc2 : ¬ sint.Z (W64 0) <
      sint.Z (W64 ((matchKeys (lastSt Hs) (decide (es = slice.nil)) kk e).length : Int)) →
      W64 ((writeRev σ.log ((matchKeys (lastSt Hs) (decide (es = slice.nil)) kk e).map Change.del) : Nat) : Int) =
        W64 (Hs.length : Int) - W64 1 := by
    intro h
    have hD : matchKeys (lastSt Hs) (decide (es = slice.nil)) kk e = [] := by
      apply List.eq_nil_of_length_eq_zero
      have : sint.Z (W64 ((matchKeys (lastSt Hs) (decide (es = slice.nil)) kk e).length : Int)) =
          (matchKeys (lastSt Hs) (decide (es = slice.nil)) kk e).length := by word
      have h0 : sint.Z (W64 0) = 0 := by decide
      omega
    simp only [hD, List.map_nil, writeRev, ↓reduceIte]
    rw [Hlen, w64_pred _ (by omega) (by omega)]
  iunfold ownPending at Hp
  icases Hp with ⟨%pv, Hpv, %Hprev, Hpst, Hpch, Hpcap⟩
  simp only [PendM.del] at Hprev
  wp_if_destruct
  all_goals (try wp_auto)
  all_goals wp_apply wp_check
  all_goals (try (ipureintro; simp only [decide_eq_true_eq, Hprev]; first | exact hc1 Hif | exact hc2 Hif))
  all_goals (try wp_auto)
  -- `w.end(p, tw.End)`
  all_goals
    have hok := pendOk_del σ Hs (decide (es = slice.nil)) kk e hM hks
    rw [hks] at hok
    ihave Hp : ownPending p (({ rev := W64 (Hs.length : Int), st := lastSt Hs, chs := [] } : PendM).del
        (decide (es = slice.nil)) kk e) $$ [Hpv Hpst Hpch Hpcap]
    · iunfold ownPending; iexists pv; iframe; ipureintro; exact Hprev
    ihave #Hkv0 : isMvcc wv.kv' γ.kv $$ []
    · rw [Hkveq]; iexact Hkv
    ihave Hcb := endCb_txnEnd hpers hEndC wv.h' γ σ Hs _ _ trace q B hok Hpn Hlen Hmatch
    wp_apply (wp_end w wv γ σ Hs p _ _ (methods tty go!"End" tv)
        iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
          inv worldN (worldInv wv.h' γ) ∗
          mvccTxn (interface.mkOk tty tv) γ.kv trace
            (.write σ ((matchKeys (lastSt Hs) (decide (es = slice.nil)) kk e).map Change.del)) ∗
          mvccBackend γ.kv q B iprop(True))
        (mvccBackend γ.kv q B iprop(True)) hok)
      $$ [$Hpkg $Hmv $Hw $Hrd $Hinv $Hkv0 $Hidle $Hp $Hcb $Htx $Hbk] as ⟨Hrd, Htt, Hbk, Hidle⟩
    iapply HΦ
    isplitr [Happ Hsav]
    · iexists _, _
      iunfold writerOwn
      iframe Htt Hbk Hrd Hidle Hlm
      isplitl [Hg]
      · iexists g2; iexact Hg
      rw [pendItems_commit]; iexact Hlo
    · iunfold hookPost; iframe

end proof

end mvccrand
end EtcdGrove
end Perennial
