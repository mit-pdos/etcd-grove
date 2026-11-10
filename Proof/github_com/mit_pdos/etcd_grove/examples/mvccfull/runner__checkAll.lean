/- Lean-first (no Rocq counterpart). The proof of `runner.checkAll`: proved.

The outline: `history.snapshot`; `KV.Read` at the incarnation's invariant (the state `σOf`,
pinned by the writer's half); the loop over `[max 1 m.cmp, m.rev]` with `Txn.Range` and
`checkRangeAt` (`logOk_hist`); the compacted read; `Txn.End`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__checkAll
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.history__snapshot
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.checkRangeAt
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.TODO
public import Spec.context.TODO
public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.RestoreLemmas
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.TxnRange

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.mvccfull mvcc mvcc.api

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

private theorem checkAll_zip_disc (ms : List GoMap) (Hs : List HRev) :
    ms.zip ((Hs.map Prod.fst).zip (List.replicate Hs.length DFrac.discard)) =
      (ms.zip Hs).map (fun x => (x.1, (x.2.1, DFrac.discard))) := by
  induction ms generalizing Hs with
  | nil => simp
  | cons m ms ih =>
    cases Hs with
    | nil => simp
    | cons e Hs => simp [List.replicate_succ, ih]

private theorem checkAll_statesAt_hist (ms : List GoMap) (Hs : List HRev) :
    statesP (GF := GF) ms Hs ⊢ statesAt ms (Hs.map Prod.fst) (List.replicate Hs.length DFrac.discard) := by
  unfold statesP statesAt
  iintro ⟨%h, H⟩
  rw [checkAll_zip_disc, BigSepL.bigSepL_map]
  isplitr
  · ipureintro; simp [h]
  iexact H

/-- The history's states match the store's at every revision of the member's log. -/
private theorem checkAll_hist_match (ks : List GoString) (hks : ks.Pairwise go.GoStringLt) (ops : List OpM)
    (hok : logOk ks ops) (n : Nat) (hn : n ≤ ops.length) (Hs' : List HRev)
    (hp : histAt ks ops n <+: Hs') :
    ∀ r : Nat, r < (σOf ks ops n).log.length →
      ∃ M, (Hs'.map Prod.fst)[r]? = some M ∧ stMatch ks M (stateAt (σOf ks ops n).log r) := by
  intro r hr
  obtain ⟨-, ⟨-, hH⟩, -⟩ := logOk_hist ks hks ops hok n n (Nat.le_refl _) hn
  rw [σOf_notified] at hH
  obtain ⟨e, he, hrev⟩ := hH r hr
  obtain ⟨t, rfl⟩ := hp
  have hlt : r < (histAt ks ops n).length := by
    have := List.getElem?_eq_some_iff.1 he; exact this.1
  refine ⟨e.1, ?_, hrev.1⟩
  rw [List.getElem?_map, List.getElem?_append_left hlt, he]; rfl

theorem runner.checkAll.wp_proof
    (hsh : mvcc.api.shapes.law (GF := GF) (hG := hG))
    (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG))
    (hRdSplit : mvcc.api.mvccReaders_split.law (GF := GF))
    (wp_snapshot : history.snapshot.spec (GF := GF) (hG := hG))
    (wp_traceTODO : traceutil.TODO.spec (GF := GF) (hG := hG))
    (wp_ctxTODO : context.TODO.spec (GF := GF) (hG := hG))
    (wp_checkRangeAt : checkRangeAt.spec (GF := GF) (hG := hG)) :
    runner.checkAll.spec (GF := GF) (hG := hG) := by
  intro x ks cfg wr h γh ops i mp m f v qw nw k hlogOk hnw hlen
  haveI : ∀ N l, Persistent (ctrInv (GF := GF) N l) := by intro N l; unfold ctrInv; infer_instance
  haveI := isInc_persistent hpers
  haveI := hpers.1
  haveI : Persistent (writerCtx (GF := GF) x ks cfg wr h γh) := writerCtx_persistent _ _ _ _ _ _
  wp_start as ⟨#Hctx, Hrd, #Hlb, Hc⟩
  iunfold writerCtx at Hctx
  icases Hctx with ⟨#Hrn, -⟩
  iunfold rnCtx at Hrn
  icases Hrn with ⟨#Hpkg, #Hpm, #Hkeys, %Hkne, #HrH, -⟩
  iunfold runnerKeys at Hkeys
  icases Hkeys with ⟨%keys, #Hkeysf, #Hksl, %Hsorted, -⟩
  iunfold runnerH at HrH
  iunfold memCore at Hc
  icases Hc with ⟨#Hid, #Hhook, HhookOk, Hpath, Hbe, Hle, Hkv, Hrev, Hcmp, Hleases, %Hvops,
    Hinc, Hopen, Hback, Hhk, Hrdrs, Hbk, Hles, %HU⟩
  iunfold incW at Hinc
  icases Hinc with ⟨#Hisinc, Hret, Hσw, Hbw⟩
  ihave #Hmv : isMvcc v.kv v.ι.kv $$ []
  · iunfold isInc at Hisinc; icases Hisinc with ⟨-, #H⟩; iexact H
  ihave %Hkvs := hsh.1 v.kv v.ι.kv $$ Hmv
  obtain ⟨kty, kvv, hkveq, hKR, -⟩ := Hkvs
  -- the model
  obtain ⟨-, -, hreach⟩ := logOk_hist ks Hsorted ops hlogOk v.ops v.ops (Nat.le_refl _) Hvops
  obtain ⟨hl2, hc1, hcr⟩ := reach_bounds _ hreach
  have hhl : 2 ≤ (histAt ks ops v.ops).length ∧ (histAt ks ops v.ops).length ≤ v.ops + 2 :=
    runM_hs_len ks ops v.ops
  have hσl : (σOf ks ops v.ops).log.length = (histAt ks ops v.ops).length := by
    simp [σOf, logOfHist]
  have hrevA : ((σOf ks ops v.ops).rev : Int) = revAfter ks ops v.ops := by rw [σOf_rev]
  have hrevlt : (revAfter ks ops v.ops : Int) < 2 ^ 40 := by
    have : (σOf ks ops v.ops).rev = (σOf ks ops v.ops).log.length - 1 := rfl
    omega
  have hcmpA : (σOf ks ops v.ops).crev = cmpAfter ks ops v.ops := rfl
  have hrZ : sint.Z (W64 (revAfter ks ops v.ops : Int)) = revAfter ks ops v.ops := by word
  have hcZ : sint.Z (W64 (cmpAfter ks ops v.ops)) = cmpAfter ks ops v.ops := by
    have : cmpAfter ks ops v.ops ≤ revAfter ks ops v.ops := by rw [← hcmpA]; omega
    have : -1 ≤ cmpAfter ks ops v.ops := by rw [← hcmpA]; omega
    word
  wp_auto
  -- `states := x.h.snapshot()`
  wp_apply wp_snapshot h γh (histAt ks ops v.ops) $$ [$Hrd $Hlb]
    as %s ⟨Hrd, %ms, %Hs', ⟨%Hpre, %H2⟩, %Hscap, #Hlb', #Hms, #Hst⟩
  ihave %Hmlen : ⌜ms.length = Hs'.length⌝ $$ [Hst]
  · iunfold statesP at Hst; icases Hst with ⟨%H, -⟩; ipureintro; exact H
  ihave #HstAt := checkAll_statesAt_hist ms Hs' $$ Hst
  have hle : (histAt ks ops v.ops).length ≤ Hs'.length := Hpre.length_le
  have hmatch := checkAll_hist_match ks Hsorted ops hlogOk v.ops Hvops Hs' Hpre
  (try wp_auto)
  wp_join iprop(from_ptr ↦ W64 (max 1 (cmpAfter ks ops v.ops))) with [«from»] as «from»
  · have : max 1 (cmpAfter ks ops v.ops) = 1 := by
      have : cmpAfter ks ops v.ops < 1 := by rw [hcZ] at Hif; exact Hif
      omega
    rw [this]; (try wp_auto); iframe
  · have : max 1 (cmpAfter ks ops v.ops) = cmpAfter ks ops v.ops := by
      have : ¬ cmpAfter ks ops v.ops < 1 := by rw [hcZ] at Hif; exact Hif
      omega
    rw [this]; (try wp_auto); iframe
  (try wp_auto)
  -- `tr := m.kv.Read(…)`
  wp_apply wp_traceTODO as %trc ⟨%Htrc, Htrco⟩
  (try wp_auto)
  have hR1' : mvccReaders (GF := GF) v.ι.kv nw ⊣⊢
      mvccReaders v.ι.kv (nw - 1) ∗ mvccReaders v.ι.kv 1 := by
    have := hRdSplit v.ι.kv (nw - 1) 1; rwa [Nat.sub_add_cancel hnw] at this
  icases hR1'.1 $$ Hrdrs with ⟨Hrdrs, Hr1⟩
  ihave Hau := read_au hpers ks γh i mp m v.ι v.kv qw (σOf ks ops v.ops) $$ [Hret Hσw]
  · iframe #; iframe
  rw [hkveq]
  wp_apply (hKR v.ι.kv (W32 1) trc true (fun σ => iprop(⌜σ = σOf ks ops v.ops⌝ ∗
      ghostVar v.ι.ret qw () ∗ ghostVar m.σ (1 : Qp).half (σOf ks ops v.ops))))
    $$ [Hr1 Htrco Hau] as %tx ⟨Htrco, %σr, Htx, %Hσr, Hret, Hσw⟩
  · iframe #; iframe; ipureintro; exact Htrc
  subst Hσr
  ihave %Htxs := hsh.2.2.1 tx v.ι.kv trc (.read (σOf ks ops v.ops)) $$ Htx
  obtain ⟨tty, tv, htx, -, -, hTRange, -, -, -, hTEnd⟩ := Htxs
  subst htx
  (try wp_auto)
  have hne : (σOf ks ops v.ops).log ≠ [] := by
    intro h0; have := congrArg List.length h0; simp only [List.length_nil] at this; omega
  have hcurlt : sint.nat (W64 (revAfter ks ops v.ops : Int)) < ms.length := by
    have : sint.nat (W64 (revAfter ks ops v.ops : Int)) = (sint.Z (W64 (revAfter ks ops v.ops : Int))).toNat := rfl
    rw [this, hrZ]
    have : (σOf ks ops v.ops).rev = (σOf ks ops v.ops).log.length - 1 := rfl
    omega
  have hM : ∀ r : Nat, sint.Z (W64 (cmpAfter ks ops v.ops)) ≤ (r : Int) →
      r ≤ sint.nat (W64 (revAfter ks ops v.ops : Int)) →
      ∃ M, (Hs'.map Prod.fst)[r]? = some M ∧ stMatch ks M (stateAt (σOf ks ops v.ops).log r) := by
    intro r _ hr
    have : sint.nat (W64 (revAfter ks ops v.ops : Int)) = (sint.Z (W64 (revAfter ks ops v.ops : Int))).toNat := rfl
    rw [this, hrZ] at hr
    have : (σOf ks ops v.ops).rev = (σOf ks ops v.ops).log.length - 1 := rfl
    exact hmatch r (by omega)
  have hrr : (MTxn.read (σOf ks ops v.ops)).readRev = W64 (revAfter ks ops v.ops : Int) := by
    simp only [MTxn.readRev, σOf_rev]
  have hrl : (MTxn.read (σOf ks ops v.ops)).readLog = (σOf ks ops v.ops).log := rfl
  have hcs : (MTxn.read (σOf ks ops v.ops)).state.crev = sint.Z (W64 (cmpAfter ks ops v.ops)) := by
    rw [hcZ]; rfl
  ihave HI : (∃ (rr : w64), "r" ∷ r_ptr ↦ rr ∗
      "%Hr" ∷ ⌜max 1 (cmpAfter ks ops v.ops) ≤ sint.Z rr ∧ sint.Z rr ≤ revAfter ks ops v.ops + 1⌝ : IProp GF)
    $$ [r]
  · iexists _; iframe; ipureintro
    have : sint.Z (W64 (max 1 (cmpAfter ks ops v.ops))) = max 1 (cmpAfter ks ops v.ops) := by
      have : cmpAfter ks ops v.ops ≤ revAfter ks ops v.ops := by rw [← hcmpA]; omega
      have : max 1 (cmpAfter ks ops v.ops) ≤ revAfter ks ops v.ops + 1 := by omega
      word
    rw [this]; constructor <;> omega
  wp_for HI
  by_cases Hlt : sint.Z rr ≤ sint.Z (W64 (revAfter ks ops v.ops : Int))
  · rw [decide_eq_true Hlt]; simp only [↓reduceIte]
    (try wp_auto)
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %ksl ⟨Hksl1, -⟩
    (try wp_auto)
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %esl ⟨Hesl1, -⟩
    (try wp_auto)
    imod ownSlice_persist _ _ _ $$ Hksl1 with #Hksl1
    imod ownSlice_persist _ _ _ $$ Hesl1 with #Hesl1
    have hel : List.replicate (go.arrayLiteralSize []).toNat (zero_val w8) = ([] : List w8) := rfl
    rw [hel]
    wp_apply wp_ctxTODO
    (try wp_auto)
    ihave #Hctxr : mvcc.rangeCtx true todoCtxVal
        ({ Values := GMap.empty, Deadline := none, Done_gn := ⟨0, 0⟩, PDone := iprop(True) } :
          context.ContextDesc (IProp GF)) $$ []
    · simp only [mvcc.rangeCtx, ↓reduceIte]; ileft; iapply mvcc.doneNil_todo
    wp_apply (hTRange v.ι.kv trc true (.read (σOf ks ops v.ops)) todoCtxVal _ true _ _ [W8 0] [] _)
        $$ [$Hpm $Htx $Htrco $Hctxr $Hksl1 $Hesl1]
      as %rr' %err ⟨%Hrn, Htx, Htrco, Hout, -, %Hlwf⟩
    rw [hrr, hrl, hcs] at *
    have hLog : txn.LogOk (σOf ks ops v.ops).log :=
      txn.LogOk.of_cert ⟨Hlwf.1, by omega, Hlwf.2⟩ hne
    (try wp_auto)
    ihave Hout : rangeOutcomeC rr' err (σOf ks ops v.ops).log (W64 (revAfter ks ops v.ops : Int))
        (sint.Z (W64 (cmpAfter ks ops v.ops)))
        (decide (slice.mk esl (W64 (go.arrayLiteralSize [])) (W64 (go.arrayLiteralSize [])) = slice.nil))
        [W8 0] []
        { Limit' := 0, Rev' := rr, CountOnly' := false, FastKeysOnly' := false, WithTotalCount' := false }
        $$ [Hout]
    · rw [hcZ]; iexact Hout
    wp_apply (wp_checkRangeAt keys ks DFrac.discard s DFrac.discard ms (Hs'.map Prod.fst)
        (List.replicate Hs'.length DFrac.discard) (W64 (revAfter ks ops v.ops : Int))
        (W64 (cmpAfter ks ops v.ops)) _ [W8 0] [] DFrac.discard DFrac.discard rr' err
        (σOf ks ops v.ops).log Hsorted hLog (by rw [hrZ]; omega) hcurlt hM)
      $$ [$Hpkg $Hpm $Hksl $Hms $HstAt Hout] as -
    · simp only; iframe #; iframe; ipureintro; exact Hrn rfl
    wp_for_post
    iframe
    iexists rr + W64 1
    iframe
    ipureintro
    have : sint.Z rr ≤ revAfter ks ops v.ops := by rw [hrZ] at Hlt; exact Hlt
    constructor <;> word
  · rw [decide_eq_false Hlt]; simp only [Bool.false_eq_true, ↓reduceIte]
    (try wp_auto)
    wp_join with [Htx Htrco Hcmp Hrev states x m tr]
    · have Hif' := Hif
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %ksl ⟨Hksl1, -⟩
      (try wp_auto)
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %esl ⟨Hesl1, -⟩
      (try wp_auto)
      imod ownSlice_persist _ _ _ $$ Hksl1 with #Hksl1
      imod ownSlice_persist _ _ _ $$ Hesl1 with #Hesl1
      have hel : List.replicate (go.arrayLiteralSize []).toNat (zero_val w8) = ([] : List w8) := rfl
      rw [hel]
      wp_apply wp_ctxTODO
      (try wp_auto)
      ihave #Hctxr : mvcc.rangeCtx true todoCtxVal
          ({ Values := GMap.empty, Deadline := none, Done_gn := ⟨0, 0⟩, PDone := iprop(True) } :
            context.ContextDesc (IProp GF)) $$ []
      · simp only [mvcc.rangeCtx, ↓reduceIte]; ileft; iapply mvcc.doneNil_todo
      wp_apply (hTRange v.ι.kv trc true (.read (σOf ks ops v.ops)) todoCtxVal _ true _ _ [W8 0] [] _)
          $$ [$Hpm $Htx $Htrco $Hctxr $Hksl1 $Hesl1]
        as %rr' %err ⟨%Hrn, Htx, Htrco, Hout, -, %Hlwf⟩
      rw [hrr, hrl, hcs] at *
      have hLog : txn.LogOk (σOf ks ops v.ops).log :=
        txn.LogOk.of_cert ⟨Hlwf.1, by omega, Hlwf.2⟩ hne
      (try wp_auto)
      ihave Hout : rangeOutcomeC rr' err (σOf ks ops v.ops).log (W64 (revAfter ks ops v.ops : Int))
          (sint.Z (W64 (cmpAfter ks ops v.ops)))
          (decide (slice.mk esl (W64 (go.arrayLiteralSize [])) (W64 (go.arrayLiteralSize [])) = slice.nil))
          [W8 0] []
          { Limit' := 0, Rev' := W64 (cmpAfter ks ops v.ops) - W64 1, CountOnly' := false, FastKeysOnly' := false, WithTotalCount' := false }
          $$ [Hout]
      · rw [hcZ]; iexact Hout
      wp_apply (wp_checkRangeAt keys ks DFrac.discard s DFrac.discard ms (Hs'.map Prod.fst)
          (List.replicate Hs'.length DFrac.discard) (W64 (revAfter ks ops v.ops : Int))
          (W64 (cmpAfter ks ops v.ops)) _ [W8 0] [] DFrac.discard DFrac.discard rr' err
          (σOf ks ops v.ops).log Hsorted hLog (by rw [hrZ]; omega) hcurlt hM)
        $$ [$Hpkg $Hpm $Hksl $Hms $HstAt Hout] as -
      · simp only; iframe #; iframe; ipureintro; exact Hrn rfl
      (try wp_auto)
      iframe
      ipureintro; rfl
    wp_apply (hTEnd v.ι.kv trc (.read (σOf ks ops v.ops)) 1 (etcdStorage v.bk) iprop(True)
      iprop(True)) $$ [Htx] as ⟨Hr1, -⟩
    · iframe #; iframe
    (try wp_auto)
    iapply HΦ
    iframe
    iunfold memCore
    dsimp only
    rw [hkveq]
    iframe #
    iframe
    isplitr
    · ipureintro; exact Hvops
    isplitl [Hret Hσw Hbw]
    · iunfold incW; iframe; iframe #
    isplitl [Hrdrs Hr1]
    · iapply hR1'.2; iframe
    iframe
    ipureintro; exact HU

end proof

end mvccfull
end EtcdGrove
end Perennial
