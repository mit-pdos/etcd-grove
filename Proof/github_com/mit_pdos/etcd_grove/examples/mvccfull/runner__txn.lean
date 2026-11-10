/- Lean-first (no Rocq counterpart). The proof of `runner.txn`: proved.

The outline: as mvccrand's `writer.txn`, at the incarnation's invariant (`reader_au`-like
updates with the writer's `m.σ` half pinning the state): `KV.Read` (either mode), `Txn.Rev`,
`Txn.FirstRev`, `history.snapshot`, `NewReadOnlyTxnWrite`, `Txn.Range` and `checkRangeAt`, `Txn.End`;
or `begin`, `KV.Write` (the hook, `hookOk`), `checkHook`, `Txn.Rev`, `writeRange`, `writeSub` per
sub-operation (`subsOk` gives each `subFresh`), `Txn.Changes`, `end`. The trace `traceutil.TODO()`
makes (`ownTrace t true`) is lent to `KV.Write` and threaded through `writeRange` and each
`writeSub` (their specs take and give back `ownTrace`), as mvccrand's `writeOp` threads it.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__txn
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__begin
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__checkHook
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__end
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__writeRange
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__writeSub
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.history__snapshot
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.checkRangeAt
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.check
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.TODO
public import Spec.context.TODO
public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.TxnLemmas

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

set_option maxHeartbeats 3200000 in
theorem runner.txn.wp_proof
    (hsh : mvcc.api.shapes.law (GF := GF) (hG := hG))
    (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG))
    (hreach : mvcc.api.mvccState_reachable.law (GF := GF) (hG := hG))
    (hRdSplit : mvcc.api.mvccReaders_split.law (GF := GF))
    (wp_traceTODO : traceutil.TODO.spec (GF := GF) (hG := hG))
    (wp_check : check.spec (GF := GF) (hG := hG))
    (wp_snapshot : history.snapshot.spec (GF := GF) (hG := hG))
    (wp_roTxn : mvcc.api.NewReadOnlyTxnWrite.spec (GF := GF) (hG := hG))
    (wp_ctxTODO : context.TODO.spec (GF := GF) (hG := hG))
    (wp_checkRangeAt : checkRangeAt.spec (GF := GF) (hG := hG))
    (wp_begin : runner.begin.spec (GF := GF) (hG := hG))
    (wp_checkHook : runner.checkHook.spec (GF := GF) (hG := hG))
    (wp_writeRange : runner.writeRange.spec (GF := GF) (hG := hG))
    (wp_writeSub : runner.writeSub.spec (GF := GF) (hG := hG))
    (wp_end : runner.end.spec (GF := GF) (hG := hG)) :
    runner.txn.spec (GF := GF) (hG := hG) := by
  intro x ks cfg wr h γh ops i mp m f v qw nw k p o lead a s hov hkind hlogOk hnw h38 ha hs
  haveI : ∀ N l, Persistent (ctrInv (GF := GF) N l) := by intro N l; unfold ctrInv; infer_instance
  haveI := isInc_persistent hpers
  haveI := hpers.1
  haveI : Persistent (writerCtx (GF := GF) x ks cfg wr h γh) := writerCtx_persistent _ _ _ _ _ _
  wp_start as ⟨#Hctx, Hrd, #Hop, Hc, Hhp, Hlead⟩
  ihave #Hctx2 := Hctx
  iunfold writerCtx at Hctx2
  icases Hctx2 with ⟨#Hrn, -, -, -, -, -, -, -, %Hkeylen, -⟩
  ihave %HksB : ⌜ks.length < 2 ^ 60⌝ $$ []
  · ihave #Hc3 := Hctx
    iunfold writerCtx at Hc3
    icases Hc3 with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, %H⟩
    ipureintro; exact H.2.2
  iunfold rnCtx at Hrn
  icases Hrn with ⟨#Hpkg, #Hpm, #Hkeys, %Hkne, #HrH, -⟩
  ihave #HrH2 := HrH
  iunfold runnerH at HrH2
  ihave #Hkeys2 := Hkeys
  iunfold runnerKeys at Hkeys2
  icases Hkeys2 with ⟨%keys, #Hkeysf, #Hksl, %Hsorted, %Hksne⟩
  iunfold memCore at Hc
  icases Hc with ⟨#Hid, #Hhook, HhookOk, Hpath, Hbe, Hle, Hkv, Hrev, Hcmp, Hleases, %Hvops,
    Hinc, Hopen, Hback, #Hhk, Hrdrs, Hbk, Hles, %HU⟩
  iunfold hookOk at HhookOk
  icases HhookOk with ⟨%Hfnil, #Hhrun⟩
  iunfold incW at Hinc
  icases Hinc with ⟨#Hisinc, Hret, Hσw, Hbw⟩
  ihave #Hmv : isMvcc v.kv v.ι.kv $$ []
  · iunfold isInc at Hisinc; icases Hisinc with ⟨-, #H⟩; iexact H
  ihave %Hkvs := hsh.1 v.kv v.ι.kv $$ Hmv
  obtain ⟨kty, kvv, hkveq, hKR, hKW, -⟩ := Hkvs
  iunfold opIs at Hop
  icases Hop with ⟨%ov, %subs, #Hov, #Hok, #Hoe, #Hoq, #Hosubs, %Hsl, #Hsubs, %Hof⟩
  ihave Hov' := Hov
  iStructNamedSuffix Hov' "O"
  obtain ⟨hk1, hk2, hk3, hk4, hk5, hk6, hk7, hk8, hk9⟩ := Hof
  -- the model
  have hnlt : v.ops < ops.length := (List.getElem?_eq_some_iff.1 hov).1
  obtain ⟨-, hhist, hreachσ⟩ := logOk_hist ks Hsorted ops hlogOk v.ops v.ops (Nat.le_refl _) Hvops
  obtain ⟨-, hhist1, -⟩ := logOk_hist ks Hsorted ops hlogOk (v.ops + 1) (v.ops + 1) (Nat.le_refl _) hnlt
  have honce1 := logOk_once ks Hsorted ops hlogOk (v.ops + 1)
  obtain ⟨hl2, hc1, hcr⟩ := reach_bounds _ hreachσ
  have hhl : 2 ≤ (histAt ks ops v.ops).length ∧ (histAt ks ops v.ops).length ≤ v.ops + 2 :=
    runM_hs_len ks ops v.ops
  have hσl : (σOf ks ops v.ops).log.length = (histAt ks ops v.ops).length := by
    simp [σOf, logOfHist]
  have hrevs : HistRevs ks (σOf ks ops v.ops).log (histAt ks ops v.ops) := by
    have := hhist.2; rwa [σOf_notified] at this
  obtain ⟨hcmp1, hls1, hgr1, hcp1⟩ := txn_fields ks ops v.ops o hov hkind
  have hvalid := hlogOk v.ops o hov
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
  have hne : (σOf ks ops v.ops).log ≠ [] := by
    intro h0; have := congrArg List.length h0; simp only [List.length_nil] at this; omega
  have hR1' : mvccReaders (GF := GF) v.ι.kv nw ⊣⊢
      mvccReaders v.ι.kv (nw - 1) ∗ mvccReaders v.ι.kv 1 := by
    have := hRdSplit v.ι.kv (nw - 1) 1; rwa [Nat.sub_add_cancel hnw] at this
  icases leadPre_lb γh ks ops v.ops lead $$ Hlead with ⟨Hlead, #Hlb⟩
  icases hR1'.1 $$ Hrdrs with ⟨Hrdrs, Hr1⟩
  wp_auto
  by_cases hw : o.write = true
  · have hw' : ov.write' = true := by rw [hk5]; exact hw
    rw [hw']
    simp only [Bool.not_true]
    wp_auto
    -- the shared-buffer read of the compare, if `o.shared`
    rw [hkveq]
    wp_bind (If _ _ _)
    iapply (wp_wand (Φ := fun vv => iprop(⌜vv = executeVal⌝ ∗ mvccReaders v.ι.kv 1 ∗
        ghostVar v.ι.ret qw () ∗ ghostVar m.σ (1 : Qp).half (σOf ks ops v.ops) ∗ histRd h γh ∗
        x_ptr ↦ x ∗ m_ptr ↦ mp ∗ o_ptr ↦ p ∗ cur_ptr ↦ W64 (revAfter ks ops v.ops : Int) ∗
        mF go!"cmp" mp ↦ W64 (cmpAfter ks ops v.ops) ∗ mF go!"kv" mp ↦{DFrac.own qw} interface.mkOk kty kvv)))
      $$ [Hr1 Hret Hσw Hrd x m o cur Hcmp Hkv]
    · cases hsv : ov.shared'
      · wp_auto
        iframe
        ipureintro; rfl
      · wp_auto
        wp_apply wp_traceTODO as %trc ⟨%Htrc, Htrco⟩
        (try wp_auto)
        ihave Hau := read_au hpers ks γh i mp m v.ι (interface.mkOk kty kvv) qw (σOf ks ops v.ops)
          $$ [Hret Hσw]
        · iframe #; iframe
        wp_apply (hKR v.ι.kv (W32 2) trc true (fun σ => iprop(⌜σ = σOf ks ops v.ops⌝ ∗
            ghostVar v.ι.ret qw () ∗ ghostVar m.σ (1 : Qp).half (σOf ks ops v.ops))))
          $$ [Hr1 Htrco Hau] as %tx ⟨Htrco, %σr, Htx, %Hσr, Hret, Hσw⟩
        · iframe #; iframe; ipureintro; exact Htrc
        subst Hσr
        ihave %Htxs := hsh.2.2.1 tx v.ι.kv trc (.read (σOf ks ops v.ops)) $$ Htx
        obtain ⟨tty, tv, htx, hTRev, hTFR, hTRange, -, -, -, hTEnd⟩ := Htxs
        subst htx
        (try wp_auto)
        wp_apply (hTRev v.ι.kv trc (.read (σOf ks ops v.ops))) $$ [Htx] as Htx
        · iframe #; iframe
        (try wp_auto)
        simp only [MTxn.state, σOf_rev, _root_.decide_true]
        (try wp_auto)
        wp_apply (hTFR v.ι.kv trc (.read (σOf ks ops v.ops))) $$ [Htx] as Htx
        · iframe #; iframe
        (try wp_auto)
        wp_apply wp_check
        · ipureintro; simp
        (try wp_auto)
        ihave #Hctxr : mvcc.rangeCtx true todoCtxVal
            ({ Values := GMap.empty, Deadline := none, Done_gn := ⟨0, 0⟩, PDone := iprop(True) } :
              context.ContextDesc (IProp GF)) $$ []
        · simp only [mvcc.rangeCtx, ↓reduceIte]; ileft; iapply mvcc.doneNil_todo
        ihave #Hoq2 := Hoq
        iunfold rangeIs at Hoq2
        icases Hoq2 with ⟨#Hqk, #Hqe, %Hqf⟩
        ihave qO' := qO
        iStructNamedSuffix qO' "Q"
        wp_apply wp_ctxTODO
        (try wp_auto)
        wp_apply (hTRange v.ι.kv trc true (.read (σOf ks ops v.ops)) todoCtxVal _ true _ _ o.q.key o.q.e _)
            $$ [$Hpm $Htx $Htrco $Hctxr $Hqk $Hqe]
          as %rr' %err ⟨%Hrn, Htx, Htrco, Hout, -, %Hlwf⟩
        have hrr : (MTxn.read (σOf ks ops v.ops)).readRev = W64 (revAfter ks ops v.ops : Int) := by
          simp only [MTxn.readRev, σOf_rev]
        have hrl : (MTxn.read (σOf ks ops v.ops)).readLog = (σOf ks ops v.ops).log := rfl
        have hcs : (MTxn.read (σOf ks ops v.ops)).state.crev = sint.Z (W64 (cmpAfter ks ops v.ops)) := by
          rw [hcZ]; rfl
        rw [hrl] at Hlwf
        (try rw [hrr]); (try rw [hrl]); (try rw [hcs])
        have hLog : txn.LogOk (σOf ks ops v.ops).log :=
          txn.LogOk.of_cert ⟨Hlwf.1, by omega, Hlwf.2⟩ hne
        (try wp_auto)
        wp_apply wp_snapshot h γh (histAt ks ops v.ops) $$ [$Hrd $Hlb]
          as %sl ⟨Hrd, %ms, %Hs', ⟨%Hpre, %H2⟩, %Hscap, #Hlb', #Hms, #Hst⟩
        ihave %Hmlen : ⌜ms.length = Hs'.length⌝ $$ [Hst]
        · iunfold statesP at Hst; icases Hst with ⟨%H, -⟩; ipureintro; exact H
        ihave #HstAt := txn_statesAt_hist ms Hs' $$ Hst
        have hmatch := txn_hist_match ks Hsorted ops hlogOk v.ops Hvops Hs' Hpre
        have hcurlt : sint.nat (W64 (revAfter ks ops v.ops : Int)) < ms.length := by
          have : sint.nat (W64 (revAfter ks ops v.ops : Int)) =
              (sint.Z (W64 (revAfter ks ops v.ops : Int))).toNat := rfl
          rw [this, hrZ]
          have : (σOf ks ops v.ops).rev = (σOf ks ops v.ops).log.length - 1 := rfl
          have := Hpre.length_le
          omega
        have hM : ∀ r : Nat, sint.Z (W64 (cmpAfter ks ops v.ops)) ≤ (r : Int) →
            r ≤ sint.nat (W64 (revAfter ks ops v.ops : Int)) →
            ∃ M, (Hs'.map Prod.fst)[r]? = some M ∧ stMatch ks M (stateAt (σOf ks ops v.ops).log r) := by
          intro r _ hr
          have : sint.nat (W64 (revAfter ks ops v.ops : Int)) =
              (sint.Z (W64 (revAfter ks ops v.ops : Int))).toNat := rfl
          rw [this, hrZ] at hr
          have : (σOf ks ops v.ops).rev = (σOf ks ops v.ops).log.length - 1 := rfl
          exact hmatch r (by omega)
        (try wp_auto)
        wp_apply (wp_checkRangeAt keys ks DFrac.discard sl DFrac.discard ms (Hs'.map Prod.fst)
            (List.replicate Hs'.length DFrac.discard) (W64 (revAfter ks ops v.ops : Int))
            (W64 (cmpAfter ks ops v.ops)) ov.q' o.q.key o.q.e DFrac.discard DFrac.discard rr' err
            (σOf ks ops v.ops).log Hsorted hLog (by rw [hrZ]; omega) hcurlt hM)
          $$ [$Hpkg $Hpm $Hksl $Hms $HstAt Hout] as -
        · iframe Hqk Hqe
          isplitr
          · ipureintro; exact Hrn rfl
          rw [hcZ]; iexact Hout
        (try wp_auto)
        wp_apply (end_readT hTEnd v.ι.kv trc (σOf ks ops v.ops)) $$ [Htx] as Hr1
        · iframe #; iframe
        (try wp_auto)
        iframe
        try (ipureintro; rfl)
    iintro %vv ⟨%hvv, Hr1, Hret, Hσw, Hrd, x, m, o, cur, Hcmp, Hkv⟩
    subst hvv
    wp_auto
    -- `p := x.begin(m)`
    have hrw : (revAfter ks ops v.ops : Int) = ((σOf ks ops v.ops).rev : Int) := by rw [σOf_rev]
    rw [hrw]
    ihave Hinc : incW ks γh i mp m v.ι (interface.mkOk kty kvv) qw (σOf ks ops v.ops) v.b
      $$ [Hret Hσw Hbw]
    · iunfold incW; iframe; iframe #
    wp_apply (wp_begin x ks h γh i mp m v.ι (interface.mkOk kty kvv) qw (σOf ks ops v.ops) v.b
        (histAt ks ops v.ops) hσl.symm rfl (by omega)) $$ [$HrH $Hrd $Hlb $Hrev $Hinc]
      as %pp ⟨Hrd, Hrev, Hinc, Hp⟩
    (try wp_auto)
    -- `tw := m.kv.Write(…)`: the hook runs at `i`
    wp_apply wp_traceTODO as %trc2 ⟨%Htr2, Htrc2⟩
    (try wp_auto)
    iunfold incW at Hinc
    icases Hinc with ⟨-, Hret, Hσw, Hbw⟩
    ihave Hau := write_au hpers ks γh i mp m v.ι (interface.mkOk kty kvv) qw (σOf ks ops v.ops) rfl
      $$ [Hret Hσw]
    · iframe #; iframe
    wp_apply (hKW v.ι.kv trc2 true 1 (etcdStorage v.bk) iprop(True) (hookPre mp a s)
        iprop(True ∗ hookPost mp a) f
        (fun σ' => iprop(⌜σ' = σOf ks ops v.ops⌝ ∗ ghostVar v.ι.ret qw () ∗
          ghostVar m.σ (1 : Qp).half (σOf ks ops v.ops))))
      $$ [Hr1 Htrc2 Hback Hhp Hau] as %tw ⟨Htrc2, Hback, ⟨%σ0, Htw, %Hσ0, Hret, Hσw⟩, -, Hpost⟩
    · iframe #; iframe
      isplitr
      · ipureintro; exact Htr2
      iapply Hhrun
    subst Hσ0
    icases (persistent_entails_right (hsh.2.2.1 tw v.ι.kv trc2 (.write (σOf ks ops v.ops) [])))
      $$ Htw with ⟨%Hsht2, Htw⟩
    obtain ⟨tty, tv, rfl, hRevW, -, -, -, -, hChW, hEndW⟩ := Hsht2
    (try wp_auto)
    iunfold hookPost at Hpost
    icases Hpost with ⟨Happ, Hsav⟩
    wp_apply wp_checkHook x mp a $$ [Hsav] as Hsav
    · iframe #; iframe
    (try wp_auto)
    wp_apply (hRevW v.ι.kv trc2 (.write (σOf ks ops v.ops) [])) $$ [Htw] as Htw
    · iframe #; iframe
    (try wp_auto)
    wp_apply wp_check
    · ipureintro; simp only [MTxn.state, _root_.decide_true]
    (try wp_auto)
    -- the model of the transaction so far
    ihave %Hksll := ownSlice_len $$ Hksl
    have hkl : ks.length < 2 ^ 63 := by
      have : sint.nat keys.len = (sint.Z keys.len).toNat := rfl
      have h2 : sint.Z keys.len < 2 ^ 63 := by word
      have := Hksll.1; omega
    have hok0 := txn_pendOk0 ks (σOf ks ops v.ops) (histAt ks ops v.ops) hσl.symm (by omega) hrevs
    have hLog0 := txn_logOk0 ks Hsorted ops hlogOk v.ops hkl (by omega)
    have h63 : (σOf ks ops v.ops).log.length + 3 ≤ 2 ^ 63 := by omega
    -- the compare in the write transaction, if not `o.shared`
    rw [← hcmpA]
    wp_bind (If _ _ _)
    iapply (wp_wand (Φ := fun vv => iprop(⌜vv = executeVal⌝ ∗ histRd h γh ∗
        mF go!"cmp" mp ↦ W64 (σOf ks ops v.ops).crev ∗
        mvccTxn (interface.mkOk tty tv) v.ι.kv trc2 (.write (σOf ks ops v.ops) []) ∗
        traceutil.ownTrace trc2 true ∗ ownPending pp (txnP0 (histAt ks ops v.ops)) ∗
        x_ptr ↦ x ∗ m_ptr ↦ mp ∗ o_ptr ↦ p ∗ tw_ptr ↦ interface.mkOk tty tv ∗ p_ptr ↦ pp)))
      $$ [Hrd Hcmp Htw Htrc2 Hp x m o tw p]
    · cases hsv : ov.shared'
      · wp_auto
        wp_apply (wp_writeRange x ks h γh mp v.ι.kv (interface.mkOk tty tv) trc2 true
            (σOf ks ops v.ops) [] (histAt ks ops v.ops) pp (txnP0 (histAt ks ops v.ops)) ov.q' o.q
            hok0 hσl.symm hrevs hreachσ hLog0 h63)
          $$ [$Hpm $Hkeys $HrH $Hrd $Hlb $Hcmp $Htw $Htrc2 $Hp $Hoq] as ⟨Hrd, Hcmp, Htw, Htrc2, Hp⟩
        (try wp_auto)
        iframe
        try (ipureintro; rfl)
      · wp_auto
        iframe
        try (ipureintro; rfl)
    iintro %vv ⟨%hvv, Hrd, Hcmp, Htw, Htrc2, Hp, x, m, o, tw, p⟩
    subst hvv
    wp_auto
    -- the sub-operations
    iunfold lessorW at Hles
    icases Hles with ⟨%rd, %r, Hl1, Hl2, Hl3, Hl4, Hl5, Hl6, Hl7, Hlo, Hl9, Hl10, Hl11, Hl12, Hl13,
      Hl14, Hl15, %Hl16, Hl17⟩
    ihave %Hsubl := ownSlice_len $$ Hosubs
    ihave HI : (∃ (j : w64) (sv0 : subOp) (pend : List Change), "Hi" ∷ i_ptr ↦ j ∗
        "Hs" ∷ s_ptr ↦ sv0 ∗
        "Htw" ∷ mvccTxn (interface.mkOk tty tv) v.ι.kv trc2 (.write (σOf ks ops v.ops) pend) ∗
        "Htrc2" ∷ traceutil.ownTrace trc2 true ∗
        "Hp" ∷ ownPending pp ((o.subs.take (sint.nat j)).foldl (subStep ks) (txnP0 (histAt ks ops v.ops))) ∗
        "Hlo" ∷ lease.leaseOwn (mvccLeases v.ι.kv) (leasesAfter ks ops v.ops)
          (pendItems (σOf ks ops v.ops).log pend) ∗
        "Hrd" ∷ histRd h γh ∗ "Hcmp" ∷ mF go!"cmp" mp ↦ W64 (σOf ks ops v.ops).crev ∗
        "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ subs.length ∧
          pendOk ks (σOf ks ops v.ops) (histAt ks ops v.ops) pend
            ((o.subs.take (sint.nat j)).foldl (subStep ks) (txnP0 (histAt ks ops v.ops))) ∧
          txn.LogOk ((σOf ks ops v.ops).log ++ [pend])⌝ : IProp GF)
      $$ [i s Htw Htrc2 Hp Hlo Hrd Hcmp]
    · iexists W64 0, _, []
      simp only [named]
      iframe
      ipureintro
      have h00 : sint.Z (W64 0) = 0 := by decide
      refine ⟨by omega, by omega, ?_, hLog0⟩
      have : sint.nat (W64 0) = 0 := by decide
      rw [this]; exact hok0
    wp_for HI
    wp_if_destruct
    · have Hlt : sint.nat j < subs.length := by word
      obtain ⟨sv, Hsv⟩ : ∃ x, subs[sint.nat j]? = some x := ⟨_, List.getElem?_eq_getElem Hlt⟩
      obtain ⟨sm, Hsm⟩ : ∃ x, o.subs[sint.nat j]? = some x :=
        ⟨_, List.getElem?_eq_getElem (by omega)⟩
      have Hbnd : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z ov.subs'.len := ⟨Hj.1, Hif⟩
      rw [ite_eq_left Hbnd]
      icases ownSlice_elem_acc (sint.Z j) sv ov.subs' DFrac.discard subs Hj.1 Hsv $$ Hosubs
        with ⟨#Hel, -⟩
      have hz : (subs.zip o.subs)[sint.nat j]? = some (sv, sm) := by
        simp [List.getElem?_zip_eq_some, Hsv, Hsm]
      ihave #Hsub := (BigSepL.bigSepL_lookup (Φ := fun _ x => subIs (GF := GF) x.1 x.2) hz) $$ Hsubs
      obtain ⟨hfresh, hput, hchl⟩ := txn_sub_facts ks Hsorted ops hlogOk v.ops o hov hkind hw
        (sint.nat j) sm Hsm
      obtain ⟨hj0, hj1, hokj, hLogj⟩ := Hj
      have hpl : pend.length + ks.length < 2 ^ 62 := by
        have h1 := pendOk_chs_length hokj
        have hks61 : ks.length < 2 ^ 61 := by omega
        omega
      (try wp_auto)
      wp_apply (wp_writeSub x ks h γh mp v.ι.kv (interface.mkOk tty tv) trc2 true (σOf ks ops v.ops)
          pend (histAt ks ops v.ops) pp _ sv sm (leasesAfter ks ops v.ops) hokj hσl.symm hrevs hreachσ
          hLogj h63 hpl hfresh hput Hkeylen) $$ [$Hpm $Hkeys $HrH $Hrd $Hlb $Hcmp $Htw $Htrc2 $Hp $Hsub $Hlo]
        as ⟨Hrd, Hcmp, %pend', %Hpo, Htw, Htrc2, Hp, Hlo⟩
      wp_for_post
      iframe
      iexists j + W64 1, sv, pend ++ pend'
      have hjs : sint.nat (j + W64 1) = sint.nat j + 1 := by word
      rw [hjs, foldl_take_succ ks o.subs _ (sint.nat j) sm Hsm]
      simp only [named]
      iframe
      ipureintro
      exact ⟨by word, by word, Hpo.1, Hpo.2.1⟩
    · -- the changes' check, then `end`
      obtain ⟨hj0, hj1, hokj, hLogj⟩ := Hj
      have hjl : sint.nat j = o.subs.length := by
        have : ¬ sint.Z j < sint.Z ov.subs'.len := Hif
        rw [← Hsl]; word
      rw [hjl, List.take_of_length_le (Nat.le_refl _)] at hokj ⊢
      have hPfin : o.subs.foldl (subStep ks) (txnP0 (histAt ks ops v.ops)) =
          opPend ks (runM ks ops v.ops) o := by
        rw [txn_opPend ks _ o hkind]; simp [hw]
      rw [hPfin] at hokj ⊢
      wp_apply (hChW v.ι.kv trc2 (.write (σOf ks ops v.ops) pend)) $$ [Htw] as %chs ⟨Htw, %Hchs⟩
      · iframe #; iframe
      iunfold ownPending at Hp
      icases Hp with ⟨%pv, Hpv, %Hprev, Hpst, Hpch, Hpcap⟩
      ihave %Hcl := ownSlice_len $$ Hpch
      have hcl' := pendOk_chs_length hokj
      (try wp_auto)
      wp_apply wp_check
      · ipureintro
        simp only [MTxn.pend] at Hchs
        have h1 : sint.Z chs.len = (pend.length : Int) := by
          obtain ⟨ha, hb⟩ := Hchs; word
        have h2 : sint.Z pv.changes'.len = (pend.length : Int) := by
          have : sint.nat pv.changes'.len = (sint.Z pv.changes'.len).toNat := rfl
          omega
        simp only [decide_eq_true_eq]; rw [h1, h2]
      (try wp_auto)
      ihave Hp : ownPending pp (opPend ks (runM ks ops v.ops) o) $$ [Hpv Hpst Hpch Hpcap]
      · iunfold ownPending; iexists pv; iframe; ipureintro; exact Hprev
      -- the model after the transaction
      obtain ⟨hσ1, hh1⟩ := σOf_succ_commit ks ops v.ops o hov pend hokj hcmp1
      have hhC : histOkM ks (commitSt (σOf ks ops v.ops) pend)
          (histAfter (histAt ks ops v.ops) (opPend ks (runM ks ops v.ops) o)) := by
        rw [← hσ1, ← hh1]; exact hhist1
      have honceC : onceUpToAll (commitSt (σOf ks ops v.ops) pend).log := by
        rw [← hσ1]; exact honce1
      have hbC : ((commitSt (σOf ks ops v.ops) pend).rev : Int) ≤
          sint.Z (W64 ((σOf ks ops v.ops).rev + 1 : Int)) := by
        have := commitSt_rev_le (σOf ks ops v.ops) pend (by omega)
        have : ((σOf ks ops v.ops).rev : Int) + 1 < 2 ^ 63 := by omega
        rw [show sint.Z (W64 ((σOf ks ops v.ops).rev + 1 : Int)) = ((σOf ks ops v.ops).rev : Int) + 1
          by word]
        omega
      let b1 : Bnd := (v.b.1, W64 ((σOf ks ops v.ops).rev + 1 : Int), v.b.2.2)
      ihave Hcb := endCb_txnEnd hpers hEndW ks γh i mp m v.ι (interface.mkOk kty kvv) qw
        (σOf ks ops v.ops) b1 pend (histAfter (histAt ks ops v.ops) (opPend ks (runM ks ops v.ops) o))
        trc2 1 (etcdStorage v.bk) rfl hhC honceC hbC
      ihave #Hctx3 := Hctx
      iunfold writerCtx at Hctx3
      icases Hctx3 with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, #Hcrevs, -⟩
      ihave Hinc : incW ks γh i mp m v.ι (interface.mkOk kty kvv) qw (σOf ks ops v.ops) b1
        $$ [Hret Hσw Hbw]
      · iunfold incW; iframe; iframe #
      ihave Hlead' : (if lead then histW γh (histAt ks ops v.ops) (compsAt ks ops v.ops)
          else monoListLbOwn γh.l
            (histAfter (histAt ks ops v.ops) (opPend ks (runM ks ops v.ops) o)) : IProp GF) $$ [Hlead]
      · unfold leadPre; rw [← hh1]; iexact Hlead
      wp_apply (wp_end x ks h γh i mp m v.ι (interface.mkOk kty kvv) qw (σOf ks ops v.ops) b1
          (histAt ks ops v.ops) (compsAt ks ops v.ops) pp (opPend ks (runM ks ops v.ops) o) pend
          (methods tty go!"End" tv)
          iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
            mvccTxn (interface.mkOk tty tv) v.ι.kv trc2 (.write (σOf ks ops v.ops) pend) ∗
            mvccBackend v.ι.kv 1 (etcdStorage v.bk) iprop(True))
          (mvccBackend v.ι.kv 1 (etcdStorage v.bk) iprop(True)) lead hokj hσl.symm rfl
          (by show sint.Z (W64 ((σOf ks ops v.ops).rev + 1 : Int)) = _; word) (by omega))
        $$ [$Hpm $HrH $Hcrevs $Hrd $Hrev $Hkv $Hinc $Hp $Hlead' $Hcb $Htw $Hback]
        as ⟨Hrd, Hrev, Hkv, Hinc, Hr1, Hback, Hlead⟩
      have hrev1 : revAfter ks ops (v.ops + 1) = (commitSt (σOf ks ops v.ops) pend).rev := by
        rw [← σOf_rev, hσ1]
      ihave HhookOk : hookOk mp f $$ []
      · iunfold hookOk; iframe #; ipureintro; exact Hfnil
      ihave Hrdrs : mvccReaders v.ι.kv nw $$ [Hrdrs Hr1]
      · iapply hR1'.2; iframe
      ihave Hles : lessorW v.ι.kv v.bk f v.lp (leasesAfter ks ops v.ops) v.U
          (commitSt (σOf ks ops v.ops) pend)
        $$ [Hl1 Hl2 Hl3 Hl4 Hl5 Hl6 Hl7 Hlo Hl9 Hl10 Hl11 Hl12 Hl13 Hl14 Hl15 Hl17]
      · iunfold lessorW; iexists rd, r; rw [pendItems_commit]; iframe; ipureintro; exact Hl16
      iapply HΦ
      isplitl [Hrd]
      · iexact Hrd
      isplitl [Hlead]
      · unfold leadPost
        cases lead
        · simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
        · simp only [↓reduceIte]; rw [hh1, hcp1]; iexact Hlead
      isplitl [Happ Hsav]
      · ileft; iunfold hookPost; iframe
      let b2 : Bnd := (W64 ((commitSt (σOf ks ops v.ops) pend).rev : Int),
          W64 ((commitSt (σOf ks ops v.ops) pend).rev : Int), v.b.2.2)
      iexists ⟨v.path, v.lp, v.kv, v.ops + 1, v.bk, v.ι, v.U, b2⟩
      isplitr
      · ipureintro; exact ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, rfl⟩
      iunfold memCore
      dsimp only
      rw [hσ1, hrev1, hcmp1, hls1, hgr1, hkveq]
      iframe #
      iframe
      ipureintro; exact ⟨by omega, HU⟩
  · -- read-only: a concurrent read transaction made a read-only write one
    have hw' : ov.write' = false := by rw [hk5]; simpa using hw
    rw [hw']
    simp only [Bool.not_false]
    wp_auto
    wp_apply wp_traceTODO as %trc ⟨%Htrc, Htrco⟩
    (try wp_auto)
    ihave Hau := read_au hpers ks γh i mp m v.ι v.kv qw (σOf ks ops v.ops) $$ [Hret Hσw]
    · iframe #; iframe
    rw [hkveq]
    wp_apply (hKR v.ι.kv (W32 1) trc true (fun σ => iprop(⌜σ = σOf ks ops v.ops⌝ ∗
        ghostVar v.ι.ret qw () ∗ ghostVar m.σ (1 : Qp).half (σOf ks ops v.ops))))
      $$ [Hr1 Htrco Hau] as %tx ⟨Htrco, %σr, Htx, %Hσr, Hret, Hσw⟩
    · iframe #; iframe; ipureintro; exact Htrc
    subst Hσr
    ihave %Htxs := hsh.2.2.1 tx v.ι.kv trc (.read (σOf ks ops v.ops)) $$ Htx
    obtain ⟨tty, tv, htx, hTRev, hTFR, -, -, -, -, -⟩ := Htxs
    subst htx
    (try wp_auto)
    wp_apply (hTRev v.ι.kv trc (.read (σOf ks ops v.ops))) $$ [Htx] as Htx
    · iframe #; iframe
    (try wp_auto)
    simp only [MTxn.state, σOf_rev, _root_.decide_true]
    (try wp_auto)
    wp_apply (hTFR v.ι.kv trc (.read (σOf ks ops v.ops))) $$ [Htx] as Htx
    · iframe #; iframe
    (try wp_auto)
    wp_apply wp_check
    · ipureintro; simp
    (try wp_auto)
    -- `states := x.h.snapshot()`
    wp_apply wp_snapshot h γh (histAt ks ops v.ops) $$ [$Hrd $Hlb]
      as %sl ⟨Hrd, %ms, %Hs', ⟨%Hpre, %H2⟩, %Hscap, #Hlb', #Hms, #Hst⟩
    ihave %Hmlen : ⌜ms.length = Hs'.length⌝ $$ [Hst]
    · iunfold statesP at Hst; icases Hst with ⟨%H, -⟩; ipureintro; exact H
    ihave #HstAt := txn_statesAt_hist ms Hs' $$ Hst
    have hmatch := txn_hist_match ks Hsorted ops hlogOk v.ops Hvops Hs' Hpre
    (try wp_auto)
    wp_apply (wp_roTxn _ v.ι.kv trc (σOf ks ops v.ops)) $$ [Htx] as %t1 Htx
    · iframe #; iframe
    icases (persistent_entails_right (hsh.2.2.1 t1 v.ι.kv trc (.read (σOf ks ops v.ops)))) $$ Htx
      with ⟨%Hsh1, Htx⟩
    obtain ⟨ty1, v1, rfl, hRev1, -, hRange1, -, -, hCh1, hEnd1⟩ := Hsh1
    (try wp_auto)
    have hcurlt : sint.nat (W64 (revAfter ks ops v.ops : Int)) < ms.length := by
      have : sint.nat (W64 (revAfter ks ops v.ops : Int)) =
          (sint.Z (W64 (revAfter ks ops v.ops : Int))).toNat := rfl
      rw [this, hrZ]
      have : (σOf ks ops v.ops).rev = (σOf ks ops v.ops).log.length - 1 := rfl
      have := Hpre.length_le
      omega
    have hM : ∀ r : Nat, sint.Z (W64 (cmpAfter ks ops v.ops)) ≤ (r : Int) →
        r ≤ sint.nat (W64 (revAfter ks ops v.ops : Int)) →
        ∃ M, (Hs'.map Prod.fst)[r]? = some M ∧ stMatch ks M (stateAt (σOf ks ops v.ops).log r) := by
      intro r _ hr
      have : sint.nat (W64 (revAfter ks ops v.ops : Int)) =
          (sint.Z (W64 (revAfter ks ops v.ops : Int))).toNat := rfl
      rw [this, hrZ] at hr
      have : (σOf ks ops v.ops).rev = (σOf ks ops v.ops).log.length - 1 := rfl
      exact hmatch r (by omega)
    have hrr : (MTxn.read (σOf ks ops v.ops)).readRev = W64 (revAfter ks ops v.ops : Int) := by
      simp only [MTxn.readRev, σOf_rev]
    have hrl : (MTxn.read (σOf ks ops v.ops)).readLog = (σOf ks ops v.ops).log := rfl
    have hcs : (MTxn.read (σOf ks ops v.ops)).state.crev = sint.Z (W64 (cmpAfter ks ops v.ops)) := by
      rw [hcZ]; rfl
    ihave #Hctxr : mvcc.rangeCtx true todoCtxVal
        ({ Values := GMap.empty, Deadline := none, Done_gn := ⟨0, 0⟩, PDone := iprop(True) } :
          context.ContextDesc (IProp GF)) $$ []
    · simp only [mvcc.rangeCtx, ↓reduceIte]; ileft; iapply mvcc.doneNil_todo
    iunfold rangeIs at Hoq
    icases Hoq with ⟨#Hqk, #Hqe, %Hqf⟩
    ihave qO' := qO
    iStructNamedSuffix qO' "Q"
    wp_apply wp_ctxTODO
    (try wp_auto)
    wp_apply (hRange1 v.ι.kv trc true (.read (σOf ks ops v.ops)) todoCtxVal _ true _ _ o.q.key o.q.e _)
        $$ [$Hpm $Htx $Htrco $Hctxr $Hqk $Hqe]
      as %rr' %err ⟨%Hrn, Htx, Htrco, Hout, -, %Hlwf⟩
    rw [hrl] at Hlwf
    (try rw [hrr]); (try rw [hrl]); (try rw [hcs])
    have hLog : txn.LogOk (σOf ks ops v.ops).log :=
      txn.LogOk.of_cert ⟨Hlwf.1, by omega, Hlwf.2⟩ hne
    (try wp_auto)
    wp_apply (wp_checkRangeAt keys ks DFrac.discard sl DFrac.discard ms (Hs'.map Prod.fst)
        (List.replicate Hs'.length DFrac.discard) (W64 (revAfter ks ops v.ops : Int))
        (W64 (cmpAfter ks ops v.ops)) ov.q' o.q.key o.q.e DFrac.discard DFrac.discard rr' err
        (σOf ks ops v.ops).log Hsorted hLog (by rw [hrZ]; omega) hcurlt hM)
      $$ [$Hpkg $Hpm $Hksl $Hms $HstAt Hout] as -
    · iframe Hqk Hqe
      isplitr
      · ipureintro; exact Hrn rfl
      rw [hcZ]; iexact Hout
    (try wp_auto)
    -- the sub-operations' ranges
    ihave %Hsubl := ownSlice_len $$ Hosubs
    ihave HI : (∃ (j : w64) (sv0 : subOp), "Hi" ∷ i_ptr ↦ j ∗ "Hs" ∷ s_ptr ↦ sv0 ∗
        "Htx" ∷ mvccTxn (interface.mkOk ty1 v1) v.ι.kv trc (.read (σOf ks ops v.ops)) ∗
        "Htrco" ∷ traceutil.ownTrace trc true ∗
        "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ subs.length⌝ : IProp GF) $$ [i s Htx Htrco]
    · iexists W64 0, _
      simp only [named]
      iframe
      ipureintro
      have : sint.Z (W64 0) = 0 := by decide
      constructor <;> omega
    wp_for HI
    wp_if_destruct
    · have Hlt : sint.nat j < subs.length := by word
      obtain ⟨sv, Hsv⟩ : ∃ x, subs[sint.nat j]? = some x := ⟨_, List.getElem?_eq_getElem Hlt⟩
      obtain ⟨sm, Hsm⟩ : ∃ x, o.subs[sint.nat j]? = some x :=
        ⟨_, List.getElem?_eq_getElem (by omega)⟩
      have Hbnd : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z ov.subs'.len := ⟨Hj.1, Hif⟩
      rw [ite_eq_left Hbnd]
      icases ownSlice_elem_acc (sint.Z j) sv ov.subs' DFrac.discard subs Hj.1 Hsv $$ Hosubs
        with ⟨#Hel, -⟩
      have hz : (subs.zip o.subs)[sint.nat j]? = some (sv, sm) := by
        simp [List.getElem?_zip_eq_some, Hsv, Hsm]
      ihave #Hsub := (BigSepL.bigSepL_lookup (Φ := fun _ x => subIs (GF := GF) x.1 x.2) hz) $$ Hsubs
      iunfold subIs at Hsub
      icases Hsub with ⟨-, -, #Hsq, -⟩
      iunfold rangeIs at Hsq
      icases Hsq with ⟨#Hsqk, #Hsqe, -⟩
      (try wp_auto)
      wp_apply wp_ctxTODO
      (try wp_auto)
      wp_apply (hRange1 v.ι.kv trc true (.read (σOf ks ops v.ops)) todoCtxVal _ true _ _ sm.q.key sm.q.e _)
          $$ [$Hpm $Htx $Htrco $Hctxr $Hsqk $Hsqe]
        as %rr2 %err2 ⟨%Hrn2, Htx, Htrco, Hout2, -, -⟩
      (try rw [hrr]); (try rw [hrl]); (try rw [hcs])
      (try wp_auto)
      wp_apply (wp_checkRangeAt keys ks DFrac.discard sl DFrac.discard ms (Hs'.map Prod.fst)
          (List.replicate Hs'.length DFrac.discard) (W64 (revAfter ks ops v.ops : Int))
          (W64 (cmpAfter ks ops v.ops)) sv.q' sm.q.key sm.q.e DFrac.discard DFrac.discard rr2 err2
          (σOf ks ops v.ops).log Hsorted hLog (by rw [hrZ]; omega) hcurlt hM)
        $$ [$Hpkg $Hpm $Hksl $Hms $HstAt Hout2] as -
      · iframe Hsqk Hsqe
        isplitr
        · ipureintro; exact Hrn2 rfl
        rw [hcZ]; iexact Hout2
      wp_for_post
      iframe
      iexists j + W64 1, sv
      simp only [named]
      iframe
      ipureintro; constructor <;> word
    · -- the read-only transaction's checks; `End`
      wp_apply (hRev1 v.ι.kv trc (.read (σOf ks ops v.ops))) $$ [Htx] as Htx
      · iframe #; iframe
      (try wp_auto)
      simp only [MTxn.state, σOf_rev, _root_.decide_true]
      (try wp_auto)
      wp_apply (hCh1 v.ι.kv trc (.read (σOf ks ops v.ops))) $$ [Htx] as %chs ⟨Htx, %Hchs⟩
      · iframe #; iframe
      (try wp_auto)
      wp_apply wp_check
      · ipureintro; simp only [decide_eq_true_eq]
        simp only [MTxn.pend, List.length_nil] at Hchs
        word
      (try wp_auto)
      wp_apply (end_readT hEnd1 v.ι.kv trc (σOf ks ops v.ops)) $$ [Htx] as Hr1
      · iframe #; iframe
      (try wp_auto)
      -- the model: nothing changed
      have hP0 : opPend ks (runM ks ops v.ops) o = txnP0 (histAt ks ops v.ops) := by
        rw [txn_opPend ks _ o hkind]; simp [hw]
      have hpend0 := txn_pendOk0 ks (σOf ks ops v.ops) (histAt ks ops v.ops) hσl.symm (by omega) hrevs
      obtain ⟨hσ1, hh1⟩ := σOf_succ_commit ks ops v.ops o hov [] (by rw [hP0]; exact hpend0) hcmp1
      rw [commitSt_nil _ rfl] at hσ1
      rw [hP0] at hh1
      have hh1' : histAt ks ops (v.ops + 1) = histAt ks ops v.ops := by
        rw [hh1]; unfold histAfter; simp
      have hrev1 : revAfter ks ops (v.ops + 1) = revAfter ks ops v.ops := by
        rw [← σOf_rev, hσ1, σOf_rev]
      ihave HhookOk : hookOk mp f $$ []
      · iunfold hookOk; iframe #; ipureintro; exact Hfnil
      ihave Hinc : incW ks γh i mp m v.ι (interface.mkOk kty kvv) qw (σOf ks ops v.ops) v.b $$ [Hret Hσw Hbw]
      · iunfold incW; iframe; iframe #
      ihave Hrdrs : mvccReaders v.ι.kv nw $$ [Hrdrs Hr1]
      · iapply hR1'.2; iframe
      iapply HΦ
      isplitl [Hrd]
      · iexact Hrd
      isplitl [Hlead]
      · unfold leadPost leadPre
        cases lead
        · simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
        · simp only [↓reduceIte]; rw [hh1', hcp1]; iexact Hlead
      isplitl [Hhp]
      · iright; iexact Hhp
      iexists { v with ops := v.ops + 1 }
      isplitr
      · ipureintro; exact ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, rfl⟩
      iunfold memCore
      dsimp only
      rw [hσ1, hrev1, hcmp1, hls1, hgr1]
      rw [hkveq]
      iframe #
      iframe
      ipureintro; exact ⟨by omega, HU⟩

end proof

end mvccfull
end EtcdGrove
end Perennial
