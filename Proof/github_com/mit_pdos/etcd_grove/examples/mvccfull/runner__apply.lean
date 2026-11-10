/- Lean-first (no Rocq counterpart). The proof of `runner.apply`: Draft, to come.

The outline: `m.ops++`, `applying.Store(i)` (the hook's counters, `memW`); by `o.kind`
(`opIs`): a put or a delete is `begin`, `m.kv.Write` (`KV.Write.contract` through `shapes.law`, the
hook at `i`: `hookOk`), `checkHook`, `Rev`, `writeRange` of the key's previous value, the put
(`pending.put`, `Txn.Put.contract`) or `writeSub` of the delete, and `end` at `tw.End` (`endCb` from
`Txn.End.contract` at the incarnation's invariant, `memberInv_live`); `txn`; a grant is
`lessor.Grant` (the lessor's contract at the member's backend, `lessorW_backend`; `csContractA` at
the hook), `checkHook`, the leases' slice appended, `Rev` unchanged; a revoke is `begin`, the keys on the lease (`onLease`), `end` at the
closure calling `lessor.Revoke` (its update through the range deleter, `mvccDeleter`), `checkHook`,
the slice filtered, `Lookup` nil; `compact`; `Commit` (`KV.Commit.contract`); a read (`KV.Read`,
`Txn.Rev`, `Txn.FirstRev`, `Txn.Range`, `history.snapshot`, `checkRangeAt`, `Txn.End`);
`checkLeases`. The model's step is `runM_succ`; the lease bucket's records (`leaseRecsOk`) follow
`Grant`'s `rbSet` and `Revoke`'s `rbDel`. The put's and the delete's trace (`traceutil.TODO()`,
`ownTrace t true`) is threaded through `writeRange`, `Txn.Put` and `writeSub`, whose specs take
and give it back.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__apply
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__begin
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__checkHook
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__writeRange
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.pending__put
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__end
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__writeSub
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__txn
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__compact
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.history__snapshot
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.checkRangeAt
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.runner__checkLeases
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccfull.check
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.TODO
public import Spec.context.TODO
public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__Grant
public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__Revoke
public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__Lookup
public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.WriterLemmas
public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.ApplyLemmas
public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.LeaseRecLemmas
public import Perennial.Spec.sync.atomic.Int64__Add

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

theorem runner.apply.wp_proof
    (hsh : mvcc.api.shapes.law (GF := GF) (hG := hG))
    (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG))
    (hreach : mvcc.api.mvccState_reachable.law (GF := GF) (hG := hG))
    (hRdSplit : mvcc.api.mvccReaders_split.law (GF := GF))
    (wp_traceTODO : traceutil.TODO.spec (GF := GF) (hG := hG))
    (wp_begin : runner.begin.spec (GF := GF) (hG := hG))
    (wp_checkHook : runner.checkHook.spec (GF := GF) (hG := hG))
    (wp_check : check.spec (GF := GF) (hG := hG))
    (wp_writeRange : runner.writeRange.spec (GF := GF) (hG := hG))
    (wp_put : pending.put.spec (GF := GF) (hG := hG))
    (wp_end : runner.end.spec (GF := GF) (hG := hG))
    (wp_writeSub : runner.writeSub.spec (GF := GF) (hG := hG))
    (wp_txn : runner.txn.spec (GF := GF) (hG := hG))
    (wp_Grant : lease.lessor.Grant.spec (GF := GF) (hG := hG))
    (wp_Revoke : lease.lessor.Revoke.spec (GF := GF) (hG := hG))
    (wp_Lookup : lease.lessor.Lookup.spec (GF := GF) (hG := hG))
    (wp_compact : runner.compact.spec (GF := GF) (hG := hG))
    (wp_snapshot : history.snapshot.spec (GF := GF) (hG := hG))
    (wp_ctxTODO : context.TODO.spec (GF := GF) (hG := hG))
    (wp_checkRangeAt : checkRangeAt.spec (GF := GF) (hG := hG))
    (wp_checkLeases : runner.checkLeases.spec (GF := GF) (hG := hG)) :
    runner.apply.spec (GF := GF) (hG := hG) := by
  intro x ks cfg wr h γh ops i mp m f v qw nw k p o lead hov hlogOk hnw hgk h38
  haveI := isInc_persistent hpers
  haveI := hpers.1
  wp_start as ⟨Hctx, Hrd, Hop, Hmw, Hlead⟩
  ihave #Hctx := Hctx
  ihave #Hctx2 := Hctx
  iunfold writerCtx at Hctx2
  icases Hctx2 with ⟨#Hrn, #Hrcfg, %Hrmix, #Hrsh, #Hpkb, #Hpks, #Hpkl, #Hpkt, %Hkslen, ⟨%lg, #Hlg, %Hlg0⟩,
    -, -, -, #Hcrev, #Hccomp, -, -, %HOps⟩
  ihave #Hrn2 := Hrn
  iunfold rnCtx at Hrn2
  icases Hrn2 with ⟨#Hpkg, #Hpkm, #Hks, %Hksne, #HH, #Hhist, #Hcfg, -⟩
  ihave #Hop := Hop
  ihave #HopF := Hop
  iunfold memW at Hmw
  icases Hmw with ⟨Hops, ⟨%a0, %s0, Hhk, %Ha0⟩, Hmc⟩
  iunfold opIs at Hop
  icases Hop with ⟨%ov, %subs, #Hp, #Hok, #Hoe, #Hoq, #Hosubs, %Hsl, #Hsubs, %Hov⟩
  have hn38 : v.ops < 2 ^ 38 := by
    have := (List.getElem?_eq_some_iff.1 hov).1; omega
  iunfold hookPre at Hhk
  icases Hhk with ⟨Happ, Hsav, %Hsa⟩
  wp_auto
  wp_apply_core sync.atomic.Int64.wp_Store (mF go!"applying" mp) (W64 (v.ops : Int) + W64 1)
    $$ [] [-]
  · iPkgInit
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ⊤ from Std.LawfulSet.empty_subset)
  iintro Hcl
  inext
  iexists _
  iframe Happ
  iintro Happ
  imod Hcl with -
  imodintro
  have hai : W64 (v.ops : Int) + W64 1 = W64 ((v.ops + 1 : Nat) : Int) := by push_cast; word
  rw [hai]
  have hsa : sint.Z s0 < sint.Z (W64 ((v.ops + 1 : Nat) : Int)) := by
    have : sint.Z (W64 ((v.ops + 1 : Nat) : Int)) = v.ops + 1 := by word
    omega
  wp_auto
  obtain ⟨hkind, hendNil, hval, hlease, hwrite, hshared, hid, hrev, hwait⟩ := Hov
  ihave ⟨#Hfkind, -⟩ := (github_com.mit_pdos.etcd_grove.examples.mvccfull.op.op_access_load_kind p ov
    DFrac.discard).access_strict $$ Hp
  ihave ⟨#Hfkey, -⟩ := (github_com.mit_pdos.etcd_grove.examples.mvccfull.op.op_access_load_key p ov
    DFrac.discard).access_strict $$ Hp
  ihave ⟨#Hfend, -⟩ := (github_com.mit_pdos.etcd_grove.examples.mvccfull.op.op_access_load_end p ov
    DFrac.discard).access_strict $$ Hp
  ihave ⟨#Hfval, -⟩ := (github_com.mit_pdos.etcd_grove.examples.mvccfull.op.op_access_load_val p ov
    DFrac.discard).access_strict $$ Hp
  ihave ⟨#Hflease, -⟩ := (github_com.mit_pdos.etcd_grove.examples.mvccfull.op.op_access_load_lease p ov
    DFrac.discard).access_strict $$ Hp
  ihave ⟨#Hfq, -⟩ := (github_com.mit_pdos.etcd_grove.examples.mvccfull.op.op_access_load_q p ov
    DFrac.discard).access_strict $$ Hp
  ihave ⟨#Hfid, -⟩ := (github_com.mit_pdos.etcd_grove.examples.mvccfull.op.op_access_load_id p ov
    DFrac.discard).access_strict $$ Hp
  wp_auto
  rw [hkind]
  have hvalid := hlogOk v.ops o hov
  obtain ⟨hk9, hk0', hvput, hvtxn, hvgrant, hvrev, hvcomp⟩ := hvalid
  have hvl : v.ops + 1 ≤ ops.length := (List.getElem?_eq_some_iff.1 hov).1
  have hsa' : sint.Z s0 ≤ sint.Z (W64 ((v.ops + 1 : Nat) : Int)) := by omega
  by_cases hk0 : o.kind = W64 0
  · -- a put
    simp only [hk0, _root_.decide_true]
    sorry
  simp only [hk0, _root_.decide_false]
  (try wp_auto)
  by_cases hk1 : o.kind = W64 1
  · -- a delete
    simp only [hk1, _root_.decide_true]
    sorry
  simp only [hk1, _root_.decide_false]
  (try wp_auto)
  by_cases hk2 : o.kind = W64 2
  · -- a transaction
    simp only [hk2, _root_.decide_true]
    (try wp_auto)
    wp_apply (wp_txn x ks cfg wr h γh ops i mp m f v qw nw k p o lead
        (W64 ((v.ops + 1 : Nat) : Int)) s0 hov hk2 hlogOk hnw h38 rfl hsa)
      $$ [Hrd Hmc Happ Hsav Hlead] as ⟨Hrd, Hlead, Hhk, %v', %Hv', Hmc⟩
    · iframe; iframe #; iunfold hookPre; iframe; ipureintro; omega
    (try wp_auto)
    iapply HΦ
    iframe Hrd Hlead
    iexists v', k
    isplitr
    · ipureintro; exact ⟨Hv'.1, Hv'.2, by omega⟩
    iapply memW_of_core ks γh ops i mp m f v' qw nw k v.ops s0 Hv'.2 hn38 hsa
    iframe
  simp only [hk2, _root_.decide_false]
  (try wp_auto)
  by_cases hk3 : o.kind = W64 3
  · -- a grant
    simp only [hk3, _root_.decide_true]
    obtain ⟨hid0, hidg⟩ := hvgrant hk3
    have hinv := runM_inv ks ops hlogOk v.ops
    obtain ⟨-, -, -, ⟨hLsub, -, hgpos, -⟩, -⟩ := hinv
    iunfold memCore at Hmc
    icases Hmc with ⟨#Hid, #Hhook, HhookOk, Hpath, Hbe, Hle, Hkv, Hrev, Hcmp, Hleases, %Hvops,
      Hinc, Hopen, Hback, #Hhk, Hrdrs, Hbk, Hles, %HU⟩
    iunfold hookOk at HhookOk
    icases HhookOk with ⟨%Hfnil, #Hhrun⟩
    iunfold bkKeep at Hbk
    icases Hbk with ⟨%HbkP, #Hisb, #Hsc, Hbf, Hoh, HRT, Htoks, Hcen⟩
    ihave ⟨Hles, Hlbk⟩ := lessorW_backend v.ι.kv v.bk f v.lp _ v.U _ Hfnil $$ [$Hles $Hisb $Hhk]
    iunfold lessorW at Hles
    icases Hles with ⟨%rd, %r, #Hlpkg, #Hlinv, #Hlcfg, #Hguard, #Hrevoc, #Hlok, Hlrd, Hlo, Hrvk, Hever,
      #Hreq, Hrdo, Hdel, Hlbe, Hrb, %Hrecs, Hstop⟩
    -- one write-back token
    obtain ⟨k1, rfl⟩ : ∃ k1, k = k1 + 1 := ⟨k - 1, by have := hgk hk3; omega⟩
    icases ownToks_add_1 1 k1 v.bk.γB.wb $$ Htoks with ⟨Htoks, Hwb⟩
    ihave Hwb := (backend.wbTok_toks v.bk.γB).2 $$ Hwb
    ihave #Hgr := lease.leaseGranted_of_guard (mvccLeases v.ι.kv) (fun _ => iprop(True)) o.id $$ [Hguard]
    · iframe #; imodintro; itrivial
    wp_auto
    rw [hid]
    have hnin : o.id ∉ leasesAfter ks ops v.ops := by
      intro h; have := hidg _ (hLsub.subset h); omega
    have hninU : o.id ∉ v.U := by
      intro h; have := hidg _ (HU _ h); omega
    wp_apply (wp_Grant v.lp (mvccLeases v.ι.kv) o.id (W64 3600) (leasesAfter ks ops v.ops)
      (pendItems (σOf ks ops v.ops).log []) iprop(True) f (backend.wbTok v.bk.γB)
      (lease.lessorBeOn v.lp v.bk.be) (apply.bkRT v.bk) (backend.rbPart v.bk.γB (· = leaseName)) r
      (hookPre mp (W64 ((v.ops + 1 : Nat) : Int)) s0)
      iprop(True ∗ hookPost mp (W64 ((v.ops + 1 : Nat) : Int)))
      (hookPost mp (W64 ((v.ops + 1 : Nat) : Int))) v.U)
      $$ [Hlbk Hlo Hrvk Hwb Hlbe HRT Hrb Happ Hsav Hever]
      as %l %err ⟨HRT, Hlbe, Hres⟩
    · iframe Hlinv Hlcfg Hlbk Hlo Hrvk Hwb Hlbe HRT Hrb Hgr Hever
      isplitl [Happ Hsav]
      · iunfold srvApi.csContractA
        isplitl
        · iunfold hookPre; iframe; ipureintro; omega
        isplitl
        · iapply Hhrun
        iintro HQ
        imodintro
        iexact HQ
      iright; ipureintro; exact hninU
    icases Hres with (⟨%Hbad, -⟩ | ⟨%Hok, Hlo, Hrvk, Hpost, -, -, Hmt⟩)
    · exfalso
      rcases Hbad.2 with h | h | h
      · rw [h] at hid0; exact absurd hid0 (by decide)
      · have : sint.Z (W64 3600) = 3600 := by word
        omega
      · exact hnin h
    obtain ⟨rfl, -, -, -, -⟩ := Hok
    icases Hmt with ⟨%mt, -, -, Hrb, Hever, HreqN⟩
    wp_auto
    wp_apply wp_check
    · ipureintro; rfl
    (try wp_auto)
    iunfold hookPost at Hpost
    icases Hpost with ⟨Happ, Hsav⟩
    wp_apply wp_checkHook x mp (W64 ((v.ops + 1 : Nat) : Int)) $$ [$Hsav] as Hsav
    icases Hleases with ⟨%lsl, Hlf, Hlsl, Hlcap⟩
    (try wp_auto)
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %osl ⟨Hosl, -⟩
    (try wp_auto)
    wp_apply wp_slice_append $$ [$Hlsl $Hlcap $Hosl] as %lsl' ⟨Hlsl, Hlcap, -⟩
    (try wp_auto)
    -- the store's revision: unchanged
    iunfold incW at Hinc
    icases Hinc with ⟨#Hisinc, Hret, Hσw, Hbw⟩
    ihave #Hmv : isMvcc v.kv v.ι.kv $$ []
    · iunfold isInc at Hisinc; icases Hisinc with ⟨-, #H⟩; iexact H
    ihave %Hkvs := hsh.1 v.kv v.ι.kv $$ Hmv
    obtain ⟨kty, kvv, hkveq, -, -, hKRev, -⟩ := Hkvs
    ihave #Hmv' : isMvcc (interface.mkOk kty kvv) v.ι.kv $$ []
    · rw [← hkveq]; iexact Hmv
    rw [hkveq]
    have hR1 : mvccReaders (GF := GF) v.ι.kv nw ⊣⊢ mvccReaders v.ι.kv (nw - 1) ∗ mvccReaders v.ι.kv 1 := by
      have := hRdSplit v.ι.kv (nw - 1) 1; rwa [Nat.sub_add_cancel hnw] at this
    icases hR1.1 $$ Hrdrs with ⟨Hrdrs, Hr1⟩
    ihave Hau := read_au hpers ks γh i mp m v.ι (interface.mkOk kty kvv) qw (σOf ks ops v.ops)
      $$ [Hret Hσw]
    · iframe #; iframe
    wp_apply (hKRev v.ι.kv (fun σ' => iprop(⌜σ' = σOf ks ops v.ops⌝ ∗ ghostVar v.ι.ret qw () ∗
        ghostVar m.σ (1 : Qp).half (σOf ks ops v.ops)))) $$ [Hr1 Hau]
      as %rv ⟨Hr1, %σr, ⟨%Hσr, Hret, Hσw⟩, %Hrv⟩
    · iframe #; iframe
    subst Hσr Hrv
    (try wp_auto)
    wp_apply wp_check
    · ipureintro; simp [σOf_rev]
    (try wp_auto)
    rw [← hkveq]
    ihave Hrdrs := hR1.2 $$ [$Hrdrs $Hr1]
    obtain ⟨hg1, hg2, hg3, hg4⟩ := runM_succ_grant ks ops v.ops o hov hk3
    have hσ1 := σOf_succ_grant ks ops v.ops o hov hk3
    have hrv1 : revAfter ks ops (v.ops + 1) = revAfter ks ops v.ops := by
      unfold revAfter MSt.rev; unfold histAt at hg1; rw [hg1]
    iapply HΦ
    iframe Hrd
    isplitl [Hlead]
    · unfold leadPre leadPost compsAt
      cases lead
      · simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
      · simp only [↓reduceIte]
        have hc : (runM ks ops (v.ops + 1)).comps = (runM ks ops v.ops).comps := by
          rw [runM_succ ks ops v.ops o hov]; unfold opStep; rw [hk3]; simp
        rw [hg1, hc]; iexact Hlead
    iexists { v with ops := v.ops + 1, U := v.U ++ [o.id] }, k1
    isplitr
    · ipureintro; exact ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, rfl, by omega⟩
    iunfold memW
    iframe Hops
    isplitl [Happ Hsav]
    · iexists _, _; iunfold hookPre; iframe; ipureintro
      have : sint.Z (W64 ((v.ops + 1 : Nat) : Int)) = v.ops + 1 := by word
      refine ⟨Int.le_refl _, by omega, by simp only; omega⟩
    iunfold memCore
    dsimp only
    rw [hσ1, hrv1, hg2, hg3, hg4]
    have hLid : ∀ l ∈ leasesAfter ks ops v.ops, 0 ≤ sint.Z l ∧ sint.Z l < sint.Z o.id := by
      intro l hl
      have hg := hLsub.subset hl
      exact ⟨by have := hgpos _ hg; omega, hidg _ hg⟩
    have hrecs' := leaseRecsOk_grant r (leasesAfter ks ops v.ops) o.id (lease.grantTTL mt (W64 3600))
      Hrecs hLid hid0 (by have := lease.grantTTL_ge mt (W64 3600); have : sint.Z (W64 3600) = 3600 := by word
                          omega)
    ihave #HreqN := HreqN
    iframe Hid Hhook
    isplitr
    · iunfold hookOk; iframe #; ipureintro; exact Hfnil
    iframe Hpath Hbe Hle Hkv Hrev Hcmp Hopen Hback Hhk Hrdrs
    isplitl [Hlf Hlsl Hlcap]
    · iexists lsl'; iframe
    isplitr
    · ipureintro; exact hvl
    isplitl [Hret Hσw Hbw]
    · iunfold incW; iframe; iframe #
    isplitl [Hbf Hoh HRT Htoks Hcen]
    · iunfold bkKeep; iframe; iframe #; ipureintro; exact HbkP
    isplitl
    · iunfold lessorW
      iexists rd, _
      iframe
      iframe #
      isplitr
      · imodintro; iapply BigSepL.bigSepL_nil.2; itrivial
      ipureintro; exact hrecs'
    ipureintro
    intro id hid'
    rcases List.mem_append.1 hid' with h | h
    · exact List.mem_append_left _ (HU _ h)
    · exact List.mem_append_right _ h
  simp only [hk3, _root_.decide_false]
  (try wp_auto)
  by_cases hk4 : o.kind = W64 4
  · -- a revoke
    simp only [hk4, _root_.decide_true]
    sorry
  simp only [hk4, _root_.decide_false]
  (try wp_auto)
  by_cases hk5 : o.kind = W64 5
  · -- a compaction
    simp only [hk5, _root_.decide_true]
    (try wp_auto)
    wp_apply (wp_compact x ks cfg wr h γh ops i mp m f v qw nw k p o lead
        (W64 ((v.ops + 1 : Nat) : Int)) s0 hov hk5 hlogOk h38 rfl hsa)
      $$ [Hmc Happ Hsav Hlead] as ⟨Hlead, Hhk, %v', %Hv', Hmc⟩
    · iframe; iframe #; iunfold hookPre; iframe; ipureintro; omega
    (try wp_auto)
    iapply HΦ
    iframe Hrd Hlead
    iexists v', k
    isplitr
    · ipureintro; exact ⟨Hv'.1, Hv'.2, by omega⟩
    iapply memW_of_core ks γh ops i mp m f v' qw nw k v.ops s0 Hv'.2 hn38 hsa
    iframe
  simp only [hk5, _root_.decide_false]
  (try wp_auto)
  by_cases hk6 : o.kind = W64 6
  · -- a commit
    simp only [hk6, _root_.decide_true]
    iunfold memCore at Hmc
    icases Hmc with ⟨#Hid, #Hhook, HhookOk, Hpath, Hbe, Hle, Hkv, Hrev, Hcmp, Hleases, %Hvops,
      Hinc, Hopen, Hback, #Hhk, Hrdrs, Hbk, Hles, %HU⟩
    iunfold incW at Hinc
    icases Hinc with ⟨#Hisinc, Hret, Hσw, Hbw⟩
    ihave #Hmv : isMvcc v.kv v.ι.kv $$ []
    · iunfold isInc at Hisinc; icases Hisinc with ⟨-, #H⟩; iexact H
    ihave %Hkvs := hsh.1 v.kv v.ι.kv $$ Hmv
    obtain ⟨kty, kvv, hkveq, -, -, -, -, -, -, -, -, hKCommit, -, -, -⟩ := Hkvs
    ihave #Hmv' : isMvcc (interface.mkOk kty kvv) v.ι.kv $$ []
    · rw [← hkveq]; iexact Hmv
    ihave Hkv : mF go!"kv" mp ↦{DFrac.own qw} interface.mkOk kty kvv $$ [Hkv]
    · rw [← hkveq]; iexact Hkv
    have hR1 : mvccReaders (GF := GF) v.ι.kv nw ⊣⊢ mvccReaders v.ι.kv (nw - 1) ∗ mvccReaders v.ι.kv 1 := by
      have := hRdSplit v.ι.kv (nw - 1) 1; rwa [Nat.sub_add_cancel hnw] at this
    icases hR1.1 $$ Hrdrs with ⟨Hrdrs, Hr1⟩
    wp_auto
    wp_apply (hKCommit v.ι.kv 1 _ iprop(True) iprop(True) iprop(True)) $$ [Hr1 Hback]
      as ⟨Hr1, Hback, -⟩
    · iframe #; iframe
      isplitr; · itrivial
      rw [etcdStorage_req]; iapply backend.commitReq_true
    (try wp_auto)
    ihave Hrdrs := hR1.2 $$ [$Hrdrs $Hr1]
    ihave Hkv : mF go!"kv" mp ↦{DFrac.own qw} v.kv $$ [Hkv]
    · rw [hkveq]; iexact Hkv
    ihave Hinc : incW ks γh i mp m v.ι v.kv qw (σOf ks ops v.ops) v.b $$ [Hret Hσw Hbw]
    · iunfold incW; iframe; iframe #
    iapply HΦ
    iframe Hrd
    iapply apply_close_same ks γh ops i mp m f v qw nw k lead s0
      (runM_succ_same ks ops v.ops o hov (Or.inl hk6)) hvl hn38 hsa'
    iframe
    iunfold memCore; dsimp only; iframe; iframe #
    ipureintro; exact ⟨Hvops, HU⟩
  simp only [hk6, _root_.decide_false]
  (try wp_auto)
  by_cases hk7 : o.kind = W64 7
  · -- a read
    simp only [hk7, _root_.decide_true]
    sorry
  simp only [hk7, _root_.decide_false]
  (try wp_auto)
  -- the leases' check
  have hk8 : o.kind = W64 8 := by word
  icases leadPre_lb γh ks ops v.ops lead $$ Hlead with ⟨Hlead, #Hlb⟩
  wp_apply (wp_checkLeases x ks cfg wr h γh ops i mp m f v qw nw k hlogOk) $$ [Hrd Hmc]
    as ⟨Hrd, Hmc⟩
  · iframe; iframe #
  (try wp_auto)
  iapply HΦ
  iframe Hrd
  iapply apply_close_same ks γh ops i mp m f v qw nw k lead s0
    (runM_succ_same ks ops v.ops o hov (Or.inr (Or.inr (Or.inl hk8)))) hvl hn38 hsa'
  iframe

end proof

end mvccfull
end EtcdGrove
end Perennial
