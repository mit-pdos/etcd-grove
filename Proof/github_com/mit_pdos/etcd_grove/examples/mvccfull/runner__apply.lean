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
    sorry
  simp only [hk2, _root_.decide_false]
  (try wp_auto)
  by_cases hk3 : o.kind = W64 3
  · -- a grant
    simp only [hk3, _root_.decide_true]
    sorry
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
    sorry
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
