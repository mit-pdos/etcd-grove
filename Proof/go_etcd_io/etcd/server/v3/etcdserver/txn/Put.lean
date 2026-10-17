/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.Put
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.EnsureTrace
public import Spec.google_golang_org.protobuf.proto.Size
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.checkLease
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__Write
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.checkAndGetPrevKV
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.put
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.metricsTxnWrite__End
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.FrozenSpecs
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.KVWrite

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver
  go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

theorem txn.Put.wp_proof
    (hEnsure : traceutil.EnsureTrace.spec (GF := GF) (hG := hG))
    (hSize : proto.Size.spec (GF := GF) (hG := hG))
    (hLease : txn.checkLease.spec (GF := GF) (hG := hG))
    (hWrite : mvcc.store.Write.spec (GF := GF) (hG := hG))
    (hWWrite : mvcc.watchableStore.Write.spec (GF := GF) (hG := hG))
    (hCheck : txn.checkAndGetPrevKV.spec (GF := GF) (hG := hG))
    (hput : txn.put.spec (GF := GF) (hG := hG))
    (hEnd : mvcc.metricsTxnWrite.End.spec (GF := GF) (hG := hG))
    (hWEnd : mvcc.watchableStoreTxnWrite.End.spec (GF := GF) (hG := hG)) :
    txn.Put.spec (GF := GF) (hG := hG) := by
  intro ctx cd lg le kv s γ p o m log₀ P Pre Q Post f L ot te Lw
  wp_start as ⟨#Hkv, Hrd, Htok, Hwt, Htoks, #Hc0, Hwl, %Hsole, #Hle, Hu, #Hp, #Hctx, #Hct, Hto, #Hlprem, #Hcok, Hcs, #Hhook⟩
  iunfold mvcc.csContract at Hcs
  icases Hcs with ⟨Hpre, #Htr, Hupd⟩
  ihave #Htu : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.traceutil $$ []
  · iPkgInit
  ihave #Hpr : isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto $$ []
  · iPkgInit
  ihave #Hmv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc $$ []
  · iPkgInit
  ihave #Hp0 := Hp
  iunfold txn.putRequestIs at Hp0
  icases Hp0 with ⟨%Hpnn, %ksl, %vsl, %k, %v, %lease, %pk, %iv, %il, #Hk, #Hks, #Hv, #Hvs, #Hl,
    #Hpk, #Hiv, #Hil, -, %Ho, -⟩
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply wp_bytes_to_string $$ [$Hks] as -
  (try wp_auto)
  wp_apply (hSize.1 p o) $$ [$Hp] as %sz -
  (try wp_auto)
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %fsl ⟨Hfsl, Hfslc⟩
  (try wp_auto)
  wp_apply (hEnsure ctx cd ot te lg _ _) $$ [$Hctx $Hct $Hto Hfsl Hfslc]
    as %ctx' %trace ⟨⟨%Ht, %Hteq⟩, Htrc, #Hct', %vs, #Hctx', -⟩
  · iunfold traceutil.ownFields
    iexists _
    iframe Hfsl Hfslc
    ipureintro
    exact traceutil.fieldsWf_cons_string _ _ _
      (traceutil.fieldsWf_cons_int _ _ _ (.int _) _ traceutil.fieldsWf_nil)
  (try wp_auto)
  -- `checkLease(lessor, p)`
  wp_apply (hLease le γ.leases p o L) $$ [$Hle $Hp $Hu] as %err ⟨Hu, Herr⟩
  (try wp_auto)
  icases Herr with (⟨%Herr, #Hlok⟩ | ⟨%Hne, #He⟩)
  rotate_left
  · -- the lease not found: nothing opened
    ihave #He' := He
    iunfold txn.errVarIs at He'
    icases He' with ⟨%e, -, %Hee⟩
    subst Hee
    (try wp_auto)
    iapply HΦ
    iframe Hrd Htoks Hu
    isplitl []
    · ipureintro; exact Ht
    isplitl [Htrc]
    · iexists false; iexact Htrc
    isplitr
    · ipureintro; exact Hteq
    ileft
    iframe He Htok Hpre Hwl
    ipureintro; exact ⟨Hne, rfl⟩
  subst Herr
  (try wp_auto)
  -- `kv.Write(trace)`: the store's, or the watchable store's (unit N4)
  ihave %Hkvok := txn.isKV_ok kv s γ $$ Hkv
  obtain ⟨kty, kvv, rfl⟩ := Hkvok
  (try wp_auto)
  wp_apply (txn.kv_Write hWrite hWWrite kty kvv s γ trace P Pre Q f false m Lw)
    $$ [$Hkv $Hrd $Htok $Hwt $Htoks $Hwl $Hhook $Hpre $Htr $Htrc]
    as %tyX %vX ⟨%ilog, %mw, Htx, Hte, Htoks, %Hil, HQ⟩
  · ipureintro; exact ⟨fun h => Hsole h, Ht⟩
  ihave ⟨Hte, #Hw⟩ := txn.twEnd_wrap s γ tyX vX mw ilog $$ Hte
  have hsole : γ.watchQ = true → m + 1 = txn.soleBudget ilog := by
    intro h; rw [Hil h]; exact (Hsole h).1
  -- the caller's update (the writes are the model's): the lock's invariant back for `End`
  imod Hupd $$ HQ with ⟨HP, HPost⟩
  (try wp_auto)
  -- the pin of the transaction's committed log
  ihave ⟨%Hpin, Htoks, -, Htx⟩ := txn.isTxnWrite_pinned γ log₀ ilog [] mw s (W64 0) (W64 0) (W64 0) m
    $$ [$Htoks $Hc0 $Htx]
  ihave ⟨%Hfx, Htx⟩ := txn.isTxnWrite_facts mw s γ ilog [] (W64 0) (W64 0) (W64 0) $$ Htx
  have hks := txn.kindState_write ilog [] (W64 0) (W64 0) (W64 0) Hfx.1 Hfx.2
  rw [txn.pendState_nil] at hks
  ihave Htx : mvcc.isTxn mw s γ trace (.write ilog [] (W64 0) (W64 0) (W64 0)) $$ [Htx]
  · simp only [mvcc.isTxn]; iexact Htx
  -- `checkAndGetPrevKV(trace, txnWrite, p)`
  wp_apply (hCheck trace mw s γ (.write ilog [] (W64 0) (W64 0) (W64 0)) p o tyX vX) $$ [$Htx $Hw $Hp]
    as %prev %err ⟨Htx, Hout⟩
  · ipureintro; exact Ht
  rw [hks]
  icases Hout with (⟨%Herr, %Hn, Hprev⟩ | ⟨%Hn, #He⟩)
  rotate_left
  · -- an ignore flag and no previous key-value: nothing written
    ihave #He' := He
    iunfold txn.errVarIs at He'
    icases He' with ⟨%e, -, %Hee⟩
    subst Hee
    (try wp_auto)
    ihave Htx : mvcc.isTxnWrite mw s γ trace ilog [] (W64 0) (W64 0) (W64 0) $$ [Htx]
    · simp only [mvcc.isTxn]; iexact Htx
    wp_apply (txn.tw_End hEnd hWEnd tyX vX s γ trace mw ilog [] (W64 0) (W64 0) (W64 0) m P f)
      $$ [$Htx $Hte $Htoks HP] as ⟨Hrd, ⟨%te', Htrc⟩, #Hc, Htok, Htoks, Hwl⟩
    · iframe HP Hhook
      isplitl []
      · ipureintro; exact hsole
      iunfold mvcc.certOkNext; ileft; ipureintro; rfl
    simp only [mvcc.commitLog, ↓reduceIte]
    (try wp_auto)
    iapply HΦ
    iframe Hrd Htoks Hu
    isplitl []
    · ipureintro; exact Ht
    isplitl [Htrc]
    · iexists te'; iexact Htrc
    isplitr
    · ipureintro; exact Hteq
    iright
    iexists ilog
    isplitl []
    · ipureintro; exact ⟨Hpin, Hfx.1⟩
    iframe HPost
    ileft
    iframe He Htok Hc Hwl
    ipureintro; exact ⟨Hn.1, Hn.2.1, rfl⟩
  subst Herr
  (try wp_auto)
  -- the lease the put writes: the request's (found by `checkLease`) or the previous one
  ihave #Hlok2 : txn.leaseOk L
      (txn.putLeaseOf o (mvcc.findKey o.key (mvcc.stateAfter ilog))) $$ []
  · cases hil : o.ignoreLease
    · unfold txn.putLeaseOf; rw [hil]; simp only [Bool.false_eq_true, ↓reduceIte]; iexact Hlok
    · iapply Hlprem
      ipureintro; exact ⟨Hpin, rfl⟩
  ihave Htx : mvcc.isTxnWrite mw s γ trace ilog [] (W64 0) (W64 0) (W64 0) $$ [Htx]
  · simp only [mvcc.isTxn]; iexact Htx
  have hp := hput trace ctx' { cd with Values := vs } mw s γ ilog [] (W64 0) (W64 0) (W64 0) p o prev L
    tyX vX
  simp only [txn.pendState_nil, List.nil_append, List.length_nil] at hp
  iunfold EtcdGrove.lease.lessorUser at Hu
  icases Hu with ⟨Hown, Hrdo⟩
  wp_apply hp $$ [$Hctx' $Hct' $Htx $Hw $Hp $Hprev $Hlok2 $Hown]
    as %resp ⟨⟨%puts', %putSize', Htx⟩, #Hresp, Hhdr, Hown⟩
  · ipureintro; exact ⟨Hn, by have := mvcc.putMax_ge γ; omega⟩
  (try wp_auto)
  -- the deferred `txnWrite.End()`: the put committed
  wp_apply (txn.tw_End hEnd hWEnd tyX vX s γ trace mw ilog
      [txn.putChangeOf o (mvcc.findKey o.key (mvcc.stateAfter ilog))] puts' (W64 0) putSize' m P f)
    $$ [$Htx $Hte $Htoks HP] as ⟨Hrd, ⟨%te', Htrc⟩, #Hc, -, Htoks, Hwl⟩
  · iframe HP Hhook
    isplitl []
    · ipureintro; exact hsole
    iunfold mvcc.certOkNext; iright; iapply Hcok; ipureintro; exact ⟨Hpin, Hn⟩
  simp only [mvcc.commitLog, List.cons_ne_nil, ↓reduceIte]
  (try wp_auto)
  iapply HΦ
  iframe Hrd Htoks
  isplitl [Hown Hrdo]
  · iunfold EtcdGrove.lease.lessorUser; iframe Hown Hrdo
  isplitl []
  · ipureintro; exact Ht
  isplitl [Htrc]
  · iexists te'; iexact Htrc
  isplitr
  · ipureintro; exact Hteq
  iright
  iexists ilog
  isplitl []
  · ipureintro; exact ⟨Hpin, Hfx.1⟩
  iframe HPost
  iright
  iframe Hresp Hhdr Hc Hlok2 Hwl
  ipureintro; exact ⟨rfl, Hn⟩

end proof

end EtcdGrove
end Perennial
