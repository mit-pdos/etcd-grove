/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.Put
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.EnsureTrace
public import Spec.google_golang_org.protobuf.proto.Size
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.checkLease
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.checkAndGetPrevKV
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.put
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.ApiLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver
  go_etcd_io.etcd.server.v3.storage.mvcc
open mvcc.api (MvccState MTxn MvccName)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

theorem txn.Put.wp_proof
    (hsh : mvcc.api.shapes.law (GF := GF) (hG := hG))
    (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG))
    (hreach : mvcc.api.mvccState_reachable.law (GF := GF) (hG := hG))
    (hEnsure : traceutil.EnsureTrace.spec (GF := GF) (hG := hG))
    (hSize : proto.Size.spec (GF := GF) (hG := hG))
    (hLease : txn.checkLease.spec (GF := GF) (hG := hG))
    (hCheck : txn.checkAndGetPrevKV.spec (GF := GF) (hG := hG))
    (hput : txn.put.spec (GF := GF) (hG := hG)) :
    txn.Put.spec (GF := GF) (hG := hG) := by
  intro ctx cd lg le kv γ p o q B P Pre Q Post f L I ot te R
  haveI := hpers.1 kv γ
  wp_start as ⟨#Hkv, Htt, #Hle, Hu, #Hp, #Hctx, #Hct, Hto, Hbk, Hcs, Hau⟩
  iunfold txn.kvBackend at Hbk
  icases Hbk with ⟨Hbk, #Hhook⟩
  iunfold txn.csA at Hcs
  icases Hcs with ⟨Hpre, Htr, Hupd⟩
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
  wp_auto
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
    as %ctx' %trace ⟨⟨%Ht, %Hteq⟩, Htrc, #Hct', -, %vs, #Hctx', -⟩
  · iunfold traceutil.ownFields
    iexists _
    iframe Hfsl Hfslc
    ipureintro
    exact traceutil.fieldsWf_cons_string _ _ _
      (traceutil.fieldsWf_cons_int _ _ _ (.int _) _ traceutil.fieldsWf_nil)
  (try wp_auto)
  -- `checkLease(lessor, p)`
  wp_apply (hLease le (mvcc.api.mvccLeases γ) p o L I) $$ [$Hle $Hp $Hu] as %err ⟨Hu, Herr⟩
  (try wp_auto)
  icases Herr with (⟨%Herr, #Hlok⟩ | ⟨%Hne, #He⟩)
  rotate_left
  · -- the lease not found: nothing opened, the caller's updates not given
    ihave #He' := He
    iunfold txn.errVarIs at He'
    icases He' with ⟨%e, -, %Hee⟩
    subst Hee
    (try wp_auto)
    iapply HΦ
    ihave Hbk : txn.kvBackend γ q B P f $$ [Hbk]
    · iunfold txn.kvBackend; iframe Hbk Hhook
    iframe Htt Hbk
    isplitl []
    · ipureintro; exact Ht
    isplitl [Htrc]
    · iexists false; iexact Htrc
    isplitr
    · ipureintro; exact Hteq
    ileft
    iframe He Hpre Hu
    ipureintro; exact ⟨Hne.1, Hne.2, rfl⟩
  subst Herr
  (try wp_auto)
  -- the lease is live: the caller's updates are given
  iunfold txn.leaseOk at Hlok
  icases Hlok with %Hlok
  rw [decide_eq_true Hlok] at *
  simp only [↓reduceIte]
  iunfold txn.putAU at Hau
  ihave Hau := txn.beginAU_reach hpers hreach kv γ _ $$ Hkv Hau
  icases txn.isMvcc_shape hsh kv γ $$ Hkv with ⟨%Hsh, -⟩
  obtain ⟨kty, kvv, rfl, -, hWriteC, -⟩ := Hsh
  (try wp_auto)
  -- `kv.Write(trace)`
  wp_apply (hWriteC γ trace false q B P Pre Q f _) $$ [$Hkv $Htt $Htrc $Hbk $Hhook $Hpre $Htr $Hau]
    as %t ⟨Htrc, Hbk, ⟨%σ₀, Htx, ⟨%Hreach0, %Hitems, Hilok, Hcommit⟩⟩, HQ⟩
  · ipureintro; exact Ht
  icases txn.mvccTxn_shape hsh t γ trace (.write σ₀ []) $$ Htx with ⟨%Hsht, Htx⟩
  obtain ⟨tty, tv, rfl, -, -, -, -, -, -, hEndC⟩ := Hsht
  -- the caller's update (the writes are the model's): the lock's invariant back for `End`
  imod Hupd $$ HQ with ⟨HP, HPost⟩
  (try wp_auto)
  -- `checkAndGetPrevKV(trace, txnWrite, p)`
  wp_apply (hCheck _ γ trace false (.write σ₀ []) p o) $$ [$Htx $Htrc $Hp]
    as %prev %err ⟨Htx, Htrc, Hout⟩
  · ipureintro; exact ⟨Ht, Hreach0.1⟩
  have hms : txn.mstate (.write σ₀ []) = mvcc.stateAfter σ₀.log := rfl
  rw [hms]
  icases Hout with (⟨%Herr, %Hn, Hprev⟩ | ⟨%Hn, #He⟩)
  rotate_left
  · -- an ignore flag and no previous key-value: nothing written
    ihave #He' := He
    iunfold txn.errVarIs at He'
    icases He' with ⟨%e, -, %Hee⟩
    subst Hee
    (try wp_auto)
    have hpp : txn.putPend o σ₀ = [] := by
      unfold txn.putPend; simp only [Hn.1, Hn.2.1, and_self, ↓reduceIte]
    rw [hpp] at *
    wp_apply (txn.end_write hEndC γ trace σ₀ _ q B P (R σ₀)) $$ [$Htx $Hbk $HP $Hcommit]
      as ⟨Htt, Hbk, HR⟩
    (try wp_auto)
    iapply HΦ
    ihave Hbk : txn.kvBackend γ q B P f $$ [Hbk]
    · iunfold txn.kvBackend; iframe Hbk Hhook
    iframe Htt Hbk
    isplitl []
    · ipureintro; exact Ht
    isplitl [Htrc]
    · iexists false; iexact Htrc
    isplitr
    · ipureintro; exact Hteq
    iright
    iexists σ₀
    isplitl []
    · ipureintro; exact Hreach0
    iframe HPost HR
    ileft
    iframe He Hu
    ipureintro; exact ⟨Hn.1, Hn.2.1, rfl⟩
  subst Herr
  (try wp_auto)
  -- the lease the put writes: the request's (found by `checkLease`) or the previous one
  ihave #Hlok2 : txn.leaseOk L
      (txn.putLeaseOf o (mvcc.findKey o.key (mvcc.stateAfter σ₀.log))) $$ [Hilok]
  · cases hil : o.ignoreLease
    · unfold txn.putLeaseOf; rw [hil]; simp only [Bool.false_eq_true, ↓reduceIte]
      iunfold txn.leaseOk; ipureintro; exact Hlok
    · have h : (if true = true then txn.leaseOk (GF := GF) L
          (txn.putLeaseOf o (mvcc.findKey o.key (mvcc.stateAfter σ₀.log))) else iprop(True)) ⊢
          txn.leaseOk L (txn.putLeaseOf o (mvcc.findKey o.key (mvcc.stateAfter σ₀.log))) := by
        simp only [↓reduceIte]; (try (iintro H; iexact H))
      iapply h $$ Hilok
  have hp := hput ctx' { cd with Values := vs } (interface.mkOk tty tv) γ trace false σ₀ [] p o prev L
  simp only [txn.pendState_nil, List.nil_append] at hp
  iunfold EtcdGrove.lease.lessorUser at Hu
  icases Hu with ⟨Hown, Hrdo, Hrvk⟩
  -- the owner's item map: the begin state's
  ihave Hown : EtcdGrove.lease.leaseOwn (mvcc.api.mvccLeases γ) L (mvcc.pendItems σ₀.log []) $$ [Hown]
  · rw [Hitems]; iexact Hown
  wp_apply hp $$ [$Hctx' $Hct' $Htx $Htrc $Hp $Hprev $Hlok2 $Hown]
    as %resp ⟨Htx, Htrc, #Hresp, Hhdr, Hown⟩
  · ipureintro; exact Hn
  (try wp_auto)
  -- the deferred `txnWrite.End()`: the put committed
  have hpp : txn.putPend o σ₀ = [txn.putChangeOf o (mvcc.findKey o.key (mvcc.stateAfter σ₀.log))] := by
    unfold txn.putPend
    have hneg : ¬ (txn.needsPrev o = true ∧ mvcc.findKey o.key (mvcc.stateAfter σ₀.log) = none) := by
      rintro ⟨h1, h2⟩
      have := Hn h1
      rw [h2] at this
      cases this
    simp only [hneg, ↓reduceIte]
  rw [hpp]
  wp_apply (txn.end_write hEndC γ trace σ₀ _ q B P (R σ₀)) $$ [$Htx $Hbk $HP $Hcommit] as ⟨Htt, Hbk, HR⟩
  (try wp_auto)
  iapply HΦ
  ihave Hbk : txn.kvBackend γ q B P f $$ [Hbk]
  · iunfold txn.kvBackend; iframe Hbk Hhook
  iframe Htt Hbk
  isplitl []
  · ipureintro; exact Ht
  isplitl [Htrc]
  · iexists false; iexact Htrc
  isplitr
  · ipureintro; exact Hteq
  iright
  iexists σ₀
  isplitl []
  · ipureintro; exact Hreach0
  iframe HPost HR
  iright
  iframe Hresp Hhdr Hlok2
  isplitl []
  · ipureintro; exact ⟨rfl, Hn⟩
  iunfold EtcdGrove.lease.lessorUser; iframe Hrdo Hrvk
  rw [hpp]
  iexact Hown

end proof

end EtcdGrove
end Perennial
