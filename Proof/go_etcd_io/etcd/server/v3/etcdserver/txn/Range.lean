/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.Range
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.EnsureTrace
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.RangeSecObserve
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.executeRange
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.ApiLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.server.v3.etcdserver.txn
  go_etcd_io.etcd.api.v3
open mvcc.api (MvccState MTxn MvccName)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

theorem txn.Range.wp_proof
    (hsh : mvcc.api.shapes.law (GF := GF) (hG := hG))
    (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG))
    (hreach : mvcc.api.mvccState_reachable.law (GF := GF) (hG := hG))
    (hEnsure : traceutil.EnsureTrace.spec (GF := GF) (hG := hG))
    (hObs : txn.RangeSecObserve.spec (GF := GF) (hG := hG))
    (hExec : txn.executeRange.spec (GF := GF) (hG := hG)) :
    txn.Range.spec (GF := GF) (hG := hG) := by
  intro ctx cd nd lg kv γ r o withTotal ot te Q
  haveI := hpers.1 kv γ
  wp_start as ⟨#Hkv, Hrd, #Hr, #Hctx, #Hct, Hto, #Hnd, %Hlg, %Hvst, Hau⟩
  icases txn.isMvcc_shape hsh kv γ $$ Hkv with ⟨%Hsh, -⟩
  obtain ⟨kty, kvv, rfl, hReadC, -⟩ := Hsh
  ihave Hau := txn.readAU_reach hpers hreach _ γ Q $$ Hkv Hau
  wp_auto
  wp_apply wp_with_defer as %defer defer
  wp_apply (hEnsure ctx cd ot te lg _ _) $$ [$Hctx $Hct $Hto]
    as %ctx' %trace ⟨⟨%Ht, %Hteq⟩, Htrc, #Hct', -, %vs, #Hctx', -⟩
  · iapply traceutil.ownFields_nil
  wp_apply time.wp_Now as %now -
  wp_apply (hReadC γ _ trace false _) $$ [$Hkv $Hrd $Htrc $Hau]
    as %t ⟨Htrc, %σ, Htx, HQ, %Hreachσ⟩
  · ipureintro; exact Ht
  icases txn.mvccTxn_shape hsh t γ trace (.read σ) $$ Htx with ⟨%Hsht, Htx⟩
  obtain ⟨tty, tv, rfl, -, -, -, -, -, -, hEndC⟩ := Hsht
  wp_auto
  have hE := hExec ctx' { cd with Values := vs } nd lg (interface.mkOk tty tv) γ trace false (.read σ) r o withTotal
  simp only [mvcc.api.MTxn.readLog, mvcc.api.MTxn.readRev, mvcc.api.MTxn.state] at hE
  wp_apply hE
    $$ [$Htx $Htrc $Hctx' $Hct' $Hr] as %resp %err ⟨Htx, Htrc, #Hres, Hhdr, %Hnd'⟩
  · isplitl [Hnd]
    · cases nd
      · simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
      · simp only [↓reduceIte, mvcc.neverDone] at *; iexact Hnd
    ipureintro
    exact ⟨Hreachσ, Hvst⟩
  wp_apply (txn.end_read hEndC γ trace σ) $$ [$Htx] as ⟨Hrd⟩
  cases err <;> wp_auto
  all_goals
    wp_apply time.wp_Since as %d -
    wp_apply hObs
    iapply HΦ
    iframe Hrd
    isplitr
    · ipureintro; exact Ht
    isplitl [Htrc]
    · iexists false; iexact Htrc
    isplitr
    · ipureintro; exact Hteq
    iexists σ
    iframe HQ Hhdr
    isplitl []
    · ipureintro; exact Hreachσ
    iframe Hres
    ipureintro; exact Hnd'


end proof

end EtcdGrove
end Perennial
