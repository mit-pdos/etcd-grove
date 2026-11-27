/-
Proof of `Spec/go_etcd_io/etcd/client/v3/kv__Compact.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.kv__Compact
public import Spec.go_etcd_io.etcd.client.v3.OpCompact
public import Spec.go_etcd_io.etcd.client.v3.CompactOp__toRequest
public import Spec.go_etcd_io.etcd.client.v3.retryKVClient__Compact
public import Spec.go_etcd_io.etcd.client.v3.ContextError
public import Proof.go_etcd_io.etcd.client.v3.KVMembers

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 client

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `kv.Compact` for any spec registered for `Compact` (`kv.Compact.specG`): `OpCompact`, its
request, the retry client's `Compact` at the spec, the error through `ContextError`. -/
theorem kv.Compact.wp_generic
    (wp_OpCompact : OpCompact.spec (GF := GF) (hG := hG))
    (wp_toRequest : CompactOp.toRequest.spec (GF := GF) (hG := hG))
    (wp_retry_Compact : retryKVClient.Compact.spec (GF := GF) (hG := hG))
    (wp_ContextError : ContextError.spec (GF := GF) (hG := hG)) :
    kv.Compact.specG (GF := GF) (hG := hG) := by
  intro api conn addr ci om cd rev Sc Qc
  wp_start as ⟨Hlt, #Hobj, #Hom, #Hctx, #Hce, #Hrpc, #Hpre⟩
  iunfold kvObjAtC at Hobj
  icases Hobj with ⟨%rkv, %sl, #Hremote, #Hrkv, #Hconn, #Hcopts, #Hco⟩
  iunfold callOptsAt at Hco
  icases Hco with ⟨%vs, #Hsl, %Hcap, #Hok, %Hsc⟩
  wp_auto
  wp_apply wp_OpCompact rev $$ []
  wp_apply wp_toRequest _ $$ [] as %p ⟨%req, Hreq, %Hrq⟩
  obtain ⟨hrv, hph, hun⟩ := Hrq
  simp only at hrv hph
  ihave Hrun : reqPre conn go!"/etcdserverpb.KV/Compact" addr vs
      (attemptPre conn om Sc ⟨req.Revision', req.Physical'⟩ Qc) $$ []
  · iapply reqPre_box
    rw [hrv, hph]
    iexact Hpre
  wp_apply wp_retry_Compact rkv conn addr Sc Qc ci om cd p req sl vs $$ [Hlt Hreq Hrun]
    as %resp %err ⟨Hlt, -, Hres⟩
  · iframe #
    iframe
    ipureintro; exact hun
  iunfold compactCallOut at Hres
  icases Hres with (⟨%Herr, %m, #Hm, HQ⟩ | ⟨%Herr, #Hse, #Hcl⟩)
  · subst Herr
    wp_auto
    iapply HΦ
    iframe Hlt
    unfold compactCallOut
    ileft
    isplitr
    · ipureintro; rfl
    iexists m
    isplitl []
    · iexact Hm
    iexact HQ
  · obtain ⟨Hne, Hce', Hnull⟩ := Herr
    cases err with
    | nil => exact absurd rfl Hne
    | ok ei =>
      wp_auto
      ihave ⟨%mC, #HmC⟩ := go_etcd_io.etcd.cache.v3.statusErrOk_descIs _ $$ Hse
      wp_apply wp_ContextError ci cd (GoInterface.ok ei) mC $$ [$Hse $HmC] as %err' ⟨%Herr', #Hse', #Hclw, -⟩
      · iframe #; ipureintro; exact fun _ => Hce'
      ihave #Hcl' := Hclw $$ Hcl
      iapply HΦ
      iframe Hlt
      unfold compactCallOut
      iright
      iframe #
      ipureintro
      exact ⟨(Herr'.2 (by simp)).1, (Herr'.2 (by simp)).2, rfl⟩

/-- `kv.Compact` on a `*kv` of etcd's KV `γ` (stage A, 2026-11-27): `kv.Compact.wp_generic` at the
view spec its endpoints register on a compacting cluster (`isKv`, `kvRegsV_rpcCompact`), met by the
caller's revision reached. -/
theorem kv.Compact.wp_proof
    (wp_OpCompact : OpCompact.spec (GF := GF) (hG := hG))
    (wp_toRequest : CompactOp.toRequest.spec (GF := GF) (hG := hG))
    (wp_retry_Compact : retryKVClient.Compact.spec (GF := GF) (hG := hG))
    (wp_ContextError : ContextError.spec (GF := GF) (hG := hG)) :
    kv.Compact.spec (GF := GF) (hG := hG) := by
  intro api γ dup ci cd rev Hr1 Hcmp
  iintro %Φ ⟨#Pc, Hlt, #Hkv, #Hctx, #Hce, #Hrv⟩ HΦ
  ihave #HctxO := ctxOk_outgoingC ci cd $$ Hctx
  iunfold metadata.outgoingCtxOkC at HctxO
  icases HctxO with ⟨%om, #Hom⟩
  iunfold isKv at Hkv
  icases Hkv with ⟨%addrs, #Hobj, #Hregs, -⟩
  icases (kvObjAt_conn api addrs).1 $$ Hobj with ⟨%conn, #Hobj⟩
  iapply (kv.Compact.wp_generic wp_OpCompact wp_toRequest wp_retry_Compact wp_ContextError api conn
    addrs ci om cd rev (etcdCompactSpecV γ) (fun _ => iprop(True))) $$ [Hlt]
  · iframe #
    iframe Hlt
    isplitl []
    · iapply (kvRegsV_rpcCompact addrs γ Hcmp) $$ Hregs
    imodintro
    inext
    unfold attemptPre etcdCompactSpecV
    iintro %md -
    isplitr
    · imodintro; iintro %_; itrivial
    isplitr
    · ipureintro; exact ⟨Hr1, rfl, Hcmp⟩
    isplitr
    · iexact Hrv
    iintro %m
    itrivial
  inext
  iintro %resp %err ⟨Hlt, Hres⟩
  iapply HΦ
  iframe Hlt
  iunfold compactCallOut at Hres
  icases Hres with (⟨%Herr, %m, #Hm, -⟩ | ⟨%Herr, #Hse, #Hcl⟩)
  · ileft
    isplitl []
    · ipureintro; exact Herr
    iexists m
    iexact Hm
  · iright
    isplitl []
    · ipureintro; exact ⟨Herr.1, Herr.2.2⟩
    unfold kvErr
    iframe #
    ipureintro; exact Herr.2.1

end proof

end EtcdGrove
end Perennial
