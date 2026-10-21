/-
Proof of `Spec/go_etcd_io/etcd/client/v3/txn__Commit.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.txn__Commit
public import Spec.go_etcd_io.etcd.client.v3.retryKVClient__Txn
public import Spec.go_etcd_io.etcd.client.v3.ContextError
public import Perennial.Proof.sync.Link

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

theorem txn.Commit.wp_proof (wp_retry_Txn : retryKVClient.Txn.spec (GF := GF) (hG := hG))
    (wp_ContextError : ContextError.spec (GF := GF) (hG := hG)) :
    txn.Commit.spec (GF := GF) (hG := hG) := by
  intro tp addr ci cd b Spec Q
  wp_start as ⟨Htx, #Hrpc, Hrun⟩
  iunfold txnObjAt at Htx
  icases Htx with ⟨%Htpn, %api, %cosl, %csl, %ssl, %fsl, %cps, %sps, %fps, %iw, #Hkvf, #Hkv, #Hctxf,
    #Hctx, #Hce, #Hmu, Hcif, Hcthen, Hcelse, Hiw, Hcmps, Hcsl, Hccap, #Hcpa, Hsus, Hssl, Hscap,
    #Hspa, Hfas, Hfsl, Hfcap, #Hfpa, #Hcof, #Hco⟩
  ihave #Hkv' := Hkv
  iunfold kvObjAt at Hkv'
  icases Hkv' with ⟨%rkv, %conn, %sl, #Hremote, #Hrkv, #Hconn, #Hcopts, #Hco'⟩
  iunfold callOptsAt at Hco
  icases Hco with ⟨%vs, #Hvs, %Hcap, #Hok, %Hsc⟩
  wp_apply wp_with_defer as %defer defer
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, -⟩
  ipersist Hcsl; ipersist Hssl; ipersist Hfsl
  ihave Hrun' : reqPre conn addr vs (Spec (txnWireOf b.model) Q) $$ [Hrun]
  · iapply kvReqPre_conn api rkv conn addr vs _ Hsc $$ [Hrun]
    iframe Hremote Hrkv
    iapply txnReqPre_kv tp api addr $$ [Hrun]
    iframe Hrun
    unfold txnKvIs; iexact Hkvf
  wp_apply wp_retry_Txn rkv conn addr Spec Q ci cd _ _ (txnWireOf b.model) cosl vs $$ [«$r0» Hrun']
    as %resp %err ⟨-, Hres⟩
  · iframe #
    iframe
    unfold txnReqAt txnWireOf
    iexists cps, sps, fps
    iframe #
  iunfold txnCallOut at Hres
  icases Hres with (⟨%Herr, Hm⟩ | ⟨%Herr, #Hse⟩)
  · subst Herr
    wp_auto
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked]
    · inext; itrivial
    iapply HΦ
    unfold txnCallOut
    ileft
    iframe Hm
    ipureintro; rfl
  · obtain ⟨Hne, Hce', Hnull⟩ := Herr
    cases err with
    | nil => exact absurd rfl Hne
    | ok ei =>
      wp_auto
      wp_apply wp_ContextError ci cd (GoInterface.ok ei) $$ [$Hse] as %err' ⟨%Herr', #Hse'⟩
      · iframe #; ipureintro; exact fun _ => Hce'
      wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked]
      · inext; itrivial
      iapply HΦ
      unfold txnCallOut
      iright
      iframe #
      ipureintro
      exact ⟨(Herr'.2 (by simp)).1, (Herr'.2 (by simp)).2, rfl⟩

end proof

end EtcdGrove
end Perennial
