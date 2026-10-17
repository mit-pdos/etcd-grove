/-
Proof of `Spec/go_etcd_io/etcd/client/v3/WithZapLogger.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.WithZapLogger

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

theorem WithZapLogger.wp_proof : WithZapLogger.spec (GF := GF) (hG := hG) := by
  intro lg
  wp_start
  iapply wp_fupd
  wp_auto
  ipersist lg
  imodintro
  simp only [recv_eq_func_mk]
  iapply HΦ
  unfold ctxClientOptOk
  imodintro
  iintro %c %lg0
  wp_start as Hp
  wp_auto
  wp_bind (App (Val #(methods _ _ _)) (Val _))
  iapply (sync.atomic.Pointer.wp_Store (T' := go_uber_org.zap.Logger) go_uber_org.zap.Logger.ty
    (clientLgAddr c) lg)
  · iPkgInit
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists lg0
  iframe Hp
  iintro Hp
  imod Hmask with -
  imodintro
  wp_auto
  iapply HΦ
  iexists lg
  iframe

end proof

end EtcdGrove
end Perennial
