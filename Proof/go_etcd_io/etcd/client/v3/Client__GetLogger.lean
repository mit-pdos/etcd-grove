/-
Proof of `Spec/go_etcd_io/etcd/client/v3/Client__GetLogger.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.Client__GetLogger
public import Proof.go_etcd_io.etcd.client.v3.InvCmpTypes

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

theorem Client.GetLogger.wp_proof : Client.GetLogger.spec (GF := GF) (hG := hG) := by
  intro cl
  wp_start as #Hlg
  wp_auto
  wp_bind (App (Val #(methods _ _ _)) (Val #()))
  iapply (sync.atomic.Pointer.wp_Load (T' := go_uber_org.zap.Logger) go_uber_org.zap.Logger.ty
    (clientLgAddr cl) (DFrac.own 1))
  · iPkgInit
  unfold isClientLogger
  iinv Hlg with ⟨%lg, >Hp, >%Hnn⟩ Hclose
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists lg
  iframe Hp
  iintro Hp
  imod Hmask with -
  imod Hclose $$ [Hp] with -
  · inext; iexists lg; iframe; ipureintro; exact Hnn
  imodintro
  wp_auto
  iapply HΦ
  ipureintro; exact Hnn


end proof

end EtcdGrove
end Perennial
