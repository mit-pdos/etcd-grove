/-
Proof of `Spec/go_etcd_io/etcd/client/v3/Client__WithLogger.lean` (PR etcd#22658).
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.Client__WithLogger
public import Proof.go_etcd_io.etcd.client.v3.InvCmpTypes

@[expose] public section

set_option linter.unusedSectionVars false

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

theorem Client.WithLogger.wp_proof : Client.WithLogger.spec (GF := GF) (hG := hG) := by
  intro cl lg
  wp_start as ⟨#Hlg, %Hnn⟩
  wp_auto
  wp_bind (App (Val #(methods _ _ _)) (Val #lg))
  iapply (sync.atomic.Pointer.wp_Store (T' := go_uber_org.zap.Logger) go_uber_org.zap.Logger.ty
    (clientLgAddr cl) lg)
  · iPkgInit
  unfold isClientLogger
  iinv Hlg with ⟨%lg0, >Hp, -⟩ Hclose
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists lg0
  iframe Hp
  iintro Hp
  imod Hmask with -
  imod Hclose $$ [Hp] with -
  · inext; iexists lg; iframe; ipureintro; exact Hnn
  imodintro
  wp_auto
  iapply HΦ
  isplitr
  · ipureintro; rfl
  iexact Hlg

end proof

end EtcdGrove
end Perennial
