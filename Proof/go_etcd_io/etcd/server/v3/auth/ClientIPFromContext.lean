/-
Proof of `Spec/go_etcd_io/etcd/server/v3/auth/ClientIPFromContext.lean` (PR etcd#22259).
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.ClientIPFromContext

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.auth auth

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

theorem auth.ClientIPFromContext.wp_proof :
    auth.ClientIPFromContext.spec (GF := GF) (hG := hG) := by
  intro ctx o
  wp_start as #Hctx
  wp_auto
  wp_bind (App (Val #(methods ctx.ty go!"Value" ctx.v)) _)
  iunfold auth.ctxClientIPIs at Hctx
  iapply Hctx
  inext
  iintro %v %Hv
  cases o with
  | some s =>
    subst Hv
    wp_auto
    simp only [Option.getD_some, Option.getD_none]
    iapply HΦ
    itrivial
  | none =>
    rcases Hv with rfl | ⟨ii, rfl, Hii⟩
    · wp_auto
      simp only [Option.getD_some, Option.getD_none]
      iapply HΦ
      itrivial
    · wp_auto
      simp only [Hii, ↓reduceIte]
      wp_auto
      simp only [Option.getD_some, Option.getD_none]
      iapply HΦ
      itrivial

end proof

end EtcdGrove
end Perennial
