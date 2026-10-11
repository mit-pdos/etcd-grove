/-
Proof of `Spec/.../mvcc/NewRevBytes.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.NewRevBytes


@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem mvcc.NewRevBytes.wp_proof : mvcc.NewRevBytes.spec (GF := GF) (hG := hG) := by
  wp_start
  (try wp_auto)
  wp_apply wp_slice_make3 (V := w8) (W64 17) (W64 18) ⟨by decide, by decide⟩ as %sl ⟨Hsl, Hcap, %Hc⟩
  (try wp_auto)
  iapply HΦ
  iframe Hcap
  isplitl
  · simp only [show (zero_val w8 : w8) = W8 0 from rfl]
    iexact Hsl
  ipureintro; exact Hc

end proof

end EtcdGrove
end Perennial
