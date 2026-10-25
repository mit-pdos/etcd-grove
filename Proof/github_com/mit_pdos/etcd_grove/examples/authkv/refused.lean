/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/authkv/refused.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.authkv.refused

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace authkv

open Iris Iris.BI Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.authkv.Assumptions]

theorem refused.wp_proof : refused.spec (GF := GF) (hG := hG) := by
  intro who what err Herr
  wp_start
  cases err with
  | nil => exact absurd rfl Herr
  | ok i =>
    wp_auto
    wp_end

end proof

end authkv
end EtcdGrove
end Perennial
