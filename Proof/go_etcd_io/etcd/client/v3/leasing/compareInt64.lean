/-
Proof of `Spec/go_etcd_io/etcd/client/v3/leasing/compareInt64.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.leasing.compareInt64

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace leasing

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.leasing go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

theorem compareInt64.wp_proof : compareInt64.spec (GF := GF) (hG := hG) := by
  intro a b
  wp_start
  wp_auto
  unfold compareInt64M
  by_cases h1 : sint.Z a < sint.Z b
  · simp only [h1, decide_true, ↓reduceIte]
    wp_auto
    wp_end
  · simp only [h1, decide_false, ↓reduceIte]
    wp_auto
    by_cases h2 : sint.Z b < sint.Z a
    · simp only [h2, decide_true, ↓reduceIte]
      wp_auto
      wp_end
    · simp only [h2, decide_false, ↓reduceIte]
      wp_auto
      wp_end

end proof

end leasing
end EtcdGrove
end Perennial
