/-
`UnsafeAdd`'s proof (`internal/common/unsafe.go`): a stub, proved by U1 of
`notes/bbolt-proof-plan.md`.
-/
module

public import Spec.go_etcd_io.bbolt.internal.common.UnsafeAdd
public import Perennial.Golang.Theory.Plain

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs
namespace internal
namespace common

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt.internal.common

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.common.Assumptions]

theorem UnsafeAdd.wp_proof : UnsafeAdd.spec (GF := GF) (hG := hG) := by
  intro base off H1 H2
  wp_start
  wp_auto
  wp_func_call
  wp_call
  wp_apply wp_pointer_plus _ _ _ ⟨H1, H2⟩
  iapply HΦ
  itrivial

end proof

end common
end internal
end bbolt
end EtcdGrove
end Perennial
