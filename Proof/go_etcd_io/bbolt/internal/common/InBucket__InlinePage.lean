/-
`(*InBucket).InlinePage`'s proof (`internal/common/bucket.go`): a stub, proved by U1 of
`notes/bbolt-proof-plan.md`.
-/
module

public import Spec.go_etcd_io.bbolt.internal.common.InBucket__InlinePage
public import Proof.go_etcd_io.bbolt.internal.common.Lemmas.Layout

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

namespace internal
namespace common

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt.internal.common

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.common.Assumptions]

theorem InBucket.InlinePage.wp_proof : InBucket.InlinePage.spec (GF := GF) (hG := hG) := by
  intro l buf Hlen Hc
  wp_start
  wp_auto
  have h16 : sint.Z (W64 16) = 16 := rfl
  rw [h16, ite_cond_eq_true _ _ (eq_true ⟨by omega, Hlen⟩), sliceIndexRef_byte _ _ Hc (by omega)]
  wp_auto
  iapply HΦ; itrivial

end proof

end common
end internal
end bbolt
end EtcdGrove
end Perennial
