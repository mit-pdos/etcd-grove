/-
`(*Page).Meta`'s proof (`internal/common/page.go`): a stub, proved by U1 of
`notes/bbolt-proof-plan.md`.
-/
module

public import Spec.go_etcd_io.bbolt.internal.common.Page__Meta
public import Proof.go_etcd_io.bbolt.internal.common.Lemmas.Layout
public import Spec.go_etcd_io.bbolt.internal.common.UnsafeAdd

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

theorem Page.Meta.wp_proof
    (wp_UnsafeAdd : UnsafeAdd.spec (GF := GF) (hG := hG)) :
    Page.Meta.spec (GF := GF) (hG := hG) := by
  intro l H1 H2
  wp_start
  wp_auto
  wp_apply wp_UnsafeAdd
  · ipureintro; rw [show sint.Z (W64 16) = 16 from rfl]; simp only [Loc.add]; omega
  · ipureintro; rw [show sint.Z (W64 16) = 16 from rfl]; simp only [Loc.add]; omega
  rw [show sint.Z (W64 16) = 16 from rfl]
  iapply HΦ
  itrivial

end proof

end common
end internal
end bbolt
end EtcdGrove
end Perennial
