/-
`clientv3.WithSort(target, order)` (`client/v3/op.go`, translated for `client/v3/concurrency`). Lean-first (no Rocq
counterpart); see `InvOp.lean`.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvOp

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `WithSort(target, order)`: an option setting the sort option (a fresh `*SortOption`), for any
`target`/`order` but a sort by key in ascending order: for that one the closure rewrites the
`order` it captured to `SortNone` (`order = SortNone`), a write to a variable shared by every call
of the closure, a data race if it is called concurrently, about which Perennial's semantics (no
atomicity for a Go variable) can say nothing; a caller wanting keys in ascending order passes no
sort. -/
abbrev WithSort.spec : Prop :=
  ∀ (target order : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      ⌜¬ (target = W64 0 ∧ order = W64 1)⌝ }}
    (App (App (Val (@! go_etcd_io.etcd.client.v3.WithSort)) (Val #target)) (Val #order))
  {{ (f : GoFunc), RET #f; optSpec f (withSortM target order) }}

end spec

end EtcdGrove
end Perennial
