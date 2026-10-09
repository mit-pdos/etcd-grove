/-
`conditionalProgressRequestor.add()` (`cache/progress_requestor.go`). Lean-first (no Rocq
counterpart); see `InvCache.lean`.
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.InvCache

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.cache.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- `p.add()`: one more waiter (the count, under `p.mux`, wraps as an `int32`), and `p.cond`
signaled. -/
abbrev conditionalProgressRequestor.add.spec : Prop :=
  ∀ (p : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗ isProgressRequestor p }}
    (App (Val (p @!! go.GoType.PointerType conditionalProgressRequestor.ty @!! go!"add")) (Val #()))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
