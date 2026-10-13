/-
`tracker.Inflights.Count`, Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.raft.v3.InvTracker

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `in.Count()` (`tracker.Inflights.Count.impl`, `Code/go_etcd_io/raft/v3/tracker.lean`;
inflights.go:136): `return in.count`. The number of messages in flight, as the `int` it
is (`i.count` is its signed value, `inflightsAbs`). -/
abbrev tracker.Inflights.Count.spec : Prop :=
  ∀ (l : Loc) (i : Inflights),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗ ownInflights l i }}
    (App (Val (l @!! go.GoType.PointerType tracker.Inflights.ty @!! go!"Count")) (Val #()))
  {{ RET #(W64 i.count); ownInflights l i }}

end spec

end EtcdGrove
end Perennial
