/-
`tracker.Inflights.Clone`, Lean-first (no Rocq counterpart).
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

/-- `in.Clone()` (`tracker.Inflights.Clone.impl`, `Code/go_etcd_io/raft/v3/tracker.lean`;
inflights.go:55):

    ins := *in
    ins.buffer = append([]inflight(nil), in.buffer...)
    return &ins

A fresh `Inflights` object at the same window, with its own copy of the ring buffer
(so the two can be used independently). No panic. -/
abbrev tracker.Inflights.Clone.spec : Prop :=
  ∀ (l : Loc) (i : Inflights),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗ ownInflights l i }}
    (App (Val (l @!! go.GoType.PointerType tracker.Inflights.ty @!! go!"Clone")) (Val #()))
  {{ (l' : Loc), RET #l'; ownInflights l i ∗ ownInflights l' i }}

end spec

end EtcdGrove
end Perennial
