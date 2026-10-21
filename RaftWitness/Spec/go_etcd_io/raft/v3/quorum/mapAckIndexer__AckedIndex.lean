/-
`quorum.mapAckIndexer.AckedIndex`, Lean-first (no Rocq counterpart).
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

/-- `m.AckedIndex(id)` for `m : mapAckIndexer`, a named `map[uint64]Index`
(`quorum.mapAckIndexer.AckedIndex.impl`, `Code/go_etcd_io/raft/v3/quorum.lean`;
quorum.go:40):

    idx, ok := m[id]
    return idx, ok

No panic, no call. The receiver is the map itself, read at any fraction; the result is
the lookup in the `(value-or-0, ok)` form of `isAckedIndexer`'s contract. -/
abbrev quorum.mapAckIndexer.AckedIndex.spec : Prop :=
  ∀ (mref : Loc) (dq : DFrac) (mm : GMap w64 w64) (id : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.quorum ∗ mref ↦${dq} mm }}
    (App (Val (mref @!! quorum.mapAckIndexer.ty @!! go!"AckedIndex")) (Val #id))
  {{ RET (PairV #((mm !! id).getD (W64 0)) #((mm !! id).isSome)); mref ↦${dq} mm }}

end spec

end EtcdGrove
end Perennial
