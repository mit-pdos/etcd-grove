/-
`logSlice.lastIndex` (`types.go`), first called from verified code by etcd-io/raft#155's
`raftLog.maybeAppend` (`notes/pr-verify/raft-155.md`).
-/
module

public import Proof.go_etcd_io.raft.v3.InvReadylog

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

/-- `s.lastIndex()` is `s.prev.index + len(s.entries)` (wrapping, as the Go does; a
well-formed slice does not wrap). The receiver is a value: nothing is read but `s`. -/
abbrev logSlice.lastIndex.spec : Prop :=
  ∀ (s : logSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 }}
    (App (Val (s @!! logSlice.ty @!! go!"lastIndex")) (Val #()))
  {{ RET #(s.prev'.index' + s.entries'.len); True }}

end spec

end EtcdGrove
end Perennial
