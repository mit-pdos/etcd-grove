/-
`cloneCommittedEntries(ents)` (`raft.go`; added by etcd-io/etcd#22496): a copy of the slice of
entry pointers in a new array of its length. Lean-first (2026-10-17, the verification of
etcd-io/etcd#22496: `notes/pr-verify/etcd-22496.md`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BaseApply

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **`cloneCommittedEntries(ents)`**, of a slice `ents` holding the pointers `L` (any fraction):
returns `ents` untouched and a slice `cp` holding the same pointers, fully owned (`↦*` at fraction
1, with its whole capacity: a new array, sharing no memory with `ents`, which is what decouples a
queued `toApply`'s entries from the raft log's array), and the nil slice when `L` is empty. The
entries themselves (the pointees) stay shared: only the pointers are copied. -/
abbrev cloneCommittedEntries.spec : Prop :=
  ∀ (ents : GoSlice) (L : List Loc) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ ents ↦*{dq} L }}
    (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.cloneCommittedEntries)) (Val #ents))
  {{ (cp : GoSlice), RET #cp; ents ↦*{dq} L ∗ cp ↦* L ∗ ownSliceCap Loc cp (DFrac.own 1) ∗
      ⌜L = [] → cp = slice.nil⌝ }}

end spec

end EtcdGrove
end Perennial
