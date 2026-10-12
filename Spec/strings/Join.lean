/-
Port of `election_proof/spec_strings_Join.v` (feb5c73d4).
-/
module

public import Proof.go_etcd_io.raft.v3.InvRaftPhys
public import Perennial.Proof.strings.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `strings.Join` is goose's translation, and Perennial proves `strings.wp_Join` for it when
the result fits (`strings.JoinFits`: at most one element, or a join of at most
`maxAlloc` bytes; Go panics otherwise). `newRaft` uses it only to build a log line; the
postcondition is *some* string. -/
abbrev strings.Join.spec : Prop :=
  ∀ (elems : GoSlice) (xs : List GoString) (dq : DFrac) (sep : GoString),
  _root_.Perennial.strings.JoinFits xs sep →
  {{ isPkgInit (PROP := IProp GF) pkg_id.strings ∗ elems ↦*{dq} xs }}
    (App (App (Val #(functions _root_.Perennial.strings.Join [])) (Val #elems)) (Val #sep))
  {{ (s : GoString), RET #s; elems ↦*{dq} xs }}

end spec

end EtcdGrove
end Perennial
