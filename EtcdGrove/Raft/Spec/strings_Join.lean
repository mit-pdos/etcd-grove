/-
Port of `election_proof/spec_strings_Join.v` (feb5c73d4).
-/
import EtcdGrove.Raft.InvRaftPhys

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

/-- `strings.Join` is not translated (`new/code/strings.v`, Lean
`Perennial/Code/strings.lean`, declares only the name), so this is an `Axiom`: Go's
standard library, outside raft. `newRaft` uses it only to build a log line; the
postcondition is *some* string. -/
abbrev strings.Join.spec : Prop :=
  ∀ (elems : GoSlice) (xs : List GoString) (dq : DFrac) (sep : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.strings ∗ elems ↦*{dq} xs }}
    (App (App (Val #(functions _root_.Perennial.strings.Join [])) (Val #elems)) (Val #sep))
  {{ (s : GoString), RET #s; elems ↦*{dq} xs }}

end spec

end EtcdGrove
end Perennial
