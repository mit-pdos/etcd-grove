/-
`raftpb.sovRaft(x)` (`raft.pb.go:1416`, gogoproto): the length of `x`'s varint
encoding, `(bits.Len64(x|1) + 6) / 7`. Lean-first (no Rocq counterpart): it is
`Entry.Size`'s one callee, translated with it on 2026-10-08.
-/
import EtcdGrove.Raft.Base

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

/-- `sovRaft` returns, and says nothing about the value: `Entry.Size`'s spec does not
either (see `Spec/Entry__Size.lean`). -/
abbrev raftpb.sovRaft.spec : Prop :=
  ∀ (x : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb }}
    (App (Val #(functions raftpb.sovRaft [])) (Val #x))
  {{ (n : w64), RET #n; True }}

end spec

end EtcdGrove
end Perennial
