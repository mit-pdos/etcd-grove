/-
`(*streamType).String` (`stream.go`; rafthttp stage 5b). Lean-first; the writer's predicates:
`rafthttp/Writer.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Writer

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.api go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`(*streamType).String`** (a pointer to a stream type, `t.String()` of a local variable): a
string. -/
abbrev rafthttp.streamType.String_ptr.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (t : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
      p ↦{dq} t }}
    (App (Val (p @!! go.GoType.PointerType rafthttp.streamType.ty @!! go!"String")) (Val #()))
  {{ (s : GoString), RET #s; p ↦{dq} t }}

end spec

end EtcdGrove
end Perennial
