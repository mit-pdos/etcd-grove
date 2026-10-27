/-
`(*streamWriter).run` (`stream.go`; rafthttp stage 5b). Lean-first; the writer's predicates:
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`cw.run()`**, the writer's goroutine, from its start (not working, no closer; with its
halves, the right to close `done`, and one of the `Raft`'s resources `Rr`): returns once stopped. -/
abbrev rafthttp.streamWriter.run.spec : Prop :=
  ∀ (Rh : RaftHttp GF) (ty : StreamTy) (lid pid : w64) (Rr : IProp GF) (cw : Loc) (mc : GoChan),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
      swFixed Rh ty lid pid Rr cw ∗ swRunOwn Rh ty lid pid cw mc false GoInterface.nil ∗
      swDoneRight cw ∗ Rr }}
    (App (Val (cw @!! go.GoType.PointerType rafthttp.streamWriter.ty @!! go!"run")) (Val #()))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
