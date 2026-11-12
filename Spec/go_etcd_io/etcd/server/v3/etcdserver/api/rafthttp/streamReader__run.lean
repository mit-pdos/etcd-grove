/-
`(*streamReader).run` (`stream.go`; rafthttp stage 5c). Lean-first; the reader's predicates:
`rafthttp/Reader.lean`, `rafthttp/ReaderRun.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.ReaderRun

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

/-- **`cr.run()`**, the reader's goroutine: dials the peer, then decodes the stream it gets
(`decodeLoop`), again and again at the rate limiter's pace, until the reader's context is done; then
closes `done` and returns. -/
abbrev rafthttp.streamReader.run.spec : Prop :=
  ∀ (Rh : RaftHttp GF) (lid pid : w64) (γd : GName) (cr : Loc) (ty : StreamTy),
  Rh.member lid → lid ≠ pid →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
      srFixed Rh lid pid γd cr ∗ srDial Rh pid ty cr ∗ srDoneRight cr }}
    (App (Val (cr @!! go.GoType.PointerType rafthttp.streamReader.ty @!! go!"run")) (Val #()))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
