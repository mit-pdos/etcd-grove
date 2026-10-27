/-
`(*streamWriter).attach` (`stream.go`; rafthttp stage 5b). Lean-first; the writer's predicates:
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

/-- **`cw.attach(conn)`** of a connection for the writer (`outConnOk`): hands it to `run` and
returns `true`, or, `run` having stopped, returns `false` with the connection. -/
abbrev rafthttp.streamWriter.attach.spec : Prop :=
  ∀ (Rh : RaftHttp GF) (ty : StreamTy) (lid pid : w64) (Rr : IProp GF) (cw conn : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
      swFixed Rh ty lid pid Rr cw ∗ outConnOk Rh ty lid pid conn }}
    (App (Val (cw @!! go.GoType.PointerType rafthttp.streamWriter.ty @!! go!"attach")) (Val #conn))
  {{ (b : Bool), RET #b; if b then iprop(True) else outConnOk Rh ty lid pid conn }}

end spec

end EtcdGrove
end Perennial
