/-
`(*remote).send(m)` (`remote.go`; rafthttp stage 6b). Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Transport

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.api

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`g.send(m)`** of a started remote and a message for its peer: it returns, the message handed
to the pipeline or dropped (its channel full). -/
abbrev rafthttp.remote.send.spec : Prop :=
  ∀ (Rh : RaftHttp GF) (lid pid : w64) (R : IProp GF) (g ml : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
      remoteOk Rh lid pid R g ∗ pipeMsg Rh pid ml }}
    (App (Val (g @!! go.GoType.PointerType rafthttp.remote.ty @!! go!"send")) (Val #ml))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
