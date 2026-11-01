/-
`(*remote).Pause()` (`remote.go`; #8's J8a-7, 2026-11-01, the fork's `goose-lean-remotepause`).
Lean-first.
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

/-- **`g.Pause()`** of a started remote: it returns, `paused` set (J8a-7: a remote paused by a flag, as a peer; until then `Pause` stopped the pipeline, a second call panicking). -/
abbrev rafthttp.remote.Pause.spec : Prop :=
  ∀ (Rh : RaftHttp GF) (lid pid : w64) (R : IProp GF) (g : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
      remoteOk Rh lid pid R g }}
    (App (Val (g @!! go.GoType.PointerType rafthttp.remote.ty @!! go!"Pause")) (Val #()))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
