/-
`(*remote).stop()` (`remote.go`; rafthttp stage 6b). Lean-first.
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

/-- **`g.stop()`** with the right to stop it: it returns, its pipeline's four resources back. -/
abbrev rafthttp.remote.stop.spec : Prop :=
  ∀ (Rh : RaftHttp GF) (lid pid : w64) (R : IProp GF) (g : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
      remoteOk Rh lid pid R g ∗ remoteStop Rh pid R g }}
    (App (Val (g @!! go.GoType.PointerType rafthttp.remote.ty @!! go!"stop")) (Val #()))
  {{ RET #(); R ∗ R ∗ R ∗ R }}

end spec

end EtcdGrove
end Perennial
