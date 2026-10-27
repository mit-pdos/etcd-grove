/-
`(*peer).stop()` (`peer.go`; rafthttp stage 6b). Lean-first.
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

/-- **`p.stop()`** of a started peer with the right to stop it: it returns, its pipeline's four
resources back (its goroutines done). -/
abbrev rafthttp.peer.stop.spec : Prop :=
  ∀ (Rh : RaftHttp GF) (lid pid : w64) (γd : GName) (R : IProp GF) (p : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
      peerOk Rh lid pid γd R p ∗ peerStop Rh pid R p }}
    (App (Val (p @!! go.GoType.PointerType rafthttp.peer.ty @!! go!"stop")) (Val #()))
  {{ RET #(); R ∗ R ∗ R ∗ R }}

end spec

end EtcdGrove
end Perennial
