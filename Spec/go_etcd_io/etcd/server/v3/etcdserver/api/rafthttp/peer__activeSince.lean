/-
`(*peer).activeSince` (`peer.go`: `p.status.activeSince()`; rdslot, 2026-11-22). Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Transport

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

/-- **`p.activeSince()`** of a started peer: the time it became active (its status's). -/
abbrev rafthttp.peer.activeSince.spec : Prop :=
  ∀ (Rh : RaftHttp GF) (lid pid : w64) (γd : GName) (R : IProp GF) (p : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
      peerOk Rh lid pid γd R p }}
    (App (Val (p @!! go.GoType.PointerType rafthttp.peer.ty @!! go!"activeSince")) (Val #()))
  {{ (t : _root_.Perennial.time.Time), RET #t; True }}

end spec

end EtcdGrove
end Perennial
