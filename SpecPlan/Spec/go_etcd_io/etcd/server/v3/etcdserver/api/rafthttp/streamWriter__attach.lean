/-
## `(*streamWriter).attach(conn)`

**Users.** `peer.attachOutgoingConn`.

**Proof sketch.** A `select` on `connc` (the loop takes the connection) and `done`.

**Changes.** Restated over the new vocabulary (was over `specs-ref`'s `TransportState`/`TransportInv` records, `NetNames`, `netBundle`); same behaviour.

**Margin.** None.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Rafthttp

open Iris Iris.BI Raft
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- (internal) Hands a connection to the loop, or `false` (stopped: the connection given back). -/
def streamWriter.attach.spec : Prop :=
  ∀ (cw : Loc) (ν : Net GF) (lid pid : w64) (K : Msg → Prop) (c : Loc) (t : StreamTy),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗ swAt cw ν lid pid K ∗ outConn c ν lid pid t ∗ ⌜t = StreamTy.msgAppV2 → ∀ m, K m → m.type = MsgApp⌝ }}
    (App (Val (cw @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.streamWriter.ty @!! go!"attach")) (Val #c))
  {{ (b : Bool), RET #b; if b then iprop(True) else outConn c ν lid pid t }}

end spec
end Rafthttp
end EtcdGrove
end Perennial
