/- Lean-first (no Rocq counterpart).

`s.ReadyNotify()` (`server.go`: `return s.readych`), etcd-dist N5 (`notes/etcd-dist-plan.md` §19): from a
receiver's share of `s.readych` (`srvReadyRecv`), it returns the channel, with the broadcast idiom's persistent
part, on which a receive blocks until `publishV3` closes it (`broadcast_chan_receive`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ReadyRecv

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- See the file header. -/
abbrev EtcdServer.ReadyNotify.spec : Prop :=
  ∀ (s : Loc),
  {{ srvReadyRecv (GF := GF) s }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"ReadyNotify")) (Val #()))
  {{ (rdc : GoChan), RET #rdc; ∃ γ : ChanNames, ownBroadcastChan rdc γ iprop(True) .Unknown }}

end spec

end EtcdGrove
end Perennial

end
