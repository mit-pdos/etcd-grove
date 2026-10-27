/-
`(*peer).pick(m)` (`peer.go`; rafthttp stage 6b). Lean-first.
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


/-- **`p.pick(m)`** of a started peer and a message of state `st`: the channel to send it on, a bag
of the msgappv2 stream's messages (for a `MsgApp`), the message stream's, or the pipeline's. -/
abbrev rafthttp.peer.pick.spec : Prop :=
  ∀ (Rh : RaftHttp GF) (lid pid : w64) (γd : GName) (R : IProp GF) (p ml : Loc) (st : MsgSt),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
      peerOk Rh lid pid γd R p ∗ msgOwn ml DFrac.discard st }}
    (App (Val (p @!! go.GoType.PointerType rafthttp.peer.ty @!! go!"pick")) (Val #ml))
  {{ (wc : GoChan) (name : GoString), RET (PairV #wc #name);
      (∃ γ, isChanBag γ wc (swMsg Rh .msgAppV2 lid pid) ∗ ⌜st.msg.Type' = MsgApp⌝) ∨
      (∃ γ, isChanBag γ wc (swMsg Rh .message lid pid)) ∨
      (∃ γ, isChanBag γ wc (pipeMsg Rh pid)) }}

end spec

end EtcdGrove
end Perennial
