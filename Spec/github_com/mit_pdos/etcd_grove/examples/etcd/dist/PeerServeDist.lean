/- Lean-first (no Rocq counterpart).

`http.Serve(pl, h)` of etcd's peer handler on a member machine's peer listener (interim trust boundary until phase 7
S5 across machines; `notes/etcd-dist-plan.md`, "Interim transport"): `examples/etcd/dist/server`'s
`go http.Serve(pl, etcdhttp.NewPeerHandler(lg, s))` after `s.Start()`. The axiom is
`Proof/.../etcd/dist/PeerServeDist.lean`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.S5Interim
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRaftHandler
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ReqOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApplyAll
public import Proof.net.InvNet
public import Proof.net.http.Boundary

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist

open Iris Iris.BI Net go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`http.Serve(pl, h)` of etcd's peer handler at the member's peer address** (see the file header): `pa` set to
etcd's peer protocols of `s`'s cluster and member (`httpAddrAt γ.cl id pa`), `pl` a listener open at `pa` (`netListenerOpen`, from `net.Listen` through
`listen_au` over `httpAddrAt`'s `addrProto`), `h` etcd's peer handler of `s` (`peerHandlerOf`), `s` started
(`isServerReqM`) and member `id` of its network (`srvNetMember`), with the handler's per-request resources
(`httpProcSlots` of `srvServeRes`, `NewServer_dist`'s post, as the in-process `http.Serve_ok` takes them). -/
abbrev PeerServe_dist.spec : Prop :=
  ∀ [π : NetProtoGS] (pl h : GoInterface) (pa : GoString) (s : Loc) (γn : NetNames GF) (id : w64)
    (τ : SrvTr GF) (on : Bool) (E : apply.AEnv GF) (ρ : ReqNames) (γ : SrvRaft),
  -- the member's network is its cluster's (`NewServer_dist`'s post)
  γn.N = srvNet γ →
  -- `pa` is the member's own peer address (its directory entry; review of 2026-11-24)
  go!"http://" ++ pa ∈ γn.dir id →
  {{ httpAddrAt (Gg := hG.goose_globalGS) γ.cl id pa ∗ netListenerOpen pl pa ∗ peerHandlerOf h s ∗
      srvNetMember γn s id τ ∗ isServerReqM on s E ρ ∗
      ([∗list] _x ∈ List.replicate http.httpProcSlots (), srvServeRes γn τ) }}
    (App (App (Val (@! _root_.Perennial.net.http.Serve)) (Val #pl)) (Val #h))
  {{ (err : GoInterface), RET #err; True }}

end spec

end etcd_dist
end EtcdGrove
end Perennial

end
