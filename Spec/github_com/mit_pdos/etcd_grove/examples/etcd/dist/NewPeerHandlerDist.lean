/- Lean-first (no Rocq counterpart).

`etcdhttp.NewPeerHandler(lg, s)` on a member machine of a distributed deployment (interim trust boundary until
phase 7 S5 and the translation of `etcdhttp`; `notes/etcd-dist-plan.md`, "Interim transport"): on a started member
(`isServerReqM`, `Start`'s post) of its network (`srvNetMember`, `NewServer_dist`'s post), it returns etcd's peer
handler of `s` (`peerHandlerOf h s`), what `PeerServe_dist` serves. The axiom is
`Proof/.../etcd/dist/NewPeerHandlerDist.lean`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.S5Interim
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRaftHandler
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ReqOn
public import Spec.go_uber_org.zap.Defs
public import GeneratedProof.go_etcd_io.etcd.server.v3.etcdserver.api.etcdhttp

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.etcdhttp.Assumptions]

/-- See the file header. `s` is passed as etcd's `ServerPeerV2` interface (the `*EtcdServer`). -/
abbrev NewPeerHandler_dist.spec : Prop :=
  ∀ (lg s : Loc) (γn : NetNames GF) (id : w64) (τ : SrvTr GF) (on : Bool) (E : apply.AEnv GF)
    (ρ : ReqNames),
  {{ zapLoggerOk lg ∗ srvNetMember γn s id τ ∗ isServerReqM on s E ρ }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.etcdhttp.NewPeerHandler)) (Val #lg))
      (Val #(interface.mkOk (go.GoType.PointerType EtcdServer.ty) #s : GoInterface)))
  {{ (h : GoInterface), RET #h; peerHandlerOf h s }}

end spec

end etcd_dist
end EtcdGrove
end Perennial

end
