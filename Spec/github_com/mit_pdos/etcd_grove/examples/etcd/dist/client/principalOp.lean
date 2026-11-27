/- Lean-first (no Rocq counterpart).

`principalOp(sys, in)` (`examples/etcd/dist/client/nodes.go`): **a principal machine's call** of the auth workload
(#50 F7 S7; `writerOp`'s pattern), the operation its `remote.ServeClient` runs for each of the orchestrator's calls:
`sys` the members' client addresses (`NodeMain` passes `eps`), `in` the principal's name; it connects the
principal's client (`principalClient`), runs `auth.Work` through it and closes it, answering `true`, or answers
`false` when the client fails to connect.

**The triple** is `remote.reportOp`'s (unfolded, as `writerOp.spec`), at the principals' wire and service (`PrincipalWire.lean`): from the
machine's resource `principalTok Γ addrs sys` (its level token, `sys` the addresses `addrs`, each serving a member
of `Γ`), a value describing the name `w` and the service's precondition `prP Γ γR addrs w` (the principals'
environment, `w` one of `auth.Principals()`), `principalOp` returns a value describing a `bool` (`prQ`: nothing
more) and gives the resource back. The pure premises are the clients' (`newClient`, `newUserClient`) and the
watch's (`WatchOn_dist`). Not yet proved: its proof is `etcd_auth.Work`'s dist proof (`notes/etcd-dist-f7.md`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.PrincipalWire
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist_client

open Iris Iris.BI Net client go_etcd_io.etcd.server.v3.etcdserver
open etcd_dist
open github_com.mit_pdos.etcd_grove.examples.lib.remote

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- See the file header. -/
abbrev principalOp.spec : Prop :=
  ∀ [π : NetProtoGS] (Γ : DistView) (γR : ServerRaftNames) (addrs : List GoString),
  Nonempty (WEnv GF) → threadBound GF ≤ 2 ^ 30 → plainEndpoints addrs → addrs ≠ [] →
  Γ.auth = true → (∀ a b : w64, Γ.au a = Γ.au b → a = b) →
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  ∀ (sys x : GoInterface) (w : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client ∗
      principalTok Γ addrs sys ∗ (principalWire (GF := GF)).ivAt x w ∗
      prP (Gg := hG.goose_globalGS) Γ γR addrs w }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.principalOp)) (Val #sys))
      (Val #x))
  {{ (v : GoInterface), RET #v; principalTok Γ addrs sys ∗
      ∃ b : Bool, (principalWire (GF := GF)).ovAt v b ∗ prQ (GF := GF) w b }}

end spec

end etcd_dist_client
end EtcdGrove
end Perennial
