/- Lean-first (no Rocq counterpart).

`Node(c, addr, eps)` (`examples/etcd/dist/kvremote`): client machine `c`'s program, at `addr`: a
clientv3 client of the endpoints `eps` (`etcdstart.NewClients`), then `remote.ServeClient` whose
operation is `txnlin.Call` through that client. It is safe (it never returns in Go once its client is
made; the post claims nothing), from `kvNodePre svc c addr eps`: for some view `Γ` of the cluster
(auth off), the level token `Call` takes, every endpoint a member of `Γ` (`membersAtV`, the start's
share: the address facts), and `addr` serving the store `kvR Γ.kv`'s calls (`remoteAddr`, at the
cluster's KV names); the pure facts `NewClients` and `Call` take (the thread bound, plain endpoints,
`EtcdError` an `errors.As` target, a watch environment to name the client at).

The spec is an instance of N7-kv's schema `Node.specWith NP` (`etcd-safe-n7kv`,
`dist/kvremote/NodeWith.lean`), at `NP := kvNodePre svc`: same binders `c addr eps epsL`, same pre
`isPkgInit kvremote ∗ eps ↦* epsL ∗ NP c addr epsL`, same post. Proved in
`Proof/.../dist/kvremote/Node.lean`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.Store
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.ClientViewDist
public import Perennial.Proof.errors.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote

open Iris Iris.BI Net
open EtcdGrove EtcdGrove.etcd_txnlin EtcdGrove.etcd_dist.view
open github_com.mit_pdos.etcd_grove.examples.lib.remote

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.Assumptions]
variable [π : NetProtoGS] [ρ : RemoteGS]

/-- **What a client machine needs** (see the file header), at its number `c` (unused), its address
`addr` and its endpoints `eps`. -/
def kvNodePre (svc : DistView → w64 → GrpcSvc GF) (_c : w64) (addr : GoString)
    (eps : List GoString) : IProp GF :=
  iprop(∃ Γ : DistView,
    ⌜Γ.auth = false ∧ threadBound GF ≤ 2 ^ 30 ∧ plainEndpoints eps ∧
      errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty ∧
      Nonempty (client.WEnv GF)⌝ ∗
    levelTok 0 ∗
    membersAtV (Gg := hG.goose_globalGS) svc eps Γ ∗
    remoteAddr (Gg := hG.goose_globalGS) (kvR (GF := GF) Γ.kv) addr)

/-- See the file header. -/
abbrev Node.spec (svc : DistView → w64 → GrpcSvc GF) : Prop :=
  ∀ (c : w64) (addr : GoString) (eps : GoSlice) (epsL : List GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote ∗
      eps ↦* epsL ∗ kvNodePre svc c addr epsL }}
    (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.Node))
      (Val #c)) (Val #addr)) (Val #eps))
  {{ RET #(); True }}

end spec

end github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote
end Perennial
