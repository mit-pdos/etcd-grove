/- Lean-first (no Rocq counterpart).

`Node(c, addr, eps)` (`examples/etcd/dist/kvremote`): client machine `c`'s program, at `addr`: a
clientv3 client of the endpoints `eps` (`etcdstart.NewClients`), then `remote.ServeClient` whose
operation is `txnlin.Call` through that client. It is safe (it never returns in Go once its client is
made; the post claims nothing), from `kvNodePreL c addr eps`: the level token `Call` takes, the thread
bound `NewClients` takes, and the machine's share `kvNodePre c addr eps` (at the global ghost state only,
what the machine's boot is handed): for some view `Γ` of the cluster (auth off), every endpoint a member
of `Γ` (`membersAt`, the start's share: the address facts), and `addr` serving the store `kvR Γ.kv`'s
calls (`remoteAddr`, at the cluster's KV names); the pure facts `NewClients` and `Call` take (plain
endpoints, `EtcdError` an `errors.As` target, a watch environment to name the client at). The level token
and the thread bound are of the machine's local ghost state, which its boot makes.

The spec is an instance of N7-kv's schema `Node.specWith NP` (`etcd-safe-n7kv`,
`dist/kvremote/NodeWith.lean`), at `NP := kvNodePreL`: same binders `c addr eps epsL`, same pre
`isPkgInit kvremote ∗ eps ↦* epsL ∗ NP c addr epsL`, same post. Proved in
`Proof/.../dist/kvremote/Node.lean`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.Store
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.KVClientDist
public import Perennial.Proof.errors.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote

open Iris Iris.BI Net
open EtcdGrove EtcdGrove.etcd_txnlin EtcdGrove.etcd_dist
open github_com.mit_pdos.etcd_grove.examples.lib.remote

section share
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [Gg : GooseGlobalGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.Assumptions]
variable [π : NetProtoGS] [ρ : RemoteGS]

/-- **A client machine's share** (see the file header), at its number `c` (unused), its address
`addr` and its endpoints `eps`; at the global ghost state only. -/
def kvNodePre (_c : w64) (addr : GoString)
    (eps : List GoString) : IProp GF :=
  iprop(∃ Γ : DistView,
    ⌜Γ.auth = false ∧ plainEndpoints eps ∧
      errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty ∧
      Nonempty (client.WEnv GF)⌝ ∗
    membersAt (Gg := Gg) eps Γ ∗
    remoteAddr (Gg := Gg) (kvR (GF := GF) Γ.kv) addr)

end share

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.Assumptions]
variable [π : NetProtoGS] [ρ : RemoteGS]

/-- **What a client machine needs** (see the file header): the level token, the thread bound and its
share `kvNodePre`. -/
def kvNodePreL (c : w64) (addr : GoString) (eps : List GoString) : IProp GF :=
  iprop(levelTok 0 ∗ ⌜threadBound GF ≤ 2 ^ 30⌝ ∗ kvNodePre (Gg := hG.goose_globalGS) c addr eps)

/-- See the file header. -/
abbrev Node.spec : Prop :=
  ∀ (c : w64) (addr : GoString) (eps : GoSlice) (epsL : List GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote ∗
      eps ↦* epsL ∗ kvNodePreL c addr epsL }}
    (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.Node))
      (Val #c)) (Val #addr)) (Val #eps))
  {{ RET #(); True }}

end spec

end github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote
end Perennial
