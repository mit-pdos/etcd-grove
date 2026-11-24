/-
`Member(peer, client)` (`examples/etcd/dist/putget/putget.go`): the member machine's program of
`putget_safe` -- the one member of a new cluster (`etcdstart.StartServer(Name, peer,
client, zap.NewNop())`), etcd's gRPC API served at `client` (`etcdstart.Serve`), then `holdForever()`; an
error from a step returns. Lean-first (no Rocq counterpart); `notes/putget-dist-plan.md`, section 10.

**The triple:** from the package's `isPkgInit`, the main thread's token, the member's named Iris premises
(`etcdstart.premises`, the in-process putget's), `ETCD_VERIFY` off (`envVerifyOff`, the statement's
`HEnvTok`), its data directory fresh (`dataDirFresh`) and its WAL area
fresh (`memberAreasFresh`), its share of the distributed start over the interim cross-machine
vocabulary (`memberShare`, `notes/putget-dist-plan.md` §12: its client address set to serve etcd's KV
calls for the publication name `γE` and its member id `id`, its half of the publication token, the
publication invariant at `Pub`) and the obligation on `Pub` (`memberPubOk`: a putget invariant gives
`Pub` of the view of its KV state variable), `Member` does not panic. It publishes its view at `γE`
(`env_publish`) before `Serve`, with the client's putget invariant allocated from the bootstrap log's
KV state.

**The pure premises:** the in-process putget's (`Spec/.../examples/etcd/putget/Main.lean`): `bootstrap`'s
results (`BootFacts`), the logic's bounds (as the logic's bound classes, `ThreadBoundLe`/`ReceiptBoundLe` at
`2 ^ 28`, the distributed adequacy's; the apply thread's write budget fixed at `2 ^ 28`), the thread levels a
served member needs (`srvLevels`), the server's workload and environment premises, the gRPC service
values' method sets; and the peer URL `http://peer` plain (`host:port`, what the one-member directory
takes).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.putget.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.OneMember
public import Proof.go_etcd_io.etcd.server.v3.storage.WalAreaFresh
public import Proof.go_etcd_io.etcd.client.pkg.v3.verify.Env

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_putget_dist

open Iris Iris.BI Net go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.putget.Assumptions]

/-- See the file header. -/
abbrev Member.spec : Prop :=
  ∀ [go_etcd_io.etcd.cache.v3.Assumptions] [π : NetProtoGS]
    [ThreadBoundLe GF (2 ^ 28)] [ReceiptBoundLe GF (2 ^ 28)]
    (peer client : GoString) (id : w64) (ctxs : List (List w8)) (boot : List LogEntry)
    (γE : GName) (Pub : etcd_dist.EnvView → IProp GF),
  etcdstart.BootFacts id ctxs boot →
  types.plainPeerURL (go!"http://" ++ peer) →
  srvLevels (GF := GF) →
  authRecordsFit → apply.backendUnderQuota → grpcRepliesFit → storage.diskOk →
  v3rpc.ServerMethodSets →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.putget ∗
      threadTok ∗ etcdstart.premises (GF := GF) name peer client (2 ^ 28) id ctxs boot ∗
      envVerifyOff (GF := GF) ∗ dataDirFresh (GF := GF) (memberDataDir name) ∗ memberAreasFresh (GF := GF) (memberDataDir name) ∗
      memberShare (G := hG.goose_globalGS) client γE id Pub ∗ memberPubOk Pub }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.dist.putget.Member)) (Val #peer))
      (Val #client))
  {{ RET #(); True }}

end spec

end etcd_putget_dist
end EtcdGrove
end Perennial
