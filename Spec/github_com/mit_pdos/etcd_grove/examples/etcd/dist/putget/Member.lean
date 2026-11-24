/-
`Member(peer, client)` (`examples/etcd/dist/putget/putget.go`): the member machine's program of
`putget_safe` -- the one member of a new cluster (`etcdstart.StartServer(Name, peer,
client, zap.NewNop())`), etcd's gRPC API served at `client` (`etcdstart.Serve`), then `holdForever()`; an
error from a step returns; it returns at once unless its addresses are valid (`AddrOk`, the net
extension's `addrOk`) and distinct (2026-11-24). Lean-first (no Rocq counterpart); `notes/putget-dist-plan.md`, section 10.

**The triple:** from the package's `isPkgInit`, the main thread's token and, once the addresses are valid and
distinct (a wand: what the machine's start gives only then), the member's named Iris premises
(`etcdstart.premises`, the in-process putget's), `ETCD_VERIFY` off (`envVerifyOff`, the statement's
`HEnvTok`), its WAL area and data directory fresh (`memberAreasFresh`; since 2026-11-24 no `dataDirFresh`,
which `bootstrap`'s slot no longer takes), its share of the distributed start over the interim cross-machine
vocabulary (`memberShare`, `notes/putget-dist-plan.md` §12: its client address set to serve etcd's KV
calls for the publication name `γE` and its member id `id`, its half of the publication token, the
publication invariant at `Pub`) and the obligation on `Pub` (`memberPubOk`: a putget invariant gives
`Pub` of the view of its KV state variable), `Member` does not panic. It publishes its view at `γE`
(`env_publish`) before `Serve`, with the client's putget invariant allocated from the bootstrap log's
KV state.

**The pure premises:** the in-process putget's (`Spec/.../examples/etcd/putget/Main.lean`): `bootstrap`'s
results (`BootFacts`), the logic's bounds (as the logic's bound classes: `ThreadBoundLe` at `2 ^ 28`, the server specs';
`ReceiptBoundLe` at `2 ^ 48`, the receipt bound of the server's request ids, `wp_StartServer1`'s ceiling, as
the single-process `etcd_all`'s; since 2026-11-24, `putget_safe`'s thread bound, before at `2 ^ 28`; the apply
thread's write budget fixed at `2 ^ 48 - 1`, the receipts less one), the thread levels a
served member needs (`srvLevels`), the server's workload and environment premises, the gRPC service
values' method sets; and the addresses' lengths those of Go strings (`AddrOk`'s loop). That the peer URL
`http://peer` is plain and the addresses within etcd's URL bounds follows from the check
(`etcd_dist.addrOk_plainPeerURL`, `etcd_dist.addrOk_addrFits`).
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
    [ThreadBoundLe GF (2 ^ 28)] [ReceiptBoundLe GF (2 ^ 48)]
    (peer client : GoString) (id : w64) (ctxs : List (List w8)) (boot : List LogEntry)
    (γE : GName) (Pub : etcd_dist.EnvView → IProp GF),
  etcdstart.BootFacts id ctxs boot →
  -- the addresses as Go strings (`AddrOk`'s loop runs to `len(a)`)
  peer.length + 1 < 2 ^ 63 → client.length + 1 < 2 ^ 63 →
  srvLevels (GF := GF) →
  authRecordsFit → apply.backendUnderQuota → grpcRepliesFit → storage.diskOk →
  v3rpc.ServerMethodSets →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.putget ∗
      threadTok ∗
      (⌜Net.addrOk peer = true ∧ Net.addrOk client = true ∧ peer ≠ client⌝ -∗
        etcdstart.premises (GF := GF) name peer client (2 ^ 48 - 1) id ctxs boot ∗
        envVerifyOff (GF := GF) ∗ memberAreasFresh (GF := GF) (memberDataDir name) ∗
        memberShare (G := hG.goose_globalGS) client γE id Pub ∗ memberPubOk Pub) }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.dist.putget.Member)) (Val #peer))
      (Val #client))
  {{ RET #(); True }}

end spec

end etcd_putget_dist
end EtcdGrove
end Perennial
