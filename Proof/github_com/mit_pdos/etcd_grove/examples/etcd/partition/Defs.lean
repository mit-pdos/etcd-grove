/-
Lean-first (no Rocq counterpart).

**linkv3p's `Main`, `startCluster`, `Apply`, `Check`: their named premises and vocabulary** (the
partition plan's S3a, 2026-10-20, `notes/partition-plan.md`). The cluster's (`examples/lib/cluster3`,
`cluster3/Defs.lean`, whose header explains each; until 2026-11-05 this file's) at linkv3p's
configuration (`clusterCfg`, `config()`'s): the member names `linkv3p-1`, `-2`, `-3`, the cluster
token `linkv3p`, the peer addresses `127.0.0.1:2384{1,2,3}`, the client addresses
`127.0.0.1:2383{1,2,3}` (every one served, to its bridge) and the bridges' `127.0.0.1:2385{1,2,3}`.
The bootstrap facts (`etcd_putget3.BootFacts`) are putget3's, which name no configuration.

**The member ids' order** (`BootFacts`): `id₁ id₂ id₃` are the ids of `linkv3p-1`, `-2`, `-3`,
and the peers `ps` (the bootstrap log's order, one conf change per member) are them in
`bootstrap`'s order, sorted by id: putget3's `BootFacts`. For linkv3p's names and token that order
is the names' (`0x77e2…`, `0xcc14…`, `0xecbe…`: `TestMemberIDs` in
`examples/etcd/partition/linkv3p_test.go` prints them; their 16 low bits `0x2126`, `0x3ef6`, `0xf29c` are
distinct and not `0`, D21e (A)), but the premises do not depend on it (2026-11-03, the final
whole-`bootOk` review's S1: until then the list `ids id₁ id₂ id₃ = [id₁, id₂, id₃]`, which putget3's
and restart3's ids do not meet).

**What a client's `Apply` takes** (`clientOk`) and **the cluster started with its clients**
(`clusterUp`, over the cluster's `cluster3.clusterAt`) are at the end.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.partition.Base
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.Inv

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_partition

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section pure
variable [GooseExts]

/-- **`bootstrap`'s results, as Go computes them**: putget3's, the peers `ps` in `bootstrap`'s
order (see the file header). -/
abbrev BootFacts (id₁ id₂ id₃ : w64) (ps : List w64) (ctxs : List (List w8)) (bl : List LogEntry) :
    Prop :=
  etcd_putget3.BootFacts id₁ id₂ id₃ ps ctxs bl

/-- The members' names. -/
abbrev name₁ : GoString := go!"linkv3p-1"
abbrev name₂ : GoString := go!"linkv3p-2"
abbrev name₃ : GoString := go!"linkv3p-3"

/-- The members' peer addresses (each member's one peer URL is `http://` of it). -/
abbrev peerAddr₁ : GoString := go!"127.0.0.1:23841"
abbrev peerAddr₂ : GoString := go!"127.0.0.1:23842"
abbrev peerAddr₃ : GoString := go!"127.0.0.1:23843"

/-- The members' client addresses (each served, to its bridge). -/
abbrev clientAddr₁ : GoString := go!"127.0.0.1:23831"
abbrev clientAddr₂ : GoString := go!"127.0.0.1:23832"
abbrev clientAddr₃ : GoString := go!"127.0.0.1:23833"

/-- The bridges' addresses (each a bridge to a member's client address, which its client dials;
`notes/client-cut-plan.md`). -/
abbrev bridgeAddr₁ : GoString := go!"127.0.0.1:23851"
abbrev bridgeAddr₂ : GoString := go!"127.0.0.1:23852"
abbrev bridgeAddr₃ : GoString := go!"127.0.0.1:23853"

/-- **The cluster's configuration** (`config()`, Go's `cluster3.Config` literal): linkv3p's token,
member names and addresses, and snapshot settings (`SnapCount`, `SnapCatchUp`: `1`, `1`). -/
abbrev clusterCfg : github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Config :=
  { Token' := go!"linkv3p", Name1' := name₁, Name2' := name₂, Name3' := name₃,
    Peer1' := peerAddr₁, Peer2' := peerAddr₂, Peer3' := peerAddr₃,
    Client1' := clientAddr₁, Client2' := clientAddr₂, Client3' := clientAddr₃,
    Bridge1' := bridgeAddr₁, Bridge2' := bridgeAddr₂, Bridge3' := bridgeAddr₃,
    SnapCount' := W64 1, SnapCatchUp' := W64 1 }

/-- **The configuration meets the cluster's specs' premise** (`cluster3.cfgOk`: its names distinct
and valid UTF-8, its peer addresses distinct plain peer URLs, its bridges distinct plain
endpoints). -/
theorem clusterCfg_ok : cluster3.cfgOk clusterCfg := by
  constructor <;> dsimp only [clusterCfg] <;> (try unfold plainEndpoint) <;> decide

end pure

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **`Main`'s named premises** (persistent): the cluster's (`cluster3.premises`, putget3's at
linkv3p's configuration): `bootstrap`'s contract for each member, at the cluster's peers `ps` and
its directory, `proto.Marshal`'s contract at the bootstrap log's conf changes (`bootMarshal`,
2026-10-27, the server port: the cluster's allocation's premise; until then `bootstrap`'s contract
gave it), and the premises the members share. -/
def premises (N : Nat) (id₁ id₂ id₃ : w64) (ps : List w64) (ctxs : List (List w8))
    (boot : List LogEntry) : IProp GF :=
  cluster3.premises clusterCfg N id₁ id₂ id₃ ps ctxs boot

instance premises_persistent (N : Nat) (id₁ id₂ id₃ : w64) (ps : List w64) (ctxs : List (List w8))
    (boot : List LogEntry) :
    Persistent (premises (GF := GF) N id₁ id₂ id₃ ps ctxs boot) := by
  unfold premises; infer_instance

/-- **What `Apply` and `Check` take of one client** (persistent): linkvtxn's `Apply.spec`'s
premises for a client `cl` of some members `ms` (at least one; all three since 2026-10-21,
failover, `notes/decisions.md` D27) -- `New`'s client of their endpoints, with the default
retries since 2026-10-21 (`isNewClient`; a write sent at most once, `clientWriteOnce`: the
endpoints refusal-free, D29), etcd's `Put`, `Range`, `DeleteRange` and `Txn` registered at each
member's endpoint with that member's apply environment, read names and ids (`kvRegsAt`), and the
instance's invariant at each member's KV names (the cluster's state, D21 M4: `linkvInv_congr`,
`Alloc.lean`). A list of clients is a `[∗list]` of these. (Until 2026-10-20, linkv's: `Put` and
`Range`, linkv's invariant; until 2026-10-21, one member.) -/
def clientOk (γ : etcd_txnlin.LinkvNames) (cl : Loc) : IProp GF :=
  iprop(∃ (ms : List (EtcdGrove.client.SrvAt GF)) (V : EtcdGrove.client.WEnv GF), ⌜ms ≠ []⌝ ∗
    isNewClient cl (ms.map EtcdGrove.client.SrvAt.addr) V ∗
    EtcdGrove.client.clientWriteOnce cl (ms.map EtcdGrove.client.SrvAt.addr) ∗
    ([∗list] sv ∈ ms, EtcdGrove.client.kvRegsAt sv) ∗
    ([∗list] sv ∈ ms, etcd_txnlin.linkvInv γ sv.γr.kv))

instance clientOk_persistent (γ : etcd_txnlin.LinkvNames) (cl : Loc) :
    Persistent (clientOk (GF := GF) γ cl) := by
  unfold clientOk; infer_instance

end defs

section cluster
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- **The cluster started, with its clients** (W4: `startCluster`'s success): the cluster's
(`cluster3.clusterAt` at `clusterCfg`: the members' slice and the bridges', each member at its
bridge, each bridge owned and not blackholed, the client's view of etcd's KV at the start store,
the members' KV state variables agreeing), the clients' slice, each client `clientv3.New`'s over the
three bridges at the watch environment (`cluster3.watchEnv`, the prefix `pfx`). -/
def clusterUp (id₁ id₂ id₃ : w64) (bootLog : List EntryM) (pfx : GoString)
    (srvs brs clis : GoSlice) : IProp GF :=
  iprop(∃ (γ : SrvRaft) (γn : NetNames GF) (ρ₁ ρ₂ ρ₃ : ReqNames) (E₁ E₂ E₃ : apply.AEnv GF)
      (cid₁ cid₂ cid₃ mid₁ mid₂ mid₃ : w64) (R₁ R₂ R₃ : v3rpc.WSrv GF) (s₁ s₂ s₃ cl₁ cl₂ cl₃ : Loc)
      (br₁ br₂ br₃ : GoInterface),
    cluster3.clusterAt clusterCfg false id₁ id₂ id₃ bootLog srvs brs γ γn ρ₁ ρ₂ ρ₃ E₁ E₂ E₃
      cid₁ cid₂ cid₃ mid₁ mid₂ mid₃ R₁ R₂ R₃ s₁ s₂ s₃ br₁ br₂ br₃ ∗
    clis ↦*□ [cl₁, cl₂, cl₃] ∗
    isNewClient cl₁ (cluster3.bridges clusterCfg) (cluster3.watchEnv clusterCfg R₁ R₂ R₃ ρ₁.rd pfx) ∗
    isNewClient cl₂ (cluster3.bridges clusterCfg) (cluster3.watchEnv clusterCfg R₁ R₂ R₃ ρ₁.rd pfx) ∗
    isNewClient cl₃ (cluster3.bridges clusterCfg) (cluster3.watchEnv clusterCfg R₁ R₂ R₃ ρ₁.rd pfx))

end cluster

end etcd_partition
end EtcdGrove
end Perennial
