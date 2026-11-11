/-
Lean-first (no Rocq counterpart).

**The three-member cluster's specs' vocabulary** (`examples/lib/cluster3`; until 2026-11-05
`partition/Defs.lean`'s, at linkv3p's configuration: the partition plan's S3a, 2026-10-20, and W4 of
`notes/watch-cut-plan.md`). A cluster is started from a configuration `cfg` (Go's `Config`): its
token, its members' names, peer, client and bridge addresses, and snapshot settings. The specs take
of it only `cfgOk cfg` (pure): the names distinct and valid UTF-8, the peer addresses distinct and
each `http://<addr>` a plain peer URL (the directory well formed, `NewServer`'s premise), the bridge
addresses distinct and each a plain `host:port` (`clientv3.New`'s premise). The bootstrap facts
(`BootFacts`) are putget3's, which name no configuration.

**The compaction mode** (`cmp`, the caller's; 2026-11-05, K6 of `notes/k8s-compactor-plan.md`): the
members' auto-compactor is off (retention `0`), and the cluster's KV names are in compaction mode
`cmp` (every compaction a client's) at retention `0`. The members are started in it (`StartMember`'s
`memberBoot`, `StartCluster`'s allocation), `memberAt` records it of each member's server and
`clusterAt` of the cluster's names; a member's watch facts (`memberWatch`, `WatchEnv.lean`) carry
the store's fact for watches (`mvcc.watchNoDup`), which compaction off gives
(`watchNoDup_of_off`) and a compacting cluster's caller proves of its workload.

**The lease mode** (`m`, the caller's; lease-mono3, 2026-11-06, `notes/lease-mono3-plan.md`, Scope
§1 and Q2): the members' lessors in the mode `m` (`lease.Mode`, the KV names' `lm`), `.none` by
default. In the mode `none` a member registers etcd's KV calls at its client address and the cluster
gives the client's `etcdKV`; in a mode that grants leases it registers instead the lease reads
(`client.etcdLeaseReadAt`) and the lease mode's grant and listing (`etcdstart.etcdLeaseServedAt`, as
lease-grant's `kv_lease_served` does: the KV calls make no claim in a cluster that grants leases, and
no client's `etcdKV` exists there, `srvClusterBoot_alloc`). At `.none` every definition below is
its text before lease-mono3 (the `_none` laws after each: `clusterAt_none` and `clusterUp_none` by
`rfl`, `memberServed_none` and `memberAt_none` by `etcdKVAt`'s law `etcdKVAt_eq` and the `∗`s'
associativity); in the monotone mode a member of the started cluster gives its bridge's grant and
listing registrations (`memberAt_mono`).

**What a started member gives** (`memberServed`), **what a bridge's start gives** (`forwards`: the
bridge's address serves what the member's does, from the bridge's trust-boundary spec of `New`,
D26), **a member of the started cluster** (`memberAt`), **the started cluster** (`clusterAt`,
`clusterUp`), and **the clients' watch environment** (`watchEnv`, over the three members at their
bridges).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.putget3.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Base
public import Proof.go_etcd_io.etcd.client.v3.ClientPutGet
public import Proof.go_etcd_io.etcd.client.v3.Results
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRaftHandler
public import Proof.github_com.mit_pdos.etcd_grove.third_party.bridge.Defs
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.HistoryModel
public import Proof.go_etcd_io.etcd.client.v3.InvWatch
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.ServedLease

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cluster3

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section pure
variable [GooseExts]

/-- **`bootstrap`'s results, as Go computes them**: putget3's, the peers `ps` in `bootstrap`'s
order. -/
abbrev BootFacts (id₁ id₂ id₃ : w64) (ps : List w64) (ctxs : List (List w8)) (bl : List LogEntry) :
    Prop :=
  etcd_putget3.BootFacts id₁ id₂ id₃ ps ctxs bl

/-- **The configurations the specs take** (see the file header). -/
structure cfgOk (cfg : github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Config) : Prop where
  n12 : cfg.Name1' ≠ cfg.Name2'
  n13 : cfg.Name1' ≠ cfg.Name3'
  n23 : cfg.Name2' ≠ cfg.Name3'
  utf1 : utf8Valid cfg.Name1'
  utf2 : utf8Valid cfg.Name2'
  utf3 : utf8Valid cfg.Name3'
  p12 : cfg.Peer1' ≠ cfg.Peer2'
  p13 : cfg.Peer1' ≠ cfg.Peer3'
  p23 : cfg.Peer2' ≠ cfg.Peer3'
  pp1 : types.plainPeerURL (go!"http://" ++ cfg.Peer1')
  pp2 : types.plainPeerURL (go!"http://" ++ cfg.Peer2')
  pp3 : types.plainPeerURL (go!"http://" ++ cfg.Peer3')
  b12 : cfg.Bridge1' ≠ cfg.Bridge2'
  b13 : cfg.Bridge1' ≠ cfg.Bridge3'
  b23 : cfg.Bridge2' ≠ cfg.Bridge3'
  bp1 : plainEndpoint cfg.Bridge1'
  bp2 : plainEndpoint cfg.Bridge2'
  bp3 : plainEndpoint cfg.Bridge3'

/-- The bridges' addresses, which every client dials (`NewClient`). -/
abbrev bridges (cfg : github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Config) : List GoString :=
  [cfg.Bridge1', cfg.Bridge2', cfg.Bridge3']

theorem cfgOk.plainBridges {cfg : github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Config}
    (h : cfgOk cfg) : plainEndpoints (bridges cfg) := by
  refine ⟨by simp, fun e he => ?_⟩
  simp only [bridges, List.mem_cons, List.not_mem_nil, _root_.or_false] at he
  rcases he with rfl | rfl | rfl
  · exact h.bp1
  · exact h.bp2
  · exact h.bp3

theorem cfgOk.bridgesNodup {cfg : github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Config}
    (h : cfgOk cfg) : (bridges cfg).Nodup := by
  simp [bridges, h.b12, h.b13, h.b23]

/-- **The initial cluster's peer URLs, by name** (the map `StartCluster` builds, `cluster`). -/
def initURLs3 (cfg : github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Config) (k : GoString) :
    List _root_.Perennial.net.url.URL :=
  if k = cfg.Name1' then [etcdstart.httpURL cfg.Peer1']
  else if k = cfg.Name2' then [etcdstart.httpURL cfg.Peer2']
  else if k = cfg.Name3' then [etcdstart.httpURL cfg.Peer3'] else []

/-- **The URLs of a member's configuration** (the shared start's `urls3` at the cluster's names). -/
abbrev urlsOk (cfg : github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Config)
    (peerAddr client : GoString) : BootURLs → Prop :=
  etcdstart.urls3 cfg.Name1' cfg.Name2' cfg.Name3' (initURLs3 cfg) peerAddr client

/-- **The peer-URL directory of the cluster** (D21 M2): each member's one peer URL. -/
def dir3 (cfg : github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Config) (id₁ id₂ id₃ : w64)
    (id : w64) : List GoString :=
  if id = id₁ then [go!"http://" ++ cfg.Peer1'] else if id = id₂ then [go!"http://" ++ cfg.Peer2']
  else if id = id₃ then [go!"http://" ++ cfg.Peer3'] else []

end pure

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **`bootstrap`'s contract for member `name`** (the shared start's `bootPremise` at the cluster's
token and URLs). -/
abbrev bootPremise (cfg : github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Config) (N : Nat)
    (ps : List w64) (bootLog : List EntryM) (ctxs : List (List w8)) (dir : w64 → List GoString)
    (name peerAddr client : GoString) (id : w64) : IProp GF :=
  etcdstart.bootPremise N ps bootLog ctxs dir cfg.Token' name (urlsOk cfg peerAddr client) id

/-- **The cluster's named premises** (persistent): `bootstrap`'s contract for each member, at the
cluster's peers `ps` and the directory `dir3`, `proto.Marshal`'s contract at the bootstrap log's
conf changes (`bootMarshal`, the cluster's allocation's premise), and the premises the members
share. -/
def premises (cfg : github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Config) (N : Nat)
    (id₁ id₂ id₃ : w64) (ps : List w64) (ctxs : List (List w8)) (boot : List LogEntry) : IProp GF :=
  iprop(
    bootPremise cfg N ps (LogEntry.toEntries boot 0) ctxs (dir3 cfg id₁ id₂ id₃)
      cfg.Name1' cfg.Peer1' cfg.Client1' id₁ ∗
    bootPremise cfg N ps (LogEntry.toEntries boot 0) ctxs (dir3 cfg id₁ id₂ id₃)
      cfg.Name2' cfg.Peer2' cfg.Client2' id₂ ∗
    bootPremise cfg N ps (LogEntry.toEntries boot 0) ctxs (dir3 cfg id₁ id₂ id₃)
      cfg.Name3' cfg.Peer3' cfg.Client3' id₃ ∗
    bootMarshal ps ctxs (LogEntry.toEntries boot 0) ∗
    etcdstart.commonPremises)

instance premises_persistent (cfg : github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Config)
    (N : Nat) (id₁ id₂ id₃ : w64) (ps : List w64) (ctxs : List (List w8)) (boot : List LogEntry) :
    Persistent (premises (GF := GF) cfg N id₁ id₂ id₃ ps ctxs boot) := by
  unfold premises; infer_instance

/-- **What a served member registers at its client address `c`, by the lease mode `m`**
(lease-mono3, 2026-11-06, Q2; `memberServed`'s and `memberAt`'s): etcd's KV calls at the server's
views in the mode `none` (`etcdstart.etcdKVAt`, `etcdLeaseServedAt`'s at `none`); in a mode that
grants leases the lease reads (`client.etcdLeaseReadAt`) and the mode's lease registrations
(`etcdstart.etcdLeaseServedAt`: the grant and the listing at the lessor's history in the monotone
mode), lease-grant's `kv_lease_served`'s post. -/
def servedRegs (m : lease.Mode) (c : GoString) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames)
    (cid mid : w64) : IProp GF :=
  match m with
  | .none => etcdstart.etcdKVAt c E ρ ρ.rd cid mid
  | m => iprop(EtcdGrove.client.etcdLeaseReadAt c ∗ etcdstart.etcdLeaseServedAt m c s E ρ ρ.rd cid mid)

instance servedRegs_persistent (m : lease.Mode) (c : GoString) (s : Loc) (E : apply.AEnv GF)
    (ρ : ReqNames) (cid mid : w64) : Persistent (servedRegs m c s E ρ cid mid) := by
  cases m <;> unfold servedRegs <;> infer_instance

/-- `(P ∗ Q) ∗ R` is `P ∗ Q ∗ R`, as an equation (for the `_none` laws). -/
private theorem sep_assoc_eq (P Q R : IProp GF) : iprop((P ∗ Q) ∗ R) = iprop(P ∗ Q ∗ R) :=
  BI.sep_assoc.to_eq

/-- **A member started and served** (the success of `StartMember`): the shared start's
`etcdstart.memberUp` reduced to what a cluster's user needs of it -- the server's request and read
views (at its apply environment `E`, agreeing with the stand-in `E₀`, auth off), the `GoAttach`
resources with the thread token (`srvGoRes`), the member's place in the network with a reader's
token of its transport (`etcdstart.srvPeerCtl`: what the partitioner's `CutPeer`/`MendPeer` take),
and etcd's `Put`, `Range`, `DeleteRange`, `Txn` and `Compact` registered at its client address
(`etcd_kv_started`), its `Watch` stream served there, and (D29) that address refusal-free
(`etcd_noRefusal`); (lease-mono3) in a lease mode `m ≠ .none`, the lease reads and the mode's
lease registrations in place of the KV calls (`servedRegs`). -/
def memberServed (γn : NetNames GF) (s : Loc) (id : w64) (ρ : ReqNames) (E₀ : apply.AEnv GF)
    (client : GoString) (m : lease.Mode := .none) : IProp GF :=
  iprop(∃ (E : apply.AEnv GF) (γw : GName) (cid mid : w64),
    ⌜envAgree E E₀ ∧ E.authOn = false⌝ ∗
    isServerReq s E { ρ with wait := γw } ∗ isServerRead s E ρ.rd ∗ srvGoRes s ∗
    etcdstart.srvPeerCtl γn s id ∗
    servedRegs m client s E ρ cid mid ∗
    -- (W2 of `notes/watch-cut-plan.md`, 2026-10-21) the member's watch server, its `Watch` stream
    -- served at the client address
    -- (R9, the `lean` merge) at the server's watch facts (`srvWOf`), with their laws
    (∃ (pw : Loc) (R : v3rpc.WSrv GF), v3rpc.isWatchServer pw R ∗ ⌜R.s = s ∧ R.E = E⌝ ∗
      EtcdGrove.client.srvWLaws (etcdstart.srvWOf E ρ.rd false) ∗
      isGrpcStreamMd (Req := v3rpc.pbWatchRequest) (Rep := v3rpc.pbWatchResponse) client
        go!"/etcdserverpb.Watch/Watch" (v3rpc.watchUp R)
        (fun md γs Dn => v3rpc.watchStreamSpec γs R (etcdstart.srvWOf E ρ.rd false)
          (auth.mdTokenOf md) Dn)) ∗
    -- (D29, 2026-10-21) the member never answers with a refusal (`etcd_noRefusal`)
    ⌜noRefusalAt client⌝)

/-- `memberServed` at the mode `none` is its text before lease-mono3 (`etcdKVAt` unfolded). -/
theorem memberServed_none (γn : NetNames GF) (s : Loc) (id : w64) (ρ : ReqNames) (E₀ : apply.AEnv GF)
    (client : GoString) :
    memberServed γn s id ρ E₀ client .none =
  iprop(∃ (E : apply.AEnv GF) (γw : GName) (cid mid : w64),
    ⌜envAgree E E₀ ∧ E.authOn = false⌝ ∗
    isServerReq s E { ρ with wait := γw } ∗ isServerRead s E ρ.rd ∗ srvGoRes s ∗
    etcdstart.srvPeerCtl γn s id ∗
    isGrpcRpc client go!"/etcdserverpb.KV/Put" (EtcdGrove.client.etcdPutSpec E ρ.rd cid mid) ∗
    isGrpcRpcMd client go!"/etcdserverpb.KV/Range" (EtcdGrove.client.etcdRangeSpecE E ρ.rd cid mid) ∗
    isGrpcRpc client go!"/etcdserverpb.KV/DeleteRange"
      (EtcdGrove.client.etcdDeleteSpec E ρ.rd cid mid) ∗
    isGrpcRpc client go!"/etcdserverpb.KV/Txn" (EtcdGrove.client.etcdTxnSpec E ρ.rd ρ.rd cid mid) ∗
    isGrpcRpc client go!"/etcdserverpb.KV/Compact" (EtcdGrove.client.etcdCompactSpec E ρ.rd cid mid) ∗
    -- (W2 of `notes/watch-cut-plan.md`, 2026-10-21) the member's watch server, its `Watch` stream
    -- served at the client address
    -- (R9, the `lean` merge) at the server's watch facts (`srvWOf`), with their laws
    (∃ (pw : Loc) (R : v3rpc.WSrv GF), v3rpc.isWatchServer pw R ∗ ⌜R.s = s ∧ R.E = E⌝ ∗
      EtcdGrove.client.srvWLaws (etcdstart.srvWOf E ρ.rd false) ∗
      isGrpcStreamMd (Req := v3rpc.pbWatchRequest) (Rep := v3rpc.pbWatchResponse) client
        go!"/etcdserverpb.Watch/Watch" (v3rpc.watchUp R)
        (fun md γs Dn => v3rpc.watchStreamSpec γs R (etcdstart.srvWOf E ρ.rd false)
          (auth.mdTokenOf md) Dn)) ∗
    -- (D29, 2026-10-21) the member never answers with a refusal (`etcd_noRefusal`)
    ⌜noRefusalAt client⌝) := by
  simp only [memberServed, servedRegs, etcdstart.etcdKVAt_eq, sep_assoc_eq]

end defs

section forwards
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The address `a` serves what `b` serves, method by method** (persistent; what a bridge's start
gives, from the bridge's trust-boundary spec of `New`), and (D29) `a` is refusal-free if `b` is,
and (D32) `a` serves `b`'s stream methods. -/
def forwards (a b : GoString) : IProp GF :=
  iprop((□ ∀ (name : GoString) (mh : val) (srv : GoInterface) (ics : List GoFunc) (S : IProp GF),
    grpcServes b name mh srv ics S -∗ grpcServes a name mh srv ics S) ∗
    ⌜noRefusalAt b → noRefusalAt a⌝ ∗
    (□ ∀ (name : GoString) (mh : val) (srv : GoInterface) (ics : List GoFunc) (S : IProp GF),
      grpcServesStream b name mh srv ics S -∗ grpcServesStream a name mh srv ics S))

instance forwards_persistent (a b : GoString) : Persistent (forwards (GF := GF) a b) := by
  unfold forwards; infer_instance

/-- A method registered at `b` is registered at an address that forwards to `b`. -/
theorem isGrpcRpc_forwards {Req Rep : ProtoMsg GF} (a b name : GoString) (Spec : GrpcSpec Req Rep) :
    forwards (GF := GF) a b ∗ isGrpcRpc b name Spec ⊢ isGrpcRpc a name Spec := by
  iintro ⟨#Hf, #Hr⟩
  iunfold forwards at Hf
  icases Hf with ⟨#Hf, -, -⟩
  unfold isGrpcRpc
  icases Hr with ⟨%mh, %srv, %ics, %S, #Hs, #Hm⟩
  iexists mh, srv, ics, S
  isplitl
  · iapply Hf $$ %name %mh %srv %ics %S Hs
  · iexact Hm

/-- A unary method registered with a metadata-indexed spec at `b` is registered at an address that
forwards to `b` (`isGrpcRpc_forwards`'s; k8s 7e-1, the members' `Range` with its error outcome). -/
theorem isGrpcRpcMd_forwards {Req Rep : ProtoMsg GF} (a b name : GoString) (Spec : GrpcSpecMd Req Rep) :
    forwards (GF := GF) a b ∗ isGrpcRpcMd b name Spec ⊢ isGrpcRpcMd a name Spec := by
  iintro ⟨#Hf, #Hr⟩
  iunfold forwards at Hf
  icases Hf with ⟨#Hf, -, -⟩
  unfold isGrpcRpcMd
  icases Hr with ⟨%mh, %srv, %ics, %S, #Hs, #Hm⟩
  iexists mh, srv, ics, S
  isplitl
  · iapply Hf $$ %name %mh %srv %ics %S Hs
  · iexact Hm

/-- (D32) A stream method registered at `b` is registered at an address that forwards to `b`
(metadata-indexed, G2). -/
theorem isGrpcStream_forwards {Req Rep : StreamMsg GF} (a b name : GoString)
    (Up : Nat → Req.M → IProp GF) (Spec : GrpcMd → StreamSpec Rep) :
    forwards (GF := GF) a b ∗ isGrpcStreamMd b name Up Spec ⊢ isGrpcStreamMd a name Up Spec := by
  iintro ⟨#Hf, #Hr⟩
  iunfold forwards at Hf
  icases Hf with ⟨-, -, #Hf⟩
  unfold isGrpcStreamMd
  icases Hr with ⟨%mh, %srv, %ics, %S, #Hs, #Hm⟩
  iexists mh, srv, ics, S
  isplitl
  · iapply Hf $$ %name %mh %srv %ics %S Hs
  · iexact Hm

end forwards

section cluster
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- (W4 of `notes/watch-cut-plan.md`) The members, each at its bridge's address with its watch
server. -/
def memAt3 (cfg : github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Config)
    (R₁ R₂ R₃ : v3rpc.WSrv GF) : Nat → GoString × v3rpc.WSrv GF
  | 0 => (cfg.Bridge1', R₁)
  | 1 => (cfg.Bridge2', R₂)
  | _ => (cfg.Bridge3', R₃)

/-- (R9) The members' watch facts (v3rpc's `SrvW`), by index. -/
def memWAt3 (W₁ W₂ W₃ : v3rpc.SrvW GF) : Nat → v3rpc.SrvW GF
  | 0 => W₁
  | 1 => W₂
  | _ => W₃

/-- **The clients' watch environment** (W4): the three members at their bridges, the watch
contract at the cluster's committed history (`etcdModelOfHistory`, at the first member's names,
which the others' agree with), under the prefix `pfx`, at the KV state variable of those names
(D47: the watches' read updates are of it). `NewClient` takes it as its caller's choice
(`isNewClient`); a client that never watches needs none of its facts. -/
def watchEnv (cfg : github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Config)
    (R₁ R₂ R₃ : v3rpc.WSrv GF) (W₁ W₂ W₃ : v3rpc.SrvW GF) (γr : ReadNames) (pfx : GoString) :
    EtcdGrove.client.WEnv GF :=
  ⟨R₁, cfg.Bridge1', [], null, null, pfx, null, v3rpc.etcdModelOfHistory γr.raft γr.kv,
    v3rpc.histWL γr.raft γr.kv, memAt3 cfg R₁ R₂ R₃, 3, γr.kv, W₁, memWAt3 W₁ W₂ W₃⟩

/-- **A member of the started cluster** (persistent; W4: what `StartCluster` gives of each, from
`memberServed` and its bridge's start): its bridge's address `b` serving its client address `c`'s,
its read view, etcd's KV specs registered at its client address and the address refusal-free, its
watch server and `Watch` stream there, its names agreeing with the cluster's (the raft names but
for the member's storage registry, `SrvRaft.reg`; what the KV model reads), and its server in the
cluster's compaction mode `cmp`. -/
def memberAt (γn : NetNames GF) (s : Loc) (id : w64) (ρ : ReqNames) (E : apply.AEnv GF)
    (cid mid : w64) (R : v3rpc.WSrv GF) (b c : GoString) (γ : SrvRaft) (cmp : Bool)
    (m : lease.Mode := .none) : IProp GF :=
  iprop(forwards b c ∗ isServerRead s E ρ.rd ∗
    servedRegs m c s E ρ cid mid ∗
    ⌜noRefusalAt c⌝ ∗ (∃ pw : Loc, v3rpc.isWatchServer pw R) ∗ ⌜R.s = s ∧ R.E = E⌝ ∗
    client.srvWLaws (etcdstart.srvWOf E ρ.rd false) ∗
    isGrpcStreamMd (Req := v3rpc.pbWatchRequest) (Rep := v3rpc.pbWatchResponse) c
      go!"/etcdserverpb.Watch/Watch" (v3rpc.watchUp R)
      (fun md γs Dn => v3rpc.watchStreamSpec γs R (etcdstart.srvWOf E ρ.rd false)
        (auth.mdTokenOf md) Dn) ∗
    ⌜(∃ reg : GName, ρ.rd.raft = ⟨{ γ with reg := reg }, [], W64 0⟩) ∧ ρ.rd.kv.c0 = W64 0 ∧
      ρ.rd.kv.ch0 = apply.alarmChain false false false ∧ ρ.rd.kv.log0 = [[], []] ∧
      -- (M2, the storage side, review round 2's N1, the approval's item 13) the member's server in
      -- the cluster's mode
      E.cmp = cmp⌝)

/-- `memberAt` at the mode `none` is its text before lease-mono3 (`etcdKVAt` unfolded). -/
theorem memberAt_none (γn : NetNames GF) (s : Loc) (id : w64) (ρ : ReqNames) (E : apply.AEnv GF)
    (cid mid : w64) (R : v3rpc.WSrv GF) (b c : GoString) (γ : SrvRaft) (cmp : Bool) :
    memberAt γn s id ρ E cid mid R b c γ cmp .none =
  iprop(forwards b c ∗ isServerRead s E ρ.rd ∗
    isGrpcRpc c go!"/etcdserverpb.KV/Put" (EtcdGrove.client.etcdPutSpec E ρ.rd cid mid) ∗
    isGrpcRpcMd c go!"/etcdserverpb.KV/Range" (EtcdGrove.client.etcdRangeSpecE E ρ.rd cid mid) ∗
    isGrpcRpc c go!"/etcdserverpb.KV/DeleteRange"
      (EtcdGrove.client.etcdDeleteSpec E ρ.rd cid mid) ∗
    isGrpcRpc c go!"/etcdserverpb.KV/Txn" (EtcdGrove.client.etcdTxnSpec E ρ.rd ρ.rd cid mid) ∗
    isGrpcRpc c go!"/etcdserverpb.KV/Compact" (EtcdGrove.client.etcdCompactSpec E ρ.rd cid mid) ∗
    ⌜noRefusalAt c⌝ ∗ (∃ pw : Loc, v3rpc.isWatchServer pw R) ∗ ⌜R.s = s ∧ R.E = E⌝ ∗
    client.srvWLaws (etcdstart.srvWOf E ρ.rd false) ∗
    isGrpcStreamMd (Req := v3rpc.pbWatchRequest) (Rep := v3rpc.pbWatchResponse) c
      go!"/etcdserverpb.Watch/Watch" (v3rpc.watchUp R)
      (fun md γs Dn => v3rpc.watchStreamSpec γs R (etcdstart.srvWOf E ρ.rd false)
        (auth.mdTokenOf md) Dn) ∗
    ⌜(∃ reg : GName, ρ.rd.raft = ⟨{ γ with reg := reg }, [], W64 0⟩) ∧ ρ.rd.kv.c0 = W64 0 ∧
      ρ.rd.kv.ch0 = apply.alarmChain false false false ∧ ρ.rd.kv.log0 = [[], []] ∧
      -- (M2, the storage side, review round 2's N1, the approval's item 13) the member's server in
      -- the cluster's mode
      E.cmp = cmp⌝) := by
  simp only [memberAt, servedRegs, etcdstart.etcdKVAt_eq, sep_assoc_eq]

instance memberAt_persistent (γn : NetNames GF) (s : Loc) (id : w64) (ρ : ReqNames)
    (E : apply.AEnv GF) (cid mid : w64) (R : v3rpc.WSrv GF) (b c : GoString) (γ : SrvRaft)
    (cmp : Bool) (m : lease.Mode) : Persistent (memberAt γn s id ρ E cid mid R b c γ cmp m) := by
  unfold memberAt; infer_instance

/-- **A member of the started cluster in the monotone mode gives its bridge's grant and listing**
(lease-mono3's review r1, SF2): `LeaseGrant` and `LeaseLeases` registered at the bridge's address
`b` at the specs at the member's lessor history (`etcdLeaseGrantSpec`, `etcdLeaseLeasesSpec` of
`(mvcc.api.mvccLeases E.γ)`), its client address's registrations forwarded (`isGrpcRpc_forwards`). -/
theorem memberAt_mono (γn : NetNames GF) (s : Loc) (id : w64) (ρ : ReqNames) (E : apply.AEnv GF)
    (cid mid : w64) (R : v3rpc.WSrv GF) (b c : GoString) (γ : SrvRaft) (cmp : Bool) :
    memberAt γn s id ρ E cid mid R b c γ cmp .mono ⊢
      isGrpcRpc b go!"/etcdserverpb.Lease/LeaseGrant"
          (etcdLeaseGrantSpec (EM := v3rpc.etcdModelOfServer E ρ.rd false) (mvcc.api.mvccLeases E.γ)) ∗
        isGrpcRpc b go!"/etcdserverpb.Lease/LeaseLeases" (etcdLeaseLeasesSpec (mvcc.api.mvccLeases E.γ)) := by
  iintro #Hm
  iunfold memberAt at Hm
  icases Hm with ⟨#Hfw, -, Hs, -⟩
  isimp only [servedRegs, etcdstart.etcdLeaseServedAt_mono] at Hs
  icases Hs with ⟨-, #Hg⟩
  icases etcdstart.etcdLeaseGrantAt_elim c E ρ.rd $$ Hg with ⟨#HG, #HL⟩
  isplitl
  · iapply isGrpcRpc_forwards b c; iframe #
  · iapply isGrpcRpc_forwards b c; iframe #

/-- **The cluster started, at given names** (`clusterUp`'s body, its names as parameters, so that a
caller can state what it builds on them: the partition example's clients, at `watchEnv` of the
members' watch servers): the members' slice and the bridges'; each member (`memberAt`) with its
place in the network (a reader's token of its transport), each bridge owned and not blackholed;
in the mode `none`, the client's view of etcd's KV at the start store; the members' KV state
variables agreeing, the
first's in the compaction mode `cmp` at retention `0`. -/
def clusterAt (cfg : github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Config) (cmp : Bool)
    (id₁ id₂ id₃ : w64) (bootLog : List EntryM) (srvs brs : GoSlice)
    (γ : SrvRaft) (γn : NetNames GF) (ρ₁ ρ₂ ρ₃ : ReqNames) (E₁ E₂ E₃ : apply.AEnv GF)
    (cid₁ cid₂ cid₃ mid₁ mid₂ mid₃ : w64) (R₁ R₂ R₃ : v3rpc.WSrv GF) (s₁ s₂ s₃ : Loc)
    (br₁ br₂ br₃ : GoInterface) (m : lease.Mode := .none) : IProp GF :=
  iprop(srvs ↦*□ [s₁, s₂, s₃] ∗ brs ↦*□ [br₁, br₂, br₃] ∗
    memberAt γn s₁ id₁ ρ₁ E₁ cid₁ mid₁ R₁ cfg.Bridge1' cfg.Client1' γ cmp m ∗
    memberAt γn s₂ id₂ ρ₂ E₂ cid₂ mid₂ R₂ cfg.Bridge2' cfg.Client2' γ cmp m ∗
    memberAt γn s₃ id₃ ρ₃ E₃ cid₃ mid₃ R₃ cfg.Bridge3' cfg.Client3' γ cmp m ∗
    etcdstart.srvPeerCtl γn s₁ id₁ ∗ etcdstart.srvPeerCtl γn s₂ id₂ ∗ etcdstart.srvPeerCtl γn s₃ id₃ ∗
    bridge.ownBridge br₁ cfg.Client1' false ∗ bridge.ownBridge br₂ cfg.Client2' false ∗
    bridge.ownBridge br₃ cfg.Client3' false ∗
    -- (lease-mono3) the client's `etcdKV` in the mode `none` only: a cluster that grants leases
    -- has none (`srvClusterBoot_alloc`)
    (match m with
    | .none => etcdKV ρ₁.rd.kv (kvModelSt ρ₁.rd.kv (bootEntries bootLog))
    | _ => iprop(True)) ∗
    ⌜kvSame ρ₂.rd.kv ρ₁.rd.kv ∧ kvSame ρ₃.rd.kv ρ₁.rd.kv ∧ ρ₁.rd.kv.cmp = cmp ∧
      ρ₁.rd.kv.cret = 0⌝)

/-- `clusterAt` at the mode `none` is its text before lease-mono3 (`rfl`). -/
theorem clusterAt_none (cfg : github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Config) (cmp : Bool)
    (id₁ id₂ id₃ : w64) (bootLog : List EntryM) (srvs brs : GoSlice)
    (γ : SrvRaft) (γn : NetNames GF) (ρ₁ ρ₂ ρ₃ : ReqNames) (E₁ E₂ E₃ : apply.AEnv GF)
    (cid₁ cid₂ cid₃ mid₁ mid₂ mid₃ : w64) (R₁ R₂ R₃ : v3rpc.WSrv GF) (s₁ s₂ s₃ : Loc)
    (br₁ br₂ br₃ : GoInterface) :
    clusterAt cfg cmp id₁ id₂ id₃ bootLog srvs brs γ γn ρ₁ ρ₂ ρ₃ E₁ E₂ E₃ cid₁ cid₂ cid₃ mid₁ mid₂ mid₃
      R₁ R₂ R₃ s₁ s₂ s₃ br₁ br₂ br₃ .none =
  iprop(srvs ↦*□ [s₁, s₂, s₃] ∗ brs ↦*□ [br₁, br₂, br₃] ∗
    memberAt γn s₁ id₁ ρ₁ E₁ cid₁ mid₁ R₁ cfg.Bridge1' cfg.Client1' γ cmp ∗
    memberAt γn s₂ id₂ ρ₂ E₂ cid₂ mid₂ R₂ cfg.Bridge2' cfg.Client2' γ cmp ∗
    memberAt γn s₃ id₃ ρ₃ E₃ cid₃ mid₃ R₃ cfg.Bridge3' cfg.Client3' γ cmp ∗
    etcdstart.srvPeerCtl γn s₁ id₁ ∗ etcdstart.srvPeerCtl γn s₂ id₂ ∗ etcdstart.srvPeerCtl γn s₃ id₃ ∗
    bridge.ownBridge br₁ cfg.Client1' false ∗ bridge.ownBridge br₂ cfg.Client2' false ∗
    bridge.ownBridge br₃ cfg.Client3' false ∗
    etcdKV ρ₁.rd.kv (kvModelSt ρ₁.rd.kv (bootEntries bootLog)) ∗
    ⌜kvSame ρ₂.rd.kv ρ₁.rd.kv ∧ kvSame ρ₃.rd.kv ρ₁.rd.kv ∧ ρ₁.rd.kv.cmp = cmp ∧
      ρ₁.rd.kv.cret = 0⌝) := rfl

/-- **The cluster started** (`StartCluster`'s success): `clusterAt` at some names. -/
def clusterUp (cfg : github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Config) (cmp : Bool)
    (id₁ id₂ id₃ : w64) (bootLog : List EntryM) (srvs brs : GoSlice)
    (m : lease.Mode := .none) : IProp GF :=
  iprop(∃ (γ : SrvRaft) (γn : NetNames GF) (ρ₁ ρ₂ ρ₃ : ReqNames) (E₁ E₂ E₃ : apply.AEnv GF)
      (cid₁ cid₂ cid₃ mid₁ mid₂ mid₃ : w64) (R₁ R₂ R₃ : v3rpc.WSrv GF) (s₁ s₂ s₃ : Loc)
      (br₁ br₂ br₃ : GoInterface),
    clusterAt cfg cmp id₁ id₂ id₃ bootLog srvs brs γ γn ρ₁ ρ₂ ρ₃ E₁ E₂ E₃ cid₁ cid₂ cid₃ mid₁ mid₂ mid₃
      R₁ R₂ R₃ s₁ s₂ s₃ br₁ br₂ br₃ m)

/-- `clusterUp` at the mode `none` is its text before lease-mono3 (`rfl`). -/
theorem clusterUp_none (cfg : github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Config) (cmp : Bool)
    (id₁ id₂ id₃ : w64) (bootLog : List EntryM) (srvs brs : GoSlice) :
    clusterUp (GF := GF) cfg cmp id₁ id₂ id₃ bootLog srvs brs .none =
  iprop(∃ (γ : SrvRaft) (γn : NetNames GF) (ρ₁ ρ₂ ρ₃ : ReqNames) (E₁ E₂ E₃ : apply.AEnv GF)
      (cid₁ cid₂ cid₃ mid₁ mid₂ mid₃ : w64) (R₁ R₂ R₃ : v3rpc.WSrv GF) (s₁ s₂ s₃ : Loc)
      (br₁ br₂ br₃ : GoInterface),
    clusterAt cfg cmp id₁ id₂ id₃ bootLog srvs brs γ γn ρ₁ ρ₂ ρ₃ E₁ E₂ E₃ cid₁ cid₂ cid₃ mid₁ mid₂ mid₃
      R₁ R₂ R₃ s₁ s₂ s₃ br₁ br₂ br₃) := rfl

end cluster

end cluster3
end EtcdGrove
end Perennial
