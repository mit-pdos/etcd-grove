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

**The compaction mode** (`compactMode`): off. The members are started with it (`StartMember`'s
`memberBoot`, `StartCluster`'s allocation), and `memberAt` and `memberWatch` (`WatchEnv.lean`) record
it; a later step generalizes them by the mode.

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

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cluster3

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section pure
variable [GooseExts]

/-- **The compaction mode of the cluster's members**: off (see the file header). -/
abbrev compactMode : Bool := false

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

/-- **A member started and served** (the success of `StartMember`): the shared start's
`etcdstart.memberUp` reduced to what a cluster's user needs of it -- the server's request and read
views (at its apply environment `E`, agreeing with the stand-in `E₀`, auth off), the `GoAttach`
resources with the thread token (`srvGoRes`), the member's place in the network with a reader's
token of its transport (`etcdstart.srvPeerCtl`: what the partitioner's `CutPeer`/`MendPeer` take),
and etcd's `Put`, `Range`, `DeleteRange`, `Txn` and `Compact` registered at its client address
(`etcd_kv_started`), its `Watch` stream served there, and (D29) that address refusal-free
(`etcd_noRefusal`). -/
def memberServed (γn : NetNames GF) (s : Loc) (id : w64) (ρ : ReqNames) (E₀ : apply.AEnv GF)
    (client : GoString) : IProp GF :=
  iprop(∃ (E : apply.AEnv GF) (γw : GName) (cid mid : w64),
    ⌜envAgree E E₀ ∧ E.authOn = false⌝ ∗
    isServerReq s E { ρ with wait := γw } ∗ isServerRead s E ρ.rd ∗ srvGoRes s ∗
    etcdstart.srvPeerCtl γn s id ∗
    isGrpcRpc client go!"/etcdserverpb.KV/Put" (EtcdGrove.client.etcdPutSpec E ρ.rd cid mid) ∗
    isGrpcRpc client go!"/etcdserverpb.KV/Range" (EtcdGrove.client.etcdRangeSpec E ρ.rd cid mid) ∗
    isGrpcRpc client go!"/etcdserverpb.KV/DeleteRange"
      (EtcdGrove.client.etcdDeleteSpec E ρ.rd cid mid) ∗
    isGrpcRpc client go!"/etcdserverpb.KV/Txn" (EtcdGrove.client.etcdTxnSpec E ρ.rd ρ.rd cid mid) ∗
    isGrpcRpc client go!"/etcdserverpb.KV/Compact" (EtcdGrove.client.etcdCompactSpec E ρ.rd cid mid) ∗
    -- (W2 of `notes/watch-cut-plan.md`, 2026-10-21) the member's watch server, its `Watch` stream
    -- served at the client address
    (∃ (pw : Loc) (R : v3rpc.WSrv GF), v3rpc.isWatchServer pw R ∗ ⌜R.s = s ∧ R.E = E⌝ ∗
      isGrpcStreamMd (Req := v3rpc.pbWatchRequest) (Rep := v3rpc.pbWatchResponse) client
        go!"/etcdserverpb.Watch/Watch" (v3rpc.watchUp R)
        (fun md γs Dn => v3rpc.watchStreamSpec γs R.γ R.s (auth.mdTokenOf md) R.cid R.mid Dn)) ∗
    -- (D29, 2026-10-21) the member never answers with a refusal (`etcd_noRefusal`)
    ⌜noRefusalAt client⌝)

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

/-- **The clients' watch environment** (W4): the three members at their bridges, the watch
contract at the cluster's committed history (`etcdModelOfHistory`, at the first member's names,
which the others' agree with), under the prefix `pfx`, at the KV state variable of those names
(D47: the watches' read updates are of it). `NewClient` takes it as its caller's choice
(`isNewClient`); a client that never watches needs none of its facts. -/
def watchEnv (cfg : github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Config)
    (R₁ R₂ R₃ : v3rpc.WSrv GF) (γr : ReadNames) (pfx : GoString) : EtcdGrove.client.WEnv GF :=
  ⟨R₁, cfg.Bridge1', [], null, null, pfx, null, v3rpc.etcdModelOfHistory γr.raft γr.kv,
    v3rpc.histWL γr.raft γr.kv, memAt3 cfg R₁ R₂ R₃, 3, γr.kv⟩

/-- **A member of the started cluster** (persistent; W4: what `StartCluster` gives of each, from
`memberServed` and its bridge's start): its bridge's address `b` serving its client address `c`'s,
its read view, etcd's KV specs registered at its client address and the address refusal-free, its
watch server and `Watch` stream there, its names agreeing with the cluster's (the raft names but
for the member's storage registry, `SrvRaft.reg`; what the KV model reads), and its server in the
cluster's compaction mode (`compactMode`). -/
def memberAt (γn : NetNames GF) (s : Loc) (id : w64) (ρ : ReqNames) (E : apply.AEnv GF)
    (cid mid : w64) (R : v3rpc.WSrv GF) (b c : GoString) (γ : SrvRaft) : IProp GF :=
  iprop(forwards b c ∗ isServerRead s E ρ.rd ∗
    isGrpcRpc c go!"/etcdserverpb.KV/Put" (EtcdGrove.client.etcdPutSpec E ρ.rd cid mid) ∗
    isGrpcRpc c go!"/etcdserverpb.KV/Range" (EtcdGrove.client.etcdRangeSpec E ρ.rd cid mid) ∗
    isGrpcRpc c go!"/etcdserverpb.KV/DeleteRange"
      (EtcdGrove.client.etcdDeleteSpec E ρ.rd cid mid) ∗
    isGrpcRpc c go!"/etcdserverpb.KV/Txn" (EtcdGrove.client.etcdTxnSpec E ρ.rd ρ.rd cid mid) ∗
    isGrpcRpc c go!"/etcdserverpb.KV/Compact" (EtcdGrove.client.etcdCompactSpec E ρ.rd cid mid) ∗
    ⌜noRefusalAt c⌝ ∗ (∃ pw : Loc, v3rpc.isWatchServer pw R) ∗ ⌜R.s = s ∧ R.E = E⌝ ∗
    isGrpcStreamMd (Req := v3rpc.pbWatchRequest) (Rep := v3rpc.pbWatchResponse) c
      go!"/etcdserverpb.Watch/Watch" (v3rpc.watchUp R)
      (fun md γs Dn => v3rpc.watchStreamSpec γs R.γ R.s (auth.mdTokenOf md) R.cid R.mid Dn) ∗
    ⌜(∃ reg : GName, ρ.rd.raft = ⟨{ γ with reg := reg }, [], W64 0⟩) ∧ ρ.rd.kv.c0 = W64 0 ∧
      ρ.rd.kv.ch0 = apply.alarmChain false false false ∧ ρ.rd.kv.log0 = [[], []] ∧
      -- (M2, the storage side, review round 2's N1, the approval's item 13) the member's server in
      -- the cluster's mode
      E.γ.cm = compactMode⌝)

instance memberAt_persistent (γn : NetNames GF) (s : Loc) (id : w64) (ρ : ReqNames)
    (E : apply.AEnv GF) (cid mid : w64) (R : v3rpc.WSrv GF) (b c : GoString) (γ : SrvRaft) :
    Persistent (memberAt γn s id ρ E cid mid R b c γ) := by
  unfold memberAt; infer_instance

/-- **The cluster started, at given names** (`clusterUp`'s body, its names as parameters, so that a
caller can state what it builds on them: the partition example's clients, at `watchEnv` of the
members' watch servers): the members' slice and the bridges'; each member (`memberAt`) with its
place in the network (a reader's token of its transport), each bridge owned and not blackholed;
the client's view of etcd's KV at the start store; the members' KV state variables agreeing. -/
def clusterAt (cfg : github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Config)
    (id₁ id₂ id₃ : w64) (bootLog : List EntryM) (srvs brs : GoSlice)
    (γ : SrvRaft) (γn : NetNames GF) (ρ₁ ρ₂ ρ₃ : ReqNames) (E₁ E₂ E₃ : apply.AEnv GF)
    (cid₁ cid₂ cid₃ mid₁ mid₂ mid₃ : w64) (R₁ R₂ R₃ : v3rpc.WSrv GF) (s₁ s₂ s₃ : Loc)
    (br₁ br₂ br₃ : GoInterface) : IProp GF :=
  iprop(srvs ↦*□ [s₁, s₂, s₃] ∗ brs ↦*□ [br₁, br₂, br₃] ∗
    memberAt γn s₁ id₁ ρ₁ E₁ cid₁ mid₁ R₁ cfg.Bridge1' cfg.Client1' γ ∗
    memberAt γn s₂ id₂ ρ₂ E₂ cid₂ mid₂ R₂ cfg.Bridge2' cfg.Client2' γ ∗
    memberAt γn s₃ id₃ ρ₃ E₃ cid₃ mid₃ R₃ cfg.Bridge3' cfg.Client3' γ ∗
    etcdstart.srvPeerCtl γn s₁ id₁ ∗ etcdstart.srvPeerCtl γn s₂ id₂ ∗ etcdstart.srvPeerCtl γn s₃ id₃ ∗
    bridge.ownBridge br₁ cfg.Client1' false ∗ bridge.ownBridge br₂ cfg.Client2' false ∗
    bridge.ownBridge br₃ cfg.Client3' false ∗
    etcdKV ρ₁.rd.kv (kvModelSt ρ₁.rd.kv (bootEntries bootLog)) ∗
    ⌜kvSame ρ₂.rd.kv ρ₁.rd.kv ∧ kvSame ρ₃.rd.kv ρ₁.rd.kv⌝)

/-- **The cluster started** (`StartCluster`'s success): `clusterAt` at some names. -/
def clusterUp (cfg : github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Config)
    (id₁ id₂ id₃ : w64) (bootLog : List EntryM) (srvs brs : GoSlice) : IProp GF :=
  iprop(∃ (γ : SrvRaft) (γn : NetNames GF) (ρ₁ ρ₂ ρ₃ : ReqNames) (E₁ E₂ E₃ : apply.AEnv GF)
      (cid₁ cid₂ cid₃ mid₁ mid₂ mid₃ : w64) (R₁ R₂ R₃ : v3rpc.WSrv GF) (s₁ s₂ s₃ : Loc)
      (br₁ br₂ br₃ : GoInterface),
    clusterAt cfg id₁ id₂ id₃ bootLog srvs brs γ γn ρ₁ ρ₂ ρ₃ E₁ E₂ E₃ cid₁ cid₂ cid₃ mid₁ mid₂ mid₃
      R₁ R₂ R₃ s₁ s₂ s₃ br₁ br₂ br₃)

end cluster

end cluster3
end EtcdGrove
end Perennial
