/-
Lean-first (no Rocq counterpart).

**linkv3p's `Main`, `startMember`, `partitioner`, `Apply`, `Check`: their named premises and
vocabulary** (the partition plan's S3a, 2026-10-20, `notes/partition-plan.md`). putget3's
(`putget3/Defs.lean`, whose header explains each) at linkv3p's configuration: the member names
`linkv3p-1`, `-2`, `-3`, the cluster token `linkv3p`, the peer addresses `127.0.0.1:2384{1,2,3}`
and the client addresses `127.0.0.1:2383{1,2,3}` (every one served, to its client). The
conf-change policy (`putget3.ccOk`), the URL builder (`putget3.httpURL`), the premises shared by
the members (`putget3.commonPremises`) are putget3's, which name no configuration.

**The member ids' order** (`BootFacts`): `id₁ id₂ id₃` are the ids of `linkv3p-1`, `-2`, `-3`.
`bootstrap` sorts the members by id, and for linkv3p's names and token the order is the names'
(`0x77e2…`, `0xcc14…`, `0xecbe…`: `TestMemberIDs` in `examples/linkv3p/linkv3p_test.go` prints
them; their 16 low bits `0x2126`, `0x3ef6`, `0xf29c` are distinct and not `0`, D21e (A)), unlike
linkv3's. So the cluster's list (`ids`: the bootstrap log's order, one conf change per member) is
`[id₁, id₂, id₃]`, and `BootFacts` is putget3's in that order.

**What a started member gives** (`memberServed`) and **what a client's `Apply` takes**
(`clientOk`) are at the end, with **what a bridge's start gives** (`forwards`: the bridge's
address serves what the member's does, from the bridge's trust-boundary spec of `New`, D26).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.putget3.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.linkv3p.Base
public import Proof.github_com.mit_pdos.etcd_grove.examples.linkvtxn.Inv
public import Proof.go_etcd_io.etcd.client.v3.ClientPutGet
public import Proof.go_etcd_io.etcd.client.v3.Results
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRaftHandler
public import Proof.github_com.mit_pdos.etcd_grove.third_party.bridge.Defs
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.HistoryModel
public import Proof.go_etcd_io.etcd.client.v3.InvWatch
public import Proof.github_com.mit_pdos.etcd_grove.examples.common.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkv3p

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section pure
variable [ext : FfiSyntax]

/-- **The cluster's members in `bootstrap`'s order** (by id; see the file header). -/
def ids (id₁ id₂ id₃ : w64) : List w64 := [id₁, id₂, id₃]

/-- **`bootstrap`'s results, as Go computes them**: putget3's, in the members' id order (see the
file header). -/
abbrev BootFacts (id₁ id₂ id₃ : w64) (bootLog : List EntryM) : Prop :=
  putget3.BootFacts id₁ id₂ id₃ bootLog

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

/-- **The initial cluster's peer URLs, by name** (the map `Main` builds, `cluster`). -/
def initURLs3 (k : GoString) : List _root_.Perennial.net.url.URL :=
  if k = name₁ then [putget3.httpURL peerAddr₁] else if k = name₂ then [putget3.httpURL peerAddr₂]
  else if k = name₃ then [putget3.httpURL peerAddr₃] else []

/-- **The URLs of member `name`'s configuration** (putget3's `urlsOk` at linkv3p's names). -/
def urlsOk (peerAddr client : GoString) (U : BootURLs) : Prop :=
  U.peer = [putget3.httpURL peerAddr] ∧ U.client = [putget3.httpURL client] ∧
    (∃ sl₁ sl₂ sl₃ : GoSlice,
      U.initMap = GMap.insert name₃ sl₃ (GMap.insert name₂ sl₂ (GMap.insert name₁ sl₁ ∅))) ∧
    U.initURLs = initURLs3

/-- **The peer-URL directory of `Main`'s cluster** (D21 M2): each member's one peer URL. -/
def dir3 (id₁ id₂ id₃ : w64) (id : w64) : List GoString :=
  if id = id₁ then [go!"http://" ++ peerAddr₁] else if id = id₂ then [go!"http://" ++ peerAddr₂]
  else if id = id₃ then [go!"http://" ++ peerAddr₃] else []

end pure

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **The configuration `startMember` passes to `NewServer`**, by its scalar fields (putget3's
`cfgOk` with the token `linkv3p`). -/
def cfgOk (name : GoString) (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) : Prop :=
  cfg.Name' = name ∧ cfg.DataDir' = name ++ go!".etcd" ∧
    cfg.InitialClusterToken' = go!"linkv3p" ∧ cfg.NewCluster' = true ∧
    cfg.TickMs' = W64 100 ∧ cfg.ElectionTicks' = W64 10

/-- **`bootstrap`'s contract for member `name`** (putget3's `bootPremise` at linkv3p's `cfgOk` and
`urlsOk`). -/
def bootPremise (N : Nat) (ps : List w64) (bootLog : List EntryM) (dir : w64 → List GoString)
    (name peerAddr client : GoString) (id : w64) : IProp GF :=
  iprop(□ ∀ (reg : GName) (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (U : BootURLs)
        (γ : RaftNames),
      ⌜cfgOk name cfg ∧ urlsOk peerAddr client U ∧ γ.reCfg = GMap.listToSet ps ∧
        γ.reDyn = none ∧ γ.reCCOk = putget3.ccOk ps ∧ γ.reBoot = bootLog ∧ γ.reNoSnap = true ∧ γ.reNoXfer = true⌝ -∗
      letI : MemStorReg GF := ⟨reg⟩; bootstrapContract cfg U γ id bootLog N dir)

instance bootPremise_persistent (N : Nat) (ps : List w64) (bootLog : List EntryM)
    (dir : w64 → List GoString) (name peerAddr client : GoString) (id : w64) :
    Persistent (bootPremise (GF := GF) N ps bootLog dir name peerAddr client id) := by
  unfold bootPremise; infer_instance

/-- **`Main`'s named premises** (persistent; putget3's at linkv3p's configuration): `bootstrap`'s
contract for each member, at the cluster `ids id₁ id₂ id₃` and the directory `dir3`, and the
premises the members share. -/
def premises (N : Nat) (id₁ id₂ id₃ : w64) (bootLog : List EntryM) : IProp GF :=
  iprop(
    bootPremise N (ids id₁ id₂ id₃) bootLog (dir3 id₁ id₂ id₃) name₁ peerAddr₁ clientAddr₁ id₁ ∗
    bootPremise N (ids id₁ id₂ id₃) bootLog (dir3 id₁ id₂ id₃) name₂ peerAddr₂ clientAddr₂ id₂ ∗
    bootPremise N (ids id₁ id₂ id₃) bootLog (dir3 id₁ id₂ id₃) name₃ peerAddr₃ clientAddr₃ id₃ ∗
    putget3.commonPremises)

instance premises_persistent (N : Nat) (id₁ id₂ id₃ : w64) (bootLog : List EntryM) :
    Persistent (premises (GF := GF) N id₁ id₂ id₃ bootLog) := by
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
def clientOk (γ : linkvtxn.LinkvNames) (cl : Loc) : IProp GF :=
  iprop(∃ (ms : List (EtcdGrove.client.SrvAt GF)) (V : EtcdGrove.client.WEnv GF), ⌜ms ≠ []⌝ ∗
    isNewClient cl (ms.map EtcdGrove.client.SrvAt.addr) V ∗
    EtcdGrove.client.clientWriteOnce cl (ms.map EtcdGrove.client.SrvAt.addr) ∗
    ([∗list] sv ∈ ms, EtcdGrove.client.kvRegsAt sv) ∗
    ([∗list] sv ∈ ms, linkvtxn.linkvInv γ sv.γr.kv))

instance clientOk_persistent (γ : linkvtxn.LinkvNames) (cl : Loc) :
    Persistent (clientOk (GF := GF) γ cl) := by
  unfold clientOk; infer_instance

/-- **A member started and served** (the success of `startMember`): the shared start's `common.memberUp` reduced
to what `Main` needs of it -- the server's request and read views (at its apply environment `E`,
agreeing with the stand-in `E₀`, auth off), the `GoAttach` resources with the thread token
(`srvGoRes`), the member's place in the network with a reader's token of its transport
(`common.srvPeerCtl`: what the partitioner's `CutPeer`/`MendPeer` take), and etcd's `Put`, `Range`, `DeleteRange` and `Txn` registered at its
client address (`etcd_kv_started`), what its client's `Apply` takes, and (D29) that address
refusal-free (`etcd_noRefusal`). -/
def memberServed (γn : NetNames GF) (s : Loc) (id : w64) (ρ : ReqNames) (E₀ : apply.AEnv GF)
    (client : GoString) : IProp GF :=
  iprop(∃ (E : apply.AEnv GF) (γw : GName) (cid mid : w64),
    ⌜envAgree E E₀ ∧ E.authOn = false⌝ ∗
    isServerReq s E { ρ with wait := γw } ∗ isServerRead s E ρ.rd ∗ srvGoRes s ∗
    common.srvPeerCtl γn s id ∗
    isGrpcRpc client go!"/etcdserverpb.KV/Put" (EtcdGrove.client.etcdPutSpec E ρ.rd cid mid) ∗
    isGrpcRpc client go!"/etcdserverpb.KV/Range" (EtcdGrove.client.etcdRangeSpec E ρ.rd cid mid) ∗
    isGrpcRpc client go!"/etcdserverpb.KV/DeleteRange"
      (EtcdGrove.client.etcdDeleteSpec E ρ.rd cid mid) ∗
    isGrpcRpc client go!"/etcdserverpb.KV/Txn" (EtcdGrove.client.etcdTxnSpec E ρ.rd ρ.rd cid mid) ∗
    -- (W2 of `notes/watch-cut-plan.md`, 2026-10-21) the member's watch server, its `Watch` stream
    -- served at the client address
    (∃ (pw : Loc) (R : v3rpc.WSrv GF), v3rpc.isWatchServer pw R ∗ ⌜R.s = s ∧ R.E = E⌝ ∗
      isGrpcStream (Req := v3rpc.pbWatchRequest) (Rep := v3rpc.pbWatchResponse) client
        go!"/etcdserverpb.Watch/Watch" (v3rpc.watchUp R.γ)
        (fun γs Dn => v3rpc.watchStreamSpec γs R.γ R.cid R.mid Dn)) ∗
    -- (D29, 2026-10-21) the member never answers with a refusal (`etcd_noRefusal`)
    ⌜noRefusalAt client⌝)

end defs

section forwards
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
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

/-- (D32) A stream method registered at `b` is registered at an address that forwards to `b`. -/
theorem isGrpcStream_forwards {Req Rep : StreamMsg GF} (a b name : GoString)
    (Up : Nat → Req.M → IProp GF) (Spec : StreamSpec Rep) :
    forwards (GF := GF) a b ∗ isGrpcStream b name Up Spec ⊢ isGrpcStream a name Up Spec := by
  iintro ⟨#Hf, #Hr⟩
  iunfold forwards at Hf
  icases Hf with ⟨-, -, #Hf⟩
  unfold isGrpcStream
  icases Hr with ⟨%mh, %srv, %ics, %S, #Hs, #Hm⟩
  iexists mh, srv, ics, S
  isplitl
  · iapply Hf $$ %name %mh %srv %ics %S Hs
  · iexact Hm

end forwards

section cluster
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- (W4 of `notes/watch-cut-plan.md`) The members, each at its bridge's address with its watch
server. -/
def memAt3 (R₁ R₂ R₃ : v3rpc.WSrv GF) : Nat → GoString × v3rpc.WSrv GF
  | 0 => (bridgeAddr₁, R₁)
  | 1 => (bridgeAddr₂, R₂)
  | _ => (bridgeAddr₃, R₃)

/-- **The clients' watch environment** (W4): the three members at their bridges, the watch
contract at the cluster's committed history (`etcdModelOfHistory`, at the first member's names,
which the others' agree with), under the prefix `pfx`. `clientv3.New` takes it as its caller's
choice (`isNewClient`); a client that never watches needs none of its facts. -/
def watchEnv (R₁ R₂ R₃ : v3rpc.WSrv GF) (γr : ReadNames) (pfx : GoString) :
    EtcdGrove.client.WEnv GF :=
  ⟨R₁, bridgeAddr₁, [], null, null, pfx, null, v3rpc.etcdModelOfHistory γr.raft γr.kv,
    v3rpc.histWL γr.raft γr.kv, memAt3 R₁ R₂ R₃, 3⟩

/-- **A member of the started cluster** (persistent; W4: what `startCluster` gives of each, from
`memberServed` and its bridge's start): its bridge's address serving
its client address's, its read view, etcd's KV specs registered at its client address and the
address refusal-free, its watch server and `Watch` stream there, its names agreeing with the
cluster's (the raft names, what the KV model reads). -/
def memberAt (γn : NetNames GF) (s : Loc) (id : w64) (ρ : ReqNames) (E : apply.AEnv GF)
    (cid mid : w64) (R : v3rpc.WSrv GF) (b c : GoString) (γ : RaftNames) : IProp GF :=
  iprop(forwards b c ∗ isServerRead s E ρ.rd ∗
    isGrpcRpc c go!"/etcdserverpb.KV/Put" (EtcdGrove.client.etcdPutSpec E ρ.rd cid mid) ∗
    isGrpcRpc c go!"/etcdserverpb.KV/Range" (EtcdGrove.client.etcdRangeSpec E ρ.rd cid mid) ∗
    isGrpcRpc c go!"/etcdserverpb.KV/DeleteRange"
      (EtcdGrove.client.etcdDeleteSpec E ρ.rd cid mid) ∗
    isGrpcRpc c go!"/etcdserverpb.KV/Txn" (EtcdGrove.client.etcdTxnSpec E ρ.rd ρ.rd cid mid) ∗
    ⌜noRefusalAt c⌝ ∗ (∃ pw : Loc, v3rpc.isWatchServer pw R) ∗ ⌜R.s = s ∧ R.E = E⌝ ∗
    isGrpcStream (Req := v3rpc.pbWatchRequest) (Rep := v3rpc.pbWatchResponse) c
      go!"/etcdserverpb.Watch/Watch" (v3rpc.watchUp R.γ)
      (fun γs Dn => v3rpc.watchStreamSpec γs R.γ R.cid R.mid Dn) ∗
    ⌜ρ.rd.raft = ⟨γ, [], W64 0⟩ ∧ ρ.rd.kv.c0 = W64 0 ∧
      ρ.rd.kv.ch0 = apply.alarmChain false false false ∧ ρ.rd.kv.log0 = [[], []]⌝)

instance memberAt_persistent (γn : NetNames GF) (s : Loc) (id : w64) (ρ : ReqNames)
    (E : apply.AEnv GF) (cid mid : w64) (R : v3rpc.WSrv GF) (b c : GoString) (γ : RaftNames) :
    Persistent (memberAt γn s id ρ E cid mid R b c γ) := by
  unfold memberAt; infer_instance

/-- **The cluster started** (W4: `startCluster`'s success): the members' slice, the bridges' and
the clients'; each member (`memberAt`), each bridge owned and not blackholed, each client
`clientv3.New`'s over the three bridges at the watch environment (`watchEnv`, the prefix `pfx`);
the client's view of etcd's KV at the start store; the members' KV names agreeing, at the workload
`W`. -/
def clusterUp (id₁ id₂ id₃ : w64) (bootLog : List EntryM) (W : SrvWorkload) (pfx : GoString)
    (srvs brs clis : GoSlice) : IProp GF :=
  iprop(∃ (γ : RaftNames) (γn : NetNames GF) (ρ₁ ρ₂ ρ₃ : ReqNames) (E₁ E₂ E₃ : apply.AEnv GF)
      (cid₁ cid₂ cid₃ mid₁ mid₂ mid₃ : w64) (R₁ R₂ R₃ : v3rpc.WSrv GF) (s₁ s₂ s₃ cl₁ cl₂ cl₃ : Loc)
      (br₁ br₂ br₃ : GoInterface),
    srvs ↦*□ [s₁, s₂, s₃] ∗ brs ↦*□ [br₁, br₂, br₃] ∗ clis ↦*□ [cl₁, cl₂, cl₃] ∗
    memberAt γn s₁ id₁ ρ₁ E₁ cid₁ mid₁ R₁ bridgeAddr₁ clientAddr₁ γ ∗
    memberAt γn s₂ id₂ ρ₂ E₂ cid₂ mid₂ R₂ bridgeAddr₂ clientAddr₂ γ ∗
    memberAt γn s₃ id₃ ρ₃ E₃ cid₃ mid₃ R₃ bridgeAddr₃ clientAddr₃ γ ∗
    -- (2026-10-24, rafthttp stage 6d) each member's place in the network, with a reader's token
    -- of its transport (until then in `memberAt`, without)
    common.srvPeerCtl γn s₁ id₁ ∗ common.srvPeerCtl γn s₂ id₂ ∗ common.srvPeerCtl γn s₃ id₃ ∗
    bridge.ownBridge br₁ clientAddr₁ false ∗ bridge.ownBridge br₂ clientAddr₂ false ∗
    bridge.ownBridge br₃ clientAddr₃ false ∗
    isNewClient cl₁ [bridgeAddr₁, bridgeAddr₂, bridgeAddr₃] (watchEnv R₁ R₂ R₃ ρ₁.rd pfx) ∗
    isNewClient cl₂ [bridgeAddr₁, bridgeAddr₂, bridgeAddr₃] (watchEnv R₁ R₂ R₃ ρ₁.rd pfx) ∗
    isNewClient cl₃ [bridgeAddr₁, bridgeAddr₂, bridgeAddr₃] (watchEnv R₁ R₂ R₃ ρ₁.rd pfx) ∗
    etcdKV ρ₁.rd.kv (kvStateOf (kvModel ρ₁.rd.kv (bootEntries bootLog))) ∗
    ⌜ρ₁.rd.kv.wl = W ∧ ρ₂.rd.kv.st = ρ₁.rd.kv.st ∧ ρ₂.rd.kv.wl = ρ₁.rd.kv.wl ∧
      ρ₃.rd.kv.st = ρ₁.rd.kv.st ∧ ρ₃.rd.kv.wl = ρ₁.rd.kv.wl⌝)

end cluster

end linkv3p
end EtcdGrove
end Perennial
