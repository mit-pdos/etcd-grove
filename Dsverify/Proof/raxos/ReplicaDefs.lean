/-
A replica's internal contracts and its boot specs (interface of stages 2-3, `notes/stage3-plan.md`):
replica `k` of a configuration `c` the orchestrator chose (`confIs γ c`).

A replica (`raxos/replica/src`) is a proxy, proposers and a recorder in one process, joined by
channels and a shared batch store. Package `proxy` proves the proxy (and the store), package
`replica` the recorder, the proposers and `server.go`; they meet here:

* **the channels' elements** (bag channels, `isChanBag`): `proposeReqP` (proxy → proposer: the
  slot, its `init` event with the request's leader flag, the batches registered, the decided
  slots piggybacked),
  `proposeRespP` (proposer → proxy: a decision), `decisionP` (recorder → proxy and proxy → proposer:
  decided slots), `fetchReqP`, `fetchRespP` (registered batches);
* **the batch store** (`isStore`, a sealed slot of package `proxy`): `ClientBatchStore.Add` of a
  registered batch, `Get` of a registered batch (`storeHas`: an id once there stays there);
* **the proxy's constructor and entry points** (`NewProxy`, `Proxy.NetworkInit`, `Proxy.Run`),
  over the sealed slots `proxyOwn` and `proxyShared` of package `proxy`;
* **the server's boot** (`raxos.New`, `Server.NetworkInit`, `Server.StartProposers`, `Server.Run`,
  what `kit.go`'s `serve` calls), over the sealed slots `serverNew`, `serverNet`, `serverProp` of
  package `replica`, from the replica's share `replicaRes γ k`.

Changed against the lab (notes/dsv-quepaxa.md): the configuration's addresses are `kit.go`'s
(`127.0.0.1`, distinct ports); the gRPC vocabulary is the hypotheses' (`Hyp.lean`); no `nodeIp`
(`Net/` has no node IPs); `ClientBatchStore`'s points-to is Perennial's generated one (`sync.Map`
is a translated struct there: the lab's `StoreInst.lean` is not needed).
-/
module

public import Dsverify.Proof.raxos.Proto
public import Dsverify.GeneratedProof.raxos.configuration

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.raxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open Perennial.raxos.pure Perennial.raxos.msg
open raxos.replica.src
open hyp.grpc (GrpcVocab)

/-- A call of the function value `f` with the arguments `args`. -/
def callV [GooseExts] (f : val) (args : List val) : Expr := args.foldl (fun e x => App e (Val x)) (Val f)

/-! ## Countable channel elements -/

section countable
variable [GooseExts]

instance ProposeRequest.countable : Pos.Countable ProposeRequest :=
  .ofInjective (fun v => Pos.Countable.encode (v.instance', v.proposalStr', v.proposalBtch',
    v.isLeader', v.lastDecidedIndexes', v.lastDecidedProposers', v.lastDecidedDecisions'))
    (by rintro ⟨⟩ ⟨⟩ h; have h := Pos.encode_inj h; simp_all)
instance ProposeResponse.countable : Pos.Countable ProposeResponse :=
  .ofInjective (fun v => Pos.Countable.encode (v.index', v.decisions', v.proposer', v.s'))
    (by rintro ⟨⟩ ⟨⟩ h; have h := Pos.encode_inj h; simp_all)
instance Decision.countable : Pos.Countable Decision :=
  .ofInjective (fun v => Pos.Countable.encode (v.indexes', v.decisions', v.proposers'))
    (by rintro ⟨⟩ ⟨⟩ h; have h := Pos.encode_inj h; simp_all)
instance FetchRequest.countable : Pos.Countable FetchRequest :=
  .ofInjective (fun v => Pos.Countable.encode v.ids')
    (by rintro ⟨⟩ ⟨⟩ h; have h := Pos.encode_inj h; simp_all)
instance FetchResposne.countable : Pos.Countable FetchResposne :=
  .ofInjective (fun v => Pos.Countable.encode v.batches')
    (by rintro ⟨⟩ ⟨⟩ h; have h := Pos.encode_inj h; simp_all)

end countable

/-! ## The configuration (`kit.go`'s `config`) -/

/-- Every node's IP as configured (`kit.go`'s address lists: `127.0.0.1`). -/
def ipOf (_k : Nat) : GoString := go!"127.0.0.1"

section cfg
variable [GooseExts]

/-- The configured replicas (`config`'s `Peers`): `1..n`. -/
def peersCfg (n : Nat) : List raxos.configuration.ReplicaInstance :=
  (List.range' 1 n).map (fun k => ⟨decStr k, ipOf k, decStr (7606 + k), decStr (7626 + k)⟩)

/-- The configured clients (`config`'s `Clients`): client `c` named `21 + c` at `clientAddr c`,
c < 6. -/
def clientsCfg : List raxos.configuration.ClientInstance :=
  (List.range 6).map (fun c => ⟨decStr (21 + c), ipOf (1 + c), decStr (7601 + c)⟩)

end cfg

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [π : NetProtoGS] [qv : hyp.QpVocab GF]

/-- An `InstanceConfig` value holding the configuration of `n` replicas (its slices
persistent). -/
def cfgVal (n : Nat) (cv : raxos.configuration.InstanceConfig) : IProp GF :=
  iprop(cv.Peers' ↦*□ peersCfg n ∗ cv.Clients' ↦*□ clientsCfg)

/-! ## The replica's share -/

/-- Replica `k`'s share of the start, in the configuration `c` (it is one of `c`'s replicas): its
addresses' tokens, its recorder's and its proxy's consensus ghost state, the configuration, the
shared invariants and protocols, the `"nil"` batch's registration. -/
def replicaRes (γ : QNames) (c : QConf) (k : Nat) : IProp GF :=
  iprop(⌜c.ok ∧ 1 ≤ k ∧ k ≤ c.n⌝ ∗ confIs γ c ∗
    addrTok (proxyAddr k) ∗ addrTok (recAddr k) ∗
    recHalf γ k ∅ ∗ initFront γ k 1 ∗
    inv consN (consInv γ) ∗ inv smrN (smrInv γ) ∗ netProtos γ ∗
    batchReg γ go!"nil" nilBatch ∗ spentLb γ 0)

/-! ## The channels' elements -/

/-- A `[]client.ClientBatch` slice's values `vs` hold the batches `bs`, each registered
(persistent). -/
def batchesP (γ : QNames) (vs : List raxos.proto.client.ClientBatch) (bs : List Batch) : IProp GF :=
  iprop(⌜vs.length = bs.length ∧ ∀ b ∈ bs, batchFit b⌝ ∗
    [∗list] k ↦ v ∈ vs, ∃ b, ⌜bs[k]? = some b⌝ ∗ repCBVal v .discard b ∗ batchReg γ b.id b)

/-- Decided slots in three parallel slices (`lastDecided*`, `Decision`'s fields), all decided
(persistent). -/
def decidedSlotsP (γ : QNames) (isl psl dsl : GoSlice) : IProp GF :=
  iprop(∃ (is : List w64) (ps : List w32) (dsls : List GoSlice) (ds : List (List GoString)),
    isl ↦*□ is ∗ psl ↦*□ ps ∗ dsl ↦*□ dsls ∗
    ⌜is.length = ds.length ∧ ps.length = ds.length ∧ dsls.length = ds.length⌝ ∗
    [∗list] k ↦ d ∈ ds, ∃ (sl : GoSlice) (i : w64), ⌜dsls[k]? = some sl ∧ is[k]? = some i ∧
      ∀ x ∈ d, strOk x⌝ ∗ sl ↦*□ d ∗ decided γ (sint.Z i) d)

/-- A propose request of proxy `me` (`proposeToIndex`, `proposePreviousEpochSummary`): its slot
was proposed with its ids and its leader flag (`init`; the event's step holds the flag's
justification), the batches are the ids' registered ones, the piggybacked slots are decided
(persistent). -/
def proposeReqP (γ : QNames) (me : Int) (v : ProposeRequest) : IProp GF :=
  iprop(∃ (ids : List GoString) (vs : List raxos.proto.client.ClientBatch) (bs : List Batch),
    v.proposalStr' ↦*□ ids ∗ v.proposalBtch' ↦*□ vs ∗ batchesP γ vs bs ∗
    ⌜bs.map Batch.id = ids⌝ ∗
    evIn γ (.init (sint.Z v.instance') me ids v.isLeader') ∗
    decidedSlotsP γ v.lastDecidedIndexes' v.lastDecidedProposers' v.lastDecidedDecisions')

/-- A propose response of proxy `me`'s proposer: a decision of a slot `me` proposed
(persistent). -/
def proposeRespP (γ : QNames) (me : Int) (v : ProposeResponse) : IProp GF :=
  iprop(∃ (ids ids0 : List GoString), v.decisions' ↦*□ ids ∗ decided γ (sint.Z v.index') ids ∗
    ∃ lead, evIn γ (.init (sint.Z v.index') me ids0 lead))

/-- Decided slots (`Decision`), at least one (`handleRecorderResponse` reads `indexes[0]`)
(persistent). -/
def decisionP (γ : QNames) (v : Decision) : IProp GF :=
  iprop(decidedSlotsP γ v.indexes' v.proposers' v.decisions' ∗ ⌜0 < sint.Z v.indexes'.len⌝)

/-- A fetch request: its ids, valid strings (persistent). -/
def fetchReqP (v : FetchRequest) : IProp GF :=
  iprop(∃ ids : List GoString, v.ids' ↦*□ ids ∗ ⌜∀ x ∈ ids, strOk x⌝)

/-- A fetch response: registered batches (persistent). -/
def fetchRespP (γ : QNames) (v : FetchResposne) : IProp GF :=
  iprop(∃ (vs : List raxos.proto.client.ClientBatch) (bs : List Batch),
    v.batches' ↦*□ vs ∗ batchesP γ vs bs)

/-! ## The proposers' gRPC clients -/

/-- The proposers' peers (`setupgRPC`'s): one per configured replica, in order, named `1..n`,
each a `consensusClient` over a gRPC client connection to that replica's recorder (persistent).
-/
def peersP (γ : QNames) (n : Nat) (sl : GoSlice) : IProp GF :=
  iprop(∃ ps : List peer, sl ↦*□ ps ∗ ⌜ps.length = n⌝ ∗
    [∗list] j ↦ p ∈ ps, ⌜sint.Z p.name' = j + 1⌝ ∗
      ∃ (l cc : Loc), ⌜p.client' = interface.mkOk (go.GoType.PointerType consensusClient.ty) #l⌝ ∗
        l ↦□ (consensusClient.mk
          (interface.mkOk (go.GoType.PointerType google_golang_org.grpc.ClientConn.ty) #cc)) ∗
        qv.grpc.isClientConn cc (world γ) (recAddr (j + 1)))

end defs

end Perennial.raxos
