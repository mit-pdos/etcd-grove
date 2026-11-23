/-
A replica's internal contracts and its boot specs (interface of stage 2, `notes/stage2-plan.md`):
replica `k` of the configuration `c` the client node chose (`confIs γ c`), whose values replace
stage 1's constants (pipeline `c.pipe`, leader timeout `c.tmo`, leader mode 2, server mode `c.se`,
epochs of `c.ep` slots, `c.n` replicas).

A replica (`raxos/replica/src`) is a proxy, proposers and a recorder in one process, joined by
channels and a shared batch store. Package `proxy` proves the proxy (and the store), package
`replica` the recorder, the proposers and `server.go`; they meet here:

* **the channels' elements** (bag channels, `isChanBag`): `proposeReqP` (proxy → proposer: the
  slot, its `init` event, the leader flag, the batches registered, the decided slots piggybacked),
  `proposeRespP` (proposer → proxy: a decision), `decisionP` (recorder → proxy and proxy → proposer:
  decided slots), `fetchReqP`, `fetchRespP` (registered batches);
* **the batch store** (`isStore`, a sealed slot of package `proxy`): `ClientBatchStore.Add` of a
  registered batch, `Get` of a registered batch (`storeHas`: an id once there stays there);
* **the proxy's constructor and entry points** (`NewProxy`, `Proxy.NetworkInit`, `Proxy.Run`),
  over the sealed slots `proxyOwn` and `proxyShared` of package `proxy`;
* **the server's boot** (`raxos.New`, `Server.NetworkInit`, `Server.StartProposers`, `Server.Run`,
  what `kit.go`'s `serve` calls), over the sealed slots `serverNew`, `serverNet`, `serverProp` of
  package `replica`, from the replica's share `replicaRes γ k`.
-/
module

public import Dsverify.Proof.raxos.Proxy.Slots
public import Dsverify.Proof.raxos.Replica.Slots
public import Dsverify.Proof.raxos.Proposer.Slots

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.raxos


open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open Perennial.raxos.pure Perennial.raxos.msg
open raxos.replica.src

/-! ## Specs -/

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [π : NetProtoGS] [qv : hyp.QpVocab GF]

/-- `cb.Add(batch)`: a registered batch (its value read for good); afterwards the store has its
id. -/
abbrev ClientBatchStore.Add.spec : Prop :=
  ∀ (γ : QNames) (γs : GName) (cb : Loc) (v : raxos.proto.client.ClientBatch) (b : Batch),
  {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.replica.src ∗ isStore γ γs cb ∗
      repCBVal v .discard b ∗ batchReg γ b.id b ∗ ⌜batchFit b⌝ }}
    (App (Val (cb @!! go.GoType.PointerType ClientBatchStore.ty @!! go!"Add")) (Val #v))
  {{ RET #(); storeHas γs b.id }}

/-- `cb.Get(x)`: the batch with id `x`, registered, if the store has it (it does if
`storeHas γs x` is known). -/
abbrev ClientBatchStore.Get.spec : Prop :=
  ∀ (γ : QNames) (γs : GName) (cb : Loc) (x : GoString) (known : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.replica.src ∗ isStore γ γs cb ∗
      (if known then storeHas γs x else iprop(True)) }}
    (App (Val (cb @!! go.GoType.PointerType ClientBatchStore.ty @!! go!"Get")) (Val #x))
  {{ (v : raxos.proto.client.ClientBatch) (ok : Bool), RET (PairV #v #ok);
      ⌜known → ok⌝ ∗
      if ok then ∃ b, ⌜b.id = x ∧ batchFit b⌝ ∗ repCBVal v .discard b ∗ batchReg γ x b ∗
        storeHas γs x
      else iprop(True) }}

/-- `NewProxy(k, cfg, ...)` with the kit's parameters (`serve`'s, through `raxos.New`) for the
configuration `c`: the proxy's state, from its channels (bags with their elements' predicates),
the store, its init frontier and the shared facts. -/
abbrev NewProxy.spec : Prop :=
  ∀ (γ : QNames) (c : QConf) (k : Nat) (cv : raxos.configuration.InstanceConfig)
    (toProp fromProp fromRec toFetch fromFetch toDec : Loc)
    (γ1 γ2 γ3 γ4 γ5 γ6 : ChanNames) (srv cb : Loc) (γs : GName) (logPath : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.replica.src ∗ ⌜c.ok ∧ 1 ≤ k ∧ k ≤ c.n⌝ ∗
      confIs γ c ∗ cfgVal c.n cv ∗
      isChanBag γ1 toProp (proposeReqP γ k) ∗ isChanBag γ2 fromProp (proposeRespP γ k) ∗
      isChanBag γ3 fromRec (decisionP γ) ∗ isChanBag γ4 toFetch fetchReqP ∗
      isChanBag γ5 fromFetch (fetchRespP γ) ∗ isChanBag γ6 toDec (decisionP γ) ∗
      isStore γ γs cb ∗ initFront γ k 1 ∗
      inv consN (consInv γ) ∗ inv smrN (smrInv γ) ∗ netProtos γ ∗
      batchReg γ go!"nil" nilBatch ∗ spentLb γ 0 }}
    (callV (@! raxos.replica.src.NewProxy)
      [ #(W64 k), #cv, #toProp, #fromProp, #fromRec, #logPath, #(W64 50), #(W64 c.pipe),
       #(W64 c.tmo), #false, #(W64 0), #srv, #(W64 2), #cb, #(W64 c.se), #toFetch, #fromFetch,
       #(W64 0), #(W64 c.ep), #toDec, #(W64 0), #(W64 8), #(W64 8), #(W64 0)])
  {{ (pr : Loc), RET #pr; proxyOwn γ c k pr ∗ proxyShared γ c k pr }}

/-- `pr.NetworkInit()`: the sender goroutines and the accept routine, on the proxy's port. -/
abbrev Proxy.NetworkInit.spec : Prop :=
  ∀ (γ : QNames) (c : QConf) (k : Nat) (pr : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.replica.src ∗ proxyShared γ c k pr ∗
      netTok γ k }}
    (App (Val (pr @!! go.GoType.PointerType Proxy.ty @!! go!"NetworkInit")) (Val #()))
  {{ RET #(); True }}

/-- `pr.Run()`: the main loop and the batch timer, in their goroutines. -/
abbrev Proxy.Run.spec : Prop :=
  ∀ (γ : QNames) (c : QConf) (k : Nat) (pr : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.replica.src ∗ proxyOwn γ c k pr ∗
      proxyShared γ c k pr }}
    (App (Val (pr @!! go.GoType.PointerType Proxy.ty @!! go!"Run")) (Val #()))
  {{ RET #(); True }}

/-- `NewProposer(k, i, peers, ...)` with the parameters `createProposers` passes (the kit's
configuration `c`): a proposer of replica `k` with thread id `i + 1`. -/
abbrev NewProposer.spec : Prop :=
  ∀ (γ : QNames) (c : QConf) (k : Nat) (i : w64) (peers : GoSlice)
    (toProp fromProp toFetch fromFetch toDec : Loc) (γ1 γ2 γ4 γ5 γ6 : ChanNames),
  {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.replica.src ∗ ⌜c.ok ∧ 1 ≤ k ∧ k ≤ c.n⌝ ∗
      confIs γ c ∗ peersP γ c.n peers ∗
      isChanBag γ1 toProp (proposeReqP γ k) ∗ isChanBag γ2 fromProp (proposeRespP γ k) ∗
      isChanBag γ4 toFetch fetchReqP ∗ isChanBag γ5 fromFetch (fetchRespP γ) ∗
      isChanBag γ6 toDec (decisionP γ) ∗
      inv consN (consInv γ) ∗ inv smrN (smrInv γ) }}
    (callV (@! raxos.replica.src.NewProposer)
      [ #(W64 k), #i, #peers, #toProp, #fromProp, #toFetch, #fromFetch, #false, #(W64 0),
        #(W64 100000), #(W64 c.se), #toDec, #false, #(W64 0), #(W64 500)])
  {{ (p : Loc), RET #p; proposerP γ c k p }}

/-- `p.runProposer()`: the proposer's loop, in its goroutine. -/
abbrev Proposer.runProposer.spec : Prop :=
  ∀ (γ : QNames) (c : QConf) (k : Nat) (p : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.replica.src ∗ proposerP γ c k p }}
    (App (Val (p @!! go.GoType.PointerType Proposer.ty @!! go!"runProposer")) (Val #()))
  {{ RET #(); True }}

/-- `raxos.New(cfg, k, ...)` with the kit's parameters (`serve`'s) for the configuration `c`. -/
abbrev New.spec : Prop :=
  ∀ (γ : QNames) (c : QConf) (k : Nat) (cfg : Loc) (cv : raxos.configuration.InstanceConfig)
    (logPath : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.replica.src ∗
      cfg ↦□ cv ∗ cfgVal c.n cv ∗ replicaRes γ c k }}
    (callV (@! raxos.replica.src.New)
      [ #cfg, #(W64 k), #logPath, #(W64 50), #(W64 c.tmo), #(W64 c.pipe), #false, #(W64 0),
       #(W64 2), #(W64 c.se), #(W64 0), #(W64 c.ep), #(W64 0), #(W64 8), #(W64 8), #(W64 0), #false,
       #(W64 0), #(W64 500)])
  {{ (s : Loc), RET #s; serverNew γ c k s }}

/-- `s.NetworkInit()`. -/
abbrev Server.NetworkInit.spec : Prop :=
  ∀ (γ : QNames) (c : QConf) (k : Nat) (s : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.replica.src ∗ serverNew γ c k s }}
    (App (Val (s @!! go.GoType.PointerType Server.ty @!! go!"NetworkInit")) (Val #()))
  {{ RET #(); serverNet γ c k s }}

/-- `s.StartProposers()`. -/
abbrev Server.StartProposers.spec : Prop :=
  ∀ (γ : QNames) (c : QConf) (k : Nat) (s : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.replica.src ∗ serverNet γ c k s }}
    (App (Val (s @!! go.GoType.PointerType Server.ty @!! go!"StartProposers")) (Val #()))
  {{ RET #(); serverProp γ c k s }}

/-- `s.Run()`. -/
abbrev Server.Run.spec : Prop :=
  ∀ (γ : QNames) (c : QConf) (k : Nat) (s : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.replica.src ∗ serverProp γ c k s }}
    (App (Val (s @!! go.GoType.PointerType Server.ty @!! go!"Run")) (Val #()))
  {{ RET #(); True }}

end specs

end Perennial.raxos
