/-
Ported from dsverify-lab examples/swiftpaxos/proof/Spec/swiftnet/Interface.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
Stage 2's interface: the hub statements of the run (notes/stage2-plan.md, "The hub map"), for
the kit with each client on a node of its own (a `RemoteDistSpec`).

* (in `Spec/swiftnet/Base.lean`, below the SwiftPaxos slot, which uses them: `Conf`, the leader
  changes and their encoding, the addresses, `confIs`, `memIs`, `linOwn`, `lin.keyName`);
* `SwiftNames`, the run's ghost names (`RemoteDistSpec.Γs`);
* the slots of each subsystem the hubs name: `conf.*` (the configuration, written once by the
  orchestrator), `mem.*` (the replicas' membership, written once by the master), `lin.*` (the
  abstract key-value state, `own_state`), and the SwiftPaxos protocol's slot `sp.*`
  (`Spec/swift/Slot.lean`, the definitions in `Spec/swift/Inv.lean`);
* the address protocols (`protoP`, `protoQ`) and the rpc services (`services`);
* the node shares (`orchShare`, `clientNodeShare`, `serverShare`);
* the abstract state the clients' updates own (`ownState`).

(dsv-swiftpaxos: the lab's assembly of its `RemoteDistSpec` goal (`StartOk`, `OrchOk`,
`ClientNodeOk`, `ServersOk`, `goal_spec_of`) is gone: the kit is remote's here, its statement
`swiftpaxos_remote_robust`.)

Everything here is over the global ghost state (`[G : GooseGlobalGS .hasLC netDistGF]`), as
`Harness/Remote.lean`'s header asks. The proofs of the parts are the Prove phase's (`Proof/`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Base
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.examples.swiftnet.Base
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.swift.Slot
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.lib.RpcHttpHyps

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

/-! ## Ghost names -/

/-- The run's ghost names (`RemoteDistSpec.Γs`). -/
structure SwiftNames (GF : BundledGFunctors) where
  /-- the configuration, written once by the orchestrator (a mono list of length ≤ 1) -/
  conf : GName
  /-- the replicas' addresses by replica id, written once by the master when it is ready -/
  mem : GName
  /-- the rpc world of the master's and the replicas' rpc addresses -/
  W : net.rpc.RpcWorld GF
  /-- the SwiftPaxos protocol's names (sealed) -/
  sp : sp.Names
  /-- the abstract key-value state (a ghost variable; half in `sp`'s invariant) -/
  lin : GName

section slots
variable [GoGlobalContext] [G : GooseGlobalGS .hasLC netDistGF] [π : NetProtoGS]

/-! ## The configuration slot (`conf`) -/

/-- The configuration is `c` (persistent). -/
def conf.is (γ : SwiftNames netDistGF) (c : Conf) : IProp netDistGF := confIs γ.conf c

/-- The orchestrator's right to write the configuration (once). -/
def conf.writer (γ : SwiftNames netDistGF) : IProp netDistGF :=
  monoListAuthOwn (A := Conf) γ.conf 1 []

/-- What a dialer of a server node's configuration port writes: a prefix of the configuration's
encoding, with no change. -/
def conf.dialP (γ : SwiftNames netDistGF) : Proto netDistGF := fun _ bs =>
  iprop(⌜bs = []⌝ ∨ ∃ c, conf.is γ c ∗ ⌜bs <+: c.encode⌝)

/-- What a dialer of a client node's configuration port writes: a prefix of the configuration's
encoding with leader changes `decode` accepts. -/
def conf.dialPC (γ : SwiftNames netDistGF) : Proto netDistGF := fun _ bs =>
  iprop(⌜bs = []⌝ ∨ ∃ c cs, conf.is γ c ∗ ⌜c.changesOk cs ∧ bs <+: c.encodeC cs⌝)

/-- What a dialer of a client node's start port writes (the orchestrator, once every node
acknowledged its configuration): a prefix of the configuration's encoding, with no change, and
the registration of every predicted node of the configuration (`sp.allPredsReg`, what the
client's connect needs). -/
def conf.startP (γ : SwiftNames netDistGF) : Proto netDistGF := fun _ bs =>
  iprop(⌜bs = []⌝ ∨ ∃ c, conf.is γ c ∗ sp.allPredsReg γ.sp γ.conf ∗ ⌜bs <+: c.encode⌝)

/-- What a configuration port's server writes: at most the acknowledgment byte. -/
def conf.ackQ : Proto netDistGF := fun _ bs => iprop(⌜bs <+: [confAck]⌝)

/-- What the configuration port of predicted node `n` (a client node, or a replica node of the
configuration) writes: at most the acknowledgment byte, which says that `n`'s prediction is
registered (L2, notes/l2-design.md §5: each predicted node registers before its first ack). -/
def conf.ackQP (γ : SwiftNames netDistGF) (n : sp.PNode) : Proto netDistGF := fun _ bs =>
  iprop(⌜bs <+: [confAck]⌝ ∗ (⌜bs = []⌝ ∨ sp.predReg γ.sp n))

/-! ## The membership slot (`mem`) -/

/-- The replicas' addresses, by replica id, are `l` (persistent; the master's `NodeList`). -/
def mem.is (γ : SwiftNames netDistGF) (l : List GoString) : IProp netDistGF := memIs γ.mem l

/-- The master's right to fix the membership (once). -/
def mem.writer (γ : SwiftNames netDistGF) : IProp netDistGF :=
  monoListAuthOwn (A := List GoString) γ.mem 1 []

/-! ## The abstract state (`lin`) -/

/-- The key-value state, as the client spec's `own_state` (the atomic updates' half): the
linearized puts so far, a ghost variable whose other half is in `sp.inv` (`Base.lean`'s
`linOwn`). -/
def lin.own (γ : SwiftNames netDistGF) (σ : (kv GoString GoString).State) : IProp netDistGF :=
  linOwn γ.lin σ

/-! ## Laws of the slots (over `Base.lean`'s) -/

instance conf.is_persistent (γ : SwiftNames netDistGF) (c : Conf) : Persistent (conf.is γ c) :=
  by unfold conf.is; infer_instance

instance mem.is_persistent (γ : SwiftNames netDistGF) (l : List GoString) :
    Persistent (mem.is γ l) := by unfold mem.is; infer_instance

theorem conf.is_agree (γ : SwiftNames netDistGF) (c1 c2 : Conf) :
    conf.is γ c1 ∗ conf.is γ c2 ⊢ ⌜c1 = c2⌝ := confIs_agree γ.conf c1 c2

theorem mem.is_agree (γ : SwiftNames netDistGF) (l1 l2 : List GoString) :
    mem.is γ l1 ∗ mem.is γ l2 ⊢ ⌜l1 = l2⌝ := memIs_agree γ.mem l1 l2

/-- `conf.is` is the slot's `confIs` at the run's name (what `sp`'s statements take). -/
theorem conf.is_confIs (γ : SwiftNames netDistGF) (c : Conf) : conf.is γ c ⊣⊢ confIs γ.conf c :=
  .rfl

/-- `mem.is` is the slot's `memIs` at the run's name. -/
theorem mem.is_memIs (γ : SwiftNames netDistGF) (l : List GoString) : mem.is γ l ⊣⊢ memIs γ.mem l :=
  .rfl

/-- The orchestrator writes the configuration once (`conf.writer` spent). -/
theorem conf.write (γ : SwiftNames netDistGF) (c : Conf) :
    ⌜c.valid⌝ ∗ conf.writer γ ⊢ |==> conf.is γ c := by
  unfold conf.writer conf.is confIs
  iintro ⟨%Hv, H⟩
  imod monoListAuthOwn_update (γ := γ.conf) [c] List.nil_prefix $$ H with ⟨-, #Hlb⟩
  imodintro
  iframe Hlb
  ipureintro; exact Hv

/-- The master fixes the membership once (`mem.writer` spent). -/
theorem mem.write (γ : SwiftNames netDistGF) (l : List GoString) :
    ⌜l.Nodup ∧ ∀ a ∈ l, a ∈ replicaAddrs⌝ ∗ mem.writer γ ⊢ |==> mem.is γ l := by
  unfold mem.writer mem.is memIs
  iintro ⟨%Hv, H⟩
  imod monoListAuthOwn_update (γ := γ.mem) [l] List.nil_prefix $$ H with ⟨-, #Hlb⟩
  imodintro
  iframe Hlb
  ipureintro; exact Hv

end slots

section protos
variable [GoGlobalContext] [G : GooseGlobalGS .hasLC netDistGF] [π : NetProtoGS]
variable [SwiftNetPkgState netDistGF]

/-- The protocol of what a dialer of `a` writes (for the plain addresses). -/
def protoP (γ : SwiftNames netDistGF) (a : GoString) : Proto netDistGF :=
  if a ∈ confAddrs then conf.dialP γ
  else if a ∈ clientConfAddrs then conf.dialPC γ
  else if a ∈ clientStartAddrs then conf.startP γ
  else match replicaAddrs.idxOf? a with
    | some _ => sp.inP γ.sp γ.conf γ.mem
    | none => fun _ _ => iprop(True)

/-- The protocol of what an acceptor at `a` writes (for the plain addresses). -/
def protoQ (γ : SwiftNames netDistGF) (a : GoString) : Proto netDistGF :=
  match clientConfAddrs.idxOf? a with
  | some c => conf.ackQP γ (sp.PNode.cl c)
  | none =>
  if a ∈ clientStartAddrs then conf.ackQ else
  match confAddrs.idxOf? a with
  | some 0 => conf.ackQ
  | some (k + 1) => conf.ackQP γ (sp.PNode.rep k)
  | none => match replicaAddrs.idxOf? a with
    | some _ => sp.outQ γ.sp γ.conf γ.mem
    | none => fun _ _ => iprop(True)

end protos

/-! ## The rpc services (`W.SS`) -/

section services
variable [GoGlobalContext] [G : GooseGlobalGS .hasLC netDistGF] [π : NetProtoGS]
variable [SwiftNetPkgState netDistGF]

/-- The services of each rpc address: the master's (`"Master"` at `masterAddr`) and each
replica node's (`"Replica"` at its rpc port). The method specs are the SwiftPaxos slot's
(`sp.masterSpec`, `sp.replicaRpcSpec`, over the codec's encodings, `Spec/swift/Inv.lean`),
accepting error answers too (`withErr`: `Net/`'s server answers undecodable arguments so). -/
def services (γconf γmem : GName) :
    GoString → GoString → Option (net.rpc.MethodSpec netDistGF) := fun a svc =>
  if a = masterAddr ∧ svc = go!"Master" then some (withErr (sp.masterSpec γconf γmem))
  else if a ∈ replicaRpcAddrs ∧ svc = go!"Replica" then some (withErr (sp.replicaRpcSpec γconf γmem))
  else none

end services

/-! ## The shares -/

section shares
variable [GoGlobalContext] [G : GooseGlobalGS .hasLC netDistGF]
variable [SwiftNetPkgState netDistGF] [RpcHttpAddr netDistGF]

/-- What every node gets: every address's protocols (persistent; the rpc listeners' over HTTP,
`RpcHttpAddr.rpcLisP`) and the shared invariants. -/
def common (γ : SwiftNames netDistGF) : IProp netDistGF :=
  iprop(([∗list] a ∈ plainAddrs, addrProto a (protoP γ a) (protoQ γ a)) ∗
    ⌜γ.W.SS = services γ.conf γ.mem⌝ ∗
    ([∗list] la ∈ rpcLis, RpcHttpAddr.rpcLisP γ.W la (connectReq defaultRPCPath) connectAns) ∗
    sp.inv γ.sp γ.conf γ.mem γ.lin)

instance common_persistent (γ : SwiftNames netDistGF) : Persistent (common γ) := by
  unfold common; infer_instance

/-- The orchestrator's share (node 0): its address's token, the configuration's writer token
and the abstract state's half at the model's initial state (`New` returns it as `own_state`). -/
def orchShare (γ : SwiftNames netDistGF) : IProp netDistGF :=
  iprop(addrTok orchAddr ∗ conf.writer γ ∗ lin.own γ (kv GoString GoString).init ∗
    common γ)

/-- Client node `c`'s share (node `1 + c`): its own address's, configuration port's and start
port's tokens,
client `c`'s share of the protocol (`sp.clientStart`: the client id `c + 1`) and the node's
right to register its prediction (L2). -/
def clientNodeShare (γ : SwiftNames netDistGF) (c : Nat) : IProp netDistGF :=
  iprop(addrTok (clientNodeAddrs.getD c go!"") ∗
    addrTok (clientConfAddrs.getD c go!"") ∗ addrTok (clientStartAddrs.getD c go!"") ∗
    sp.clientStart γ.sp c ∗
    sp.predTok γ.sp (sp.PNode.cl c) ∗ common γ)

/-- Server node `i + 1`'s addresses (node `7 + i`): the master's rpc address and configuration
port; replica `k + 2`'s peer and client port, rpc port and configuration port. -/
def serverAddrs (i : Nat) : List GoString :=
  if i = 0 then [masterAddr, confAddrs.getD 0 go!""]
  else [replicaAddrs.getD (i - 1) go!"", replicaRpcAddrs.getD (i - 1) go!"", confAddrs.getD i go!""]

/-- Server node `i + 1`'s share (node `7 + i`): its addresses' tokens (`nodeAddrs[7 + i]`), and
the master's (server node 1) the membership's writer token; a replica node's (server node
`k + 2`) its protocol share. -/
def serverShare (γ : SwiftNames netDistGF) (i : Nat) : IProp netDistGF :=
  iprop(([∗list] a ∈ serverAddrs i, addrTok a) ∗
    (if i = 0 then mem.writer γ
     else sp.replicaStart γ.sp (i - 1) ∗ sp.predTok γ.sp (sp.PNode.rep (i - 1))) ∗
    common γ)

end shares

/-! ## The parts of `goal_spec` -/

section parts
variable [GoGlobalContext]

/-- The abstract state (`RemoteDistSpec.own_state`): the linearized puts' state, whose values
are not empty (a put's value is not empty, `kit.pre`; `Op` reads an empty value as "not
found"), and the fact that every predicted node registered its prediction (L2: the orchestrator
gathers it before any operation; a client peeks it from its update at an invocation). -/
def ownState [G : GooseGlobalGS .hasLC netDistGF] (γ : SwiftNames netDistGF)
    (σ : (kv GoString GoString).State) : IProp netDistGF :=
  iprop(lin.own γ σ ∗ ⌜∀ k v, σ k = some v → v ≠ []⌝ ∗ sp.allPredsReg γ.sp γ.conf)

end parts

end Perennial.github_com.imdea_software.swiftpaxos

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

instance ownState_timeless [GoGlobalContext] [GooseGlobalGS .hasLC netDistGF]
    (γ : SwiftNames netDistGF) (σ : (kv GoString GoString).State) : Timeless (ownState γ σ) := by
  unfold ownState lin.own linOwn; infer_instance

end Perennial.github_com.imdea_software.swiftpaxos
