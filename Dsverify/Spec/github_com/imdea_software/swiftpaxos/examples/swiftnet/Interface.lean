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
* the parts of `goal_spec` as named statements (`StartOk`, `OrchOk`, `ClientNodeOk`,
  `ServersOk`) and `goal_spec_of`, which assembles them (proved here, no sorry: only plumbing).

Everything here is over the global ghost state (`[G : GooseGlobalGS .hasLC netDistGF]`), as
`Harness/Remote.lean`'s header asks. The proofs of the parts are the Prove phase's (`Proof/`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Base
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.examples.swiftnet.Base
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.swift.Slot

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

/-- The protocol of what a dialer of `a` writes (for the plain addresses). -/
def protoP (γ : SwiftNames netDistGF) (a : GoString) : Proto netDistGF :=
  if a ∈ confAddrs then conf.dialP γ
  else if a ∈ clientConfAddrs then conf.dialPC γ
  else match replicaAddrs.idxOf? a with
    | some _ => sp.inP γ.sp γ.conf γ.mem
    | none => fun _ _ => iprop(True)

/-- The protocol of what an acceptor at `a` writes (for the plain addresses). -/
def protoQ (γ : SwiftNames netDistGF) (a : GoString) : Proto netDistGF :=
  match clientConfAddrs.idxOf? a with
  | some c => conf.ackQP γ (sp.PNode.cl c)
  | none =>
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

/-- The services of each rpc address: the master's (`"Master"` at `masterAddr`) and each
replica node's (`"Replica"` at its rpc port). The method specs are the SwiftPaxos slot's
(`sp.masterSpec`, `sp.replicaRpcSpec`, over the codec's encodings, `Spec/swift/Inv.lean`). -/
def services (γconf γmem : GName) :
    GoString → GoString → Option (net.rpc.MethodSpec netDistGF) := fun a svc =>
  if a = masterAddr ∧ svc = go!"Master" then some (sp.masterSpec γconf γmem)
  else if a ∈ replicaRpcAddrs ∧ svc = go!"Replica" then some (sp.replicaRpcSpec γconf γmem)
  else none

end services

/-! ## The shares -/

section shares
variable [GoGlobalContext] [G : GooseGlobalGS .hasLC netDistGF] [π : NetProtoGS]

/-- What every node gets: every address's protocols (persistent) and the shared invariants. -/
def common (γ : SwiftNames netDistGF) : IProp netDistGF :=
  iprop(([∗list] a ∈ plainAddrs, addrProtoG netDistGS a (protoP γ a) (protoQ γ a)) ∗
    ⌜γ.W.SS = services γ.conf γ.mem⌝ ∗
    ([∗list] a ∈ rpcAddrs, net.rpc.rpcAddr (GF := netDistGF) γ.W a) ∗
    sp.inv γ.sp γ.conf γ.mem γ.lin)

/-- The orchestrator's share (node 0): its address's token, the configuration's writer token
and the abstract state's half at the model's initial state (`New` returns it as `own_state`). -/
def orchShare (γ : SwiftNames netDistGF) : IProp netDistGF :=
  iprop(addrTokG netDistGS orchAddr ∗ conf.writer γ ∗ lin.own γ (kv GoString GoString).init ∗
    common γ)

/-- Client node `c`'s share (node `1 + c`): its own address's and configuration port's tokens,
client `c`'s share of the protocol (`sp.clientStart`: the client id `c + 1`) and the node's
right to register its prediction (L2). -/
def clientNodeShare (γ : SwiftNames netDistGF) (c : Nat) : IProp netDistGF :=
  iprop(addrTokG netDistGS (clientNodeAddrs.getD c go!"") ∗
    addrTokG netDistGS (clientConfAddrs.getD c go!"") ∗ sp.clientStart γ.sp c ∗
    sp.predTok γ.sp (sp.PNode.cl c) ∗ common γ)

/-- Server node `i + 1`'s share (node `7 + i`): its addresses' tokens (`nodeAddrs[7 + i]`), and
the master's (server node 1) the membership's writer token; a replica node's (server node
`k + 2`) its protocol share. -/
def serverShare (γ : SwiftNames netDistGF) (i : Nat) : IProp netDistGF :=
  iprop(([∗list] a ∈ nodeAddrs.getD (7 + i) [], addrTokG netDistGS a) ∗
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

/-- The start: from the network's start resources of every address but the client nodes'
request addresses, the run's ghost names and the shares. -/
def StartOk [G : GooseGlobalGS .hasLC netDistGF] : Prop :=
  ⊢ ([∗list] a ∈ swiftNetCfg.addrs.filter (fun a => a ∉ kit.reqAddrs),
        addrTokG netDistGS a ∗ addrUnsetG netDistGS a) ={⊤}=∗
    ∃ γ : SwiftNames netDistGF, orchShare γ ∗
      ([∗list] c ↦ _nd ∈ clientNodes, clientNodeShare γ c) ∗
      [∗list] i ↦ _nd ∈ serverNodes, serverShare γ i

/-- The orchestrator's spec at node 0, from its share. -/
def OrchOk (S : SwiftNetPkgStates) [G : GooseGlobalGS .hasLC netDistGF] : Prop :=
  ∀ (γ : SwiftNames netDistGF) (hG : HeapGS .hasLC netDistGF) (s : go.Semantics),
    hG.goose_globalGS = G →
    @Node.Assumptions _ orchNode hG.goose_localGS.goose_go_local_context s.sem_fn →
    ∀ (ip : IPv4), swiftNetCfg.ips[0]? = some ip →
      netIp (L := hG.goose_localGS) (GF := netDistGF) = ip.spell →
    Nonempty (@OrchSpec _ _ _ _ netDistGF hG s (kv GoString GoString) kit
      (@kit_isPkgInit _ netDistGF hG s (@S netDistGF hG s))
      (@kit_get_isPkgInit_wf _ netDistGF hG s (@S netDistGF hG s)) (ownState γ) (orchShare γ))

/-- Client node `c`'s spec, from its share. -/
def ClientNodeOk (S : SwiftNetPkgStates) [G : GooseGlobalGS .hasLC netDistGF] : Type 1 :=
  ∀ (γ : SwiftNames netDistGF) (c : Nat) (nd : Node) (hG : HeapGS .hasLC netDistGF)
    (s : go.Semantics), clientNodes[c]? = some nd →
    hG.goose_globalGS = G →
    @Node.Assumptions _ nd hG.goose_localGS.goose_go_local_context s.sem_fn →
    ∀ (ip : IPv4), swiftNetCfg.ips[1 + c]? = some ip →
      netIp (L := hG.goose_localGS) (GF := netDistGF) = ip.spell →
    @ClientNodeSpec _ _ _ _ netDistGF hG s (kv GoString GoString) kit
      (@kit_isPkgInit _ netDistGF hG s (@S netDistGF hG s))
      (@kit_get_isPkgInit_wf _ netDistGF hG s (@S netDistGF hG s)) (ownState γ)
      (W64 (c : Int)) (clientNodeShare γ c)

/-- Each server node's boot program, from its share. -/
def ServersOk [G : GooseGlobalGS .hasLC netDistGF] : Prop :=
  ∀ (γ : SwiftNames netDistGF) (i : Nat) (nd : Node) (ip : IPv4), serverNodes[i]? = some nd →
    swiftNetCfg.ips[1 + clientNodes.length + i]? = some ip →
    NodeBootWpAt (G := G) nd ip (serverShare γ i)

end parts

end Perennial.github_com.imdea_software.swiftpaxos

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

instance ownState_timeless [GoGlobalContext] [GooseGlobalGS .hasLC netDistGF]
    (γ : SwiftNames netDistGF) (σ : (kv GoString GoString).State) : Timeless (ownState γ σ) := by
  unfold ownState lin.own linOwn; infer_instance

/-- `goal_spec` from its parts (plumbing only). -/
theorem goal_spec_of [GoGlobalContext] (S : SwiftNetPkgStates)
    (hstart : ∀ [GooseGlobalGS .hasLC netDistGF], StartOk)
    (horch : ∀ [GooseGlobalGS .hasLC netDistGF], OrchOk S)
    (hclient : ∀ [GooseGlobalGS .hasLC netDistGF], ClientNodeOk S)
    (hservers : ∀ [GooseGlobalGS .hasLC netDistGF], ServersOk) : SwiftNetSpecHolds := by
  refine ⟨S, ?_⟩
  intro G
  constructor
  refine dsverify_lab.harness.RemoteDistSpec.mk (pkgInst := _) (pkgWf := _) (SwiftNames netDistGF)
    ownState (fun γ σ => ownState_timeless γ σ) orchShare clientNodeShare serverShare ?_ ?_ ?_ ?_
  · exact hstart
  · intro γ hG s hG' hA ip hip hnet
    exact Classical.choice (horch γ hG s hG' hA ip hip hnet)
  · exact hclient
  · exact hservers

end Perennial.github_com.imdea_software.swiftpaxos
