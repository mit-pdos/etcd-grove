/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/Shares.lean (run gryff-bump-1, lab
master 915f964; notes/dsv-gryff.md), redesigned for `Net/` and `examples/lib/remote`.

The nodes' shares of the start, and the slots they are made of. Every slot is sealed: its body is
its subsystem's (`Proto`, `Server`, `Client`), and the hub names only the slot.

Port (`Net/` + remote):
* The lab's per-address protocols (`addrP`, `addrQ`), the start's address lists (`ourAddrs`,
  `ourNodeAddrs`) and the address tokens of `netShare` are gone. The start sets, once, the
  protocols of every **listener address** (all the kit's servers listen at wildcards): a replica
  port `portAddr k`'s at `lisAddrOf (portAddr k)` (`":750(2+k)"`), Gryff's wire protocols
  (`replicaLis`, `lis_set_proto`); the master's and the replicas' net/rpc listeners
  (`masterRpcLis`, `replicaRpcLis k`) the rpc world's behind net/rpc's HTTP handshake
  (`RpcHttpAddr.rpcLisP`, `rpcLisP_set`). Those facts are persistent: `netShare γ` holds them all,
  for every node.
* `sharedInvs γ`: Gryff's and the placers' invariants (`protoInvs`) and the rpc world's registry.
* The lab's `orchNodeShare` (the client's half of the abstract register) is gone: under remote it
  is the far side's store's state (`Kit.lean`'s `casR`, `sysState := regHalf`), which remote's
  pending library holds from the start.
-/
module

public import Dsverify.Proof.gryff.Names
public import Dsverify.Proof.gryff.Proto.Inv
public import Dsverify.Proof.gryff.Proto.Wire
public import Dsverify.Proof.gryff.Proto.ClientLaws
public import Dsverify.Proof.gryff.Proto2.InvDefs
public import Dsverify.Proof.gryff.Server.Deploy
public import Dsverify.Proof.gryff.Rpc.RpcHttpHyps

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

attribute [local instance] GooseGlobalGS.gooseInvGS

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [G : GooseGlobalGS .hasLC GF] [π : NetProtoGS]

/-- Gryff's invariant: stage 2's (`Proto2/InvDefs.lean`). -/
def gryffInv (γ : GryffNames GF) : IProp GF := gryffInv2 γ.proto

/-- The invariants every node shares (persistent): Gryff's and the placers' (`protoInvs`), and
the rpc world's registry. -/
def sharedInvs (γ : GryffNames GF) : IProp GF :=
  iprop(protoInvs γ ∗ inv net.rpc.regN' (net.rpc.regInv γ.rpc))

instance sharedInvs_persistent (γ : GryffNames GF) : Persistent (sharedInvs γ) := by
  unfold sharedInvs; infer_instance

theorem sharedInvs_proto (γ : GryffNames GF) : sharedInvs γ ⊢ protoInvs γ := by
  unfold sharedInvs; iintro ⟨H, -⟩; iexact H

/-- Replica port `k`'s listener protocols (persistent): every address the wildcard
`lisAddrOf (portAddr k)` takes has Gryff's wire protocols of `portAddr k`. -/
def replicaLis (γ : GryffNames GF) (k : Nat) : IProp GF :=
  lisProto (lisAddrOf (portAddr k)) (gryffWireP γ (portAddr k)) (gryffWireQ γ (portAddr k))

instance replicaLis_persistent (γ : GryffNames GF) (k : Nat) :
    Persistent (replicaLis γ k) := by
  unfold replicaLis; infer_instance

/-- Gryff client id of client `c`'s `g`-th connection (kit.go's `c + NC * gen`). -/
def gid (c g : Nat) : w32 := W32 (c + 6 * g)

/-- The ids and turns of client `c`'s connection generations `g`, `gen ≤ g < 5` (unused). -/
def unusedIds (γ : GryffNames GF) (c gen : Nat) : IProp GF :=
  [∗list] g ∈ List.range' gen (5 - gen),
    iprop(idTok γ (gid c g) ∗ turnTok (GF := GF) γ.proto (c + 6 * g) 0)

/-- Client node `c`'s start resources: the id and turn tokens of the Gryff client ids
`c + 6 g` (`g < 5`) its client may use and its 4 budget units (D14; kit.go's `Op` answers at most
`K = 4` operations). -/
def clientStartRes (γ : GryffNames GF) (c : Nat) : IProp GF :=
  iprop(unusedIds γ c 0 ∗ budget (GF := GF) γ.proto 4)

@[irreducible] def masterStartRes (_γ : GryffNames GF) : IProp GF :=
  deployStartDef _γ
@[irreducible] def replicaStartRes (_γ : GryffNames GF) (_k : Nat) : IProp GF :=
  deployRegResDef _γ _k

/-- Replica node `k`'s boot resources (D13): its prediction token (`pred_set`, at its boot,
after the gryff package's initialization created its prophecy) and its claim of its replica
id's start resources (`deploy_claim`, after registration). -/
def replicaBootRes (γ : GryffNames GF) (k : Nat) : IProp GF :=
  iprop(predTok (GF := GF) γ.proto k ∗ slotClaimTok (GF := GF) γ.proto k)

end ghost

section net
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [G : GooseGlobalGS .hasLC GF] [π : NetProtoGS] [RA : RpcHttpAddr GF]

/-- The rpc listeners' protocols (persistent): the master's and each replica's net/rpc listener
serve the rpc world behind net/rpc's HTTP handshake. -/
def rpcLises (γ : GryffNames GF) : IProp GF :=
  iprop(RA.rpcLisP γ.rpc masterRpcLis (net.rpc.connectReq net.rpc.defaultRPCPath)
      net.rpc.connectAns ∗
    [∗list] k ∈ [0, 1, 2], RA.rpcLisP γ.rpc (replicaRpcLis k)
      (net.rpc.connectReq net.rpc.defaultRPCPath) net.rpc.connectAns)

instance rpcLises_persistent (γ : GryffNames GF) : Persistent (rpcLises γ) := by
  unfold rpcLises; infer_instance

/-- Every node's network share (persistent): the listeners' protocols the start set. -/
def netShare (γ : GryffNames GF) : IProp GF :=
  iprop(([∗list] k ∈ [0, 1, 2], replicaLis γ k) ∗ rpcLises γ)

instance netShare_persistent (γ : GryffNames GF) : Persistent (netShare γ) := by
  unfold netShare; infer_instance

/-- Client node `c`'s share. -/
def clientNodeShare (γ : GryffNames GF) (c : Nat) : IProp GF :=
  iprop(netShare γ ∗ □ sharedInvs γ ∗ clientStartRes γ c)

/-- Server node `i`'s share: server node 0 is the master, server nodes 1..3 the replicas. -/
def serverShare (γ : GryffNames GF) (i : Nat) : IProp GF :=
  iprop(netShare γ ∗ □ sharedInvs γ ∗
    (if i = 0 then masterStartRes γ else replicaStartRes γ (i - 1) ∗ replicaBootRes γ (i - 1)))

end net

end Perennial.gryff
