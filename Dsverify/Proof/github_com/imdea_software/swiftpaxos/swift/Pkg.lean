/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/Pkg.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The package-level state of `swift` (the run's choice for `SwiftNetPkgState.swift`, change log
C2, C6, C10) and of the packages whose globals `swift.New` relies on (`concurrent-map`'s
`SHARD_COUNT`, `replica`'s quorum errors, `replica/defs`' `LatencyConf`): what each package's
initialization establishes, and the laws the replica's and the client's proofs use.

* The hooks `ExecHook`, `SyncHook`, `ReplyHook` are `nil` for good (test-only instrumentation;
  nothing in the deployment writes them).
* `errVarintOverflow` is `errors.New(...)`'s error for good (`errors.newVar`).
* `fastAckPool` is a `sync.Pool` of owned `*MFastAck`s.
* The mutable globals `MaxDescRoutines`, `useFastAckPool` and `cmap.SHARD_COUNT` (change log
  C14): on a node whose IP is a replica node's (`swift.replicaNode netIp`) they are not in the
  package state: the node's boot thread owns them (`swift.mutGlobals`, from the server-side
  initialization `swiftnetInitSrv.spec`) and gives them to the adapter's store and to
  `swift.New` (a Go store is not atomic in Perennial: it needs the exclusive points-to). On any
  other node (the client node, the master) they keep their initial values, `100`, `false`, a
  positive `SHARD_COUNT`, for good (the client's handler reads `useFastAckPool ↦□ false`, C6).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Base
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.examples.swiftnet.Base
public import Perennial.Proof.errors.NewVar
public import Perennial.Proof.sync.PoolDefs
public import Dsverify.GeneratedProof.github_com.imdea_software.swiftpaxos.swift
public import Dsverify.GeneratedProof.github_com.orcaman.concurrent_map

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

/-- A replica node's IP: the host of one of the replicas' addresses. -/
def swift.replicaNode (ip : GoString) : Prop := ∃ a ∈ replicaAddrs, ip ++ [W8 58] <+: a

section defs
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]

/-- What `fastAckPool` holds: owned `*MFastAck`s. -/
def swift.fastAckP (x : GoAny) : IProp GF :=
  iprop(∃ (l : Loc) (fa : swift.MFastAck),
    ⌜x = interface.mkOk (go.GoType.PointerType swift.MFastAck.ty) #l⌝ ∗ l ↦ fa)

/-- The mutable globals, owned (change log C14; see the file header). -/
def swift.mutGlobals : IProp GF :=
  iprop(∃ (d : w64) (v : Bool) (n : w64), globalAddr swift.MaxDescRoutines ↦ d ∗
    globalAddr swift.useFastAckPool ↦ v ∗
    typedPointsto (globalAddr _root_.Perennial.github_com.orcaman.concurrent_map.SHARD_COUNT) n
      (DFrac.own 1))

open Classical in
/-- What the boot thread of a node gets from the server-side initialization: on a replica node,
the mutable globals. -/
def swift.mutGlobalsAt (ip : GoString) : IProp GF :=
  if swift.replicaNode ip then swift.mutGlobals else iprop(True)

open Classical in
/-- **swift's package state** (see the file header). -/
def swift.pkgSt : IProp GF :=
  iprop(globalAddr swift.ExecHook ↦□ func.nil ∗ globalAddr swift.SyncHook ↦□ func.nil ∗
    globalAddr swift.ReplyHook ↦□ func.nil ∗
    errors.newVar swift.errVarintOverflow go!"binary: varint overflows a 64-bit integer" ∗
    (∃ f : GoFunc, sync.isPool (globalAddr swift.fastAckPool) f iprop(True) swift.fastAckP ∗ ⌜f ≠ func.nil⌝) ∗
    (if swift.replicaNode (netIp (L := hG.goose_localGS) (GF := GF))
     then iprop(True)
     else globalAddr swift.MaxDescRoutines ↦□ (W64 100) ∗
       globalAddr swift.useFastAckPool ↦□ false))

instance swift.pkgSt_persistent : Persistent (swift.pkgSt (GF := GF)) := by
  unfold swift.pkgSt; split <;> infer_instance

open Classical in
/-- `concurrent-map`'s package state: off a replica node, `SHARD_COUNT` is positive, for good
(`cmap.New` needs `SHARD_COUNT ↦□ n`); on a replica node the boot thread owns it
(`swift.mutGlobals`: `swift.New` stores `32768`, C14). -/
def cmap.pkgSt : IProp GF :=
  if swift.replicaNode (netIp (L := hG.goose_localGS) (GF := GF)) then iprop(True) else
  iprop(∃ n : w64, typedPointsto (globalAddr _root_.Perennial.github_com.orcaman.concurrent_map.SHARD_COUNT) n DFrac.discard ∗
    ⌜0 < sint.Z n⌝)

instance cmap.pkgSt_persistent : Persistent (cmap.pkgSt (GF := GF)) := by
  unfold cmap.pkgSt; split <;> infer_instance

/-- `replica`'s package state: its two `errors.New` errors (`NewQuorumSystem` compares with
them). -/
def replica.pkgSt : IProp GF :=
  iprop(errors.newVar replica.NO_QUORUM_FILE go!"Quorum file is not provided" ∗
    errors.newVar replica.THREE_QUARTERS go!"ThreeQuarters")

instance replica.pkgSt_persistent : Persistent (replica.pkgSt (GF := GF)) := by
  unfold replica.pkgSt; infer_instance

/-- `replica/defs`' package state: no latency file (`LatencyConf = ""`, for good). -/
def defs.pkgSt : IProp GF :=
  iprop(typedPointsto (globalAddr replica.defs.LatencyConf) (go!"" : GoString) DFrac.discard)

instance defs.pkgSt_persistent : Persistent (defs.pkgSt (GF := GF)) := by
  unfold defs.pkgSt; infer_instance

/-! ## Laws -/

/-- The overflow error, as the varint readers take it. -/
theorem swift.pkgSt_errVarint :
    swift.pkgSt (GF := GF) ⊢ ∃ ov : GoInterface,
      typedPointsto (globalAddr swift.errVarintOverflow) ov DFrac.discard ∗
      ⌜ov ≠ interface.nil⌝ := by
  unfold swift.pkgSt errors.newVar
  iintro ⟨-, -, -, ⟨%x, #Hx, -⟩, -, -⟩
  iexists _
  iframe Hx
  ipureintro
  intro h; cases h

/-- The hooks are `nil`. -/
theorem swift.pkgSt_hooks :
    swift.pkgSt (GF := GF) ⊢ globalAddr swift.ExecHook ↦□ func.nil ∗
      globalAddr swift.SyncHook ↦□ func.nil ∗ globalAddr swift.ReplyHook ↦□ func.nil := by
  unfold swift.pkgSt
  iintro ⟨#H1, #H2, #H3, -⟩
  iframe H1 H2 H3

/-- Off a replica node (the client node), the fast-ack pool is off for good (C6). -/
theorem swift.pkgSt_poolOff (ip : GoString) (hip : ¬ swift.replicaNode ip) :
    swift.pkgSt (GF := GF) ∗ nodeIp (L := hG.goose_localGS) (GF := GF) ip ⊢
      globalAddr swift.useFastAckPool ↦□ false := by
  unfold swift.pkgSt
  iintro ⟨⟨-, -, -, -, -, H⟩, %Hip⟩
  rw [Hip, if_neg hip]
  icases H with ⟨-, #H⟩
  iexact H

/-- The client node is not a replica node. -/
theorem swift.clientIp_not_replicaNode : ¬ swift.replicaNode go!"10.77.0.10" := by
  unfold swift.replicaNode
  decide

end defs

end Perennial.github_com.imdea_software.swiftpaxos
