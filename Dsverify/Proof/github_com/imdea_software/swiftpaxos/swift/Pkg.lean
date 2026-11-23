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
  C14) are in no package state: every node's boot thread owns them at their initial values
  (`swift.mutGlobalsInit`: `100`, `false`, `32`), from the initialization. A replica node gives
  them to the adapter's store and to `swift.New` (a Go store is not atomic in Perennial: it needs
  the exclusive points-to); the client node persists `useFastAckPool ↦□ false`
  (`swift.mutGlobalsInit_poolOff`; the client's handler reads it, C6).
  **Port change** (notes/dsv-swiftpaxos.md): the lab kept them in the package state off a replica
  node, told apart by the node's IP (its harness's `netIp`); here every node is on loopback and
  `Net/` has no node IP, so the package state is the same on every node and the boot thread
  holds them everywhere.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Base
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.Base
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

/-- The mutable globals, owned (change log C14; see the file header). -/
def swift.mutGlobals : IProp GF :=
  iprop(∃ (d : w64) (v : Bool) (n : w64), globalAddr swift.MaxDescRoutines ↦ d ∗
    globalAddr swift.useFastAckPool ↦ v ∗
    typedPointsto (globalAddr _root_.Perennial.github_com.orcaman.concurrent_map.SHARD_COUNT) n
      (DFrac.own 1))

/-- The mutable globals at their initial values (`MaxDescRoutines = 100`, `useFastAckPool =
false`, `SHARD_COUNT = 32`), owned: what every node's boot thread gets from the initialization. -/
def swift.mutGlobalsInit : IProp GF :=
  iprop(globalAddr swift.MaxDescRoutines ↦ (W64 100) ∗ globalAddr swift.useFastAckPool ↦ false ∗
    typedPointsto (globalAddr _root_.Perennial.github_com.orcaman.concurrent_map.SHARD_COUNT)
      (W64 32) (DFrac.own 1))

theorem swift.mutGlobalsInit_mutGlobals : swift.mutGlobalsInit (GF := GF) ⊢ swift.mutGlobals := by
  unfold swift.mutGlobalsInit swift.mutGlobals
  iintro ⟨H1, H2, H3⟩
  iexists _, _, _
  iframe

-- `swift.fastAckP` and `swift.pkgSt` (swift's package fact) are defined in `swift/Base.lean`.

instance swift.pkgSt_persistent : Persistent (swift.pkgSt (GF := GF)) := by
  unfold swift.pkgSt; infer_instance

/-- `concurrent-map`'s package state: nothing (`SHARD_COUNT` is the boot thread's,
`swift.mutGlobalsInit`). -/
def cmap.pkgSt : IProp GF := iprop(True)

instance cmap.pkgSt_persistent : Persistent (cmap.pkgSt (GF := GF)) := by
  unfold cmap.pkgSt; infer_instance

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
  iintro ⟨-, -, -, ⟨%x, #Hx, -⟩, -⟩
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

/-- The client node's boot thread makes the fast-ack pool off for good (C6). -/
theorem swift.mutGlobalsInit_poolOff :
    swift.mutGlobalsInit (GF := GF) ⊢ |==> globalAddr swift.useFastAckPool ↦□ false := by
  unfold swift.mutGlobalsInit
  iintro ⟨-, H, -⟩
  ipersist H
  iexact H

end defs

end Perennial.github_com.imdea_software.swiftpaxos
