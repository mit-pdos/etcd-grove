/-
Ported from dsverify-lab examples/swiftpaxos/proof/Spec/master/Defs.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The master between `master.New` and `Master.Run` (the master group owns the body): its struct,
fresh, with the membership's writer token and the configuration it was built for.
-/
module

public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.swift.Inv
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.dlog.Defs
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.config.Defs
public import Perennial.Proof.sync.CondDefs

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section spec
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]

/-- The body of `master.created` (the master group's; change log C7): the struct (`N` and
`port`, no replica registered, not initialized, no next leader), a quiet logger, the
configuration (with `N` replicas), the membership's writer token (the master fixes the membership
when the `N`-th replica registers), the slices' contents, the plain configuration, the mutex
(unused yet) and the condition variable on it. -/
def master.createdBody (m : Loc) (γc γm : GName) (N : Nat) (port : w64) : IProp netDistGF :=
  iprop(∃ (v : master.Master) (c : Conf) (fr : Bool), m ↦ v ∗ dlog.quiet v.Logger' ∗
    confIs γc c ∗ monoListAuthOwn (A := List GoString) γm 1 [] ∗
    v.nodeList' ↦* ([] : List GoString) ∗ v.addrList' ↦* ([] : List GoString) ∗
    v.portList' ↦* ([] : List w64) ∗
    ownSliceCap GoString v.nodeList' (DFrac.own 1) ∗ ownSliceCap GoString v.addrList' (DFrac.own 1) ∗
    ownSliceCap w64 v.portList' (DFrac.own 1) ∗
    v.nodes' ↦* List.replicate N null ∗ v.leader' ↦* List.replicate N false ∗
    v.alive' ↦* List.replicate N false ∗ v.latencies' ↦* List.replicate N (W64 0) ∗
    config.plain v.config' fr ∗ v.lock' ↦ (zero_val sync.Mutex) ∗
    sync.isCond v.initCond' (interface.mk (go.GoType.PointerType sync.Mutex.ty) #v.lock') ∗
    ⌜c.n = N ∧ v.N' = W64 N ∧ v.port' = port ∧ v.finishInit' = false ∧ v.nextLeader' = W64 (-1) ∧
      v.nodeList'.cap = W64 N ∧ v.addrList'.cap = W64 N ∧ v.portList'.cap = W64 N ∧
      v.lock' ≠ null⌝)

/-- `master.New(N, port, conf, lg)`'s result, before `Run` (sealed, change log C7: its body is
the master group's, `master.createdBody`; clients pass it from `New` to `Run`). -/
@[no_expose] def master.created (m : Loc) (γc γm : GName) (N : Nat) (port : w64) :
    IProp netDistGF :=
  master.createdBody m γc γm N port

/-- The seal's law (the master group's proofs only). -/
theorem master.created_eq (m : Loc) (γc γm : GName) (N : Nat) (port : w64) :
    master.created m γc γm N port = master.createdBody m γc γm N port := by
  unfold master.created; rfl

end spec

end Perennial.github_com.imdea_software.swiftpaxos
