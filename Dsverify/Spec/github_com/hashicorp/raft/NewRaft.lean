/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/NewRaft.lean (241f27e).
-/
/-
`raft.NewRaft`'s spec (raft-internal interface, notes/raft-iface.md). Builds server `i` of protocol `γ` from its bootstrapped stores (log `[g]`, current term 1, no vote), the contracts of the interface values and the server's protocol bundle; starts `run`, `runFSM`, `runSnapshots` (each through `goFunc`); returns `r` with `isRaft` and no error.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.core.Laws

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std
open github_com.hashicorp.raft github_com.hashicorp.raft.gprot github_com.hashicorp.raft.proto

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]

/-- `NewRaft`: Builds server `i` of protocol `γ` from its stores (stage 4: a bootstrap voter's, `i ∈ γ.cv γ.g.data`: log `[g]`, current term 1, no vote; any other server's empty, as a non-member, term 0: `proto.initSrv`; stage 3: every server bootstrapped), the contracts of the interface values and the server's protocol bundle; starts `run`, `runFSM`, `runSnapshots` (each through `goFunc`); returns `r` with `isRaft` and no error. Needs the thread bound `2 ^ 28` (its `RWMutex` thread pools, as `NewInmemStore`). (Stage 3) The log store over a partial map (`LogAbs`, holding the genesis), not a `MonotonicLogStore`; an empty snapshot store (`isSnapStore`, `snapstore`'s); the FSM's and the transport's snapshot meaning `snapP`. (Stage 4) The protocol's decoding of a
configuration's voters is `DecodeConfiguration`'s (`γ.cv = cfgDec γ.srvs`; `isRaft` keeps it); the genesis
encodes a valid configuration. -/
abbrev github_com.hashicorp.raft.NewRaft.spec : Prop :=
  ThreadBoundLe GF (2 ^ 28) →
  ∀ (Wl : LogOp → IProp GF) (Ws : StableOp → IProp GF) (Qc : SnapshotMeta → List w8 → IProp GF) (cp : Loc) (c : Config) (fsmI logsI stableI snapsI transI : GoInterfaceOk) (rpcCh : Loc)
    (γ : GNames) (i : SID) (ownL : LogAbs → IProp GF) (ownS : StableAbs → IProp GF)
    (ownSS : SnapLatest → IProp GF) (eof : GoInterface) (snapP : Nat → List w8 → IProp GF)
    (fsmOwn : Nat → IProp GF) (respP : Nat → GoInterface → IProp GF) (sst : StableAbs) (tid : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ cp ↦ c ∗ ⌜cfgOk c i⌝ ∗
     isFSM fsmI γ i fsmOwn respP snapP ∗ ⌜fsmNotBatching fsmI⌝ ∗
     isLogStore logsI ownL Wl ∗ ⌜go.typeSetContains logsI.ty MonotonicLogStore.ty = false⌝ ∗
     isStableStore stableI ownS Ws ∗ isSnapStore snapsI ownSS eof Qc ∗ globalAddr io.EOF ↦□ eof ∗
     isTransport transI γ snapP i rpcCh ∗ ⌜go.typeSetContains transI.ty WithPreVote.ty = true⌝ ∗
     ownL (LogAbs.empty.store 1 (initSrv γ.cv γ.g i).log) ∗ ownS sst ∗ ownSS none ∗
     ⌜sst.ints.lookup (go!"CurrentTerm" : List w8) =
         (if i ∈ γ.cv γ.g.data then some (W64 1) else none) ∧
       sst.ints.lookup (go!"LastVoteTerm" : List w8) = none⌝ ∗
     Inv γ ∗ isSrv γ i ∗ srvOwn γ i (initSrv γ.cv γ.g i) ∗ termCouple γ i (initSrv γ.cv γ.g i).term ∗
     logCouple γ i (initSrv γ.cv γ.g i).log ∗ cidxCouple γ i 0 ∗ durView γ i (1 : Qp).half 0 ∗
     ⌜γ.cv = cfgDec γ.srvs ∧ ∃ ss, srvsOk γ ss ∧ γ.g = genesisOf ss⌝ ∗ fsmOwn 0 ∗ rtok tid }}
    (App (App (App (App (App (App (Val (@! github_com.hashicorp.raft.NewRaft)) (Val #cp)) (Val #(GoInterface.ok fsmI))) (Val #(GoInterface.ok logsI))) (Val #(GoInterface.ok stableI))) (Val #(GoInterface.ok snapsI))) (Val #(GoInterface.ok transI)))
  {{ (r : Loc), RET (PairV #r #interface.nil);
      (∃ (names : RNames) (dn : DurNames), isRaft r γ (RCtx.mk ownL ownSS snapP ownS fsmOwn respP names dn) i) ∗ cp ↦ c ∗
      rtok tid }}

end spec

end Perennial
