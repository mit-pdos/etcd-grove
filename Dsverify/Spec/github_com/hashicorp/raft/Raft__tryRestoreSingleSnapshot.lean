/-
(hraft_robust R5) New: restoreSnapshot restores a recovered latest snapshot.
-/
/-
`raft.(*Raft).tryRestoreSingleSnapshot`'s spec (API-internal, hraft_robust R5): restores the store's latest snapshot into the FSM.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.core.Laws
public import Dsverify.Proof.github_com.hashicorp.raft.SnapDefs

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

/-- `(*Raft).tryRestoreSingleSnapshot(mp)` (`NewRaft`'s restore, hraft_robust R5): with snapshot restore at
start on (`NoSnapshotRestoreOnStart = false`, the configuration read from `r.conf`), opens the snapshot
`*mp = m` in the store, whose latest is `(m, b)` (the caller's accessor `P`: an atomic read of the store's
state, given back), restores the FSM from it (`fsmRestoreAndMeasure`, `b` a snapshot of `m`'s index past the
FSM's position) and closes the reader; returns true. -/
abbrev github_com.hashicorp.raft.Raft.tryRestoreSingleSnapshot.spec : Prop :=
  ∀ (r : Loc) (c : Config) (x fx : GoInterfaceOk) (own : SnapLatest → IProp GF) (eof : GoInterface)
    (Qc : SnapshotMeta → List w8 → IProp GF) (γ : GNames) (i : SID) (fsmOwn : Nat → IProp GF)
    (respP : Nat → GoInterface → IProp GF) (snapP : Nat → List w8 → IProp GF) (mp : Loc)
    (m : SnapshotMeta) (b : List w8) (P : IProp GF) (k0 : Nat) (tid : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗
     sync.atomic.ownValue (r.[Raft, go!"conf"]) DFrac.discard (interface.mkOk Config.ty #c) ∗
     ⌜c.NoSnapshotRestoreOnStart' = false⌝ ∗
     r.[Raft, go!"snapshots"] ↦□ (GoInterface.ok x) ∗ isSnapStore x own eof Qc ∗ globalAddr io.EOF ↦□ eof ∗
     r.[Raft, go!"fsm"] ↦□ (GoInterface.ok fx) ∗ isFSM fx γ i fsmOwn respP snapP ∗
     mp ↦ m ∗ P ∗
     (P -∗ |NC={⊤ \ ↑storeN, ∅}=> ▷ ∃ old, own old ∗ ⌜old = some (m, b)⌝ ∗
        (own old ={∅, ⊤ \ ↑storeN}=∗ P)) ∗
     snapP (uint.nat m.Index') b ∗ fsmOwn k0 ∗ ⌜k0 ≤ uint.nat m.Index'⌝ ∗ rtok tid }}
    (App (Val (r @!! go.GoType.PointerType Raft.ty @!! go!"tryRestoreSingleSnapshot")) (Val #mp))
  {{ RET #true; mp ↦ m ∗ P ∗ rtok tid ∗
      ∃ (k0' : Nat) (res : GoInterface), fsmOwn k0' ∗ ⌜k0' ≤ uint.nat m.Index'⌝ ∗
        noCmdBetween γ k0' (uint.nat m.Index' + 1) ∗ (⌜k0' = 0⌝ ∨ respP k0' res) }}

end spec

end Perennial
