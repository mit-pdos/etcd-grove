/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/fsmRestoreAndMeasure.lean (241f27e).
-/
/-
``getSnapshotVersion(v)``'s spec (stage 3, raft-internal, snap: package-internal).
-/
module

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

/-- `fsmRestoreAndMeasure(fsm, source, size)`: the FSM's `Restore` from a counting wrapper of
`source` (a reader that never fails of a snapshot `b` of `s`, past the FSM's last command), with a
restore monitor: returns nil with the FSM's state the snapshot's (`isFSM`'s `Restore`). -/
abbrev github_com.hashicorp.raft.fsmRestoreAndMeasure.spec : Prop :=
  ∀ (fx : GoInterfaceOk) (γ : GNames) (i : SID) (fsmOwn : Nat → IProp GF)
    (respP : Nat → GoInterface → IProp GF) (snapP : Nat → List w8 → IProp GF) (k0 s : Nat)
    (rd : GoInterfaceOk) (R : List w8 → IProp GF) (b : List w8) (eof : GoInterface) (size : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗
     isFSM fx γ i fsmOwn respP snapP ∗ fsmOwn k0 ∗ ⌜k0 ≤ s⌝ ∗ globalAddr io.EOF ↦□ eof ∗
     readCloserOk rd R eof ∗ R b ∗ snapP s b }}
    (App (App (App (Val (@! github_com.hashicorp.raft.fsmRestoreAndMeasure)) (Val #(GoInterface.ok fx)))
      (Val #(GoInterface.ok rd))) (Val #size))
  {{ RET #interface.nil; ∃ (k0' : Nat) (r : GoInterface), fsmOwn k0' ∗ ⌜k0' ≤ s⌝ ∗
      noCmdBetween γ k0' (s + 1) ∗ (⌜k0' = 0⌝ ∨ respP k0' r) }}

end spec

end Perennial
