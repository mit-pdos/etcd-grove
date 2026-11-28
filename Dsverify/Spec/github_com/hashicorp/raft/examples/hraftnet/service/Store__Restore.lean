/-
`service.Store.Restore`'s spec (the hraft kit's state machine, notes/dsv-hraft.md, S5).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.service.FsmDefs

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.hraftnet.service.Assumptions]

open github_com.hashicorp.raft.examples.hraftnet.service github_com.hashicorp.raft
  github_com.hashicorp.raft.proto github_com.hashicorp.raft.gprot

/-- `s.Restore(rd)`: from a reader that never fails of a snapshot `b` of `x` (past the FSM's last
command `k0`), no panic: the store's state becomes the snapshot's. -/
abbrev github_com.hashicorp.raft.examples.hraftnet.service.Store.Restore.spec : Prop :=
  ∀ (γ : GNames) (fc : FCtx GF) (alb : GName) (i : SID) (s : Loc) (k0 x : Nat) (rd : GoInterfaceOk)
    (R : List w8 → IProp GF) (b : List w8) (eof : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.service ∗
      isStore γ fc alb i s ∗ fsmOwn alb k0 ∗ ⌜k0 ≤ x⌝ ∗ globalAddr io.EOF ↦□ eof ∗
      readCloserOk rd R eof ∗ R b ∗ snapP γ fc x b }}
    (App (Val (s @!! go.GoType.PointerType Store.ty @!! go!"Restore")) (Val #(GoInterface.ok rd)))
  {{ RET #interface.nil; ∃ (k0' : Nat) (r : GoInterface), fsmOwn alb k0' ∗ ⌜k0' ≤ x⌝ ∗
      noCmdBetween γ k0' (x + 1) ∗ (⌜k0' = 0⌝ ∨ respP γ fc alb k0' r) }}

end spec

end Perennial
