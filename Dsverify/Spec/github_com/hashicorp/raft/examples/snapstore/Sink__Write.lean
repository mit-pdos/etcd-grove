/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/examples/snapstore/Sink__Write.lean (241f27e).
-/
/-
`snapstore.Sink.Write`'s spec (stage 3, package-internal).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.snapstore.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std
open github_com.hashicorp.raft github_com.hashicorp.raft.examples.snapstore

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.snapstore.Assumptions]

/-- `k.Write(p)` on an open sink: appends `p`'s bytes. -/
abbrev github_com.hashicorp.raft.examples.snapstore.Sink.Write.spec : Prop :=
  ∀ (k : Loc) (p : GoSlice) (dq : DFrac) (bs c : List w8),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.snapstore ∗ sinkSt k (some bs) ∗ p ↦*{dq} c }}
      (App (Val (k @!! go.GoType.PointerType Sink.ty @!! go!"Write")) (Val #p))
    {{ RET (PairV #(W64 c.length) #interface.nil); sinkSt k (some (bs ++ c)) ∗ p ↦*{dq} c }}

end spec

end Perennial
