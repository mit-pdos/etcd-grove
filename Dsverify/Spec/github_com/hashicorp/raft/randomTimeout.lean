/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/randomTimeout.lean (241f27e).
-/
/-
`raft.randomTimeout`'s spec (raft-internal interface, notes/raft-iface.md). A timer channel (`time.After`), or `nil` for a zero duration (a receive on it never fires).
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

/-- `randomTimeout`: A timer channel (`time.After`), or `nil` for a zero duration (a receive on it never fires). -/
abbrev github_com.hashicorp.raft.randomTimeout.spec : Prop :=
  ∀ (d : time.Duration),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft }}
    (App (Val (@! github_com.hashicorp.raft.randomTimeout)) (Val #d))
  {{ (ch : Loc), RET #ch; ⌜ch = chan.nil⌝ ∨
      ∃ γc : ChanNames, isChanBag (V := time.Time) γc ch (fun _ => iprop(True)) }}

end spec

end Perennial
