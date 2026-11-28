/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/Raft__compactLogs.lean (241f27e).
-/
/-
`raft.(*Raft).compactLogs`'s spec (stage 3, raft-internal: called by the snapshot goroutine's `takeSnapshot` and the main goroutine's `installSnapshot`).
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

/-- `(*Raft).compactLogs(x)`: deletes from the log store the entries from its first index up to at
most `x` (keeping `TrailingLogs` entries behind the last one, `lastLog`), where `x` is at most the
compaction frontier (`compLb rc x`: the log cell lets the store lose the entries `1..x`); returns nil
(the store's `FirstIndex` and `DeleteRange` never fail). -/
abbrev github_com.hashicorp.raft.Raft.compactLogs.spec : Prop :=
  ∀ (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (x : w64) (tid : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ isRaft r γ rc i ∗
     compLb rc (uint.nat x) ∗ latLb rc (uint.nat x) ∗ ⌜uint.nat x < 2 ^ 62⌝ ∗ rtok tid }}
    (App (Val (r @!! go.GoType.PointerType Raft.ty @!! go!"compactLogs")) (Val #x))
  {{ (err : GoInterface), RET #err; ⌜err = interface.nil⌝ ∗ rtok tid }}

end spec

end Perennial
