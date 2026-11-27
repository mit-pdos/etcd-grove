/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/overrideNotifyBool.lean (241f27e).
-/
/-
`raft.overrideNotifyBool`'s spec (raft-internal interface, notes/raft-iface.md). On a 1-buffered channel owned by the caller alone (`leaderCh`): afterwards it holds exactly `v` (so the `panic` is unreachable).
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

/-- `overrideNotifyBool`: On a 1-buffered channel owned by the caller alone (`leaderCh`): afterwards it holds exactly `v` (so the `panic` is unreachable). -/
abbrev github_com.hashicorp.raft.overrideNotifyBool.spec : Prop :=
  ∀ (γc : ChanNames) (ch : Loc) (bs : List Bool) (v : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ isChan ch γc Bool ∗ ownChan γc Bool (.Buffered bs) ∗
     ⌜sint.Z γc.chanCap = 1 ∧ bs.length ≤ 1⌝ }}
    (App (App (Val (@! github_com.hashicorp.raft.overrideNotifyBool)) (Val #ch)) (Val #v))
  {{ RET #(); ownChan γc Bool (.Buffered [v]) }}

end spec

end Perennial
