/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/nextConfiguration.lean (241f27e).
-/
/-
`raft.nextConfiguration`'s spec (stage 4 interface).
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

/-- `nextConfiguration(current, currentIndex, change)` (stage 4), on a valid configuration `ss` and a
request in scope (`cfgReqOk`): a fresh configuration `ss'` (owned) that is valid and whose voters are
`ss`'s or differ by the request's server (`adjV`: the four changes add or remove at most one voter;
`AddNonvoter` of a voter keeps its vote), and `nil`; or an error (`errOk`): `prevIndex ≠ 0` other
than `currentIndex`, or `checkConfiguration` refusing a configuration with no voter left (formatted
with `%v` of the configuration: Design question I2-2). -/
abbrev github_com.hashicorp.raft.nextConfiguration.spec : Prop :=
  ∀ (γ : GNames) (c : Configuration) (ss : List Server) (dq : DFrac) (ci : w64)
    (rq : configurationChangeRequest),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ c.Servers' ↦*{dq} ss ∗ ⌜srvsOk γ ss ∧ cfgReqOk γ rq⌝ }}
    (App (App (App (Val (@! github_com.hashicorp.raft.nextConfiguration)) (Val #c)) (Val #ci)) (Val #rq))
  {{ (c' : Configuration) (err : GoInterface), RET (PairV #c' #err); c.Servers' ↦*{dq} ss ∗
      ((⌜err = interface.nil⌝ ∗ ∃ ss' : List Server, c'.Servers' ↦* ss' ∗
         ⌜srvsOk γ ss' ∧ adjV (srvVoters ss) (srvVoters ss')⌝) ∨
       (errOk err ∗ ⌜∃ x : Loc, err = interface.mkOk (go.GoType.PointerType errors.errorString.ty) #x⌝)) }}

end spec

end Perennial
