/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/Raft__persistVote.lean (241f27e).
-/
/-
`raft.(*Raft).persistVote`'s spec (raft-internal interface, notes/raft-iface.md). Writes the vote to the stable store (whose writes never fail). (hraft_robust L0, R1 §2.4) Writes `LastVoteCand` first, then `LastVoteTerm`, where the vote step (`grantVote_upd`) fires, at the second write's commit point: the caller lends its view `srvV` and the candidate's `candIs`, and gets the vote back.
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

/-- `(*Raft).persistVote`: Writes the vote to the stable store (whose writes never fail). (hraft_robust L0, R1 §2.4) Writes `LastVoteCand` first, then `LastVoteTerm`, where the vote step (`grantVote_upd`) fires, at the second write's commit point: the caller lends its view `srvV` and the candidate's `candIs`, and gets the vote back. (hraft_robust R4a) The stable view keeps its staged commit index `g` (`stVS`). -/
abbrev github_com.hashicorp.raft.Raft.persistVote.spec : Prop :=
  ∀ (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (s : SState) (sst : StableAbs) (g : w64) (t : w64)
    (cs : GoSlice) (c : SID) (li lt : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ isRaft r γ rc i ∗
     srvV rc s ∗ stVS rc sst g ∗ cs ↦*□ c ∗ candIs γ c s.term li lt ∗
     ⌜uint.nat t = s.term ∧ s.vterm < s.term ∧ upToDate li lt s.log⌝ }}
    (App (App (Val (r @!! go.GoType.PointerType Raft.ty @!! go!"persistVote")) (Val #t)) (Val #cs))
  {{ RET #interface.nil; srvV rc { s with vterm := s.term, vcand := c } ∗ voteIs γ i s.term c ∗
      stVS rc (StableAbs.mk (sst.ints.insert (go!"LastVoteTerm" : List w8) t)
        (sst.bytes.insert (go!"LastVoteCand" : List w8) c)) g }}

end spec

end Perennial
