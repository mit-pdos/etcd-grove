/-
The definitions, specs and lemmas of `AliveQuorum.lean` that its proofs do not need (split out for the import tiers, CLAUDE.md "Import tiers": its importers that are not linking modules import this module, and see no proof).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.QuorumOkDefs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.Defs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section specs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF]
variable [swift.Assumptions] [replica.Assumptions]

/-- `r.aliveQuorumBallot(b)` for `b ≥ 0` (see the file header). -/
abbrev swift.Replica.aliveQuorumBallot.spec : Prop :=
  ∀ (rp rr qs : Loc) (γ : sp.Names) (γc γm γw : GName) (N : Nat) (me b : w32),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      swift.fld rp go!"Replica" ↦□ rr ∗ replica.isReplica rr γ γc γm γw N me ∗
      swift.fld rp go!"qs" ↦□ qs ∗ replica.quorum.isQS qs N ∗
      swift.fld rp go!"fixedMajority" ↦□ true ∗
      ⌜0 ≤ sint.Z b ∧ 1 ≤ N ∧ sint.Z b % (N : Int) = sint.Z me⌝ }}
    (App (Val (rp @!! go.GoType.PointerType swift.Replica.ty @!! go!"aliveQuorumBallot")) (Val #b))
  {{ (b' : w32) (ok : Bool), RET (PairV #b' #ok);
      ⌜ok = true → 0 ≤ sint.Z b' ∧ sint.Z b' % (N : Int) = sint.Z me⌝ }}

end specs

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF]
variable [swift.Assumptions] [replica.Assumptions]

set_option goose.wp.extras true

open replica.quorum

end proof

end Perennial.github_com.imdea_software.swiftpaxos

end
