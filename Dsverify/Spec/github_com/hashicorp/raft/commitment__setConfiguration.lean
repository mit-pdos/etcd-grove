/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/commitment__setConfiguration.lean (241f27e).
-/
/-
`raft.commitment.setConfiguration`'s spec (stage 4 interface).
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

/-- `(*commitment).setConfiguration(c)` (stage 4), by the main goroutine of the leader `i` of `s.term`
(after `appendConfigurationEntry`'s dispatch) with its half of the configuration the commitment counts
(`ccfgOwn`) and `c` the latest configuration of its log (`cfgAtIs` at `lastCfgIdx s.log ≥ 1`): under
the lock, the match indexes become those of `c`'s voters (the kept ones' values stay: acknowledgements
of `s.term`), the commitment counts the latest configuration (`gprot.installCfg_upd` with the lock's
half), and the commit index is recalculated with its quorum (`gprot.commit_upd`). -/
abbrev github_com.hashicorp.raft.commitment.setConfiguration.spec : Prop :=
  ∀ (γ : GNames) (rc : RCtx GF) (i : SID) (s : SState) (cm : Loc) (c : Configuration) (p : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ isCommitment γ i s.term cm ∗ Inv γ ∗ srvDurInv γ rc i ∗ srvV rc s ∗ leaderIs γ s.term i ∗
     ccfgOwn γ i s.term p ∗ cfgAtIs γ s.log (lastCfgIdx s.log) c ∗
     ⌜1 ≤ lastCfgIdx s.log ∧ γ.cv = cfgDec γ.srvs⌝ }}
    (App (Val (cm @!! go.GoType.PointerType commitment.ty @!! go!"setConfiguration")) (Val #c))
  {{ RET #(); srvV rc s ∗ ccfgOwn γ i s.term (lastCfgIdx s.log) }}

end spec

end Perennial
