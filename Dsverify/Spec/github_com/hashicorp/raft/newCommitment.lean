/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/newCommitment.lean (241f27e).
-/
/-
`raft.newCommitment`'s spec (raft-internal interface, notes/raft-iface.md). The commitment of the leader `i` of term `T` (elected with `n0` entries), over the bootstrap configuration's voters, starting at `n0 + 1`.
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

/-- `newCommitment`: The commitment of the leader `i` of term `T` (elected with `n0` entries), starting
at `n0 + 1`, over the voters of `c` (stage 4: the configuration entry at `p` of `llog T`, which the
commitment counts: it takes its half of `ccfgOwn γ i T p`; stage 3: the bootstrap configuration's
voters). -/
abbrev github_com.hashicorp.raft.newCommitment.spec : Prop :=
  ∀ (γ : GNames) (i : SID) (T n0 p : Nat) (ch : Loc) (c : Configuration) (ss : List Server)
    (e : Entry) (si : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ Inv γ ∗ notifyChan ch ∗
     cfgVal γ c ss ∗ llogIdx γ T p e ∗ ⌜e.kind = kConfig ∧ e.data = encodeServers ss ∧ γ.cv = cfgDec γ.srvs⌝ ∗
     ccfgOwn γ i T p ∗ leaderIs γ T i ∗ len0Is γ T n0 ∗
     ⌜uint.nat si = n0 + 1⌝ }}
    (App (App (App (Val (@! github_com.hashicorp.raft.newCommitment)) (Val #ch)) (Val #c)) (Val #si))
  {{ (cm : Loc), RET #cm; isCommitment γ i T cm }}

end spec

end Perennial
