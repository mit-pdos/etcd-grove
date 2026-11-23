/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Proof/replica/CheckTimers.lean (lab master 915f964;
notes/dsv-vr.md): over any `GF`, on the net extension; the hypotheses `H : replica.Hyps`
(`Hyps.lean`) for the `log/slog` methods and the `network`/`events` calls.
-/
/-
`checkTimers`: the three checks.
(Proved.)
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.replica.Send
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.replica.Log
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.replica.Helpers
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.time.Results
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.log.Logs
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.ipv4port.Results
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.queue.Results
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.assert.Results
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.replica.CheckGetStateTimeout
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.replica.CheckCommitTimeout
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.replica.CheckViewChangeTimer

@[expose] public section

noncomputable section

namespace Perennial.github_com.tangledbytes.go_vsr.pkg

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net VsrModel


section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : replica.Assumptions] [net.FieldAssumptions] [π : NetProtoGS]
variable [encoding.json.DecoderRep GF]

set_option goose.wp.extras true

/-- The timers. -/
theorem replica.wp_checkTimers (H : replica.Hyps (GF := GF) (hG := hG)) (rp : Loc) (γ : VsrGhost.Names) (r : Nat) (tcp : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.replica ∗
        replica.ownR rp γ r tcp }}
      (App (Val (rp @!! go.GoType.PointerType replica.Replica.ty @!! go!"checkTimers")) (Val #()))
    {{ RET #(); replica.ownR rp γ r tcp }} := by
  wp_start as Hown
  wp_auto
  wp_apply replica.wp_checkGetStateTimeout H rp γ r tcp $$ [Hown] as Hown
  · iexact Hown
  wp_apply replica.wp_checkCommitTimeout H rp γ r tcp $$ [Hown] as Hown
  · iexact Hown
  wp_apply replica.wp_checkViewChangeTimer H rp γ r tcp $$ [Hown] as Hown
  · iexact Hown
  try wp_auto
  iapply HΦ; iexact Hown

end proofs

end Perennial.github_com.tangledbytes.go_vsr.pkg
