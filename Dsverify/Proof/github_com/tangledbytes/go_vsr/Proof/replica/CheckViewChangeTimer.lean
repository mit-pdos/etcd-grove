/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Proof/replica/CheckViewChangeTimer.lean (lab master 915f964;
notes/dsv-vr.md): over any `GF`, on the net extension; the hypotheses `H : replica.Hyps`
(`Hyps.lean`) for the `log/slog` methods and the `network`/`events` calls.
-/
/-
`checkViewChangeTimer`: a backup whose timer fired queues a ProposeViewChange (an `sqElem`).
(Proved.)
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.replica.Send
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.replica.Log
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.replica.Helpers
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.time
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.log
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.ipv4port
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.queue
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.assert

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

/-- The timers' third check. -/
theorem replica.wp_checkViewChangeTimer (H : replica.Hyps (GF := GF) (hG := hG)) (rp : Loc) (γ : VsrGhost.Names) (r : Nat) (tcp : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.replica ∗
        replica.ownR rp γ r tcp }}
      (App (Val (rp @!! go.GoType.PointerType replica.Replica.ty @!! go!"checkViewChangeTimer")) (Val #()))
    {{ RET #(); replica.ownR rp γ r tcp }} := by
  wp_start as Hown
  unfold replica.ownR
  icases Hown with ⟨%v, Hr, Hinv⟩
  unfold replica.repInv
  iNamed Hinv
  wp_auto
  wp_apply (replica.wp_potentialPrimary rp v ms n (by omega)) $$ [Hr] as Hr
  · iframe Hr Hms; ipureintro; exact Hmslen
  try wp_auto
  wp_if_destruct
  · close_own
  wp_apply H.wp_Done $$ [Hvct] as %b Hvct
  · iexact Hvct
  cases b
  · wp_auto
    close_own
  wp_auto
  wp_log
  try wp_auto
  ipersist «$v0»
  wp_apply (H.wp_Push events.NetworkEvent.ty (replica.sqElem γ tcp) v.internal'.sq'
    { Src' := zeroValDef, Event' := «$v0_ptr» }) $$ []
  · iframe Hsq
    unfold replica.sqElem
    iright; iright; iexact «$v0»
  wp_apply H.wp_Reset $$ [Hvct] as Hvct
  · iexact Hvct
  close_own

end proofs

end Perennial.github_com.tangledbytes.go_vsr.pkg
