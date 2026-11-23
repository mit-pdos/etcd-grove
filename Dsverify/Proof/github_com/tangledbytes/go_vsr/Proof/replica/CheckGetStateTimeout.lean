/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Proof/replica/CheckGetStateTimeout.lean (lab master 915f964;
notes/dsv-vr.md): over any `GF`, on the net extension; the hypotheses `H : replica.Hyps`
(`Hyps.lean`) for the `log/slog` methods and the `network`/`events` calls.
-/
/-
`checkGetStateTimeout`: on the timer, the stored `[view, op, target]` restarts the state transfer.
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
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.replica.InitiateStateTransfer

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

/-- The timers' first check. -/
theorem replica.wp_checkGetStateTimeout (H : replica.Hyps (GF := GF) (hG := hG)) (rp : Loc) (γ : VsrGhost.Names) (r : Nat) (tcp : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.replica ∗
        replica.ownR rp γ r tcp }}
      (App (Val (rp @!! go.GoType.PointerType replica.Replica.ty @!! go!"checkGetStateTimeout")) (Val #()))
    {{ RET #(); replica.ownR rp γ r tcp }} := by
  wp_start as Hown
  unfold replica.ownR
  icases Hown with ⟨%v, Hr, Hinv⟩
  unfold replica.repInv
  iNamed Hinv
  by_cases hn : v.internal'.getStateTimer' = null
  · wp_auto
    rw [hn]
    wp_auto
    close_own
  ihave Hgst' : iprop(⌜v.internal'.getStateTimer' = null⌝ ∨
      ((∃ a : GoArray w64 3, time.isTimer v.internal'.getStateTimer'
        (interface.mkOk (go.ArrayType 3 go.uint64) #a)) ∗
      ⌜replica.statusOf v.state'.Status' ≠ .viewChange ∧
        primary n (uint.nat v.state'.ViewNumber') ≠ r⌝)) $$ [Hgst]
  · unfold replica.gstOk; iexact Hgst
  icases Hgst' with (%Hnull | ⟨⟨%a, Hgt⟩, %Hgs⟩)
  · exact absurd Hnull hn
  wp_auto
  simp only [hn, decide_false]
  wp_auto
  wp_apply time.Timer.Done.wp $$ [Hgt] as %b Hgt
  · iexact Hgt
  ihave Hgst : replica.gstOk n v r $$ [Hgt]
  · unfold replica.gstOk; iright; isplitl [Hgt]
    · iexists a; iexact Hgt
    ipureintro; exact Hgs
  cases b
  · wp_auto
    close_own
  wp_auto
  ihave Hgst' : iprop(⌜v.internal'.getStateTimer' = null⌝ ∨
      ((∃ a : GoArray w64 3, time.isTimer v.internal'.getStateTimer'
        (interface.mkOk (go.ArrayType 3 go.uint64) #a)) ∗
      ⌜replica.statusOf v.state'.Status' ≠ .viewChange ∧
        primary n (uint.nat v.state'.ViewNumber') ≠ r⌝)) $$ [Hgst]
  · unfold replica.gstOk; iexact Hgst
  icases Hgst' with (%Hnull | ⟨⟨%a, Hgt⟩, %Hgs⟩)
  · exact absurd Hnull hn
  wp_apply time.Timer.State.wp $$ [Hgt] as Hgt
  · iexact Hgt
  wp_auto
  wp_apply assert.Assert.wp
  try wp_auto
  wp_log
  obtain ⟨arr⟩ := a
  icases BI.persistent_entails_left (array_len (GF := GF) _ _ _ _) $$ castedState
    with ⟨castedState, %Hal⟩
  obtain ⟨x0, hx0⟩ : ∃ x, arr[0]? = some x := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨x1, hx1⟩ : ∃ x, arr[1]? = some x := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  icases array_acc (GF := GF) _ (sint.Z (W64 0)) _ _ _ x0 (by decide) (by simpa using hx0)
    $$ castedState with ⟨Hp0, castedState⟩
  try wp_auto
  ihave castedState := castedState $$ %x0 Hp0
  icases array_acc (GF := GF) _ (sint.Z (W64 1)) _ _ _ x1 (by decide)
    (by simpa [List.getElem?_set] using hx1) $$ castedState with ⟨Hp1, castedState⟩
  try wp_auto
  ihave Hgst : replica.gstOk n v r $$ [Hgt]
  · unfold replica.gstOk; iright; isplitl [Hgt]
    · iexists _; iexact Hgt
    ipureintro; exact Hgs
  ihave Hinv : replica.repInv γ r tcp v $$ [Hsender Hrep Hcap Hstore Htbl Hpk Hpks Hsv Hsvs Hdv
      Hdvs Hvct Hct Hgst]
  · unfold replica.repInv
    iexists lg, mine, cw, mw, me, C, F, P, ms, tbl, pk, sv, dv, vst, cst, n
    iFrameNamed
    ipureintro
    exact ⟨Hid, Hmslen, Hnet, Htime, Hstatus, Hst, Hopnum, Hcommit, Hmine, Htmine, Htlog⟩
  wp_apply (replica.wp_initiateStateTransfer H rp γ r tcp v n x0 x1) $$ [Hr Hinv]
    as ⟨%v', Hr, Hinv, -⟩
  · iframe Hr Hinv Hsize; ipureintro; intro _; exact Hgs.2
  iapply HΦ
  iexists v'; iframe Hr; unfold replica.repInv; iexact Hinv

end proofs

end Perennial.github_com.tangledbytes.go_vsr.pkg
