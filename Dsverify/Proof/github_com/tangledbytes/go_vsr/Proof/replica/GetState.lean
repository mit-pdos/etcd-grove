/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Proof/replica/GetState.lean (lab master 915f964;
notes/dsv-vr.md): over any `GF`, on the net extension; the hypotheses `H : replica.Hyps`
(`Hyps.lean`) for the `log/slog` methods and the `network`/`events` calls.
-/
/-
`onGetState`: a normal replica of the view answers with its log after the op (`sendNewState`).
(Stub: the spec, for parallel proving; `sorry` until proved.)
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
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.replica.SendNewState

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

/-- A GetState from an `addrOk` source. -/
theorem replica.wp_onGetState (H : replica.Hyps (GF := GF) (hG := hG)) (rp : Loc) (γ : VsrGhost.Names) (r : Nat) (tcp : Loc)
    (src : ipv4port.IPv4Port) (ev : events.GetState) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.replica ∗
        replica.ownR rp γ r tcp ∗ network.addrOk tcp src }}
      (App (App (Val (rp @!! go.GoType.PointerType replica.Replica.ty @!! go!"onGetState")) (Val #src)) (Val #ev))
    {{ RET #(); replica.ownR rp γ r tcp }} := by
  wp_start as ⟨Hown, #Hsrc⟩
  unfold replica.ownR
  icases Hown with ⟨%v, Hr, Hinv⟩
  unfold replica.repInv
  iNamed Hinv
  wp_auto
  wp_apply (ipv4port.IPv4Port.String_ptr.wp src_ptr (DFrac.own 1) src) $$ [src] as src
  · iexact src
  wp_log
  wp_if_destruct
  rotate_left
  · -- not normal
    wp_log
    close_own
  wp_if_destruct
  rotate_left
  · -- another view
    wp_log
    close_own
  wp_if_destruct
  · -- behind
    wp_log
    close_own
  have Hn0 : v.state'.Status' = W64 0 := by assumption
  have hr3 : r < n := Hid.2
  ihave #Hnil : ([∗list] f ∈ ([] : List Fact), VsrGhost.fact γ f) $$ []
  · iapply (BI.BigSepL.bigSepL_nil (PROP := IProp GF)).2; iempintro
  imod VsrReplica.ghost_pure_rep' γ n r _ [] (lg.length ≤ 6 * 2 ^ 28)
    (fun s hs hsn hrp _ => by
      have := VsrModel.repLog_length_le s hs r (show r < s.n from hsn ▸ hr3); rw [hrp] at this; exact this)
    $$ Hsize Hsys Hrep Hnil with ⟨Hrep, %Hlen⟩
  have hk0 : 0 ≤ sint.Z ev.OpNum' := by
    have : uint.Z ev.OpNum' ≤ uint.Z v.state'.OpNum' := by omega
    have : uint.nat v.state'.OpNum' ≤ 6 * 2 ^ 28 := by omega
    word
  have hkl : sint.nat ev.OpNum' ≤ lg.length := by
    have : uint.Z ev.OpNum' ≤ uint.Z v.state'.OpNum' := by omega
    have : uint.nat v.state'.OpNum' ≤ 6 * 2 ^ 28 := by omega
    word
  imod VsrReplica.ghost_fact' γ n r _ []
    (.msg (.newState (uint.nat v.state'.ViewNumber') (lg.drop (sint.nat ev.OpNum'))
      (uint.nat v.state'.CommitNumber') (uint.nat v.state'.OpNum') (uint.nat v.state'.ID')))
    (fun s hs hsn hrp _ => by
      have := VsrModel.newState_own s hs r (sint.nat ev.OpNum') (uint.nat v.state'.CommitNumber')
        (show r < s.n from hsn ▸ hr3) (by rw [hrp]; simp [replica.repOf, replica.statusOf, Hn0]) (by rw [hrp]; exact hkl)
      rw [hrp] at this
      simp only [replica.repOf] at this
      rw [Hopnum, Hid.1]; exact this)
    $$ Hsize Hsys Hrep Hnil with ⟨Hrep, #Hnsf⟩
  wp_apply (replica.wp_sendNewState H rp v γ tcp C F src ev.OpNum' lg hk0 hkl) $$ [Hr Hsender]
    as %err ⟨Hr, Hsender, #Herr⟩
  · iframe Hr Hsender Hsrc Hlog Hnsf
    unfold replica.sendCtx
    iexists me
    iframe HisTCP Hprotos Hcodec Hkit Hsys
    ipureintro; exact Hnet
  cases err with
  | nil =>
    wp_auto
    close_own
  | ok ii =>
    wp_auto
    wp_apply (ipv4port.IPv4Port.String_ptr.wp src_ptr (DFrac.own 1) src) $$ [src] as src
    · iexact src
    wp_log
    close_own

end proofs

end Perennial.github_com.tangledbytes.go_vsr.pkg
