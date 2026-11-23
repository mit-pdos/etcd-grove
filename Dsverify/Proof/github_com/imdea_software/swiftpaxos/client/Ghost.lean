/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/client/Ghost.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
L2's node ghost in the client package (fork e968d22, `client/ghost.go`; notes/prove-s2-e.md):
the specs of `theGhost`, `Ghost.Invoke`, `Ghost.Accept` that `Write`/`Read` are proved over.

* `theGhost()` returns the package's `nodeGhost`, which (`client.nodeGhostB`) is claimed for the
  caller's predicted node;
* `g.Invoke(...)`: lock; resolve the invocation's words (`sp.encP (inv x c)`); at the last one,
  `sp.l2_invoke` (the registration, the update deposited in the slot, the node's future words
  advanced); unlock;
* `g.Accept(...)`: likewise with `sp.l2_accept` (the commits and the client's receipt), with a
  later credit of a pure step.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.client.L2Laws
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.client.ISpecs
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.client.NodeGhost
public import Perennial.Proof.github_com.goose_lang.primitive.Link
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.client.GhostDefs

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section spec
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF]
variable [client.Assumptions]

set_option goose.wp.extras true

/-- `theGhost`: load `nodeGhost`. -/
theorem client.theGhost.wp_proof : client.theGhost.specG (hG := hG) := by
  intro γ n
  wp_start as #Hok
  iunfold client.nodeGhostB at Hok
  icases Hok with ⟨-, %g, #Hg, #Hng⟩
  wp_auto
  iapply HΦ
  iexact Hng

/-- `Ghost.Invoke`: lock `g.mu`; the resolutions (`encP (inv x c)`); `sp.l2_invoke`; unlock. -/
theorem client.Ghost.Invoke.wp_proof : client.Ghost.Invoke.specG (hG := hG) := by
  intro g γ γc γm γl x c vsl Ψ
  wp_start as ⟨#Hg, #Hinv, #Hreg, Hs, Hau, #Hv, %Hb⟩
  iunfold client.isNodeGhost at Hg
  icases Hg with ⟨%p, %Hne, #Hp, #Hmu⟩
  wp_auto
  wp_apply sync.Mutex.wp_Lock $$ [] as ⟨Hlocked, HR⟩
  · iexact Hmu
  iunfold client.nodeLockR at HR
  icases HR with ⟨%pvs, Hpr, Hw⟩
  wp_auto
  wp_apply client.Ghost.resolveField.wp $$ [Hpr] as %pv1 ⟨%Hpv1, Hpr⟩
  · iframe Hp Hpr
  wp_auto
  wp_apply client.Ghost.resolveField.wp $$ [Hpr] as %pv2 ⟨%Hpv2, Hpr⟩
  · iframe Hp Hpr
  wp_auto
  wp_apply client.Ghost.resolveField.wp $$ [Hpr] as %pv3 ⟨%Hpv3, Hpr⟩
  · iframe Hp Hpr
  wp_auto
  wp_apply client.Ghost.resolveField.wp $$ [Hpr] as %pv4 ⟨%Hpv4, Hpr⟩
  · iframe Hp Hpr
  wp_auto
  wp_apply client.Ghost.resolveBytes.wp $$ [Hpr] as ⟨%pv5, %Hpv5, Hpr⟩
  · iframe Hp Hpr Hv
  have hpvs : pvs.map sp.valW = sp.encP (.inv x c) ++ pv5.map sp.valW := by
    have : pvs = sp.encV (.inv x c) ++ pv5 := by
      rw [Hpv1, Hpv2, Hpv3, Hpv4, Hpv5]
      simp [sp.encV, sp.encP, sp.idW, sp.w8w, sp.w32w]
    rw [this, sp.encV, List.map_append, sp.map_valW_enc]
  rw [hpvs]
  iapply fupd_wp
  imod (saved_pred_alloc Ψ DFrac.discard DFrac.valid_discard) with ⟨%γΨ, #HΨ⟩
  imod (sp.l2_invoke (γ := γ) (γc := γc) (γm := γm) (γl := γl) ⊤ (by solve_ndisj) x c Ψ γΨ
      (pv5.map sp.valW)) $$ [Hs Hau Hw] with ⟨#Hc, Hs, Hpend, Hw⟩
  · iframe Hinv Hreg Hs Hau HΨ Hw
    ipureintro; exact Hb
  imodintro
  wp_auto
  wp_apply sync.Mutex.wp_Unlock $$ [Hlocked Hpr Hw]
  · iframe Hmu Hlocked
    iunfold client.nodeLockR
    iexists pv5
    iframe
  iapply HΦ
  iframe Hc Hs Hpend

/-- `Ghost.Accept`: lock `g.mu`; the resolutions (`encP (resp x v)`); `sp.l2_accept` (with a
pure step's later credit); unlock. -/
theorem client.Ghost.Accept.wp_proof : client.Ghost.Accept.specG (hG := hG) := by
  intro g γ γc γm γl x v vsl Ψ
  wp_start as ⟨#Hg, #Hinv, Hpend, #Hd, #Hv⟩
  iunfold client.isNodeGhost at Hg
  icases Hg with ⟨%p, %Hne, #Hp, #Hmu⟩
  wp_auto_lc 1
  wp_apply sync.Mutex.wp_Lock $$ [] as ⟨Hlocked, HR⟩
  · iexact Hmu
  iunfold client.nodeLockR at HR
  icases HR with ⟨%pvs, Hpr, Hw⟩
  try wp_auto
  wp_apply client.Ghost.resolveField.wp $$ [Hpr] as %pv1 ⟨%Hpv1, Hpr⟩
  · iframe Hp Hpr
  wp_auto
  wp_apply client.Ghost.resolveField.wp $$ [Hpr] as %pv2 ⟨%Hpv2, Hpr⟩
  · iframe Hp Hpr
  wp_auto
  wp_apply client.Ghost.resolveField.wp $$ [Hpr] as %pv3 ⟨%Hpv3, Hpr⟩
  · iframe Hp Hpr
  wp_auto
  wp_apply client.Ghost.resolveBytes.wp $$ [Hpr] as ⟨%pv4, %Hpv4, Hpr⟩
  · iframe Hp Hpr Hv
  ihave %Hlen := ownSlice_len $$ Hv
  have hv : v.length < 2 ^ 64 := by rw [Hlen.1]; word
  have hpvs : pvs.map sp.valW = sp.encP (.resp x v) ++ pv4.map sp.valW := by
    have : pvs = sp.encV (.resp x v) ++ pv4 := by
      rw [Hpv1, Hpv2, Hpv3, Hpv4]
      simp [sp.encV, sp.encP, sp.idW, sp.w32w]
    rw [this, sp.encV, List.map_append, sp.map_valW_enc]
  rw [hpvs]
  iapply fupd_wp
  imod (sp.l2_accept (γ := γ) (γc := γc) (γm := γm) (γl := γl) x v Ψ (pv4.map sp.valW) hv)
    $$ [Hpend Hlc1 Hw] with ⟨HΨv, Hw⟩
  · iframe Hinv Hd Hpend Hlc1 Hw
  imodintro
  wp_auto
  wp_apply sync.Mutex.wp_Unlock $$ [Hlocked Hpr Hw]
  · iframe Hmu Hlocked
    iunfold client.nodeLockR
    iexists pv4
    iframe
  iapply HΦ
  iexact HΨv

/-- `Ghost.Step`: lock `g.mu`; resolve the words (the range loop); the caller's update; unlock. -/
theorem client.Ghost.Step.wp_proof : client.Ghost.Step.specG (hG := hG) := by
  intro g γ n e wsl Q
  wp_start as ⟨#Hg, #Hws, Hupd⟩
  iunfold client.isNodeGhost at Hg
  icases Hg with ⟨%p, %Hne, #Hp, #Hmu⟩
  wp_auto
  wp_apply sync.Mutex.wp_Lock $$ [] as ⟨Hlocked, HR⟩
  · iexact Hmu
  iunfold client.nodeLockR at HR
  icases HR with ⟨%pvs, Hpr, Hw⟩
  wp_auto
  ihave %Hlen := ownSlice_len $$ Hws
  ihave IH : iprop(∃ (k : w64) (pv : List val) (wv : w64),
      "i" ∷ i_ptr ↦ k ∗ "w" ∷ w_ptr ↦ wv ∗ "Hpr" ∷ proph p pv ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ ((sp.encP e).length : Int)⌝ ∗
      "%Hpv" ∷ ⌜pvs = ((sp.encP e).take (sint.Z k).toNat).map (fun w => (#w : val)) ++ pv⌝)
      $$ [i w Hpr]
  · iexists _, _, _
    iframe
    ipureintro
    exact ⟨⟨by word, by word⟩, by simp⟩
  wp_for IH
  wp_if_destruct
  · have Hlt : (sint.Z k).toNat < (sp.encP e).length := by word
    obtain ⟨x, Hx⟩ : ∃ x, (sp.encP e)[(sint.Z k).toNat]? = some x :=
      ⟨_, List.getElem?_eq_getElem Hlt⟩
    simp only [show 0 ≤ sint.Z k ∧ sint.Z k < sint.Z wsl.len from ⟨Hn.1, Hif⟩]
    wp_apply wp_load_slice_index wsl (sint.Z k) (sp.encP e) DFrac.discard x Hn.1 $$ [] as -
    · iframe Hws; ipureintro; exact Hx
    wp_apply client.Ghost.resolveField.wp $$ [Hpr] as %pv2 ⟨%Hpv2, Hpr⟩
    · iframe Hp Hpr
    wp_for_post
    iframe
    iexists _, _, _
    iframe
    ipureintro
    refine ⟨⟨by word, by word⟩, ?_⟩
    have Hsucc : (sint.Z (k + W64 1)).toNat = (sint.Z k).toNat + 1 := by word
    rw [Hsucc, Hpv, Hpv2, List.take_succ, Hx]
    simp
  · have hk : (sint.Z k).toNat = (sp.encP e).length := by word
    rw [hk, List.take_of_length_le (Nat.le_refl _)] at Hpv
    have hpvs : pvs.map sp.valW = sp.encP e ++ pv.map sp.valW := by
      rw [Hpv, List.map_append, sp.map_valW_enc]
    rw [hpvs]
    iapply fupd_wp
    imod Hupd $$ %(pv.map sp.valW) Hw with ⟨Hw, HQ⟩
    imodintro
    try wp_auto
    wp_apply sync.Mutex.wp_Unlock $$ [Hlocked Hpr Hw]
    · iframe Hmu Hlocked
      iunfold client.nodeLockR
      iexists pv
      iframe
    iapply HΦ
    iexact HQ

theorem client.GhostStep.wp_proof : client.GhostStep.specG (hG := hG) := by
  intro γ n e wsl Q
  wp_start as ⟨#Hok, #Hws, Hupd⟩
  iunfold client.nodeGhostOk at Hok
  wp_auto
  wp_apply client.theGhost.wp_proof γ n $$ [] as %g #Hg
  · iexact Hok
  try wp_auto
  have wpS : client.Ghost.Step.specG (hG := hG) := client.Ghost.Step.wp_proof
  wp_bind (App (Val _) (Val #wsl))
  iapply (wpS g γ n e wsl Q) $$ [Hupd]
  · iframe Hupd; iframe #
  inext
  iintro HQ
  wp_auto
  iapply HΦ
  iexact HQ

end spec

end Perennial.github_com.imdea_software.swiftpaxos
