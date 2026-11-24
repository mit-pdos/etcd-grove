/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/client/Ghost.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
L2's node prophecy in the client package (the prophecy patch's prophecy-only helpers,
etc/proph-patches/dsv-swiftpaxos; notes/proph-swiftpaxos.md): the proofs of `resolveInvoke` and
`resolveAccept`, which `Write`/`Read` are proved over.

Each builds its event's string (`sp.strW (sp.encP e)`: a word statement per word, a counted loop
over the value's bytes), then resolves the node's prophecy once with it (`sp.encE e`), inside the
node prophecy's invariant (`client.wp_resolveNode`), where the protocol's update runs:
`sp.l2_invoke` (the registration, the update deposited in the slot) or `sp.l2_accept` (the commits
and the client's receipt, with a later credit of a pure step).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.client.L2Laws
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.client.ISpecs
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.client.NodeGhost
public import Perennial.Proof.github_com.mit_pdos.perennial.proph.Link
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

/-- `resolveAccept`: the words of `resp x v`; the resolution, with `sp.l2_accept` (a pure step's
later credit) inside the node prophecy's invariant. -/
theorem client.resolveAccept.wp_proof : client.resolveAccept.specG (hG := hG) := by
  intro γ γc γm γl x v vsl Ψ
  wp_start as ⟨#Hng, #Hinv, Hpend, #Hd, #Hv⟩
  iunfold client.nodeGhostB at Hng
  icases Hng with ⟨#Hreg, %p, #Hp, #Hi⟩
  simp only [client.nodeVar]
  ihave %Hlen := ownSlice_len $$ Hv
  wp_auto_lc 1
  simp only [sp.strW1_eval]
  obtain ⟨S0, hS0⟩ : ∃ S0 : List w8, S0 = [] ++ sp.strW1 (W64 3) ++ sp.strW1 (W64 (uint.Z x.cl)) ++
      sp.strW1 (W64 (uint.Z x.seq)) ++ sp.strW1 vsl.len := ⟨_, rfl⟩
  rw [← hS0]
  ihave IH : iprop(∃ (k : w64) (wv : w64),
      "i" ∷ i_ptr ↦ k ∗ "w" ∷ w_ptr ↦ wv ∗
      "s" ∷ s_ptr ↦ (S0 ++ sp.strW ((v.take (sint.Z k).toNat).map sp.w8w)) ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ (v.length : Int)⌝) $$ [i w s]
  · iexists _, _
    iframe
    isplitl [s]
    · simp [sp.strW]; iexact s
    ipureintro; exact ⟨by word, by word⟩
  wp_for IH
  wp_if_destruct
  · have Hlt : (sint.Z k).toNat < v.length := by word
    obtain ⟨y, Hy⟩ : ∃ y, v[(sint.Z k).toNat]? = some y := ⟨_, List.getElem?_eq_getElem Hlt⟩
    simp only [show 0 ≤ sint.Z k ∧ sint.Z k < sint.Z vsl.len from ⟨Hk.1, Hif⟩]
    wp_apply wp_load_slice_index vsl (sint.Z k) v DFrac.discard y Hk.1 $$ [] as -
    · iframe Hv; ipureintro; exact Hy
    simp only [sp.strW1_eval]
    wp_for_post
    iframe
    iexists _, _
    iframe
    isplitl [s]
    · have Hsucc : (sint.Z (k + W64 1)).toNat = (sint.Z k).toNat + 1 := by word
      rw [Hsucc, List.take_add_one, Hy]
      simp only [Option.toList_some, List.map_append, List.map_cons, List.map_nil, sp.strW,
        List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]
      rw [show sp.w8w y = W64 (uint.Z y) from rfl]
      iexact s
    ipureintro; exact ⟨by word, by word⟩
  · have hk : (sint.Z k).toNat = v.length := by word
    have hl : vsl.len = W64 (v.length : Int) := by word
    have hv : v.length < 2 ^ 64 := by rw [Hlen.1]; word
    have hs : S0 ++ sp.strW (List.map sp.w8w (List.take (sint.Z k).toNat v)) =
        sp.strW (sp.encP (.resp x v)) := by
      rw [hk, List.take_of_length_le (Nat.le_refl _), hS0, hl]
      simp [sp.encP, sp.idW, sp.wordsOf, sp.strW, sp.w32w]
    rw [hs]
    wp_method_call
    wp_auto
    wp_method_call
    wp_auto
    rw [show (#(interface.mkOk go.string #(sp.strW (sp.encP (.resp x v)))) : val) =
      sp.encE (.resp x v) from rfl]
    wp_bind (ResolveProph _ _)
    iapply (client.wp_resolveNode γ (sp.PNode.cl (sp.clOf x)) p (.resp x v) hv iprop(▷ Ψ v))
    iframe Hi
    isplitl [Hpend Hlc1]
    · iintro %W' Hw
      imod (sp.l2_accept (γ := γ) (γc := γc) (γm := γm) (γl := γl) x v Ψ W' hv)
        $$ [Hpend Hlc1 Hw] with ⟨HΨ, Hw⟩
      · iframe Hinv Hd Hpend Hlc1 Hw
      imodintro
      iframe
    · iintro HQ
      wp_auto
      iapply HΦ
      iexact HQ

/-- `resolveInvoke`: the words of `inv x c`; the resolution, with `sp.l2_invoke` (the
registration, the update deposited) inside the node prophecy's invariant. -/
theorem client.resolveInvoke.wp_proof : client.resolveInvoke.specG (hG := hG) := by
  intro γ γc γm γl x c vsl Ψ
  wp_start as ⟨#Hng, #Hinv, #Hreg, Hs, Hau, #Hv, %Hb⟩
  iunfold client.nodeGhostB at Hng
  icases Hng with ⟨#Hreg', %p, #Hp, #Hi⟩
  simp only [client.nodeVar]
  ihave %Hlen := ownSlice_len $$ Hv
  wp_auto
  simp only [sp.strW1_eval]
  obtain ⟨S0, hS0⟩ : ∃ S0 : List w8, S0 = [] ++ sp.strW1 (W64 (uint.Z c.op)) ++
      sp.strW1 (W64 (uint.Z x.cl)) ++ sp.strW1 (W64 (uint.Z x.seq)) ++ sp.strW1 c.key ++
      sp.strW1 vsl.len := ⟨_, rfl⟩
  rw [← hS0]
  ihave IH : iprop(∃ (k : w64) (wv : w64),
      "i" ∷ i_ptr ↦ k ∗ "w" ∷ w_ptr ↦ wv ∗
      "s" ∷ s_ptr ↦ (S0 ++ sp.strW ((c.val.take (sint.Z k).toNat).map sp.w8w)) ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ (c.val.length : Int)⌝) $$ [i w s]
  · iexists _, _
    iframe
    isplitl [s]
    · simp [sp.strW]; iexact s
    ipureintro; exact ⟨by word, by word⟩
  wp_for IH
  wp_if_destruct
  · have Hlt : (sint.Z k).toNat < c.val.length := by word
    obtain ⟨y, Hy⟩ : ∃ y, c.val[(sint.Z k).toNat]? = some y := ⟨_, List.getElem?_eq_getElem Hlt⟩
    simp only [show 0 ≤ sint.Z k ∧ sint.Z k < sint.Z vsl.len from ⟨Hk.1, Hif⟩]
    wp_apply wp_load_slice_index vsl (sint.Z k) c.val DFrac.discard y Hk.1 $$ [] as -
    · iframe Hv; ipureintro; exact Hy
    simp only [sp.strW1_eval]
    wp_for_post
    iframe
    iexists _, _
    iframe
    isplitl [s]
    · have Hsucc : (sint.Z (k + W64 1)).toNat = (sint.Z k).toNat + 1 := by word
      rw [Hsucc, List.take_add_one, Hy]
      simp only [Option.toList_some, List.map_append, List.map_cons, List.map_nil, sp.strW,
        List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]
      rw [show sp.w8w y = W64 (uint.Z y) from rfl]
      iexact s
    ipureintro; exact ⟨by word, by word⟩
  · have hk : (sint.Z k).toNat = c.val.length := by word
    have hl : vsl.len = W64 (c.val.length : Int) := by word
    have hv : c.val.length < 2 ^ 64 := by rw [Hlen.1]; word
    have hs : S0 ++ sp.strW (List.map sp.w8w (List.take (sint.Z k).toNat c.val)) =
        sp.strW (sp.encP (.inv x c)) := by
      rw [hk, List.take_of_length_le (Nat.le_refl _), hS0, hl]
      simp [sp.encP, sp.idW, sp.wordsOf, sp.strW, sp.w32w, sp.w8w]
    rw [hs]
    wp_method_call
    wp_auto
    wp_method_call
    wp_auto
    rw [show (#(interface.mkOk go.string #(sp.strW (sp.encP (.inv x c)))) : val) =
      sp.encE (.inv x c) from rfl]
    wp_bind (ResolveProph _ _)
    have he : sp.PEvWf (.inv x c) := by
      refine ⟨?_, hv⟩
      rcases Hb.2.1 with h | h
      · left; simpa [sp.Cmd.isPut] using h
      · right; simpa [sp.Cmd.isGet] using h
    iapply (client.wp_resolveNode γ (sp.PNode.cl (sp.clOf x)) p (.inv x c) he
      iprop(sp.cmdIs γ x c ∗ sp.clientSeq γ x.cl (x.seq.toNat + 1) ∗ sp.pend γ x Ψ))
    iframe Hi
    isplitl [Hs Hau]
    · iintro %W' Hw
      imod (saved_pred_alloc Ψ DFrac.discard DFrac.valid_discard) with ⟨%γΨ, #HΨ⟩
      imod (sp.l2_invoke (γ := γ) (γc := γc) (γm := γm) (γl := γl) (⊤ \ ↑client.nodeProphN)
          sp.spN_prophN x c Ψ γΨ W') $$ [Hs Hau Hw] with ⟨#Hc, Hs, Hpend, Hw⟩
      · iframe Hinv Hreg Hs Hau HΨ Hw
        ipureintro; exact Hb
      imodintro
      iframe Hw Hc Hs Hpend
    · iintro HQ
      wp_auto
      iapply HΦ
      iexact HQ

end spec

end Perennial.github_com.imdea_software.swiftpaxos
