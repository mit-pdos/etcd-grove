/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/GhostSteps.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
L2 (notes/prove-s2-e.md, item 4; notes/proph-swiftpaxos.md): the specs of the swift package's
prophecy-only resolvers (etc/proph-patches/dsv-swiftpaxos, `resolveX` in swift/recovery.go): each
builds its event's string (`sp.strW (sp.encP e)`) and resolves the node's prophecy once with it,
inside the node prophecy's invariant (`client.wp_resolveNode`), where the caller's update runs
with the node's half of its future words (`sp.predPre` / `sp.predPost`, Steps.lean), at
`⊤ ∖ ↑client.nodeProphN`. A site proof calls the resolver with its step lemma (a `swift.*_stepD`
at that mask) inside the update.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.Steps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.client.GhostDefs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.InternalDeps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.HashLeafDefs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.AcksSpecs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.RunCtx

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section defs
variable [GoGlobalContext] [G : GooseGlobalGS .hasLC netDistGF] [π : NetProtoGS]

/-- **A site's update at a resolution** at replica node `k`'s step `e`: with the node's half of
its future words starting with `e`'s, give back the rest and `Q`, inside the node prophecy's
invariant (`⊤ ∖ ↑client.nodeProphN`). -/
def swift.resolveUpd (γ : sp.Names) (k : Nat) (e : sp.PEv) (Q : IProp netDistGF) : IProp netDistGF :=
  iprop(∀ W' : List w64, sp.predPre γ k (some (e, W')) ={⊤ \ ↑client.nodeProphN}=∗
    sp.predPost γ k (some (e, W')) ∗ Q)

end defs

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions] [client.Assumptions]

set_option goose.wp.extras true

/-- **A replica's resolution** of its event `e` (the string `s` of `e`'s words), with a site's
update. -/
theorem swift.wp_resolveStep (γ : sp.Names) (k : Nat) (p : proph_id) (e : sp.PEv) (he : sp.PEvWf e)
    (Q : IProp netDistGF) (Φ : val → IProp netDistGF) (s : List w8)
    (hs : s = sp.strW (sp.encP e)) :
    inv client.nodeProphN (client.nodeLockR γ (sp.PNode.rep k) p) ∗ swift.resolveUpd γ k e Q ∗
      (Q -∗ Φ #()) ⊢
    WP (ResolveProph (Val #p) (Val #(interface.mkOk go.string #s))) {{ Φ }} := by
  subst hs
  rw [show (#(interface.mkOk go.string #(sp.strW (sp.encP e))) : val) = sp.encE e from rfl]
  iintro ⟨#Hi, Hupd, HΦ⟩
  iapply (client.wp_resolveNode γ (sp.PNode.rep k) p e he Q Φ)
  iframe Hi HΦ
  iintro %W' Hw
  iunfold swift.resolveUpd at Hupd
  simp only [sp.predPre_some, sp.predPost_some]
  imod Hupd $$ %W' [Hw] with ⟨Hp, HQ⟩
  · iframe Hw; ipureintro; exact he
  imodintro
  iframe

theorem swift.bal_lt (b : w32) : sp.bal b < 2 ^ 31 := by
  unfold sp.bal; have := BitVec.toInt_lt (x := b); simp at this; omega

theorem swift.setWidth_w32w (n : w32) : BitVec.setWidth 64 n = sp.w32w n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, sp.w32w]
  have := n.isLt
  rw [show (W64 (n.toNat : Int)).toNat = n.toNat from by
    simp only [W64, BitVec.toNat_ofInt]; omega]
  omega

theorem swift.bal_wf (b : w32) : sp.PEvWf (.newBallot (sp.bal b)) := by
  show sp.bal b < 2 ^ 64; have := swift.bal_lt b; omega

theorem swift.setWidth_w8w (n : w8) : BitVec.setWidth 64 n = sp.w8w n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, sp.w8w]
  have := n.isLt
  rw [show (W64 (n.toNat : Int)).toNat = n.toNat from by
    simp only [W64, BitVec.toNat_ofInt]; omega]
  omega

/-- `resolveAccept(b, id)`. -/
theorem swift.wp_resolveAccept (γ : sp.Names) (k : Nat) (b : w32) (x : swift.CommandId)
    (Q : IProp netDistGF) :
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.client ∗
      client.nodeGhostOk γ (sp.PNode.rep k) ∗ ⌜0 ≤ sint.Z b⌝ ∗
      swift.resolveUpd γ k (.accept (sp.bal b) (toCmdId x)) Q }}
    (App (App (Val (@! swift.resolveAccept)) (Val #b)) (Val #x))
  {{ RET #(); Q }} := by
  wp_start as ⟨#Hok, %Hb, Hupd⟩
  iunfold client.nodeGhostOk at Hok
  iunfold client.nodeGhostB at Hok
  icases Hok with ⟨#Hreg, %p, #Hp, #Hi⟩
  simp only [client.nodeVar]
  wp_auto
  simp only [sp.strW1_eval]
  wp_method_call
  wp_auto
  wp_method_call
  wp_auto
  wp_bind (ResolveProph _ _)
  iapply (swift.wp_resolveStep γ k p (.accept (sp.bal b) (toCmdId x))
    (by show sp.bal b < 2 ^ 64; have := swift.bal_lt b; omega) Q _ _ ?hs)
  case hs =>
    have h : (((sint.Z b).toNat : Nat) : Int) = sint.Z b := Int.toNat_of_nonneg Hb
    simp [sp.encP, sp.natW, sp.bal, h, sp.idW, toCmdId, sp.strW, sp.w32w]
  iframe Hi Hupd
  iintro HQ
  wp_auto
  iapply HΦ
  iexact HQ

/-- `resolveNewBallot`. -/
theorem swift.wp_resolveNewBallot (γ : sp.Names) (k : Nat) (b : w32) (Q : IProp netDistGF) :
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.client ∗
      client.nodeGhostOk γ (sp.PNode.rep k) ∗ ⌜0 ≤ sint.Z b⌝ ∗
      swift.resolveUpd γ k (.newBallot (sp.bal b)) Q }}
    (App (Val (@! swift.resolveNewBallot)) (Val #b))
  {{ RET #(); Q }} := by
  wp_start as ⟨#Hok, %Hb, Hupd⟩
  iunfold client.nodeGhostOk at Hok
  iunfold client.nodeGhostB at Hok
  icases Hok with ⟨#Hreg, %p, #Hp, #Hi⟩
  simp only [client.nodeVar]
  wp_auto
  simp only [sp.strW1_eval]
  wp_method_call
  wp_auto
  wp_method_call
  wp_auto
  wp_bind (ResolveProph _ _)
  iapply (swift.wp_resolveStep γ k p (.newBallot (sp.bal b)) (by show sp.bal b < 2 ^ 64; have := swift.bal_lt b; omega) Q _ _ ?hs)
  case hs =>
    have h : (((sint.Z b).toNat : Nat) : Int) = sint.Z b := Int.toNat_of_nonneg Hb
    simp [sp.encP, sp.natW, sp.bal, h, sp.idW, toCmdId, sp.strW, sp.w32w]
  iframe Hi Hupd
  iintro HQ
  wp_auto
  iapply HΦ
  iexact HQ

/-- `resolveTakeSync`. -/
theorem swift.wp_resolveTakeSync (γ : sp.Names) (k : Nat) (b : w32) (Q : IProp netDistGF) :
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.client ∗
      client.nodeGhostOk γ (sp.PNode.rep k) ∗ ⌜0 ≤ sint.Z b⌝ ∗
      swift.resolveUpd γ k (.takeSync (sp.bal b)) Q }}
    (App (Val (@! swift.resolveTakeSync)) (Val #b))
  {{ RET #(); Q }} := by
  wp_start as ⟨#Hok, %Hb, Hupd⟩
  iunfold client.nodeGhostOk at Hok
  iunfold client.nodeGhostB at Hok
  icases Hok with ⟨#Hreg, %p, #Hp, #Hi⟩
  simp only [client.nodeVar]
  wp_auto
  simp only [sp.strW1_eval]
  wp_method_call
  wp_auto
  wp_method_call
  wp_auto
  wp_bind (ResolveProph _ _)
  iapply (swift.wp_resolveStep γ k p (.takeSync (sp.bal b)) (by show sp.bal b < 2 ^ 64; have := swift.bal_lt b; omega) Q _ _ ?hs)
  case hs =>
    have h : (((sint.Z b).toNat : Nat) : Int) = sint.Z b := Int.toNat_of_nonneg Hb
    simp [sp.encP, sp.natW, sp.bal, h, sp.idW, toCmdId, sp.strW, sp.w32w]
  iframe Hi Hupd
  iintro HQ
  wp_auto
  iapply HΦ
  iexact HQ

/-- `resolveCommit`. -/
theorem swift.wp_resolveCommit (γ : sp.Names) (k : Nat) (b : w32) (x : swift.CommandId) (Q : IProp netDistGF) :
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.client ∗
      client.nodeGhostOk γ (sp.PNode.rep k) ∗ ⌜0 ≤ sint.Z b⌝ ∗
      swift.resolveUpd γ k (.commit (sp.bal b) (toCmdId x)) Q }}
    (App (App (Val (@! swift.resolveCommit)) (Val #b)) (Val #x))
  {{ RET #(); Q }} := by
  wp_start as ⟨#Hok, %Hb, Hupd⟩
  iunfold client.nodeGhostOk at Hok
  iunfold client.nodeGhostB at Hok
  icases Hok with ⟨#Hreg, %p, #Hp, #Hi⟩
  simp only [client.nodeVar]
  wp_auto
  simp only [sp.strW1_eval]
  wp_method_call
  wp_auto
  wp_method_call
  wp_auto
  wp_bind (ResolveProph _ _)
  iapply (swift.wp_resolveStep γ k p (.commit (sp.bal b) (toCmdId x)) (by show sp.bal b < 2 ^ 64; have := swift.bal_lt b; omega) Q _ _ ?hs)
  case hs =>
    have h : (((sint.Z b).toNat : Nat) : Int) = sint.Z b := Int.toNat_of_nonneg Hb
    simp [sp.encP, sp.natW, sp.bal, h, sp.idW, toCmdId, sp.strW, sp.w32w]
  iframe Hi Hupd
  iintro HQ
  wp_auto
  iapply HΦ
  iexact HQ

/-- `resolveHandle(b, id, c)`. -/
theorem swift.wp_resolveHandle (γ : sp.Names) (k : Nat) (b : w32) (x : swift.CommandId)
    (c : sp.Cmd) (vs : GoSlice) (dq : DFrac) (Q : IProp netDistGF) :
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.client ∗
      client.nodeGhostOk γ (sp.PNode.rep k) ∗ ⌜0 ≤ sint.Z b⌝ ∗ vs ↦*{dq} c.val ∗
      swift.resolveUpd γ k (.handle (sp.bal b) (toCmdId x) c) Q }}
    (App (App (App (Val (@! swift.resolveHandle)) (Val #b)) (Val #x))
      (Val #(state.Command.mk c.op c.key vs)))
  {{ RET #(); vs ↦*{dq} c.val ∗ Q }} := by
  wp_start as ⟨#Hok, %Hb, Hv, Hupd⟩
  ihave %Hlen := ownSlice_len $$ Hv
  iunfold client.nodeGhostOk at Hok
  iunfold client.nodeGhostB at Hok
  icases Hok with ⟨#Hreg, %p, #Hp, #Hi⟩
  simp only [client.nodeVar]
  wp_auto
  simp only [sp.strW1_eval]
  obtain ⟨S0, hS0⟩ : ∃ S0 : List w8, S0 = [] ++ sp.strW1 (W64 4) ++ sp.strW1 (W64 (sint.Z b)) ++
      sp.strW1 (W64 (uint.Z x.ClientId')) ++ sp.strW1 (W64 (uint.Z x.SeqNum')) ++
      sp.strW1 (W64 (uint.Z c.op)) ++ sp.strW1 c.key ++ sp.strW1 vs.len := ⟨_, rfl⟩
  rw [← hS0]
  ihave IH : iprop(∃ (j : w64) (wv : w64),
      "i" ∷ k_ptr ↦ j ∗ "w" ∷ w_ptr ↦ wv ∗
      "s" ∷ s_ptr ↦ (S0 ++ sp.strW ((c.val.take (sint.Z j).toNat).map sp.w8w)) ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ (c.val.length : Int)⌝) $$ [k w s]
  · iexists _, _
    iframe
    isplitl [s]
    · simp [sp.strW]; iexact s
    ipureintro; exact ⟨by word, by word⟩
  wp_for IH
  wp_if_destruct
  · have Hlt : (sint.Z j).toNat < c.val.length := by word
    obtain ⟨y, Hy⟩ : ∃ y, c.val[(sint.Z j).toNat]? = some y := ⟨_, List.getElem?_eq_getElem Hlt⟩
    simp only [show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z vs.len from ⟨Hj.1, Hif⟩]
    wp_apply wp_load_slice_index vs (sint.Z j) c.val dq y Hj.1 $$ [Hv] as Hv
    · iframe Hv; ipureintro; exact Hy
    simp only [sp.strW1_eval]
    wp_for_post
    iframe
    iexists _, _
    iframe
    isplitl [s]
    · have Hsucc : (sint.Z (j + W64 1)).toNat = (sint.Z j).toNat + 1 := by word
      iExactEq s
      rw [Hsucc, List.take_add_one, Hy]
      simp [sp.strW, swift.setWidth_w8w]
    ipureintro; exact ⟨by word, by word⟩
  · have hj : (sint.Z j).toNat = c.val.length := by word
    have hl : vs.len = W64 (c.val.length : Int) := by word
    rw [hj, List.take_of_length_le (Nat.le_refl _)]
    wp_method_call
    wp_auto
    wp_method_call
    wp_auto
    wp_bind (ResolveProph _ _)
    iapply (swift.wp_resolveStep γ k p (.handle (sp.bal b) (toCmdId x) c) (⟨by have := swift.bal_lt b; omega, by unfold sp.CmdWf; rw [Hlen.1]; word⟩) Q _ _ ?hs)
    case hs =>
      have h : (((sint.Z b).toNat : Nat) : Int) = sint.Z b := Int.toNat_of_nonneg Hb
      rw [hS0]
      simp [sp.encP, sp.natW, sp.bal, h, sp.idW, toCmdId, sp.strW, sp.w32w, sp.cmdW, sp.wordsOf, sp.w8w, hl]
    iframe Hi Hupd
    iintro HQ
    wp_auto
    iapply HΦ
    iframe

/-- `resolvePreaccept(b, id, dep)`. -/
theorem swift.wp_resolvePreaccept (γ : sp.Names) (k : Nat) (b : w32) (x : swift.CommandId)
    (dsl : GoSlice) (D : List swift.CommandId) (Q : IProp netDistGF) :
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.client ∗
      client.nodeGhostOk γ (sp.PNode.rep k) ∗ ⌜0 ≤ sint.Z b⌝ ∗ dsl ↦*□ D ∗
      swift.resolveUpd γ k (.preaccept (sp.bal b) (toCmdId x) (D.map toCmdId)) Q }}
    (App (App (App (Val (@! swift.resolvePreaccept)) (Val #b)) (Val #x)) (Val #dsl))
  {{ RET #(); dsl ↦*□ D ∗ Q }} := by
  wp_start as ⟨#Hok, %Hb, #Hv, Hupd⟩
  ihave %Hlen := ownSlice_len $$ Hv
  iunfold client.nodeGhostOk at Hok
  iunfold client.nodeGhostB at Hok
  icases Hok with ⟨#Hreg, %p, #Hp, #Hi⟩
  simp only [client.nodeVar]
  wp_auto
  simp only [sp.strW1_eval]
  obtain ⟨S0, hS0⟩ : ∃ S0 : List w8, S0 = [] ++ sp.strW1 (W64 5) ++ sp.strW1 (W64 (sint.Z b)) ++
      sp.strW1 (W64 (uint.Z x.ClientId')) ++ sp.strW1 (W64 (uint.Z x.SeqNum')) ++
      sp.strW1 dsl.len := ⟨_, rfl⟩
  rw [← hS0]
  ihave IH : iprop(∃ (j : w64) (wv : w64),
      "i" ∷ j_ptr ↦ j ∗ "w" ∷ w_ptr ↦ wv ∗
      "s" ∷ s_ptr ↦ (S0 ++ sp.strW ((D.take (sint.Z j).toNat).flatMap (fun y => sp.idW (toCmdId y)))) ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ (D.length : Int)⌝) $$ [j w s]
  · iexists _, _
    iframe
    isplitl [s]
    · simp [sp.strW]; iexact s
    ipureintro; exact ⟨by word, by word⟩
  wp_for IH
  wp_if_destruct
  · have Hlt : (sint.Z j).toNat < D.length := by word
    obtain ⟨y, Hy⟩ : ∃ y, D[(sint.Z j).toNat]? = some y := ⟨_, List.getElem?_eq_getElem Hlt⟩
    simp only [show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z dsl.len from ⟨Hj.1, Hif⟩]
    icases ownSlice_elem_acc (sint.Z j) y dsl DFrac.discard D Hj.1 Hy $$ Hv with ⟨#Hel, -⟩
    iStructNamed Hel
    have hbd : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z dsl.len := ⟨Hj.1, Hif⟩
    wp_auto
    simp only [hbd]
    wp_auto
    try (simp only [hbd]; wp_auto)
    simp only [sp.strW1_eval]
    wp_for_post
    iframe
    iexists _, _
    iframe
    isplitl [s]
    · have Hsucc : (sint.Z (j + W64 1)).toNat = (sint.Z j).toNat + 1 := by word
      iExactEq s
      rw [Hsucc, List.take_add_one, Hy]
      simp [sp.strW, sp.idW, toCmdId, sp.w32w]
    ipureintro; exact ⟨by word, by word⟩
  · have hj : (sint.Z j).toNat = D.length := by word
    have hl : dsl.len = W64 (D.length : Int) := by word
    rw [hj, List.take_of_length_le (Nat.le_refl _)]
    wp_method_call
    wp_auto
    wp_method_call
    wp_auto
    wp_bind (ResolveProph _ _)
    iapply (swift.wp_resolveStep γ k p (.preaccept (sp.bal b) (toCmdId x) (D.map toCmdId)) (⟨by have := swift.bal_lt b; omega, by simp only [List.length_map]; rw [Hlen.1]; word⟩) Q _ _ ?hs)
    case hs =>
      have h : (((sint.Z b).toNat : Nat) : Int) = sint.Z b := Int.toNat_of_nonneg Hb
      rw [hS0]
      simp [sp.encP, sp.natW, sp.bal, h, sp.idW, toCmdId, sp.strW, sp.w32w, sp.listW, hl, List.flatMap_map]
    iframe Hi Hupd
    iintro HQ
    wp_auto
    iapply HΦ
    iframe Hv HQ

/-- The node's claimed prophecy from the descriptors' context. -/
theorem swift.DC.ctx_ng (c : swift.DC) : c.ctx ⊢ client.nodeGhostOk c.γ (sp.PNode.rep c.k) := by
  iintro #H
  iunfold swift.DC.ctx at H
  iunfold swift.descCtxE at H
  icases H with ⟨%me, %fr, %l, %dm, %dc, %ex, %dr, %oe, %γa, %γrm, %rc, %γrc, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, -, -, -, -, -, #Hng⟩
  iexact Hng

/-- The node's claimed prophecy from the run loop's context. -/
theorem swift.runCtxD_ng (γ : sp.Names) (γc γm γl γw γv γe γo : GName) (sn : swift.StN)
    (γdl : GName) (rp : Loc) (N r k : Nat) :
    swift.runCtxD γ γc γm γl γw γv γe γo sn γdl rp N r k ⊢ client.nodeGhostOk γ (sp.PNode.rep k) := by
  iintro #H
  iunfold swift.runCtxD at H
  icases H with ⟨%rr, %me, %fr, %l, %dm, -, -, -, -, -, -, -, -, -, -, #Hng⟩
  iexact Hng

end proof

end Perennial.github_com.imdea_software.swiftpaxos
