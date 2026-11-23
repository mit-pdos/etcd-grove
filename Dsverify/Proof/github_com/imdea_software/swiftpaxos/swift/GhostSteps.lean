/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/GhostSteps.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
L2 (notes/prove-s2-e.md, item 4): the specs of the swift package's ghost step resolvers
(fork db37a86, swift/ghost.go): each builds its event's words (`sp.encP e`) and resolves them on
the node's ghost (`client.GhostStep`); the caller's update runs at the last word with the node's
half of its future words (`sp.predPre` / `sp.predPost`, Steps.lean). A site proof calls the
resolver with its step lemma (a `swift.*_stepD`) inside the update.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.Steps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.client.Ghost
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.HashLeaf
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.AcksSpecs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.RunCtx

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section defs
variable [GoGlobalContext] [G : GooseGlobalGS .hasLC netDistGF]

/-- **A site's ghost update** at replica node `k`'s step `e`: with the node's half of its future
words starting with `e`'s, give back the rest and `Q`. -/
def swift.ghostUpd (γ : sp.Names) (k : Nat) (e : sp.PEv) (Q : IProp netDistGF) : IProp netDistGF :=
  iprop(∀ W' : List w64, sp.predPre γ k (some (e, W')) ={⊤}=∗ sp.predPost γ k (some (e, W')) ∗ Q)

end defs

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [swift.Assumptions] [client.Assumptions]

set_option goose.wp.extras true

/-- From a site's update to `GhostStep`'s (the words' bound `PEvWf e`). -/
theorem swift.ghostUpd_step (γ : sp.Names) (k : Nat) (e : sp.PEv) (Q : IProp netDistGF)
    (he : sp.PEvWf e) :
    swift.ghostUpd γ k e Q ⊢
      ∀ W' : List w64, ghostMapElem γ.pred (sp.PNode.rep k) (DFrac.own (1 : Qp).half)
        (sp.encP e ++ W') ={⊤}=∗
        ghostMapElem γ.pred (sp.PNode.rep k) (DFrac.own (1 : Qp).half) W' ∗ Q := by
  iintro Hupd %W' Hw
  iunfold swift.ghostUpd at Hupd
  simp only [sp.predPre_some, sp.predPost_some]
  imod Hupd $$ %W' [Hw] with ⟨Hp, HQ⟩
  · iframe Hw; ipureintro; exact he
  imodintro
  iframe

/-- `client.GhostStep(ws)` on a fresh slice of `e`'s words, from a site's update. -/
theorem swift.ghostStep_slice (γ : sp.Names) (k : Nat) (e : sp.PEv) (Q : IProp netDistGF)
    (he : sp.PEvWf e) (sl : GoSlice) (Φ : val → IProp netDistGF) :
    isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.client ∗
      client.nodeGhostOk γ (sp.PNode.rep k) ∗ sl ↦* sp.encP e ∗ swift.ghostUpd γ k e Q ∗
      (Q -∗ Φ #()) ⊢
    WP (App (Val (@! client.GhostStep)) (Val #sl)) {{ Φ }} := by
  iintro ⟨#Hpkg, #Hok, Hsl, Hupd, HΦ⟩
  imod ownSlice_persist $$ Hsl with #Hsl
  iapply (client.GhostStep.wp_proof (hG := hG) γ (sp.PNode.rep k) e sl Q) $$ [Hupd]
  · iframe Hpkg Hok Hsl
    iapply (swift.ghostUpd_step γ k e Q he) $$ Hupd
  inext
  iexact HΦ

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

/-- `ghostNewBallot(b)`. -/
theorem swift.wp_ghostNewBallot (γ : sp.Names) (k : Nat) (b : w32) (Q : IProp netDistGF) :
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.client ∗
      client.nodeGhostOk γ (sp.PNode.rep k) ∗ ⌜0 ≤ sint.Z b⌝ ∗
      swift.ghostUpd γ k (.newBallot (sp.bal b)) Q }}
    (App (Val (@! swift.ghostNewBallot)) (Val #b))
  {{ RET #(); Q }} := by
  wp_start as ⟨#Hok, %Hb, Hupd⟩
  wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.uint64))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := w64) (t := go.uint64) (sp.encP (.newBallot (sp.bal b)))
  wp_auto
  isplitl []
  · ipureintro
    have h : (((sint.Z b).toNat : Nat) : Int) = sint.Z b := Int.toNat_of_nonneg Hb
    simp [sp.encP, sp.natW, sp.bal, h]
    rfl
  iintro %sp_ ⟨Hl, -⟩
  wp_auto
  wp_bind (App (Val (@! client.GhostStep)) (Val _))
  iapply (swift.ghostStep_slice γ k _ Q (swift.bal_wf b) _ _)
  iframe Hpkg2 Hok Hl Hupd
  iintro HQ
  wp_auto
  iapply HΦ
  iexact HQ

/-- `ghostTakeSync(b)`. -/
theorem swift.wp_ghostTakeSync (γ : sp.Names) (k : Nat) (b : w32) (Q : IProp netDistGF) :
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.client ∗
      client.nodeGhostOk γ (sp.PNode.rep k) ∗ ⌜0 ≤ sint.Z b⌝ ∗
      swift.ghostUpd γ k (.takeSync (sp.bal b)) Q }}
    (App (Val (@! swift.ghostTakeSync)) (Val #b))
  {{ RET #(); Q }} := by
  wp_start as ⟨#Hok, %Hb, Hupd⟩
  wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.uint64))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := w64) (t := go.uint64) (sp.encP (.takeSync (sp.bal b)))
  wp_auto
  isplitl []
  · ipureintro
    have h : (((sint.Z b).toNat : Nat) : Int) = sint.Z b := Int.toNat_of_nonneg Hb
    simp [sp.encP, sp.natW, sp.bal, h]
    rfl
  iintro %sp_ ⟨Hl, -⟩
  wp_auto
  wp_bind (App (Val (@! client.GhostStep)) (Val _))
  iapply (swift.ghostStep_slice γ k (.takeSync (sp.bal b)) Q
    (by show sp.bal b < 2 ^ 64; have := swift.bal_lt b; omega) _ _)
  iframe Hpkg2 Hok Hl Hupd
  iintro HQ
  wp_auto
  iapply HΦ
  iexact HQ

/-- `ghostAccept(b, id)`. -/
theorem swift.wp_ghostAccept (γ : sp.Names) (k : Nat) (b : w32) (x : swift.CommandId)
    (Q : IProp netDistGF) :
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.client ∗
      client.nodeGhostOk γ (sp.PNode.rep k) ∗ ⌜0 ≤ sint.Z b⌝ ∗
      swift.ghostUpd γ k (.accept (sp.bal b) (toCmdId x)) Q }}
    (App (App (Val (@! swift.ghostAccept)) (Val #b)) (Val #x))
  {{ RET #(); Q }} := by
  wp_start as ⟨#Hok, %Hb, Hupd⟩
  wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.uint64))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := w64) (t := go.uint64) (sp.encP (.accept (sp.bal b) (toCmdId x)))
  wp_auto
  isplitl []
  · ipureintro
    have h : (((sint.Z b).toNat : Nat) : Int) = sint.Z b := Int.toNat_of_nonneg Hb
    simp [sp.encP, sp.natW, sp.bal, h, sp.idW, toCmdId, swift.setWidth_w32w]
    rfl
  iintro %sp_ ⟨Hl, -⟩
  wp_auto
  wp_bind (App (Val (@! client.GhostStep)) (Val _))
  iapply (swift.ghostStep_slice γ k (.accept (sp.bal b) (toCmdId x)) Q
    (by show sp.bal b < 2 ^ 64; have := swift.bal_lt b; omega) _ _)
  iframe Hpkg2 Hok Hl Hupd
  iintro HQ
  wp_auto
  iapply HΦ
  iexact HQ

/-- `ghostCommit(b, id)`. -/
theorem swift.wp_ghostCommit (γ : sp.Names) (k : Nat) (b : w32) (x : swift.CommandId)
    (Q : IProp netDistGF) :
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.client ∗
      client.nodeGhostOk γ (sp.PNode.rep k) ∗ ⌜0 ≤ sint.Z b⌝ ∗
      swift.ghostUpd γ k (.commit (sp.bal b) (toCmdId x)) Q }}
    (App (App (Val (@! swift.ghostCommit)) (Val #b)) (Val #x))
  {{ RET #(); Q }} := by
  wp_start as ⟨#Hok, %Hb, Hupd⟩
  wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.uint64))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := w64) (t := go.uint64) (sp.encP (.commit (sp.bal b) (toCmdId x)))
  wp_auto
  isplitl []
  · ipureintro
    have h : (((sint.Z b).toNat : Nat) : Int) = sint.Z b := Int.toNat_of_nonneg Hb
    simp [sp.encP, sp.natW, sp.bal, h, sp.idW, toCmdId, swift.setWidth_w32w]
    rfl
  iintro %sp_ ⟨Hl, -⟩
  wp_auto
  wp_bind (App (Val (@! client.GhostStep)) (Val _))
  iapply (swift.ghostStep_slice γ k (.commit (sp.bal b) (toCmdId x)) Q
    (by show sp.bal b < 2 ^ 64; have := swift.bal_lt b; omega) _ _)
  iframe Hpkg2 Hok Hl Hupd
  iintro HQ
  wp_auto
  iapply HΦ
  iexact HQ

/-- `ghostId(ws, id)`: the id's two words appended. -/
theorem swift.wp_ghostId (sl : GoSlice) (l : List w64) (x : swift.CommandId) :
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      sl ↦* l ∗ ownSliceCap w64 sl (DFrac.own 1) }}
    (App (App (Val (@! swift.ghostId)) (Val #sl)) (Val #x))
  {{ (s' : GoSlice), RET #s'; s' ↦* (l ++ sp.idW (toCmdId x)) ∗ ownSliceCap w64 s' (DFrac.own 1) }} := by
  wp_start as ⟨Hsl, Hcap⟩
  wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.uint64))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := w64) (t := go.uint64) (sp.idW (toCmdId x))
  wp_auto
  isplitl []
  · ipureintro
    simp [sp.idW, toCmdId, swift.setWidth_w32w]
    rfl
  iintro %lp ⟨Hl, -⟩
  wp_auto
  wp_apply wp_slice_append $$ [Hsl Hcap Hl] as %s' ⟨Hs, Hc, -⟩
  · iframe
  iapply HΦ
  iframe

/-- `ghostIds(ws, ids)`: the list's length, then each id's words. -/
theorem swift.wp_ghostIds (sl : GoSlice) (l : List w64) (isl : GoSlice) (L : List swift.CommandId)
    (dq : DFrac) :
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      sl ↦* l ∗ ownSliceCap w64 sl (DFrac.own 1) ∗ isl ↦*{dq} L }}
    (App (App (Val (@! swift.ghostIds)) (Val #sl)) (Val #isl))
  {{ (s' : GoSlice), RET #s'; s' ↦* (l ++ sp.listW sp.idW (L.map toCmdId)) ∗
      ownSliceCap w64 s' (DFrac.own 1) ∗ isl ↦*{dq} L }} := by
  wp_start as ⟨Hsl, Hcap, Hisl⟩
  ihave %Hlen := ownSlice_len $$ Hisl
  wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.uint64))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := w64) (t := go.uint64) [W64 (L.length : Int)]
  wp_auto
  isplitl []
  · ipureintro
    have : isl.len = W64 (L.length : Int) := by have := Hlen.1; word
    rw [this]
  iintro %lp ⟨Hl, -⟩
  wp_auto
  wp_apply wp_slice_append $$ [Hsl Hcap Hl] as %s1 ⟨Hs, Hc, -⟩
  · iframe
  wp_auto
  ihave IH : iprop(∃ (n : w64) (s2 : GoSlice) (iv : swift.CommandId),
      "i" ∷ i_ptr ↦ n ∗ "id" ∷ id_ptr ↦ iv ∗ "ws" ∷ ws_ptr ↦ s2 ∗
      "Hs" ∷ s2 ↦* (l ++ [W64 (L.length : Int)] ++
        (L.take (sint.Z n).toNat).flatMap (fun y => sp.idW (toCmdId y))) ∗
      "Hc" ∷ ownSliceCap w64 s2 (DFrac.own 1) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (L.length : Int)⌝) $$ [i id ws Hs Hc]
  · iexists _, _, _
    iframe
    isplitl [Hs]
    · simp; iexact Hs
    ipureintro; exact ⟨by word, by word⟩
  wp_for IH
  wp_if_destruct
  · have hlt : sint.Z n < sint.Z isl.len := by
      first | exact Hif | exact of_decide_eq_true (go.intoVal_inj Hif)
    have Hlt : (sint.Z n).toNat < L.length := by have := Hlen.1; word
    obtain ⟨y, Hy⟩ : ∃ y, L[(sint.Z n).toNat]? = some y := ⟨_, List.getElem?_eq_getElem Hlt⟩
    rw [ite_eq_left ⟨Hn.1, hlt⟩]
    wp_apply wp_load_slice_index isl (sint.Z n) L dq y Hn.1 $$ [Hisl] as Hisl
    · iframe; ipureintro; exact Hy
    wp_apply swift.wp_ghostId $$ [Hs Hc] as %s3 ⟨Hs, Hc⟩
    · iframe
    wp_for_post
    iframe
    iexists _, _, _
    iframe
    isplitl [Hs]
    · have Hsucc : (sint.Z (n + W64 1)).toNat = (sint.Z n).toNat + 1 := by word
      rw [Hsucc, List.take_succ, Hy]
      simp only [Option.toList_some, List.flatMap_append, List.flatMap_singleton,
        List.append_assoc]
      iexact Hs
    ipureintro; exact ⟨by word, by word⟩
  · have hge : ¬ sint.Z n < sint.Z isl.len := by
      first | exact Hif | exact fun h => absurd (go.intoVal_inj Hif) (by simp [h])
    have hk : (sint.Z n).toNat = L.length := by have := Hlen.1; word
    try rw [if_pos (by simp [hge])]
    try wp_auto
    iapply HΦ
    iframe
    rw [hk, List.take_of_length_le (Nat.le_refl _)] at *
    simp [sp.listW, List.flatMap_map]
    iexact Hs

theorem swift.encP_preaccept (b : Nat) (x : sp.CmdId) (D : List sp.CmdId) :
    sp.encP (.preaccept b x D) =
      [W64 5, sp.natW b] ++ sp.idW x ++ sp.listW sp.idW D := by
  simp [sp.encP]

/-- `ghostPreaccept(b, id, dep)`. -/
theorem swift.wp_ghostPreaccept (γ : sp.Names) (k : Nat) (b : w32) (x : swift.CommandId)
    (dsl : GoSlice) (D : List swift.CommandId) (dq : DFrac) (Q : IProp netDistGF) :
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.client ∗
      client.nodeGhostOk γ (sp.PNode.rep k) ∗ ⌜0 ≤ sint.Z b⌝ ∗ dsl ↦*{dq} D ∗
      swift.ghostUpd γ k (.preaccept (sp.bal b) (toCmdId x) (D.map toCmdId)) Q }}
    (App (App (App (Val (@! swift.ghostPreaccept)) (Val #b)) (Val #x)) (Val #dsl))
  {{ RET #(); dsl ↦*{dq} D ∗ Q }} := by
  wp_start as ⟨#Hok, %Hb, Hd, Hupd⟩
  ihave %Hlen := ownSlice_len $$ Hd
  try wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.uint64))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := w64) (t := go.uint64) [W64 5, sp.natW (sp.bal b)]
  try wp_auto
  isplitl []
  · ipureintro
    have h : (((sint.Z b).toNat : Nat) : Int) = sint.Z b := Int.toNat_of_nonneg Hb
    simp [sp.natW, sp.bal, h]
    rfl
  iintro %lp ⟨Hl, Hc⟩
  try wp_auto
  wp_apply swift.wp_ghostId $$ [Hl Hc] as %s1 ⟨Hs, Hc⟩
  · iframe
  try wp_auto
  wp_apply swift.wp_ghostIds $$ [Hs Hc Hd] as %s2 ⟨Hs, Hc, Hd⟩
  · iframe
  try wp_auto
  wp_bind (App (Val (@! client.GhostStep)) (Val _))
  iapply (swift.ghostStep_slice γ k (.preaccept (sp.bal b) (toCmdId x) (D.map toCmdId)) Q
    ⟨by have := swift.bal_lt b; omega, by simp only [List.length_map]; rw [Hlen.1]; word⟩ _ _)
  rw [swift.encP_preaccept]
  iframe Hpkg2 Hok Hs Hupd
  iintro HQ
  try wp_auto
  iapply HΦ
  iframe

theorem swift.setWidth_w8w (n : w8) : BitVec.setWidth 64 n = sp.w8w n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, sp.w8w]
  have := n.isLt
  rw [show (W64 (n.toNat : Int)).toNat = n.toNat from by
    simp only [W64, BitVec.toNat_ofInt]; omega]
  omega

/-- `ghostCmd(ws, c)`: the command's op, key, value length and bytes appended. -/
theorem swift.wp_ghostCmd (sl : GoSlice) (l : List w64) (c : sp.Cmd) (vs : GoSlice) (dq : DFrac) :
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      sl ↦* l ∗ ownSliceCap w64 sl (DFrac.own 1) ∗ vs ↦*{dq} c.val }}
    (App (App (Val (@! swift.ghostCmd)) (Val #sl)) (Val #(state.Command.mk c.op c.key vs)))
  {{ (s' : GoSlice), RET #s'; s' ↦* (l ++ sp.cmdW c) ∗ ownSliceCap w64 s' (DFrac.own 1) ∗
      vs ↦*{dq} c.val }} := by
  wp_start as ⟨Hsl, Hcap, Hv⟩
  ihave %Hlen := ownSlice_len $$ Hv
  wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.uint64))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := w64) (t := go.uint64) [sp.w8w c.op, c.key, W64 (c.val.length : Int)]
  wp_auto
  isplitl []
  · ipureintro
    have : vs.len = W64 (c.val.length : Int) := by have := Hlen.1; word
    rw [this]
    simp [sp.w8w]
    rfl
  iintro %lp ⟨Hl, -⟩
  wp_auto
  wp_apply wp_slice_append $$ [Hsl Hcap Hl] as %s1 ⟨Hs, Hc, -⟩
  · iframe
  try wp_auto
  ihave IH : iprop(∃ (n : w64) (s2 : GoSlice) (bv : w8),
      "i" ∷ i_ptr ↦ n ∗ "b" ∷ b_ptr ↦ bv ∗ "ws" ∷ ws_ptr ↦ s2 ∗
      "Hs" ∷ s2 ↦* (l ++ [sp.w8w c.op, c.key, W64 (c.val.length : Int)] ++
        (c.val.take (sint.Z n).toNat).map sp.w8w) ∗
      "Hc" ∷ ownSliceCap w64 s2 (DFrac.own 1) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (c.val.length : Int)⌝) $$ [i b ws Hs Hc]
  · iexists _, _, _
    iframe
    isplitl [Hs]
    · simp; iexact Hs
    ipureintro; exact ⟨by word, by word⟩
  wp_for IH
  wp_if_destruct
  · have hlt : sint.Z n < sint.Z vs.len := by
      first | exact Hif | exact of_decide_eq_true (go.intoVal_inj Hif)
    have Hlt : (sint.Z n).toNat < c.val.length := by have := Hlen.1; word
    obtain ⟨y, Hy⟩ : ∃ y, c.val[(sint.Z n).toNat]? = some y := ⟨_, List.getElem?_eq_getElem Hlt⟩
    try rw [ite_eq_left ⟨Hn.1, hlt⟩]
    wp_apply wp_load_slice_index vs (sint.Z n) c.val dq y Hn.1 $$ [Hv] as Hv
    · iframe; ipureintro; exact Hy
    try wp_auto
    wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.uint64))))
      (Val (LiteralValueV _)))
    iapply wp_slice_literal (V := w64) (t := go.uint64) [sp.w8w y]
    wp_auto
    isplitl []
    · ipureintro; simp [sp.w8w]; try rfl
    iintro %lq ⟨Hq, -⟩
    wp_auto
    wp_apply wp_slice_append $$ [Hs Hc Hq] as %s3 ⟨Hs, Hc, -⟩
    · iframe
    wp_for_post
    iframe
    iexists _, _, _
    iframe
    isplitl [Hs]
    · have Hsucc : (sint.Z (n + W64 1)).toNat = (sint.Z n).toNat + 1 := by word
      rw [Hsucc, List.take_succ, Hy]
      simp only [Option.toList_some, List.map_append, List.map_cons, List.map_nil,
        List.append_assoc]
      iexact Hs
    ipureintro; exact ⟨by word, by word⟩
  · have hge : ¬ sint.Z n < sint.Z vs.len := by
      first | exact Hif | exact fun h => absurd (go.intoVal_inj Hif) (by simp [h])
    have hk : (sint.Z n).toNat = c.val.length := by have := Hlen.1; word
    try rw [if_pos (by simp [hge])]
    try wp_auto
    iapply HΦ
    iframe
    rw [hk, List.take_of_length_le (Nat.le_refl _)] at *
    simp [sp.cmdW, sp.wordsOf]
    iexact Hs

theorem swift.encP_handle (b : Nat) (x : sp.CmdId) (c : sp.Cmd) :
    sp.encP (.handle b x c) = [W64 4, sp.natW b] ++ sp.idW x ++ sp.cmdW c := by
  simp [sp.encP]

/-- `ghostHandle(b, id, c)`. -/
theorem swift.wp_ghostHandle (γ : sp.Names) (k : Nat) (b : w32) (x : swift.CommandId)
    (c : sp.Cmd) (vs : GoSlice) (dq : DFrac) (Q : IProp netDistGF) :
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.client ∗
      client.nodeGhostOk γ (sp.PNode.rep k) ∗ ⌜0 ≤ sint.Z b⌝ ∗ vs ↦*{dq} c.val ∗
      swift.ghostUpd γ k (.handle (sp.bal b) (toCmdId x) c) Q }}
    (App (App (App (Val (@! swift.ghostHandle)) (Val #b)) (Val #x))
      (Val #(state.Command.mk c.op c.key vs)))
  {{ RET #(); vs ↦*{dq} c.val ∗ Q }} := by
  wp_start as ⟨#Hok, %Hb, Hv, Hupd⟩
  ihave %Hlen := ownSlice_len $$ Hv
  try wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.uint64))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := w64) (t := go.uint64) [W64 4, sp.natW (sp.bal b)]
  try wp_auto
  isplitl []
  · ipureintro
    have h : (((sint.Z b).toNat : Nat) : Int) = sint.Z b := Int.toNat_of_nonneg Hb
    simp [sp.natW, sp.bal, h]
    rfl
  iintro %lp ⟨Hl, Hc⟩
  try wp_auto
  wp_apply swift.wp_ghostId $$ [Hl Hc] as %s1 ⟨Hs, Hc⟩
  · iframe
  try wp_auto
  wp_apply swift.wp_ghostCmd $$ [Hs Hc Hv] as %s2 ⟨Hs, Hc, Hv⟩
  · iframe
  try wp_auto
  wp_bind (App (Val (@! client.GhostStep)) (Val _))
  iapply (swift.ghostStep_slice γ k (.handle (sp.bal b) (toCmdId x) c) Q
    ⟨by have := swift.bal_lt b; omega, by unfold sp.CmdWf; rw [Hlen.1]; word⟩ _ _)
  rw [swift.encP_handle]
  iframe Hpkg2 Hok Hs Hupd
  iintro HQ
  try wp_auto
  iapply HΦ
  iframe

/-- The node's claimed ghost from the descriptors' context. -/
theorem swift.DC.ctx_ng (c : swift.DC) : c.ctx ⊢ client.nodeGhostOk c.γ (sp.PNode.rep c.k) := by
  iintro #H
  iunfold swift.DC.ctx at H
  iunfold swift.descCtxE at H
  icases H with ⟨%me, %fr, %l, %dm, %dc, %ex, %dr, %oe, %γa, %γrm, %rc, %γrc, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, -, -, -, -, -, #Hng⟩
  iexact Hng

/-- The node's claimed ghost from the run loop's context. -/
theorem swift.runCtxD_ng (γ : sp.Names) (γc γm γl γw γv γe γo : GName) (sn : swift.StN)
    (γdl : GName) (rp : Loc) (N r k : Nat) :
    swift.runCtxD γ γc γm γl γw γv γe γo sn γdl rp N r k ⊢ client.nodeGhostOk γ (sp.PNode.rep k) := by
  iintro #H
  iunfold swift.runCtxD at H
  icases H with ⟨%rr, %me, %fr, %l, %dm, -, -, -, -, -, -, -, -, -, -, #Hng⟩
  iexact Hng

end proof

end Perennial.github_com.imdea_software.swiftpaxos
