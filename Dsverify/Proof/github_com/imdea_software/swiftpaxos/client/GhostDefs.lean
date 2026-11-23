/-
The definitions, specs and lemmas of `Ghost.lean` that its proofs do not need (split out for the import tiers, CLAUDE.md "Import tiers": its importers that are not linking modules import this module, and see no proof).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.client.L2Laws
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.client.ISpecs
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.client.NodeGhost
public import Perennial.Proof.github_com.goose_lang.primitive.Link

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

/-- `theGhost()`: the node's ghost, claimed for `n`. -/
abbrev client.theGhost.specG : Prop :=
  ∀ (γ : sp.Names) (n : sp.PNode),
  {{ client.nodeGhostB γ n }}
    (App (Val (@! client.theGhost)) (Val #()))
  {{ (g : Loc), RET #g; client.isNodeGhost γ n g }}

/-- `g.Invoke(op, cl, seq, key, val)`: client `cl` (predicted node `cl (clOf x)`, whose ghost
`g` is) invokes command `x = (cl, seq)`, `c = (op, key, val)` with its update: registered, the
update deposited (`pend`). -/
abbrev client.Ghost.Invoke.specG : Prop :=
  ∀ (g : Loc) (γ : sp.Names) (γc γm γl : GName) (x : sp.CmdId) (c : sp.Cmd) (vsl : GoSlice)
    (Ψ : List w8 → IProp netDistGF),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.client ∗
      client.isNodeGhost γ (sp.PNode.cl (sp.clOf x)) g ∗ sp.inv γ γc γm γl ∗
      sp.allPredsReg γ γc ∗ sp.clientSeq γ x.cl x.seq.toNat ∗
      sp.cmdAU γl c Ψ ∗ vsl ↦*□ c.val ∗
      ⌜x.cl.toInt ≥ 1 ∧ (c.isPut ∨ c.isGet) ∧ c.val.length < 2 ^ 16 ∧ 0 ≤ x.seq.toInt ∧
        x.seq.toNat < 2 ^ 10⌝ }}
    (App (App (App (App (App (Val (g @!! go.GoType.PointerType client.Ghost.ty @!! go!"Invoke"))
      (Val #c.op)) (Val #x.cl)) (Val #x.seq)) (Val #c.key)) (Val #vsl))
  {{ RET #(); sp.cmdIs γ x c ∗ sp.clientSeq γ x.cl (x.seq.toNat + 1) ∗ sp.pend γ x Ψ }}

/-- `g.Accept(cl, seq, val)`: client `cl` accepts command `x = (cl, seq)` with its decided result
`v`: its continuation applied to `v`. -/
abbrev client.Ghost.Accept.specG : Prop :=
  ∀ (g : Loc) (γ : sp.Names) (γc γm γl : GName) (x : sp.CmdId) (v : List w8)
    (vsl : GoSlice) (Ψ : List w8 → IProp netDistGF),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.client ∗
      client.isNodeGhost γ (sp.PNode.cl (sp.clOf x)) g ∗ sp.inv γ γc γm γl ∗ sp.pend γ x Ψ ∗
      sp.doneRes γ x v ∗ vsl ↦*□ v }}
    (App (App (App (Val (g @!! go.GoType.PointerType client.Ghost.ty @!! go!"Accept"))
      (Val #x.cl)) (Val #x.seq)) (Val #vsl))
  {{ RET #(); ▷ Ψ v }}

/-- `g.Step(ws)` (a replica's protocol event `e`, its words `ws = encP e`): lock, resolve the
words, unlock; at the last word the caller's ghost update runs with the node's half of its future
words (which then start with `e`'s). -/
abbrev client.Ghost.Step.specG : Prop :=
  ∀ (g : Loc) (γ : sp.Names) (n : sp.PNode) (e : sp.PEv) (wsl : GoSlice) (Q : IProp netDistGF),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.client ∗
      client.isNodeGhost γ n g ∗ wsl ↦*□ sp.encP e ∗
      (∀ W' : List w64, ghostMapElem γ.pred n (DFrac.own (1 : Qp).half) (sp.encP e ++ W') ={⊤}=∗
        ghostMapElem γ.pred n (DFrac.own (1 : Qp).half) W' ∗ Q) }}
    (App (Val (g @!! go.GoType.PointerType client.Ghost.ty @!! go!"Step")) (Val #wsl))
  {{ RET #(); Q }}

set_option goose.wp.extras true

/-- The prophecy type is not an interface (for `MethodResolve` on `ProphId`'s value methods). -/
instance notInterface_prophId : go.NotInterface go.prophId := by
  unfold go.prophId; exact ⟨trivial⟩

/-- `g.p.ResolveU64(w)`. -/
theorem client.Ghost.resolveField.wp (g : Loc) (p : proph_id) (pvs : List val) (w : w64) :
  {{ structFieldRef client.Ghost go!"p" g ↦□ p ∗ proph p pvs }}
    (App (Val (structFieldRef client.Ghost go!"p" g @!!
      go.GoType.PointerType github_com.goose_lang.primitive.ProphId.ty @!! go!"ResolveU64"))
      (Val #w))
  {{ (pvs' : List val), RET #(); ⌜pvs = #w :: pvs'⌝ ∗ proph p pvs' }} := by
  wp_start as ⟨#Hp, Hpr⟩
  wp_auto
  wp_apply github_com.goose_lang.primitive.ProphId.wp_ResolveU64 $$ [Hpr] as %pvs' ⟨%Hpvs, Hpr⟩
  · iexact Hpr
  iapply HΦ
  iframe Hpr
  ipureintro; exact Hpvs

theorem client.Ghost.resolveBytes.wp (g : Loc) (p : proph_id) (pvs : List val) (vsl : GoSlice)
    (bs : List w8) :
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.client ∗
      structFieldRef client.Ghost go!"p" g ↦□ p ∗ proph p pvs ∗ vsl ↦*□ bs }}
    (App (Val (g @!! go.GoType.PointerType client.Ghost.ty @!! go!"resolveBytes")) (Val #vsl))
  {{ RET #(); ∃ pvs', ⌜pvs = (sp.wordsOf bs).map (fun w => (#w : val)) ++ pvs'⌝ ∗
      proph p pvs' }} := by
  wp_start as ⟨#Hp, Hpr, #Hv⟩
  wp_auto
  wp_apply client.Ghost.resolveField.wp $$ [Hpr] as %pvs1 ⟨%Hpvs1, Hpr⟩
  · iframe Hp Hpr
  wp_auto
  ihave %Hlen := ownSlice_len $$ Hv
  ihave IH : iprop(∃ (n : w64) (pv : List val) (bv : w8),
      "i" ∷ i_ptr ↦ n ∗ "b" ∷ b_ptr ↦ bv ∗ "Hpr" ∷ proph p pv ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (bs.length : Int)⌝ ∗
      "%Hpv" ∷ ⌜pvs1 = (bs.take (sint.Z n).toNat).map (fun b => (#(sp.w8w b) : val)) ++ pv⌝)
      $$ [i b Hpr]
  · iexists _, _, _
    iframe
    ipureintro
    exact ⟨⟨by word, by word⟩, by simp⟩
  wp_for IH
  wp_if_destruct
  · have Hlt : (sint.Z n).toNat < bs.length := by word
    obtain ⟨x, Hx⟩ : ∃ x, bs[(sint.Z n).toNat]? = some x :=
      ⟨_, List.getElem?_eq_getElem Hlt⟩
    simp only [show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z vsl.len from ⟨Hn.1, Hif⟩]
    wp_apply wp_load_slice_index vsl (sint.Z n) bs DFrac.discard x Hn.1 $$ [] as -
    · iframe Hv; ipureintro; exact Hx
    wp_apply client.Ghost.resolveField.wp $$ [Hpr] as %pv2 ⟨%Hpv2, Hpr⟩
    · iframe Hp Hpr
    wp_for_post
    iframe
    iexists _, _, _
    iframe
    ipureintro
    refine ⟨⟨by word, by word⟩, ?_⟩
    have Hsucc : (sint.Z (n + W64 1)).toNat = (sint.Z n).toNat + 1 := by word
    rw [Hsucc, Hpv, Hpv2, List.take_succ, Hx]
    simp [sp.w8w]
  · have hk : (sint.Z n).toNat = bs.length := by word
    have hl : vsl.len = W64 (bs.length : Int) := by word
    iapply HΦ
    iexists pv
    iframe Hpr
    ipureintro
    rw [Hpvs1, Hpv, hk, List.take_of_length_le (Nat.le_refl _), hl]
    simp [sp.wordsOf]

/-- `client.GhostStep(ws)` (L2: a replica's protocol event `e`, its words `ws`): the node's
ghost's `Step`, on the node's claimed ghost (`client.nodeGhostOk`). -/
abbrev client.GhostStep.specG : Prop :=
  ∀ (γ : sp.Names) (n : sp.PNode) (e : sp.PEv) (wsl : GoSlice) (Q : IProp netDistGF),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.client ∗
      client.nodeGhostOk γ n ∗ wsl ↦*□ sp.encP e ∗
      (∀ W' : List w64, ghostMapElem γ.pred n (DFrac.own (1 : Qp).half) (sp.encP e ++ W') ={⊤}=∗
        ghostMapElem γ.pred n (DFrac.own (1 : Qp).half) W' ∗ Q) }}
    (App (Val (@! client.GhostStep)) (Val #wsl))
  {{ RET #(); Q }}

end spec

end Perennial.github_com.imdea_software.swiftpaxos
