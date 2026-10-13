module

public import Spec.go_etcd_io.etcd.pkg.v3.adt.intervalNode__min

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.pkg.v3.adt

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.adt.Assumptions]

theorem adt.intervalNode.min.wp_proof : adt.intervalNode.min.spec (GF := GF) (hG := hG) := by
  intro x0 s p0 T0 hT0
  wp_start as Hn
  wp_auto
  ihave HI : (∃ (y yp : Loc) (A : adt.RbCtx adt.Entry) (ls : List (Loc × Loc))
      (Ty : adt.RbT adt.Entry),
      "x" ∷ x_ptr ↦ y ∗ "HA" ∷ adt.ownPathAt s 1 A ls y yp Ty.maxEnd ∗
      "Hy" ∷ adt.ownNode s 1 yp y Ty ∗
      "%Hinv" ∷ ⌜adt.topAt A ls y yp = (x0, p0) ∧ A.plug Ty = T0 ∧ A.AllL ∧ Ty ≠ .leaf⌝ :
      IProp GF) $$ [x Hn]
  · iexists x0, p0, .top, [], T0
    rw [adt.ownPathAt_top]
    iframe
    isplitl []
    · ipureintro; trivial
    ipureintro; simp_all [adt.RbCtx.AllL]
  wp_for HI
  obtain ⟨Htop, Hplug, Hall, Hne⟩ := Hinv
  cases Ty with
  | leaf => exact absurd rfl Hne
  | node c l e r =>
  icases adt.ownNode_node_open _ _ _ _ _ _ _ _ $$ Hy with
    ⟨%lp, %rp, %Hyn, Hiv, Hmx, Hl, Hr, Hp, Hc, Hnl, Hnr⟩
  wp_auto
  have hvb : decide ((#false : val) = #true) = false :=
    decide_eq_false (fun h => Bool.false_ne_true (go.intoVal_inj h))
  by_cases hls : lp = s
  · -- no left child: `y` is the leftmost node
    rw [hls]
    simp only [_root_.decide_true, Bool.not_true, hvb, Bool.false_eq_true, ↓reduceIte]
    cases l with
    | node cl ll el rl =>
      icases adt.ownNode_node_open _ _ _ _ _ _ _ _ $$ Hnl with ⟨%a, %b, %Hn, -⟩
      exact absurd rfl Hn.1
    | leaf =>
    wp_auto
    iapply HΦ
    iexists A, ls, yp, c, e, r
    simp only [adt.maxEnd_node]
    iframe HA
    isplitl [Hiv Hmx Hl Hr Hp Hc Hnl Hnr]
    · iapply adt.ownNode_node_close
      iexists s, rp
      iframe
      ipureintro; exact Hyn
    ipureintro; exact ⟨Htop, Hplug, Hall⟩
  · simp only [decide_false, hls, Bool.not_false, _root_.decide_true, ↓reduceIte]
    cases l with
    | leaf =>
      icases adt.ownNode_leaf_open _ _ _ _ $$ Hnl with %Hn
      exact absurd Hn hls
    | node cl ll el rl =>
    wp_auto
    wp_for_post
    iframe
    iexists lp, y, .inL c A e r, (yp, rp) :: ls, .node cl ll el rl
    iframe Hnl
    ihave HA := adt.ownPathAt_push_inL _ 1 A ls y yp c (.node cl ll el rl) e r lp rp Hyn $$
      [HA Hiv Hmx Hl Hr Hp Hc Hnr]
    · iframe
    iframe
    ipureintro
    exact ⟨Htop, by rw [← Hplug]; rfl, Hall, by simp⟩

end proof

end EtcdGrove
end Perennial
