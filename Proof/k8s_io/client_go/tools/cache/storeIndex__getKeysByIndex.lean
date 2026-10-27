/-
Proof of `Spec/k8s_io/client_go/tools/cache/storeIndex__getKeysByIndex.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.tools.cache.storeIndex__getKeysByIndex
public import Perennial.Proof.fmt.Link

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI Iris.ProofMode k8s_io.client_go.tools.cache

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

theorem storeIndex.getKeysByIndex.wp_proof :
    storeIndex.getKeysByIndex.spec (GF := GF) (hG := hG) := by
  intro i im ip dqi dqm dq fv fns ix OK n v
  wp_start as ⟨Hixr, Him, #Hfns, Hipr, Hix⟩
  ihave #Hfmt : isPkgInit (PROP := IProp GF) pkg_id.fmt $$ []
  · iPkgInit
  iunfold fnsOk at Hfns
  icases Hfns with ⟨%hdom, #Hfv⟩
  wp_auto
  wp_apply (wp_map_lookup1 go.string IndexFunc.ty im fv n dqm) $$ [$Him] as Him
  cases hf : fv !! n with
  | none =>
    have hn : n ∉ fns := by
      intro h; have := (hdom n).1 h; rw [GMap.mem_iff, hf] at this; cases this
    simp only [Option.getD_none]
    (try wp_auto)
    simp only [show zero_val GoFunc = func.nil from rfl, _root_.decide_true]
    (try wp_auto)
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %l1 ⟨Hl1, -⟩
    simp only [go.arrayLiteralSize, List.foldl]
    (try wp_auto)
    wp_apply (fmt.wp_Errorf _ _ _ (_root_.Perennial.fmt.ArgsWf.cons_string n []
      _root_.Perennial.fmt.ArgsWf.nil)) $$ [$Hl1] as %err #Herr
    (try wp_auto)
    iapply HΦ
    iframe
    ipureintro
    exact ⟨fun h => absurd h hn, fun _ h => by cases h⟩
  | some f =>
    ihave ⟨%F, %hF, #Hfn⟩ := BigSepM.bigSepM_lookup hf $$ Hfv
    iunfold fnOk at Hfn
    icases Hfn with ⟨%hfnn, -⟩
    have hn : n ∈ fns := (hdom n).2 (by rw [GMap.mem_iff, hf]; rfl)
    simp only [Option.getD_some, decide_eq_false hfnn]
    (try wp_auto)
    iunfold ownIx at Hix
    icases Hix with ⟨Hip, HIX⟩
    wp_apply (wp_map_lookup1 go.string index.ty ip _ n dq) $$ [$Hip] as Hip

    cases hx : ix !! n with
    | none =>
      simp only [Option.map_none, Option.getD_none, show zero_val Loc = map.nil from rfl]
      (try wp_auto)
      iapply HΦ
      iunfold ownIx
      iframe
      ipureintro
      refine ⟨fun _ => ⟨rfl, ?_⟩, fun h => absurd hn h⟩
      unfold setLoc; rw [hx]; rfl
    | some e =>
      obtain ⟨l, X⟩ := e
      simp only [Option.map_some, Option.getD_some]
      icases (BigSepM.bigSepM_lookup_acc hx) $$ HIX with ⟨HX, HIXc⟩
      iunfold ownIxN at HX
      icases HX with ⟨Hl, HXs⟩
      (try wp_auto)
      wp_apply (wp_map_lookup1 go.string (k8s_io.apimachinery.pkg.util.sets.Set'.ty go.string)
        l _ v dq) $$ [$Hl] as Hl
      (try wp_auto)
      iapply HΦ
      iframe
      isplitl
      · iunfold ownIx
        iframe
        iapply HIXc
        iunfold ownIxN
        iframe
      ipureintro
      refine ⟨fun _ => ⟨rfl, ?_⟩, fun h => absurd hn h⟩
      unfold setLoc; rw [hx]
      simp only [Option.bind_some]; cases X !! v <;> rfl

end proof

end cache
end EtcdGrove
end Perennial
