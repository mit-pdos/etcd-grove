/-
Proof of `Spec/k8s_io/client_go/listers/ResourceIndexer__List.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.listers.ResourceIndexer__List

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace listers

open Iris Iris.BI Iris.ProofMode cache k8s_io.client_go.listers

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.listers.Assumptions]

theorem ResourceIndexer.List.wp_proof
    (wp_LABN : cache.ListAllByNamespace.spec (GF := GF) (hG := hG)) :
    ResourceIndexer.List.spec (GF := GF) (hG := hG) := by
  intro X ca ts γ OK Fam kf res ns sel F
  iintro %Φ ⟨#Hpkg, #Hca, Hr, #HT, #Hsel, #Hq⟩ HAU
  ihave #Hcpkg : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache $$ []
  · iPkgInit
  wp_method_call
  wp_call
  (try wp_auto)
  wp_func_lits
  (try wp_auto)
  -- the closure appends to `ret`: `A ms` is `ret`'s slice of the pointers of `ms`
  ihave HA : iprop(∃ (sl : GoSlice) (ls : List Loc), ret_ptr ↦ sl ∗ sl ↦* ls ∗
      ownSliceCap Loc sl (DFrac.own 1) ∗ ⌜ls.map (ptrObj X) = ([] : List GoInterface)⌝ ∗
      □ ([∗list] l ∈ ls, OK (ptrObj X l))) $$ [ret]
  · iexists slice.nil, []
    iframe
    isplitr
    · iapply ownSlice_nil
    isplitr
    · iapply ownSliceCap_nil
    isplitr
    · ipureintro; rfl
    imodintro; iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2; itrivial
  wp_bind
  iapply (wp_LABN ca ts γ OK Fam kf ns sel _ (fun ms => iprop(∃ (sl : GoSlice) (ls : List Loc),
      ret_ptr ↦ sl ∗ sl ↦* ls ∗ ownSliceCap Loc sl (DFrac.own 1) ∗ ⌜ls.map (ptrObj X) = ms⌝ ∗
      □ ([∗list] l ∈ ls, OK (ptrObj X l)))) F) $$ [$Hcpkg $Hca $Hr $Hsel $HA $Hq]
  · iunfold appendOk
    imodintro
    iintro %ms %m
    imodintro
    dsimp only
    iintro %Ψ ⟨⟨%sl, %ls, Hret, Hsl, Hcap, %Hls, #Hoks⟩, #HOKm⟩ HΨ
    iunfold typedOK at HT
    ihave %hty := HT $$ HOKm
    obtain ⟨r, rfl⟩ := hty
    wp_pures
    (try wp_auto)
    have hm : ptrObj X r = GoInterface.ok ⟨X.PointerType, #r⟩ := rfl
    rw [hm]
    (try wp_auto)
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %l1 ⟨Hl1, -⟩
    simp only [go.arrayLiteralSize, List.foldl]
    (try wp_auto)
    wp_apply wp_slice_append $$ [$Hsl $Hcap $Hl1] as %sl' ⟨Hsl, Hcap, -⟩
    (try wp_auto)
    rw [← hm]
    iapply HΨ
    iexists sl', ls ++ [r]
    iframe
    isplitr
    · ipureintro; rw [List.map_append, Hls]; rfl
    imodintro
    iapply (BigSepL.bigSepL_snoc (Φ := fun _ l => iprop(OK (ptrObj X l)))).2
    iframe #
  inext
  imod HAU with ⟨%σ, ⟨Hst, %hσ⟩, Hcl⟩
  imodintro
  iexists σ
  iframe Hst
  isplitr
  · ipureintro; exact hσ
  iintro ⟨Hst, -⟩
  imod Hcl $$ [Hst] with HK
  · iframe; ipureintro; exact hσ
  imodintro
  iintro ⟨%q, %ks, %Hks, Hqm, ⟨%sl, %ls, Hret, Hsl, -, %Hls, #Hoks⟩, Hr⟩
  (try wp_auto)
  iapply HK
  isplitr
  · ipureintro; rfl
  iexists q, ks, ls
  iframe
  iframe #
  ipureintro
  exact ⟨Hks, Hls⟩

end proof

end listers
end EtcdGrove
end Perennial
