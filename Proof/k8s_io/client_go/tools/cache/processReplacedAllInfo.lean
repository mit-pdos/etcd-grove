/-
Proof of `Spec/k8s_io/client_go/tools/cache/processReplacedAllInfo.lean`. Lean-first.

The closures `reconcileReplacement` calls collect the deletions (`deletions`, the tombstones) and
the replacements (`replacements`, each new object with the store's old object at its key, read
through the exclusive writer); the store is replaced; then the handler gets the events in order.
-/
module

public import Spec.k8s_io.client_go.tools.cache.processReplacedAllInfo
public import Spec.k8s_io.client_go.tools.cache.cache__Get
public import Spec.k8s_io.client_go.tools.cache.cache__Replace

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

theorem processReplacedAllInfo.wp_proof
    (wp_reconcile : reconcileReplacement.spec (GF := GF) (hG := hG))
    (wp_Get : cache.Get.spec (GF := GF) (hG := hG))
    (wp_Replace : cache.Replace.spec (GF := GF) (hG := hG)) :
    processReplacedAllInfo.spec (GF := GF) (hG := hG) := by
  intro lg h ca ts γ OK Fam kf kf' KF SW Rw σ H evs rv isl objs b
  wp_start as ⟨#Hca, Hr, #Hsw, HSW, %HRw, #Hh, HH, Hisl, #Hoks, #Hkey, #Hkey'⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hisl
  (try wp_auto)
  wp_apply (wp_slice_make3 (V := replacement) (W64 0) isl.len (by word)) as %rsl0 ⟨Hrsl0, Hrcap0, -⟩
  (try wp_auto)
  wp_func_lits
  (try wp_auto)
  ipersist clientState
  wp_bind
  iapply (wp_reconcile lg ca ts γ OK Fam kf kf' KF SW Rw σ isl (DFrac.own 1) objs _ _
    (fun ds => iprop(∃ (sl : GoSlice) (dvs : List DeletedFinalStateUnknown),
      deletions_ptr ↦ sl ∗ sl ↦* dvs ∗ ownSliceCap DeletedFinalStateUnknown sl (DFrac.own 1) ∗
      ⌜dvs.map (fun d => tombstone d.Key' d.Obj') = ds⌝ ∗ □ ([∗list] d ∈ dvs, okNil OK d.Obj')))
    (fun rs => iprop(∃ (sl : GoSlice) (rvs : List replacement),
      replacements_ptr ↦ sl ∗ sl ↦* rvs ∗ ownSliceCap replacement sl (DFrac.own 1) ∗
      ⌜rvs = rs.map (fun x => replacement.mk (objAt σ.items (KF x)) x)⌝ ∗
      □ ([∗list] x ∈ rs, okNil OK (objAt σ.items (KF x)) ∗ OK x))))
    $$ [$Hpkg $Hca $Hr $Hsw $HSW $Hisl $Hkey' deletions Hrsl0 Hrcap0 replacements clientState]
  · isplitr
    · ipureintro; exact HRw.1
    isplitl [deletions]
    · iexists slice.nil, []
      iframe
      isplitr
      · iapply ownSlice_nil
      isplitr
      · iapply ownSliceCap_nil
      isplitr
      · ipureintro; rfl
      imodintro; iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2; itrivial
    isplitl [Hrsl0 Hrcap0 replacements]
    · iexists rsl0, []
      iframe
      isplitr
      · ipureintro; rfl
      imodintro; iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2; itrivial
    isplitr
    · -- `onDelete`: the tombstone appended to `deletions`
      imodintro
      iintro %ds %k %x
      imodintro
      iintro %Ψ ⟨⟨%sl, %dvs, Hd, Hsl, Hcap, %Hdvs, #Hdoks⟩, #Hokx⟩ HΨ
      wp_pures
      (try wp_auto)
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %l1 ⟨Hl1, -⟩
      simp only [go.arrayLiteralSize, List.foldl]
      (try wp_auto)
      wp_apply wp_slice_append $$ [$Hsl $Hcap $Hl1] as %sl' ⟨Hsl, Hcap, -⟩
      (try wp_auto)
      iapply HΨ
      iexists sl', dvs ++ [DeletedFinalStateUnknown.mk k x]
      iframe
      isplitr
      · ipureintro; rw [List.map_append, Hdvs]; rfl
      imodintro
      iapply (BigSepL.bigSepL_snoc (Φ := fun _ (d : DeletedFinalStateUnknown) => iprop(okNil OK d.Obj'))).2
      iframe #
    · -- `onReplace`: the new object with the store's old one appended to `replacements`
      imodintro
      iintro %rs %o
      imodintro
      iintro %Ψ ⟨⟨%sl, %rvs, Hrp, Hsl, Hcap, %Hrvs, #Hroks⟩, HSW, Hr, %ho⟩ HΨ
      wp_pures
      (try wp_auto)
      wp_bind
      iapply (wp_Get ca ts γ OK Fam kf (fun x => iprop(⌜x ∈ objs⌝)) KF o) $$ [$Hpkg $Hca $Hkey $Hr]
      · imodintro; ipureintro; exact ho
      inext
      iapply (writer_read γ SW Rw σ HRw.1) $$ Hsw HSW
      iintro HSW %item %ok ⟨%Hitem, #Hold, Hr⟩
      obtain ⟨rfl, rfl⟩ := Hitem
      ihave #HOKo := BigSepL.bigSepL_mem (Φ := fun x => iprop(OK x)) ho $$ Hoks
      (try wp_auto)
      by_cases hin : KF o ∈ σ.items
      · rw [decide_eq_true hin]
        (try wp_auto)
        wp_apply wp_slice_literal
        isplitr
        · ipureintro; rfl
        iintro %l1 ⟨Hl1, -⟩
        simp only [go.arrayLiteralSize, List.foldl]
        (try wp_auto)
        wp_apply wp_slice_append $$ [$Hsl $Hcap $Hl1] as %sl' ⟨Hsl, Hcap, -⟩
        (try wp_auto)
        iapply HΨ
        iframe
        isplitr
        · ipureintro; rw [List.map_append, Hrvs]; rfl
        imodintro
        iapply (BigSepL.bigSepL_snoc (Φ := fun _ x =>
          iprop(okNil OK (objAt σ.items (KF x)) ∗ OK x))).2
        iframe #
      · rw [decide_eq_false hin]
        have hnil : objAt σ.items (KF o) = interface.nil := by
          unfold objAt; rw [GMap.mem_iff] at hin
          cases h' : σ.items !! KF o with
          | none => rfl
          | some _ => rw [h'] at hin; exact absurd rfl hin
        (try wp_auto)
        wp_apply wp_slice_literal
        isplitr
        · ipureintro; rfl
        iintro %l1 ⟨Hl1, -⟩
        simp only [go.arrayLiteralSize, List.foldl]
        (try wp_auto)
        wp_apply wp_slice_append $$ [$Hsl $Hcap $Hl1] as %sl' ⟨Hsl, Hcap, -⟩
        (try wp_auto)
        iapply HΨ
        iframe
        isplitr
        · ipureintro; rw [List.map_append, Hrvs]; simp [hnil]
        imodintro
        iapply (BigSepL.bigSepL_snoc (Φ := fun _ x =>
          iprop(okNil OK (objAt σ.items (KF x)) ∗ OK x))).2
        iframe #
  inext
  iintro ⟨%dks, %Hdks, ⟨%dsl, %dvs, Hdel, Hdsl, Hdcap, %Hdvs, #Hdoks⟩,
    ⟨%rsl, %rvs, Hrep, Hrsl, Hrcap, %Hrvs, #Hroks⟩, HSW, Hisl, Hr⟩
  (try wp_auto)
  -- the store replaced, by its exclusive writer
  wp_bind
  iapply (wp_Replace ca ts γ OK Fam kf (fun x => iprop(⌜x ∈ objs⌝)) KF isl objs rv)
    $$ [$Hpkg $Hca $Hkey $Hisl]
  · isplitr
    · imodintro
      iapply (BigSepL.bigSepL_intro (P := iprop(emp))
        (fun {_ x} hx => pure_intro (List.mem_of_getElem? hx)))
      iempintro
    iframe #
  inext
  iapply (writer_step γ SW Rw σ (fun σ => σ.replace (keyedItems KF objs) rv) HRw.2) $$ Hsw HSW
  iintro HSW Hisl
  (try wp_auto)
  iunfold handlerOk at Hh
  icases Hh with ⟨%hi, %hh, #HonAdd, #HonUpd, #HonDel⟩
  subst hh
  ihave %Hdlen := ownSlice_len _ _ _ $$ Hdsl
  -- the deletions' events
  ihave IH5 : iprop(∃ (n : w64) (x : DeletedFinalStateUnknown),
      "i" ∷ i_ptr ↦ n ∗
      "od" ∷ objToDelete_ptr ↦ x ∗
      "HH" ∷ H (evs ++ (dvs.take (sint.nat n)).map (fun d => Ev.delete (tombstone d.Key' d.Obj'))) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.nat n ≤ dvs.length⌝) $$ [i objToDelete HH]
  · iexists W64 0, _
    iframe
    rw [show sint.nat (W64 0) = 0 by rfl, List.take_zero, List.map_nil, List.append_nil]
    iframe
    ipureintro
    exact ⟨by decide, by simp⟩
  wp_for IH5
  wp_if_destruct
  · have Hlt : sint.nat n < dvs.length := by word
    obtain ⟨d, Hd⟩ : ∃ d, dvs[sint.nat n]? = some d := ⟨_, List.getElem?_eq_getElem Hlt⟩
    simp only [show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z dsl.len from ⟨Hn.1, Hif⟩, _root_.and_self,
      ↓reduceIte]
    wp_apply wp_load_slice_index dsl (sint.Z n) dvs (DFrac.own 1) d Hn.1 $$ [Hdsl] as Hdsl
    · iframe; ipureintro; exact Hd
    ihave #Hdok := BigSepL.bigSepL_lookup
      (Φ := fun _ (d : DeletedFinalStateUnknown) => iprop(okNil OK d.Obj')) Hd $$ Hdoks
    (try wp_auto)
    have hdt : interface.mkOk DeletedFinalStateUnknown.ty #d = tombstone d.Key' d.Obj' := by
      unfold tombstone; cases d; rfl
    rw [hdt]
    ihave #HonDel1 := HonDel $$ %(evs ++ (dvs.take (sint.nat n)).map
      (fun d => Ev.delete (tombstone d.Key' d.Obj'))) %(tombstone d.Key' d.Obj')
    wp_bind (App (Val #(methods hi.ty go!"OnDelete" hi.v)) _)
    iapply HonDel1 $$ [$HH]
    · iunfold delOk; iright; iexists d.Key', d.Obj'; iframe #; ipureintro; rfl
    inext
    iintro HH
    (try wp_auto)
    wp_for_post
    iframe
    iexists n + W64 1, d
    iframe
    have hn1 : sint.nat (n + W64 1) = sint.nat n + 1 := by
      have := Hn.1; have := Hlt; have := Hdlen.1; word
    have h1 : 0 ≤ sint.Z (n + W64 1) := by have := Hn.1; have := Hlt; have := Hdlen.1; word
    rw [hn1, List.take_add_one, Hd]
    simp only [Option.toList_some, List.map_append, List.map_cons, List.map_nil, List.append_assoc]
    iframe
    ipureintro; exact ⟨h1, by omega⟩
  · have hnl : sint.nat n = dvs.length := by word
    rw [hnl, List.take_length]
    (try wp_auto)
    -- the replacements' events
    subst Hrvs
    ihave %Hrlen := ownSlice_len _ _ _ $$ Hrsl
    rw [List.length_map] at Hrlen
    ihave IH6 : iprop(∃ (m : w64) (y : replacement),
        "j" ∷ i_ptr ↦ m ∗
        "r" ∷ r_ptr ↦ y ∗
        "HH" ∷ H (evs ++ dvs.map (fun d => Ev.delete (tombstone d.Key' d.Obj')) ++
          (objs.take (sint.nat m)).map (fun x => putEvR σ.items (KF x) x b)) ∗
        "%Hm" ∷ ⌜0 ≤ sint.Z m ∧ sint.nat m ≤ objs.length⌝) $$ [i r HH]
    · iexists W64 0, _
      iframe
      rw [show sint.nat (W64 0) = 0 by rfl, List.take_zero, List.map_nil, List.append_nil]
      iframe
      ipureintro
      exact ⟨by decide, by simp⟩
    wp_for IH6
    wp_if_destruct
    · have Hlt : sint.nat m < objs.length := by word
      obtain ⟨o, Ho⟩ : ∃ o, objs[sint.nat m]? = some o := ⟨_, List.getElem?_eq_getElem Hlt⟩
      have Hro : (objs.map (fun x => replacement.mk (objAt σ.items (KF x)) x))[sint.nat m]? =
          some (replacement.mk (objAt σ.items (KF o)) o) := by
        rw [List.getElem?_map, Ho]; rfl
      simp only [show 0 ≤ sint.Z m ∧ sint.Z m < sint.Z rsl.len from ⟨Hm.1, Hif⟩,
        _root_.and_self, ↓reduceIte]
      wp_apply wp_load_slice_index rsl (sint.Z m) _ (DFrac.own 1) _ Hm.1 $$ [Hrsl] as Hrsl
      · iframe; ipureintro; exact Hro
      ihave #Hrok := BigSepL.bigSepL_lookup
        (Φ := fun _ x => iprop(okNil OK (objAt σ.items (KF x)) ∗ OK x)) Ho $$ Hroks
      icases Hrok with ⟨#Hold, #Hnew⟩
      have hm1 : sint.nat (m + W64 1) = sint.nat m + 1 := by
        have := Hm.1; have := Hlt; have := Hrlen.1; word
      have h1 : 0 ≤ sint.Z (m + W64 1) := by have := Hm.1; have := Hlt; have := Hrlen.1; word
      have h2 : sint.nat (m + W64 1) ≤ objs.length := by rw [hm1]; exact Hlt
      (try wp_auto)
      have Htake : objs.take (sint.nat (m + W64 1)) = objs.take (sint.nat m) ++ [o] := by
        rw [hm1, List.take_add_one, Ho]; rfl
      cases hob : objAt σ.items (KF o) with
      | nil =>
        have hev : putEvR σ.items (KF o) o b = Ev.add o b := by unfold putEvR; rw [hob]; simp
        (try wp_auto)
        ihave #HonAdd1 := HonAdd $$ %(evs ++ dvs.map (fun d => Ev.delete (tombstone d.Key' d.Obj')) ++
          (objs.take (sint.nat m)).map (fun x => putEvR σ.items (KF x) x b)) %o %b
        wp_bind (App (App (Val #(methods hi.ty go!"OnAdd" hi.v)) _) _)
        iapply HonAdd1 $$ [$HH $Hnew]
        inext
        iintro HH
        (try wp_auto)
        wp_for_post
        iframe
        iexists m + W64 1, _
        iframe
        rw [Htake, List.map_append, List.map_cons, List.map_nil, hev, ← List.append_assoc]
        iframe
        ipureintro; exact ⟨h1, h2⟩
      | ok io =>
        have hev : putEvR σ.items (KF o) o b = Ev.update (GoInterface.ok io) o := by
          unfold putEvR; rw [hob]; simp
        (try wp_auto)
        rw [hob] at *
        ihave #HonUpd1 := HonUpd $$ %(evs ++ dvs.map (fun d => Ev.delete (tombstone d.Key' d.Obj')) ++
          (objs.take (sint.nat m)).map (fun x => putEvR σ.items (KF x) x b)) %(GoInterface.ok io) %o
        wp_bind (App (App (Val #(methods hi.ty go!"OnUpdate" hi.v)) _) _)
        iapply HonUpd1 $$ [$HH $Hold $Hnew]
        inext
        iintro HH
        (try wp_auto)
        wp_for_post
        iframe
        iexists m + W64 1, _
        iframe
        rw [Htake, List.map_append, List.map_cons, List.map_nil, hev, ← List.append_assoc]
        iframe
        ipureintro; exact ⟨h1, h2⟩
    · have hml : sint.nat m = objs.length := by word
      rw [hml, List.take_length]
      (try wp_auto)
      iapply HΦ
      iexists dks
      iframe
      isplitr
      · ipureintro; exact Hdks
      unfold replacedEvs
      have hd : dvs.map (fun d => Ev.delete (tombstone d.Key' d.Obj')) =
          dks.map (fun k => Ev.delete (tombstone k (objAt σ.items k))) := by
        have := congrArg (List.map Ev.delete) Hdvs
        simpa [List.map_map, Function.comp_def] using this
      rw [hd, List.append_assoc]
      iframe

end proof

end cache
end EtcdGrove
end Perennial
