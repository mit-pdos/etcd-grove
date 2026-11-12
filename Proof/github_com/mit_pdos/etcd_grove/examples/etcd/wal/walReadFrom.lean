/- Lean-first (no Rocq counterpart). The proof of `walReadFrom`. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.walReadFrom
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.walLastHS
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.walSaveSnap
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.phsNext
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.readEnt
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.RefLemmas

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_wal

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.etcd.wal

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.wal.Assumptions]

theorem tNewest_snoc (F : List TOp) (o : TOp) :
    tNewest (F ++ [o]) = if o.snap then
      (match tNewest F with
        | none => some (o.idx, o.term)
        | some b => if uint.nat b.1 ≤ uint.nat o.idx then some (o.idx, o.term) else some b)
      else tNewest F := by
  unfold tNewest
  rw [List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]
  split
  · split <;> simp_all
  · rfl

theorem walReadFrom.wp_proof (wp_walLastHS : walLastHS.spec (GF := GF) (hG := hG))
    (wp_walSaveSnap : walSaveSnap.spec (GF := GF) (hG := hG))
    (wp_phsNext : phsNext.spec (GF := GF) (hG := hG)) (wp_readEnt : readEnt.spec (GF := GF) (hG := hG)) :
    walReadFrom.spec (GF := GF) (hG := hG) := by
  intro s h k hw hk0 hk
  wp_start as #Hr
  ihave Hr2 := Hr
  iunfold opsRep at Hr2
  icases Hr2 with ⟨%es, #Hs, #Hel⟩
  ihave %Hlen := ownSlice_len $$ Hs
  ihave %Hel_len := opsElems_length $$ Hel
  ihave %Hwf := ownSlice_wf $$ Hs
  have hkl : sint.Z k ≤ sint.Z s.len := by
    have : sint.nat k ≤ sint.nat s.len := by omega
    word
  have hb0 : 0 ≤ sint.Z k ∧ sint.Z k ≤ sint.Z s.len ∧ sint.Z s.len ≤ sint.Z s.cap := ⟨hk0, hkl, Hwf.2⟩
  wp_auto
  simp only [hb0, _root_.and_self, ↓reduceIte]
  wp_auto
  wp_apply wp_walLastHS
  · iexact Hr
  iintro -
  wp_auto
  wp_apply +noauto (wp_slice_make2 (V := TEnt) (W64 0)) as %e0 ⟨He0, -⟩
  · ipureintro; word
  simp only [show sint.nat (W64 0) = 0 from rfl, List.replicate_zero]
  ipersist He0
  wp_auto
  have hb1 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z k ∧ sint.Z k ≤ sint.Z s.cap :=
    ⟨by word, hk0, by omega⟩
  simp only [hb1, _root_.and_self, ↓reduceIte]
  ihave Hpre := opsRep_slice s h (W64 0) k ⟨by word, hk0, hkl⟩ $$ Hr
  wp_apply wp_walLastHS
  · iexact Hpre
  iintro -
  have hpre : subslice (sint.nat (W64 0)) (sint.nat k) h = h.take (sint.nat k) := by
    rw [show sint.nat (W64 0) = 0 from rfl]; simp [subslice]
  rw [hpre]
  wp_auto
  -- the suffix `s[k:]`
  ihave Hsuf := opsRep_slice s h k s.len ⟨hk0, hkl, by omega⟩ $$ Hr
  have hD : subslice (sint.nat k) (sint.nat s.len) h = h.drop (sint.nat k) := by
    simp only [subslice]; rw [show sint.nat s.len = h.length by omega, List.take_length]
  rw [hD]
  iunfold opsRep at Hsuf
  icases Hsuf with ⟨%dvs, #Hd, #Hde⟩
  ihave %Hdlen := ownSlice_len $$ Hd
  ihave %Hde_len := opsElems_length $$ Hde
  have hsl : (slice.slice s walOp k s.len).len = s.len - k := rfl
  have hdl : dvs.length = sint.nat (s.len - k) := by rw [← hsl]; exact Hdlen.1
  wp_apply +noauto (wp_slice_make3 (V := walOp) (W64 0) (s.len - k) (by constructor <;> word))
    as %f0 ⟨Hf0, Hf0cap, -⟩
  simp only [show sint.nat (W64 0) = 0 from rfl, List.replicate_zero]
  ipersist Hf0
  wp_auto
  ihave HI : (∃ (i : w64) (fs : GoSlice) (fvs : List walOp),
      "i" ∷ i_ptr ↦ i ∗ "f" ∷ f_ptr ↦ fs ∗ "s" ∷ s_ptr ↦ slice.slice s walOp k s.len ∗
      "Hf" ∷ fs ↦*□ fvs ∗ "Hfcap" ∷ ownSliceCap walOp fs (DFrac.own 1) ∗
      "Hfe" ∷ opsElems fvs (((h.drop (sint.nat k)).take (sint.nat i)).filter (tKeep (tLastHS h).commit')) ∗
      "found" ∷ found_ptr ↦ (tNewest (((h.drop (sint.nat k)).take (sint.nat i)).filter
        (tKeep (tLastHS h).commit'))).isSome ∗
      "base" ∷ base_ptr ↦ contents.mk (tLastHS (h.take (sint.nat k)))
        ((tNewest (((h.drop (sint.nat k)).take (sint.nat i)).filter (tKeep (tLastHS h).commit'))).getD
          (W64 0, W64 0)).1
        ((tNewest (((h.drop (sint.nat k)).take (sint.nat i)).filter (tKeep (tLastHS h).commit'))).getD
          (W64 0, W64 0)).2 e0 ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z (s.len - k)⌝ : IProp GF) $$ [i f s Hf0cap found base]
  · iexists W64 0, f0, []
    simp only [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.filter_nil]
    iframe
    isplitl []
    · iexact Hf0
    isplitl []
    · iapply opsElems_nil
    ipureintro; constructor <;> word
  wp_for HI
  icases Hf with #Hf
  icases Hfe with #Hfe
  cleanup_bool_decide
  wp_if_destruct
  · have hil : sint.nat i < dvs.length := by
      have : sint.nat i < sint.nat (s.len - k) := by word
      omega
    obtain ⟨v, Hv⟩ : ∃ v, dvs[sint.nat i]? = some v := ⟨_, List.getElem?_eq_getElem hil⟩
    have hb : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z (s.len - k) := ⟨Hi.1, Hif⟩
    simp only [hb, _root_.and_self, ↓reduceIte]
    icases ownSlice_elem_acc (sint.Z i) v (slice.slice s walOp k s.len) DFrac.discard dvs Hi.1
      (by simpa [sint.nat] using Hv) $$ Hd with ⟨Hv, -⟩
    icases opsElems_lookup dvs (h.drop (sint.nat k)) (sint.nat i) v Hv $$ Hde with ⟨%op, #Hop⟩
    icases Hop with ⟨%Hop, #Hopr⟩
    ihave Hopr2 := Hopr
    iunfold opRep at Hopr2
    icases Hopr2 with ⟨%Hf, -⟩
    obtain ⟨hsn, hhs, hix, htm⟩ := Hf
    iStructNamed Hv
    have hi1 : sint.nat (i + W64 1) = sint.nat i + 1 := by word
    have hstep := tKeep_filter_take_succ (tLastHS h).commit' (h.drop (sint.nat k)) (sint.nat i) op Hop
    wp_auto
    rw [hsn]
    cases hos : op.snap
    · have hk : tKeep (tLastHS h).commit' op = true := by simp [tKeep, hos]
      have hnew : tNewest ((((h.drop (sint.nat k)).take (sint.nat i)).filter (tKeep (tLastHS h).commit')) ++ [op]) = tNewest (((h.drop (sint.nat k)).take (sint.nat i)).filter (tKeep (tLastHS h).commit')) := by
        rw [tNewest_snoc, hos]; rfl
      wp_auto
      repeat (simp only [hb, _root_.and_self, ↓reduceIte]; try wp_auto)
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %osl ⟨Hosl, -⟩
      wp_auto
      wp_apply wp_slice_append_persistent (sl := fs) (vs := fvs) $$ [$Hfcap $Hosl] as %fs' ⟨Hf', Hfcap, -⟩
      · iexact Hf
      wp_for_post
      iframe
      iexists i + W64 1, fs', fvs ++ [v]
      rw [hi1, hstep]
      simp only [hk, ↓reduceIte, hnew]
      iframe
      isplitl []
      · iapply opsElems_snoc
        isplitl []
        · iexact Hfe
        · iexact Hopr
      ipureintro; constructor <;> word
    · wp_auto
      simp only [hb, _root_.and_self, ↓reduceIte]
      wp_auto
      rw [hix]
      wp_if_destruct
      · have hk : tKeep (tLastHS h).commit' op = false := by
          simp only [tKeep, hos, Bool.true_and, Bool.not_eq_false', decide_eq_true_eq]; word
        simp only [hk, Bool.false_eq_true, ↓reduceIte, List.append_nil] at hstep
        wp_for_post
        iframe
        iexists i + W64 1, fs, fvs
        rw [hi1, hstep]
        iframe
        isplitl []
        · iexact Hf
        isplitl []
        · iexact Hfe
        ipureintro; constructor <;> word
      · have hk : tKeep (tLastHS h).commit' op = true := by
          simp only [tKeep, hos, Bool.true_and, Bool.not_eq_true', decide_eq_false_iff_not]
          intro h'; apply Hif; word
        simp only [hk, ↓reduceIte] at hstep
        cases hN : tNewest (((h.drop (sint.nat k)).take (sint.nat i)).filter (tKeep (tLastHS h).commit')) with
        | none =>
          have hnew : tNewest ((((h.drop (sint.nat k)).take (sint.nat i)).filter (tKeep (tLastHS h).commit')) ++ [op]) = some (op.idx, op.term) := by
            rw [tNewest_snoc, hos, hN]; rfl
          simp only [hN, Option.isSome_none]
          repeat (simp only [hb, _root_.and_self, ↓reduceIte]; try wp_auto)
          rw [htm]
          repeat (simp only [hb, _root_.and_self, ↓reduceIte]; try wp_auto)
          wp_apply wp_slice_literal
          isplitr
          · ipureintro; rfl
          iintro %osl ⟨Hosl, -⟩
          wp_auto
          wp_apply wp_slice_append_persistent (sl := fs) (vs := fvs) $$ [$Hfcap $Hosl] as %fs' ⟨Hf', Hfcap, -⟩
          · iexact Hf
          wp_for_post
          iframe
          iexists i + W64 1, fs', fvs ++ [v]
          rw [hi1, hstep]
          simp only [hk, ↓reduceIte, hnew]
          iframe
          isplitl []
          · iapply opsElems_snoc
            isplitl []
            · iexact Hfe
            · iexact Hopr
          ipureintro; constructor <;> word
        | some b =>
          simp only [hN, Option.isSome_some, Option.getD_some]
          repeat (simp only [hb, _root_.and_self, ↓reduceIte]; try wp_auto)
          wp_if_destruct
          · have hnew : tNewest ((((h.drop (sint.nat k)).take (sint.nat i)).filter (tKeep (tLastHS h).commit')) ++ [op]) = some (op.idx, op.term) := by
              rw [tNewest_snoc, hos, hN]; simp only [↓reduceIte]; rw [if_pos (by word)]
            rw [htm]
            repeat (simp only [hb, _root_.and_self, ↓reduceIte]; try wp_auto)
            wp_apply wp_slice_literal
            isplitr
            · ipureintro; rfl
            iintro %osl ⟨Hosl, -⟩
            wp_auto
            wp_apply wp_slice_append_persistent (sl := fs) (vs := fvs) $$ [$Hfcap $Hosl] as %fs' ⟨Hf', Hfcap, -⟩
            · iexact Hf
            wp_for_post
            iframe
            iexists i + W64 1, fs', fvs ++ [v]
            rw [hi1, hstep]
            simp only [hk, ↓reduceIte, hnew]
            iframe
            isplitl []
            · iapply opsElems_snoc
              isplitl []
              · iexact Hfe
              · iexact Hopr
            ipureintro; constructor <;> word
          · have hnew : tNewest ((((h.drop (sint.nat k)).take (sint.nat i)).filter (tKeep (tLastHS h).commit')) ++ [op]) = some b := by
              rw [tNewest_snoc, hos, hN]; simp only [↓reduceIte]; rw [if_neg (by intro h'; apply Hif; word)]
            repeat (simp only [hb, _root_.and_self, ↓reduceIte]; try wp_auto)
            wp_apply wp_slice_literal
            isplitr
            · ipureintro; rfl
            iintro %osl ⟨Hosl, -⟩
            wp_auto
            wp_apply wp_slice_append_persistent (sl := fs) (vs := fvs) $$ [$Hfcap $Hosl] as %fs' ⟨Hf', Hfcap, -⟩
            · iexact Hf
            wp_for_post
            iframe
            iexists i + W64 1, fs', fvs ++ [v]
            rw [hi1, hstep]
            simp only [hk, ↓reduceIte, hnew]
            iframe
            isplitl []
            · iapply opsElems_snoc
              isplitl []
              · iexact Hfe
              · iexact Hopr
            ipureintro; constructor <;> word
  · have hin : sint.nat i = (h.drop (sint.nat k)).length := by
      have : sint.nat i = sint.nat (s.len - k) := by word
      omega
    rw [hin, List.take_length]
    cases hN : tNewest ((h.drop (sint.nat k)).filter (tKeep (tLastHS h).commit')) with
    | none =>
      simp only [Option.isSome_none, Option.getD_none]
      wp_auto
      wp_end
      simp only [tReadFrom, hN, readRes]
      itrivial
    | some p =>
      obtain ⟨bi, bt⟩ := p
      simp only [Option.isSome_some, Option.getD_some]
      wp_auto
      have hRF : tReadFrom h (sint.nat k) =
          tFoldChkFrom ⟨tLastHS (h.take (sint.nat k)), bi, bt, []⟩
            ((h.drop (sint.nat k)).filter (tKeep (tLastHS h).commit')) := by
        simp only [tReadFrom, hN]
      obtain ⟨FF, hFF⟩ : ∃ FF, FF = ((h.drop (sint.nat k)).filter (tKeep (tLastHS h).commit')) := ⟨_, rfl⟩
      obtain ⟨base0, hbase0⟩ : ∃ b : TContents, b = ⟨tLastHS (h.take (sint.nat k)), bi, bt, []⟩ := ⟨_, rfl⟩
      rw [← hFF] at hN hRF
      rw [← hFF]
      rw [← hbase0] at hRF
      have hwF : tHistWf FF := fun o ho => by
        rw [hFF] at ho; exact hw o (List.mem_of_mem_drop (List.mem_filter.1 ho).1)
      ihave %Hflen := ownSlice_len $$ Hf
      ihave %Hfe_len := opsElems_length $$ Hfe
      ihave HI2 : (∃ (i : w64) (sv : contents) (cur : TContents),
          "i" ∷ i_ptr ↦ i ∗ "st" ∷ st_ptr ↦ sv ∗ "f" ∷ f_ptr ↦ fs ∗ "Hc" ∷ contentsRep sv cur ∗
          "%Hfold" ∷ ⌜tFoldChkFrom base0 (FF.take (sint.nat i)) = some cur⌝ ∗
          "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z fs.len⌝ : IProp GF) $$ [i st f]
      · iexists W64 0, _, base0
        iframe
        simp only [show sint.nat (W64 0) = 0 from rfl, List.take_zero, contentsRep]
        isplitl []
        · isplitr
          · ipureintro; subst hbase0; exact ⟨rfl, rfl, rfl⟩
          · subst hbase0; iexact He0
        isplit
        · ipureintro; rfl
        · ipureintro; constructor <;> word
      wp_for HI2
      cleanup_bool_decide
      wp_if_destruct
      · have hil : sint.nat i < fvs.length := by
          have : sint.nat i < sint.nat fs.len := by word
          omega
        obtain ⟨v, Hv⟩ : ∃ v, fvs[sint.nat i]? = some v := ⟨_, List.getElem?_eq_getElem hil⟩
        have hb : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z fs.len := ⟨Hi.1, Hif⟩
        simp only [hb, _root_.and_self, ↓reduceIte]
        wp_apply wp_load_slice_index fs (sint.Z i) fvs DFrac.discard v hb.1 as -
        · isplitl []
          · iexact Hf
          ipureintro
          simpa [sint.nat] using Hv
        icases opsElems_lookup fvs FF (sint.nat i) v Hv $$ Hfe with ⟨%op, %Hop, Hopr⟩
        iunfold opRep at Hopr
        icases Hopr with ⟨%Hopf, #Hoe⟩
        obtain ⟨hsn, hhs, hix, htm⟩ := Hopf
        have hwo := hwF op (List.mem_of_getElem? Hop)
        have hi1 : sint.nat (i + W64 1) = sint.nat i + 1 := by word
        have hstep := tFoldChkFrom_take_succ base0 FF (sint.nat i) op Hop
        rw [Hfold, Option.bind_some] at hstep
        rw [hsn]
        cases hos : op.snap
        · -- a Save
          rw [tFoldChkFrom_save cur op hos] at hstep
          wp_auto
          iunfold contentsRep at Hc
          icases Hc with ⟨%Hcf, #Hce⟩
          obtain ⟨hchs, hcbi, hcbt⟩ := Hcf
          wp_apply wp_phsNext
          ihave %Hoel := ownSlice_len $$ Hoe
          ihave HJ : (∃ (jj : w64) (es_s : GoSlice) (x : List TEnt),
              "j" ∷ j_ptr ↦ jj ∗
              "st" ∷ st_ptr ↦ contents.mk (tPhsNext sv.hs' v.hs') sv.baseIdx' sv.baseTerm' es_s ∗
              "Hxs" ∷ es_s ↦*□ x ∗
              "%Hx" ∷ ⌜(op.ents.take (sint.nat jj)).foldlM (fun ents e => tReadEnt cur.baseIdx ents e) cur.ents =
                some x⌝ ∗
              "%Hj" ∷ ⌜0 ≤ sint.Z jj ∧ sint.Z jj ≤ sint.Z v.ents'.len⌝ : IProp GF) $$ [j st]
          · iexists W64 0, sv.ents', cur.ents
            iframe
            isplitl []
            · iexact Hce
            isplit
            · ipureintro; rfl
            · ipureintro; constructor <;> word
          wp_for HJ
          icases Hxs with #Hxs
          cleanup_bool_decide
          wp_if_destruct
          · have hjl : sint.nat jj < op.ents.length := by
              have : sint.nat jj < sint.nat v.ents'.len := by word
              omega
            obtain ⟨e, He⟩ : ∃ e, op.ents[sint.nat jj]? = some e := ⟨_, List.getElem?_eq_getElem hjl⟩
            have hb : 0 ≤ sint.Z jj ∧ sint.Z jj < sint.Z v.ents'.len := ⟨Hj.1, Hif⟩
            simp only [hb, _root_.and_self, ↓reduceIte]
            wp_apply wp_load_slice_index v.ents' (sint.Z jj) op.ents DFrac.discard e hb.1 as -
            · isplitl []
              · iexact Hoe
              ipureintro
              simpa [sint.nat] using He
            have hwe := hwo.2 hos e (List.mem_of_getElem? He)
            wp_apply wp_readEnt sv.baseIdx' es_s x e hwe.2.2.1 as %r %ok Hres
            · iexact Hxs
            have hj1 : sint.nat (jj + W64 1) = sint.nat jj + 1 := by word
            have hxs := tReadEnts_take_succ cur.baseIdx op.ents (sint.nat jj) e He cur.ents
            rw [Hx, Option.bind_some] at hxs
            rw [hcbi]
            cases hre : tReadEnt cur.baseIdx x e with
            | none =>
              simp only [hre, entsRes]
              icases Hres with %hok
              subst hok
              wp_auto
              wp_for_post
              wp_for_post
              iapply HΦ
              have hall := tReadEnts_prefix_none cur.baseIdx op.ents (sint.nat jj + 1) cur.ents (by rw [hxs, hre])
              rw [hall] at hstep
              simp only [Option.map_none] at hstep
              simp only [hRF, tFoldChkFrom_prefix_none base0 FF (sint.nat i + 1) hstep, readRes]
              itrivial
            | some y =>
              simp only [hre, entsRes]
              icases Hres with ⟨%hok, #Hr⟩
              subst hok
              wp_auto
              wp_for_post
              iframe
              iexists jj + W64 1, r, y
              iframe
              isplitl []
              · iexact Hr
              isplit
              · ipureintro; rw [hj1, hxs, hre]
              · ipureintro; constructor <;> word
          · have hjn : sint.nat jj = op.ents.length := by
              have : sint.nat jj = sint.nat v.ents'.len := by word
              omega
            rw [hjn, List.take_length] at Hx
            rw [Hx, Option.map_some] at hstep
            wp_for_post
            iframe
            iexists i + W64 1, _, { cur with hs := tPhsNext cur.hs op.hs, ents := x }
            iframe
            iunfold contentsRep
            isplitl []
            · isplitr
              · ipureintro; simp [hchs, hhs, hcbi, hcbt]
              · iexact Hxs
            isplit
            · ipureintro; rw [hi1, hstep]
            · ipureintro; constructor <;> word
        · -- a snapshot record
          rw [tFoldChkFrom_snap cur op hos] at hstep
          wp_auto
          wp_apply wp_walSaveSnap $$ [$Hc] as %sv' Hc
          wp_for_post
          iframe
          iexists i + W64 1, sv', _
          iframe
          rw [hi1, hstep, hix, htm]
          ipureintro; exact ⟨rfl, by word, by word⟩
      · have hin : sint.nat i = FF.length := by
          have : sint.nat i = sint.nat fs.len := by word
          omega
        rw [hin, List.take_length] at Hfold
        wp_end
        simp only [hRF, Hfold, readRes]
        iframe

end proof

end etcd_wal
end EtcdGrove
end Perennial
