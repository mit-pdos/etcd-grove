/-
Proof of `Spec/go_etcd_io/etcd/client/v3/lessor__closeRequireLeader.lean` (etcd#22291; here of etcd#22087's code). Lean-first
(no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.lessor__closeRequireLeader
public import Spec.google_golang_org.grpc.metadata.FromOutgoingContext

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

set_option hygiene false in
/-- The marking loop's continue at a kept subscription (`hq`: its context does not ask for a
leader): the invariant at `n + 1`. -/
local macro "keep_tail" : tactic => `(tactic| (
  obtain ⟨Hr1, Hc1, Hcnt1⟩ :=
    lessor.mark_step_keep (lessor.rlSub kl hl) Prod.fst chan.nil subs (sint.nat n) Hlt hq
  (try wp_auto)
  wp_for_post
  iframe
  iexists n + W64 1, _, _, r
  simp only [named]
  rw [Hn1, Hc1, Hr1]
  iframe
  ipureintro; refine ⟨by word, by omega, Hn.2.2.1, by rw [Hcnt1]; exact Hn.2.2.2⟩))

theorem lessor.closeRequireLeader.wp_proof
    (wp_FromOutgoingContext : metadata.FromOutgoingContext.spec (GF := GF) (hG := hG)) :
    lessor.closeRequireLeader.spec (GF := GF) (hG := hG) := by
  intro l R kl hl
  wp_start as ⟨#Hkl, #Hhl, #Hmu, #Hclose⟩
  wp_apply wp_with_defer as %defer defer
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, HR⟩
  iunfold lessor.muInv at HR
  icases HR with ⟨%mp, %m, Hkas, Hm, HM⟩
  wp_auto
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range_mut_keys (fun (_keys : List w64) (_i : Nat) (m' : GMap w64 Loc) =>
      iprop(∃ (x : Loc), "ka" ∷ ka_ptr ↦ x ∗
        "Hkas" ∷ structFieldRef go_etcd_io.etcd.client.v3.lessor go!"keepAlives" l ↦ mp ∗
        "HM" ∷ [∗map] _k ↦ ka ∈ m', lessor.kaOwn R ka)) $$ Hm
  iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
  isplitl [ka Hkas HM]
  · iexists _
    simp only [named]
    iframe
  isplitr
  · imodintro
    iintro %i %key %v %m' ⟨%Hkey, %Hv, %Hagree⟩ HP Hm
    iNamed HP
    have Hv' : m' !! key = some v := (Hagree i key (Nat.le_refl _) Hkey).trans Hv
    icases (BigSepM.bigSepM_delete (m := m') Hv').1 $$ HM with ⟨Hka, HM⟩
    iunfold lessor.kaOwn at Hka
    icases Hka with ⟨%chsSl, %ctxsSl, %subs, Hchs, Hctxs, HchsS, HchsC, HctxsS, HctxsC, %Hsubs,
      HRs⟩
    wp_auto
    rename_i iu_ptr
    irename : (iu_ptr ↦ (zero_val w64) : IProp GF) => iu
    ihave %HchsL := ownSlice_len $$ HchsS
    ihave %HctxsL := ownSlice_len $$ HctxsS
    simp only [List.length_map] at HchsL HctxsL
    ihave IH : iprop(∃ (n : w64) (cv : GoInterface) (iv : w64) (r : w64),
        "i" ∷ i_ptr ↦ n ∗ "ctx" ∷ ctx_ptr ↦ cv ∗ "iu" ∷ iu_ptr ↦ iv ∗ "reqIdxs" ∷ reqIdxs_ptr ↦ r ∗
        "HchsS" ∷ chsSl ↦* ((subs.take (sint.nat n)).map
          (fun p => if lessor.rlSub kl hl p then chan.nil else Prod.fst p) ++
          (subs.drop (sint.nat n)).map Prod.fst) ∗
        "HRs" ∷ ([∗list] p ∈ (subs.take (sint.nat n)).filter (fun p => !lessor.rlSub kl hl p) ++
          subs.drop (sint.nat n), R p.1 p.2) ∗
        "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.nat n ≤ subs.length ∧ 0 ≤ sint.Z r ∧
          sint.nat r = ((subs.take (sint.nat n)).filter (lessor.rlSub kl hl)).length⌝) $$ [i ctx iu reqIdxs HchsS HRs]
    · iexists W64 0, _, _, W64 0
      simp only [named, show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.map_nil,
        List.nil_append, List.drop_zero, List.filter_nil]
      iframe
      ipureintro; refine ⟨by word, by omega, by word, rfl⟩
    wp_for IH
    wp_if_destruct
    · have Hlt : sint.nat n < subs.length := by word
      have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z ctxsSl.len := ⟨Hn.1, Hif⟩
      rw [if_pos Hbnd]
      wp_apply wp_load_slice_index ctxsSl (sint.Z n) (subs.map Prod.snd) _ (subs[sint.nat n]).2 Hn.1
        $$ [HctxsS] as HctxsS
      · iframe
        ipureintro
        rw [List.getElem?_map, List.getElem?_eq_getElem (show (sint.Z n).toNat < subs.length by word)]
        rfl
      wp_apply (wp_FromOutgoingContext _ (Hsubs.2 _ (List.getElem_mem Hlt))) as %md %ok Hmd
      have Hnat : (sint.Z n).toNat = sint.nat n := rfl
      have Hn1 : sint.nat (n + W64 1) = sint.nat n + 1 := by word
      cases hmd : metadata.outgoingMD (subs[sint.nat n]).2 with
      | none =>
        icases Hmd with %Hok
        subst Hok
        have hq : lessor.rlSub kl hl subs[sint.nat n] = false := by
          simp [lessor.rlSub, lessor.ctxRequiresLeader, hmd]
        keep_tail
      | some mv =>
        icases Hmd with ⟨%Hok, %m0, Hm0, %Hdom, Hsls⟩
        subst Hok
        wp_auto
        wp_apply (wp_map_lookup1 go.string (go.GoType.SliceType go.string) md m0 kl (DFrac.own 1)) $$ [$Hm0]
          as Hm0
        cases hkl : m0 !! kl with
        | none =>
          have hmv : mv !! kl = none := by
            have h := Hdom kl
            rw [hkl] at h
            cases h' : mv !! kl <;> simp_all
          have hq : lessor.rlSub kl hl subs[sint.nat n] = false := by
            simp [lessor.rlSub, lessor.ctxRequiresLeader, hmd, hmv]
          simp only [Option.getD_none]
          keep_tail
        | some ksl =>
          simp only [Option.getD_some]
          icases (BigSepM.bigSepM_lookup_acc (Φ := fun (k : GoString) (sl : GoSlice) =>
            iprop(∃ vs : List GoString, sl ↦* vs ∗ ⌜mv !! k = some vs⌝)) hkl).1 $$ Hsls
            with ⟨⟨%vs, Hvs, %Hmvk⟩, -⟩
          ihave %Hvl := ownSlice_len $$ Hvs
          cases vs with
          | nil =>
            have hq : lessor.rlSub kl hl subs[sint.nat n] = false := by
              simp [lessor.rlSub, lessor.ctxRequiresLeader, hmd, Hmvk]
            have Hk0 : sint.Z ksl.len < sint.Z (W64 1) := by simp at Hvl; word
            simp only [Hk0, decide_true]
            keep_tail
          | cons v0 vs' =>
            have Hk0 : ¬ sint.Z ksl.len < sint.Z (W64 1) := by simp at Hvl; word
            simp only [Hk0, decide_false]
            wp_auto
            simp only [show (0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z ksl.len) from by
              simp at Hvl; word, _root_.and_self, ↓reduceIte]
            wp_apply wp_load_slice_index ksl (sint.Z (W64 0)) (v0 :: vs') _ v0 (by word) $$ [Hvs]
              as Hvs
            · iframe; ipureintro; rfl
            by_cases hv0 : v0 = hl
            · subst hv0
              simp only [_root_.decide_true, Bool.not_true]
              have hq : lessor.ctxRequiresLeader kl v0 subs[sint.nat n].2 = true := by
                simp [lessor.ctxRequiresLeader, hmd, Hmvk]
              obtain ⟨Hr1, Hc1, Hcnt1⟩ := lessor.mark_step_close (lessor.rlSub kl v0) Prod.fst chan.nil
                subs (sint.nat n) Hlt hq
              rw [Hr1]
              icases BigSepL.bigSepL_append.1 $$ HRs with ⟨HRs, HRd⟩
              icases BigSepL.bigSepL_cons.1 $$ HRd with ⟨HR, HRd⟩
              wp_auto
              have Hbc : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z chsSl.len := ⟨Hn.1, by word⟩
              simp only [Hbc, _root_.and_self, ↓reduceIte]
              wp_apply wp_load_slice_index chsSl (sint.Z n) _ _ (subs[sint.nat n]).1 Hn.1 $$ [HchsS]
                as HchsS
              · iframe; ipureintro; rw [Hnat]; exact lessor.take_map_append_drop_get _ _ _ _ Hlt
              ihave #Hc0 := Hclose
              iunfold lessor.closeOk at Hc0
              ihave #Hc := Hc0 $$ %(subs[sint.nat n].1) %(subs[sint.nat n].2) %hq
              wp_apply Hc $$ [$HR]
              rw [if_pos Hbc]
              wp_apply wp_store_slice_index chsSl (sint.Z n) _ chan.nil $$ [HchsS] as HchsS
              · iframe; ipureintro
                refine ⟨Hn.1, ?_⟩
                simp only [List.length_append, List.length_map, List.length_take, List.length_drop]
                omega
              rw [Hnat, Hc1]
              wp_for_post
              iframe
              iexists n + W64 1, _, _, r + W64 1
              simp only [named]
              rw [Hn1]
              iframe
              ipureintro
              have Hle := lessor.length_filter_take_le_n (lessor.rlSub kl v0) subs (sint.nat n)
              have Hr0 := Hn.2.2.1
              have Hrn : sint.nat r ≤ sint.nat n := by rw [Hn.2.2.2]; exact Hle
              have Hr1' : sint.nat (r + W64 1) = sint.nat r + 1 := by word
              refine ⟨by word, by omega, by word, ?_⟩
              rw [Hcnt1, Hr1', Hn.2.2.2]
            · simp only [hv0, _root_.decide_false, Bool.not_false]
              have hq : lessor.rlSub kl hl subs[sint.nat n] = false := by
                simp [lessor.rlSub, lessor.ctxRequiresLeader, hmd, Hmvk, hv0]
              keep_tail
    · have Hge : sint.nat n = subs.length := by word
      obtain ⟨Hm1, Hm2, Hm3⟩ := lessor.mark_done (lessor.rlSub kl hl) Prod.fst chan.nil subs
        (sint.nat n) (by omega)
      rw [Hm1, Hm2]
      have Hr := Hn.2.2.2
      rw [Hm3] at Hr
      have Hcount := lessor.filter_count (lessor.rlSub kl hl) subs
      wp_if_destruct
      · obtain ⟨Hmn1, Hmn2⟩ := lessor.mark_none (lessor.rlSub kl hl) Prod.fst chan.nil subs
          (by rw [← Hr]; rfl)
        rw [Hmn1, Hmn2]
        unfold forMapPostcondition
        ileft
        isplitr
        · ipureintro; rfl
        iexists m'
        iframe Hm
        isplitl
        · iexists v
          simp only [named]
          iframe
          iapply (BigSepM.bigSepM_delete (m := m') Hv').2
          iframe HM
          unfold lessor.kaOwn
          iexists chsSl, ctxsSl, subs
          iframe
          ipureintro; exact Hsubs
        · ipureintro; intro k _; rfl
      · have HrL : sint.nat r ≤ subs.length := by omega
        have HKn : sint.nat (chsSl.len - r) = (subs.filter (fun p => !lessor.rlSub kl hl p)).length := by
          have Hr0 := Hn.2.2.1
          word
        wp_apply (wp_slice_make2 (V := GoChan) (chsSl.len - r)) as %nsl ⟨Hns, Hnc⟩
        · ipureintro; word
        ihave %Hnsl := ownSlice_len $$ Hns
        wp_apply (wp_slice_make2 (V := GoInterface) nsl.len) as %ncsl ⟨Hncs, Hncc⟩
        · ipureintro; word
        rename_i iu2_ptr
        irename : (iu2_ptr ↦ (zero_val w64) : IProp GF) => iu2
        have HnslK : sint.nat nsl.len =
            (subs.filter (fun p => !lessor.rlSub kl hl p)).length := by
          rw [← HKn, ← Hnsl.1, List.length_replicate]
        rw [HnslK, HKn]
        ihave IH2 : iprop(∃ (j : w64) (iv : w64) (ni : w64),
            "i" ∷ i_ptr ↦ j ∗ "iu2" ∷ iu2_ptr ↦ iv ∗ "newIdx" ∷ newIdx_ptr ↦ ni ∗
            "Hns" ∷ nsl ↦* (((subs.take (sint.nat j)).filter (fun p => !lessor.rlSub kl hl p)).map
              Prod.fst ++ List.replicate ((subs.filter (fun p => !lessor.rlSub kl hl p)).length -
              ((subs.take (sint.nat j)).filter (fun p => !lessor.rlSub kl hl p)).length)
              (zero_val GoChan)) ∗
            "Hncs" ∷ ncsl ↦* (((subs.take (sint.nat j)).filter (fun p => !lessor.rlSub kl hl p)).map
              Prod.snd ++
              List.replicate ((subs.filter (fun p => !lessor.rlSub kl hl p)).length -
              ((subs.take (sint.nat j)).filter (fun p => !lessor.rlSub kl hl p)).length)
              (zero_val GoInterface)) ∗
            "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.nat j ≤ subs.length ∧ 0 ≤ sint.Z ni ∧
              sint.nat ni = ((subs.take (sint.nat j)).filter
                (fun p => !lessor.rlSub kl hl p)).length⌝) $$ [i iu2 newIdx Hns Hncs]
        · iexists W64 0, _, W64 0
          simp only [named, show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.filter_nil,
            List.map_nil, List.nil_append, List.length_nil, Nat.sub_zero]
          iframe
          ipureintro; exact ⟨by word, by omega, by word, by simp⟩
        wp_for IH2
        wp_if_destruct
        · have Hlt : sint.nat j < subs.length := by word
          have Hbnd : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z chsSl.len := ⟨Hj.1, Hif⟩
          have Hjnat : (sint.Z j).toNat = sint.nat j := rfl
          have Hmk : (subs.map (fun p => if lessor.rlSub kl hl p then chan.nil else p.1))[
              (sint.Z j).toNat]? = some (if lessor.rlSub kl hl subs[sint.nat j] then chan.nil
                else subs[sint.nat j].1) := by
            rw [Hjnat, List.getElem?_map, List.getElem?_eq_getElem Hlt]; rfl
          rw [if_pos Hbnd]
          wp_apply wp_load_slice_index chsSl (sint.Z j) _ _ _ Hj.1 $$ [HchsS] as HchsS
          · iframe; ipureintro; exact Hmk
          rw [if_pos Hbnd]
          wp_apply wp_load_slice_index chsSl (sint.Z j) _ _ _ Hj.1 $$ [HchsS] as HchsS
          · iframe; ipureintro; exact Hmk
          have Hstep := lessor.compact_step (lessor.rlSub kl hl) subs (sint.nat j) Hlt
          have Hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
          cases hq : lessor.rlSub kl hl subs[sint.nat j]
          · have Hne : subs[sint.nat j].1 ≠ chan.nil := Hsubs.1 _ (List.getElem_mem Hlt)
            simp only [hq, Bool.false_eq_true, ↓reduceIte] at Hstep ⊢
            simp only [Hne, _root_.decide_false]
            ihave %HnsL := ownSlice_len $$ Hns
            ihave %HncsL := ownSlice_len $$ Hncs
            have HA1 := lessor.length_filter_take_le (fun p => !lessor.rlSub kl hl p) subs
              (sint.nat j + 1)
            have HAn := lessor.length_filter_take_le_n (fun p => !lessor.rlSub kl hl p) subs
              (sint.nat j)
            rw [Hstep, List.length_append, List.length_singleton] at HA1
            simp only [List.length_append, List.length_map, List.length_replicate] at HnsL HncsL
            have HniA := Hj.2.2.2
            have Hnb : 0 ≤ sint.Z ni ∧ sint.Z ni < sint.Z nsl.len := ⟨Hj.2.2.1, by word⟩
            have Hncb : 0 ≤ sint.Z ni ∧ sint.Z ni < sint.Z ncsl.len := ⟨Hj.2.2.1, by word⟩
            have Hcb : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z ctxsSl.len := ⟨Hj.1, by word⟩
            wp_auto
            rw [if_pos Hnb]
            wp_auto
            rw [if_pos Hncb]
            wp_auto
            rw [if_pos Hbnd]
            wp_apply wp_load_slice_index chsSl (sint.Z j) _ _ _ Hj.1 $$ [HchsS] as HchsS
            · iframe; ipureintro; exact Hmk
            rw [if_pos Hcb]
            simp only [hq, Bool.false_eq_true, ↓reduceIte]
            wp_apply wp_load_slice_index ctxsSl (sint.Z j) (subs.map Prod.snd) _
              (subs[sint.nat j]).2 Hj.1 $$ [HctxsS] as HctxsS
            · iframe; ipureintro
              rw [Hjnat, List.getElem?_map, List.getElem?_eq_getElem Hlt]; rfl
            have Hnin : (sint.Z ni).toNat =
                ((subs.take (sint.nat j)).filter (fun p => !lessor.rlSub kl hl p)).length := HniA
            wp_apply wp_store_slice_index nsl (sint.Z ni) _ subs[sint.nat j].1 $$ [Hns] as Hns
            · iframe; ipureintro
              refine ⟨Hj.2.2.1, ?_⟩
              simp only [List.length_append, List.length_map, List.length_replicate]
              omega
            wp_apply wp_store_slice_index ncsl (sint.Z ni) _ _ $$ [Hncs] as Hncs
            · iframe; ipureintro
              refine ⟨Hj.2.2.1, ?_⟩
              simp only [List.length_append, List.length_map, List.length_replicate]
              omega
            have Hpos : 0 < (subs.filter (fun p => !lessor.rlSub kl hl p)).length -
                ((subs.take (sint.nat j)).filter (fun p => !lessor.rlSub kl hl p)).length := by
              omega
            have Hnin' : (sint.Z ni).toNat =
                (((subs.take (sint.nat j)).filter (fun p => !lessor.rlSub kl hl p))).length := HniA
            rw [Hnin', lessor.compact_snd _ subs[sint.nat j] _ _ Hpos]
            rw [lessor.compact_chs _ subs[sint.nat j] _ _ Hpos]
            wp_for_post
            iframe
            iexists j + W64 1, _, ni + W64 1
            simp only [named]
            rw [Hj1, Hstep]
            simp only [List.length_append, List.length_singleton, Nat.sub_sub]
            iframe
            ipureintro
            have Hni1 : sint.nat (ni + W64 1) = sint.nat ni + 1 := by word
            exact ⟨by word, by omega, by word, by rw [Hni1, HniA]⟩
          · simp only [hq, ↓reduceIte, if_true] at Hstep ⊢
            wp_auto
            wp_for_post
            iframe
            iexists j + W64 1, _, ni
            simp only [named]
            rw [Hj1, Hstep, List.append_nil]
            iframe
            ipureintro
            exact ⟨by word, by omega, Hj.2.2.1, by rw [Hj.2.2.2]⟩
        · have Hjl : sint.nat j = subs.length := by word
          rw [Hjl, List.take_of_length_le (Nat.le_refl _)]
          simp only [Nat.sub_self, List.replicate_zero, List.append_nil]
          unfold forMapPostcondition
          iright; ileft
          isplitr
          · ipureintro; rfl
          iexists m'
          iframe Hm
          isplitl
          · iexists v
            simp only [named]
            iframe
            iapply (BigSepM.bigSepM_delete (m := m') Hv').2
            iframe HM
            unfold lessor.kaOwn
            iexists nsl, ncsl, subs.filter (fun p => !lessor.rlSub kl hl p)
            iframe
            ipureintro
            exact ⟨fun q hq => Hsubs.1 q (List.mem_filter.1 hq).1,
              fun q hq => Hsubs.2 q (List.mem_filter.1 hq).1⟩
          · ipureintro; intro k _; rfl
  · iintro %m' HP Hm
    iNamed HP
    wp_auto
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked Hkas Hm HM]
    · inext
      unfold lessor.muInv
      iexists mp, m'
      iframe
    iapply HΦ
    itrivial

end proof

end EtcdGrove
end Perennial
