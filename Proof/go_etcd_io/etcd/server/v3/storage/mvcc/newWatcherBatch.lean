/-
Proof of `Spec/.../mvcc/newWatcherBatch.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.newWatcherBatch
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watcherGroup__watcherSetByKey
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watcherBatch__add

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem mvcc.newWatcherBatch.wp_proof
    (hSet : mvcc.watcherGroup.watcherSetByKey.spec (GF := GF) (hG := hG))
    (hAdd : mvcc.watcherBatch.add.spec (GF := GF) (hG := hG)) :
    mvcc.newWatcherBatch.spec (GF := GF) (hG := hG) := by
  intro wg W ST evs dq es evm
  wp_start as ⟨Hg, HST, %Hdom, Hevs, #Hes, %Hlen⟩
  ihave %Hsl := ownSlice_len $$ Hevs
  icases mvcc.ownWatcherGroup_watchers wg W $$ Hg with ⟨%v, Hwg, Hws, Hback⟩
  iunfold mvcc.ownWatcherSet at Hws
  wp_auto
  wp_apply wp_map_len_lt $$ Hws as ⟨Hws, %Hlt⟩
  ihave Hg := Hback $$ Hwg [Hws]
  · iunfold mvcc.ownWatcherSet; iexact Hws
  have hs : GMap.size (domSet W) = GMap.size W := GMap.map_size_fmap _ _
  rw [hs] at Hlt ⊢
  (try wp_auto)
  by_cases hW : W = ∅
  · subst hW
    rw [GMap.map_size_empty]
    rw [_root_.decide_eq_true (by rfl)]
    wp_auto
    iapply HΦ
    iframe Hg HST Hevs
    ileft; ipureintro; exact ⟨rfl, rfl⟩
  have hW0 : W64 (GMap.size W : Int) ≠ W64 0 := by
    intro h
    apply hW
    apply GMap.map_size_empty_inv
    word
  rw [_root_.decide_eq_false hW0]
  wp_auto
  rw [go.make1_underlying, go.is_underlying (t := watcherBatch.ty)]
  wp_apply (wp_map_make1 (K := Loc) (V := Loc)) as %wbm Hwbm
  (try wp_auto)
  ihave Hwb0 : mvcc.ownWatcherBatch wbm (mvcc.batchOf W ST (evm.take (sint.nat (W64 0)))) $$ [Hwbm]
  · iunfold mvcc.ownWatcherBatch
    iexists ∅
    rw [GMap.fmap_empty]
    iframe Hwbm
    isplitl []
    · ipureintro
      rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero, mvcc.batchOf_nil, GMap.fmap_empty]
    iapply BigSepM.bigSepM_empty.2; iempintro
  ihave IH : iprop(∃ (n : w64) (evv : Loc),
      "i" ∷ i_ptr ↦ n ∗ "ev" ∷ ev_ptr ↦ evv ∗ "Hg" ∷ mvcc.ownWatcherGroup wg W ∗
      "HST" ∷ mvcc.ownStates ST ∗ "Hevs" ∷ evs ↦*{dq} es ∗ "wg" ∷ wg_ptr ↦ wg ∗ "wb" ∷ wb_ptr ↦ wbm ∗
      "Hwb" ∷ mvcc.ownWatcherBatch wbm (mvcc.batchOf W ST (evm.take (sint.nat n))) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z evs.len⌝) $$ [i ev Hg HST Hevs wg wb Hwb0]
  · iexists W64 0, _
    simp only [named]
    iframe
    ipureintro; exact ⟨by decide, Hsl.2⟩
  wp_for IH
  wp_if_destruct
  · have Hlt' : sint.nat n < es.length := by have := Hsl.1; word
    obtain ⟨en, Hen⟩ : ∃ en, es[sint.nat n]? = some en := ⟨_, List.getElem?_eq_getElem Hlt'⟩
    obtain ⟨evn, Hevn⟩ : ∃ evn, evm[sint.nat n]? = some evn :=
      ⟨_, List.getElem?_eq_getElem (by rw [← Hlen]; exact Hlt')⟩
    rw [ite_eq_left (show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z evs.len by constructor <;> word)]
    wp_apply wp_load_slice_index evs (sint.Z n) es _ en Hn.1 $$ [Hevs] as Hevs
    · iframe Hevs; ipureintro; exact Hen
    have hzip : (es.zip evm)[sint.nat n]? = some (en, evn) := by
      rw [List.getElem?_zip_eq_some]; exact ⟨Hen, Hevn⟩
    ihave #He : mvcc.evIs en evn $$ []
    · iapply (BigSepL.bigSepL_lookup hzip) $$ Hes
    ihave #He' := He
    iunfold mvcc.evIs at He'
    icases He' with ⟨%p, %q, %st, %uf, %sc, %Hnn, #Hev, #Hkv, #Hprev⟩
    ihave #Hkv' := Hkv
    iunfold mvcc.kvPtrFixed at Hkv'
    icases Hkv' with ⟨%ks, %vs, %kst, %kuf, %ksc, #Hks, -, #Hk⟩
    icases mvcc.event_fields _ _ _ $$ Hev with ⟨#HevT, #HevK, #HevP⟩
    icases mvcc.kv_fields _ _ _ $$ Hk with ⟨#HkK, #HkM⟩
    wp_auto
    simp only
    wp_apply wp_bytes_to_string ks evn.kv.key DFrac.discard $$ [$Hks] as -
    wp_apply (hSet wg W evn.kv.key) $$ [$Hg] as %m ⟨Hm, Hgback⟩
    have htake : evm.take (sint.nat (n + W64 1)) = evm.take (sint.nat n) ++ [evn] := by
      rw [show sint.nat (n + W64 1) = sint.nat n + 1 by word, List.take_add_one, Hevn]; rfl
    iunfold mvcc.ownWatcherSetOpt at Hm
    icases Hm with (%Hnil | Hm)
    · -- no member holds the key
      obtain ⟨rfl, HS⟩ := Hnil
      wp_func_lits
      wp_auto
      ihave Hg := Hgback $$ []
      · iunfold mvcc.ownWatcherSetOpt; ileft; ipureintro; exact ⟨rfl, HS⟩
      have hB : mvcc.batchOf W ST (evm.take (sint.nat n) ++ [evn]) =
          mvcc.batchOf W ST (evm.take (sint.nat n)) := by
        rw [← mvcc.batchOf_snoc W ST _ evn [] List.nodup_nil (fun w => by rw [HS]; simp)]; rfl
      wp_for_post
      iframe
      iexists n + W64 1, en
      simp only [named]
      rw [htake, hB]
      iframe
      ipureintro; constructor <;> word
    iunfold mvcc.ownWatcherSet at Hm
    wp_func_lits
    wp_bind (App (App (Val (map.forRange _ _)) _) _)
    iapply (wp_wand_r (Φ := fun bv => iprop(⌜bv = executeVal⌝ ∗
        m ↦$ mvcc.membersBy W (·.covers evn.kv.key) ∗ ev_ptr ↦ en ∗ wb_ptr ↦ wbm ∗
        (∃ wv : Loc, w_ptr ↦ wv) ∗ mvcc.ownStates ST ∗
        mvcc.ownWatcherBatch wbm (mvcc.batchOf W ST (evm.take (sint.nat n) ++ [evn])))))
    isplitl [Hm ev wb w HST Hwb]
    · iapply wp_map_for_range (fun (keys : List Loc) (j : Int) => iprop(∃ (wv : Loc),
          "ev" ∷ ev_ptr ↦ en ∗ "wb" ∷ wb_ptr ↦ wbm ∗ "w" ∷ w_ptr ↦ wv ∗ "HST" ∷ mvcc.ownStates ST ∗
          "Hwb" ∷ mvcc.ownWatcherBatch wbm
            (mvcc.batchStepL ST evn (keys.take j.toNat) (mvcc.batchOf W ST (evm.take (sint.nat n)))) ∗
          "%Hj" ∷ ⌜0 ≤ j⌝)) $$ Hm
      iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
      isplitl [ev wb w HST Hwb]
      · iexists _
        simp only [named]
        iframe
        ipureintro; exact Int.le_refl _
      isplitr
      · imodintro
        iintro %j %key %u ⟨%Hkey, %Hu⟩ HP
        iNamed HP
        obtain ⟨r, hr, hcov⟩ := (mvcc.mem_membersBy W _ key).1 (by rw [Hu]; rfl)
        obtain ⟨stw, hstw⟩ : ∃ stw, ST !! key = some stw :=
          Option.isSome_iff_exists.1 (Hdom key (by rw [hr]; rfl))
        iunfold mvcc.ownStates at HST
        icases (BigSepM.bigSepM_lookup_acc hstw).1 $$ HST with ⟨Hw, HST⟩
        iunfold mvcc.watcherOwn at Hw
        icases Hw with ⟨Hmin, Hvic, Hcomp, Hres, Hch⟩
        wp_auto
        ihave HST := HST $$ [Hmin Hvic Hcomp Hres Hch]
        · iunfold mvcc.watcherOwn; iframe
        have Hstep : ∀ B : GMap Loc mvcc.EventBatch,
            mvcc.batchStepL ST evn (keys.take (j + 1).toNat) B =
              (if mvcc.minRevLe ST evn key then
                <[key := mvcc.ebAdd
                  ((mvcc.batchStepL ST evn (keys.take j.toNat) B !! key).getD .empty) evn]>
                  (mvcc.batchStepL ST evn (keys.take j.toNat) B)
              else mvcc.batchStepL ST evn (keys.take j.toNat) B) := by
          intro B
          rw [show (j + 1).toNat = j.toNat + 1 by omega, List.take_add_one, Hkey]
          simp only [Option.toList_some]
          unfold mvcc.batchStepL
          rw [List.foldl_append]; rfl
        have Hmle : mvcc.minRevLe ST evn key =
            decide (sint.Z stw.minRev ≤ sint.Z evn.kv.modRev) := by
          unfold mvcc.minRevLe; rw [hstw]
        wp_if_destruct
        · (try wp_auto)
          ihave %Ha1 := typedPointsto_not_null $$ «$a1»
          ipersist «$a1»
          ihave #Hnew : mvcc.evIs «$a1_ptr» evn $$ []
          · iunfold mvcc.evIs
            iexists p, q, _, _, _
            iframe «$a1» Hkv Hprev
            ipureintro; exact ⟨Ha1, Hnn.2⟩
          wp_method_call
          wp_call
          wp_load
          wp_apply (hAdd wbm _ key «$a1_ptr» evn) $$ [$Hwb $Hnew] as Hwb
          (try wp_auto)
          unfold forMapPostcondition
          iright; ileft
          isplitr
          · ipureintro; rfl
          iexists _
          simp only [named]
          rw [Hstep, Hmle, _root_.decide_eq_true Hif]
          iunfold mvcc.ownStates
          iframe
          ipureintro; omega
        · unfold forMapPostcondition
          iright; ileft
          isplitr
          · ipureintro; rfl
          iexists _
          simp only [named]
          rw [Hstep, Hmle, _root_.decide_eq_false Hif]
          iunfold mvcc.ownStates
          iframe
          ipureintro; omega
      iintro HP Hm
      iNamed HP
      isplitr
      · ipureintro; rfl
      iframe Hm ev wb HST
      isplitl [w]
      · iexists wv; iexact w
      rw [show (((GMap.size (mvcc.membersBy W (·.covers evn.kv.key))) : Int)).toNat = keys.length
        by omega, List.take_length, mvcc.batchOf_snoc W ST _ evn keys Hknodup Hkset]
      iexact Hwb
    iintro %bv ⟨%Hbv, Hm, ev, wb, ⟨%wv, w⟩, HST, Hwb⟩
    subst Hbv
    ihave Hg := Hgback $$ [Hm]
    · iunfold mvcc.ownWatcherSetOpt; iright; iunfold mvcc.ownWatcherSet; iexact Hm
    wp_for_post
    iframe
    iexists n + W64 1, en
    simp only [named]
    rw [htake]
    iframe
    ipureintro; constructor <;> word
  have hall : evm.take (sint.nat n) = evm := by
    apply List.take_of_length_le
    have := Hsl.1; rw [← Hlen]; word
  rw [hall]
  iapply HΦ
  iframe Hg HST Hevs
  iright
  iframe Hwb
  ipureintro; exact hW

end proof

end EtcdGrove
end Perennial
