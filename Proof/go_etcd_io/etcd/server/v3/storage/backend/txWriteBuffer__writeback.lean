/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/backend/txWriteBuffer__writeback.lean`.
Lean-first (no Rocq counterpart).

The loop over the write buffer's buckets: after the first `i` keys `D`, a bucket of `D` the read
buffer did not have is moved there (deleted here), canonical (`dedupe`, or already sorted); one
it had is merged into the read buffer's (`merge`), after `sort.Sort` if `put` wrote it. The read
buffer's buckets are `wbMerge` on `D`, as they were elsewhere; the write buffer's are as they
were outside `D`, and on `D` empty exactly when the moved-out model (`writebackW`'s filter) says
so, which is all `reset` looks at (`bksReset_congr`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.txWriteBuffer__writeback
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.bucketBuffer__dedupe
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.bucketBuffer__Len
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.bucketBuffer__Less
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.bucketBuffer__Swap
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.bucketBuffer__merge
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.txWriteBuffer__reset
public import Spec.sort.Sort
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.ModelLemmas
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.WBufLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace backend

/-! ## Pure facts -/

/-- `txBuffer.reset` sees only which buckets are empty. -/
theorem bksReset_congr {B1 B2 : GMap w64 (List Ent)}
    (h : ∀ id, (B1 !! id).map List.isEmpty = (B2 !! id).map List.isEmpty) :
    bksReset B1 = bksReset B2 := by
  apply GMap.ext; intro id
  have := h id
  show (bksReset B1) !! id = (bksReset B2) !! id
  unfold bksReset
  rw [GMap.lookup_fmap, GMap.lookup_fmap, GMap.lookup_filter, GMap.lookup_filter]
  cases h1 : B1 !! id <;> cases h2 : B2 !! id <;> rw [h1, h2] at this <;> simp_all [Option.filter]
  · rename_i a b
    cases ha : a.isEmpty <;> simp_all

theorem WBuf.reset_congr {W1 W2 : WBuf} (hb : bksReset W1.bks = bksReset W2.bks)
    (hs : W1.seq = W2.seq) : W1.reset = W2.reset := by
  unfold WBuf.reset; simp only [hb, hs]

theorem wbMerge_lookup_some {W R : GMap w64 (List Ent)} {id : w64} {es : List Ent}
    (h : W !! id = some es) : wbMerge W R !! id = some (canon (bkOf R id ++ es)) := by
  unfold wbMerge
  rw [show GMap.union (gmapImap (fun id es => canon (bkOf R id ++ es)) W) R =
    (gmapImap (fun id es => canon (bkOf R id ++ es)) W) ∪ R from rfl, GMap.lookup_union]
  show (((W.lookup id).map _).or _) = _
  rw [show W.lookup id = some es from h]
  rfl

theorem wbMerge_lookup_none {W R : GMap w64 (List Ent)} {id : w64}
    (h : W !! id = none) : wbMerge W R !! id = R !! id := by
  unfold wbMerge
  rw [show GMap.union (gmapImap (fun id es => canon (bkOf R id ++ es)) W) R =
    (gmapImap (fun id es => canon (bkOf R id ++ es)) W) ∪ R from rfl, GMap.lookup_union]
  show (((W.lookup id).map _).or _) = _
  rw [show W.lookup id = none from h]
  rfl

theorem entsSorted_le_one (es : List Ent) (h : es.length ≤ 1) : entsSorted es := by
  unfold entsSorted
  match es, h with
  | [], _ => exact List.Pairwise.nil
  | [_], _ => exact List.pairwise_singleton _ _

end backend

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.backend backend

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- A bucket buffer is a `sort.Interface` over its entries, ordered by key. -/
theorem backend.txWriteBuffer.writeback.bbSorter
    (hLen : backend.bucketBuffer.Len.spec (GF := GF) (hG := hG))
    (hLess : backend.bucketBuffer.Less.spec (GF := GF) (hG := hG))
    (hSwap : backend.bucketBuffer.Swap.spec (GF := GF) (hG := hG)) (bb : Loc) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ⊢
      sorterSpec (interface.mk (go.GoType.PointerType bucketBuffer.ty) #bb) (ownBB bb)
        (fun a b : Ent => decide (strLt a.1 b.1)) := by
  iintro #Hpkg
  unfold sorterSpec
  isplitr
  · imodintro
    iintro %l
    iintro !> %Φ Hl HΦ
    iapply (hLen bb l) $$ [$Hpkg $Hl] HΦ
  isplitr
  · imodintro
    iintro %l %i %j %a %b %Hij
    iintro !> %Φ Hl HΦ
    obtain ⟨hi, hj, ha, hb⟩ := Hij
    iapply (hLess bb l i j a b hi hj ha hb) $$ [$Hpkg $Hl] HΦ
  imodintro
  iintro %l %i %j %a %b %Hij
  iintro !> %Φ Hl HΦ
  obtain ⟨hi, hj, ha, hb⟩ := Hij
  iapply (hSwap bb l i j a b hi hj ha hb) $$ [$Hpkg $Hl] HΦ

theorem backend.txWriteBuffer.writeback.wp_proof
    (hDedupe : backend.bucketBuffer.dedupe.spec (GF := GF) (hG := hG))
    (hSort : sort.«Sort».spec (GF := GF) (hG := hG))
    (hLen : backend.bucketBuffer.Len.spec (GF := GF) (hG := hG))
    (hLess : backend.bucketBuffer.Less.spec (GF := GF) (hG := hG))
    (hSwap : backend.bucketBuffer.Swap.spec (GF := GF) (hG := hG))
    (hMerge : backend.bucketBuffer.merge.spec (GF := GF) (hG := hG))
    (hReset : backend.txWriteBuffer.reset.spec (GF := GF) (hG := hG)) :
    backend.txWriteBuffer.writeback.spec (GF := GF) (hG := hG) := by
  intro txw W txr R HWf HRf Hbound
  wp_start as ⟨HWb, HRb⟩
  unfold ownWB
  icases HWb with ⟨%mW, %s, HbkW, Hseq, HbksW, Hs⟩
  unfold ownRB
  icases HRb with ⟨%mR, HbkR, Hver, HbksR⟩
  icases ownBks_open mW W.bks $$ HbksW with ⟨%MW, HmW, HW⟩
  icases ownBks_open mR R.bks $$ HbksR with ⟨%MR, HmR, HR⟩
  ihave %HdomW := bksOwn_dom MW W.bks $$ HW
  wp_auto
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range_gen (fun (keys : List w64) (i : Nat) (MW' : GMap w64 Loc) =>
      iprop(∃ (kv : w64) (wv : Loc) (BW BR : GMap w64 (List Ent)) (MR' : GMap w64 Loc),
        "k" ∷ k_ptr ↦ kv ∗ "wb" ∷ wb_ptr ↦ wv ∗ "txw" ∷ txw_ptr ↦ txw ∗ "txr" ∷ txr_ptr ↦ txr ∗
        "HbkW" ∷ structFieldRef txWriteBuffer go!"txBuffer" txw ↦ ({ buckets' := mW } : txBuffer) ∗
        "Hseq" ∷ structFieldRef txWriteBuffer go!"bucket2seq" txw ↦ s ∗
        "Hs" ∷ s ↦$ W.seq ∗
        "HbkR" ∷ structFieldRef txReadBuffer go!"txBuffer" txr ↦ ({ buckets' := mR } : txBuffer) ∗
        "Hver" ∷ structFieldRef txReadBuffer go!"bufVersion" txr ↦ R.ver ∗
        "HW" ∷ bksOwn MW' BW ∗ "HmR" ∷ mR ↦$ MR' ∗ "HR" ∷ bksOwn MR' BR ∗
        "%HBW" ∷ ⌜∀ id, id ∉ keys.take i → BW !! id = W.bks !! id⌝ ∗
        "%HBW'" ∷ ⌜∀ id, id ∈ keys.take i → (BW !! id).map List.isEmpty =
            ((W.bks.filter (fun id _ => decide (id ∈ R.bks))) !! id).map List.isEmpty⌝ ∗
        "%HBR" ∷ ⌜∀ id, BR !! id =
            if id ∈ keys.take i then wbMerge W.bks R.bks !! id else R.bks !! id⌝))
    _ _ _ mW MW (DFrac.own 1) $$ HmW
  iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
  isplitl [k wb txw txr HbkW Hseq Hs HbkR Hver HW HmR HR]
  · iexists _, _, W.bks, R.bks, MR
    simp only [named]
    iframe
    ipureintro
    refine ⟨fun _ _ => by simp, fun id h => by simp at h, fun id => by simp⟩
  isplitr
  · imodintro
    iintro %i %key %wbv %MW' ⟨%Hki, %Hmv⟩ HP HmW
    iNamed HP
    ihave %HdomW' := bksOwn_dom _ _ $$ HW
    ihave %HdomR' := bksOwn_dom _ _ $$ HR
    have hnot := not_mem_take_of_getElem?' Hknodup Hki
    have htake := take_succ_of_getElem? Hki
    obtain ⟨es, hBW⟩ := bksOwn_some HdomW' Hmv
    have hWk : W.bks !! key = some es := by rw [← HBW key hnot]; exact hBW
    have hBRk : BR !! key = R.bks !! key := by rw [HBR key]; simp [hnot]
    wp_auto
    wp_apply wp_map_lookup2 $$ HmR as HmR
    have hwf0 := HWf key es hWk
    cases hMR : MR' !! key with
    | none =>
      have hRk : R.bks !! key = none := by rw [← hBRk]; exact bksOwn_none HdomR' hMR
      -- a bucket the read buffer lacks may repeat a key: `dedupe` canonicalizes it anyway
      have hwf : wbBucketOk (W.seq !! key) es ∨ W.seq !! key = some false :=
        hwf0.imp_right And.left
      unfold wbBucketOk at hwf
      simp only [Option.isSome_none, Bool.false_eq_true, decide_false, Bool.not_false]
      wp_auto
      wp_apply wp_mapDelete $$ HmW as HmW
      icases bksOwn_delete Hmv hBW $$ HW with ⟨Hwb, HW⟩
      wp_apply wp_map_lookup2 $$ Hs as Hs
      have hlen : es.length < bufBound := by
        have := Hbound key; unfold bkOf at this; rw [hWk, hRk] at this; simpa using this
      rcases hseq : W.seq !! key with _ | ⟨_ | _⟩
      all_goals simp only [hseq, Option.isSome_none, Option.isSome_some, Bool.false_eq_true,
        decide_false, _root_.decide_true, ↓reduceIte, reduceCtorEq, Option.some.injEq,
        Bool.true_eq_false, _root_.or_false] at hwf ⊢
      all_goals wp_auto
      all_goals first
        | wp_apply (hDedupe wbv es) $$ [$Hwb] as Hwb
        | (ihave Hwb : ownBB wbv (canon es) $$ [Hwb]
           · rw [canon_of_sorted hwf]; iexact Hwb)
      all_goals
        wp_apply wp_mapInsert $$ HmR as HmR
        ihave HR := bksOwn_insert hMR $$ [$HR $Hwb]
        unfold forMapPostcondition
        ileft
        isplitr
        · ipureintro; rfl
        iexists _
        iframe HmW
        iexists key, wbv, GMap.delete key BW, <[key := canon es]> BR, <[key := wbv]> MR'
        simp only [named]
        iframe
        ipureintro
        refine ⟨?_, ?_, ?_⟩
        · intro id hid
          rw [htake] at hid
          have hne : id ≠ key := fun h => hid (by rw [h]; exact List.mem_append_right _ (List.mem_singleton_self _))
          rw [GMap.lookup_delete_ne _ (Ne.symm hne)]
          exact HBW id (fun h => hid (List.mem_append_left _ h))
        · intro id hid
          rw [htake, List.mem_append, List.mem_singleton] at hid
          by_cases he : id = key
          · subst he
            rw [GMap.lookup_delete, GMap.lookup_filter, hWk]
            simp [GMap.mem_iff, hRk]
          · rw [GMap.lookup_delete_ne _ (Ne.symm he)]
            exact HBW' id (hid.resolve_right he)
        · intro id
          rw [htake]
          by_cases he : id = key
          · subst he
            rw [GMap.lookup_insert, wbMerge_lookup_some hWk]
            simp [bkOf, hRk]
          · rw [GMap.lookup_insert_ne _ _ (Ne.symm he), HBR id]
            simp [he]
    | some rbv =>
      obtain ⟨res, hBRr⟩ := bksOwn_some HdomR' hMR
      have hRk : R.bks !! key = some res := by rw [← hBRk]; exact hBRr
      have hwf : wbBucketOk (W.seq !! key) es :=
        hwf0.resolve_right (fun h => by rw [h.2] at hRk; cases hRk)
      unfold wbBucketOk at hwf
      have hRs : entsSorted res := HRf key res hRk
      have hlen : res.length + es.length < bufBound := by
        have := Hbound key; unfold bkOf at this; rw [hWk, hRk] at this; simpa using this
      simp only [Option.isSome_some, _root_.decide_true, Bool.not_true, Option.getD_some]
      wp_auto
      wp_apply wp_map_lookup2 $$ Hs as Hs
      icases bksOwn_acc Hmv hBW $$ HW with ⟨Hwb, HWback⟩
      rcases hseq : W.seq !! key with _ | ⟨_ | _⟩
      all_goals simp only [hseq, Option.isSome_none, Option.isSome_some, Bool.false_eq_true,
        decide_false, _root_.decide_true, ↓reduceIte, reduceCtorEq] at hwf ⊢
      case' some.false =>
        iunfold ownBB at Hwb
        icases Hwb with ⟨%p, Hwb, %Hok⟩
        iunfold bbAt at Hwb
        icases Hwb with ⟨Hbb, Hsl, Hcap, #Hro, #Hin⟩
        wp_auto
        ihave Hwb : ownBB wbv es $$ [Hbb Hsl Hcap]
        · iunfold ownBB
          iexists p
          iunfold bbAt
          iframe Hbb Hsl Hcap Hro Hin
          ipureintro; exact Hok
        have hlen' : es.length < bufBound := by omega
        unfold bufBound at hlen'
        by_cases hgt : 1 < es.length
        case' pos =>
          rw [_root_.decide_eq_true (show sint.Z (W64 1) < sint.Z (W64 es.length) by word)]
          wp_auto
          ihave #Hsorter := backend.txWriteBuffer.writeback.bbSorter hLen hLess hSwap wbv $$ Hpkg
          wp_apply (hSort Ent (interface.mk (go.GoType.PointerType bucketBuffer.ty) #wbv) (ownBB wbv)
              (fun a b : Ent => decide (strLt a.1 b.1)) es entLt_swo) $$ [$Hsorter $Hwb]
            as %es2 ⟨Hwb, %Hes2⟩
          · ipureintro; omega
          have hperm : es.Perm es2 := Hes2.1
          have hs2 : entsSorted es2 := entsSorted_of_sorted_nodup Hes2.1 hwf Hes2.2
          have hnd : (es.map Prod.fst).Nodup := hwf
        case' neg =>
          rw [_root_.decide_eq_false (show ¬ sint.Z (W64 1) < sint.Z (W64 es.length) by word)]
          wp_auto
          obtain ⟨es2, hes2⟩ : ∃ es2, es2 = es := ⟨es, rfl⟩
          ihave Hwb : ownBB wbv es2 $$ [Hwb]
          · rw [hes2]; iexact Hwb
          have hperm : es.Perm es2 := hes2 ▸ List.Perm.refl es
          have hs2 : entsSorted es2 := hes2 ▸ entsSorted_le_one es (by omega)
          have hnd : (es.map Prod.fst).Nodup := hwf
      case' none | some.true =>
        wp_auto
        obtain ⟨es2, hes2⟩ : ∃ es2, es2 = es := ⟨es, rfl⟩
        ihave Hwb : ownBB wbv es2 $$ [Hwb]
        · rw [hes2]; iexact Hwb
        have hperm : es.Perm es2 := hes2 ▸ List.Perm.refl es
        have hs2 : entsSorted es2 := hes2 ▸ hwf
        have hnd : (es.map Prod.fst).Nodup := entsSorted_nodup hwf
      all_goals
        icases bksOwn_acc hMR hBRr $$ HR with ⟨Hrb, HRback⟩
        wp_apply (hMerge rbv res wbv es2 hRs hs2 (by rw [← hperm.length_eq]; exact hlen))
          $$ [$Hrb $Hwb] as ⟨Hrb, Hwb⟩
        ihave HW := HWback $$ %es2 Hwb
        ihave HR := HRback $$ %(canon (res ++ es2)) Hrb
        unfold forMapPostcondition
        iright; ileft
        isplitr
        · ipureintro; rfl
        iexists MW'
        iframe HmW
        iexists key, wbv, <[key := es2]> BW, <[key := canon (res ++ es2)]> BR, MR'
        simp only [named]
        iframe
        ipureintro
        refine ⟨?_, ?_, ?_⟩
        · intro id hid
          rw [htake] at hid
          have hne : id ≠ key := fun h =>
            hid (by rw [h]; exact List.mem_append_right _ (List.mem_singleton_self _))
          rw [GMap.lookup_insert_ne _ _ (Ne.symm hne)]
          exact HBW id (fun h => hid (List.mem_append_left _ h))
        · intro id hid
          rw [htake, List.mem_append, List.mem_singleton] at hid
          by_cases he : id = key
          · subst he
            rw [GMap.lookup_insert, GMap.lookup_filter, hWk]
            have : decide (id ∈ R.bks) = true := by simp [GMap.mem_iff, hRk]
            simp only [Option.map_some, Option.filter, this, ↓reduceIte, Option.some.injEq]
            cases es <;> cases es2 <;> simp_all [List.Perm.length_eq hperm] <;>
              exact absurd hperm.length_eq (by simp)
          · rw [GMap.lookup_insert_ne _ _ (Ne.symm he)]
            exact HBW' id (hid.resolve_right he)
        · intro id
          rw [htake]
          by_cases he : id = key
          · subst he
            rw [GMap.lookup_insert, wbMerge_lookup_some hWk]
            simp only [List.mem_append, List.mem_singleton, _root_.or_true, ↓reduceIte, bkOf, hRk,
              Option.getD_some]
            rw [canon_append_perm hperm hnd]
          · rw [GMap.lookup_insert_ne _ _ (Ne.symm he), HBR id]
            simp [he]
  isplitr
  · imodintro
    iintro %i %key %MW' ⟨%Hki, %Hnone⟩ HP
    iNamed HP
    ihave %HdomW' := bksOwn_dom _ _ $$ HW
    exfalso
    have hnot := not_mem_take_of_getElem?' Hknodup Hki
    have h1 := (Hkset key).1 (List.mem_of_getElem? Hki)
    have h2 := HdomW' key
    rw [Hnone, HBW key hnot, ← HdomW key, h1] at h2
    cases h2
  iintro %MW' HP HmW
  iNamed HP
  rw [List.take_length] at HBW HBW' HBR
  have hWnone : ∀ id, id ∉ keys → W.bks !! id = none := by
    intro id h
    cases hw : W.bks !! id with
    | none => rfl
    | some _ =>
      exact absurd ((Hkset id).2 (by rw [HdomW id, hw]; rfl)) h
  have hBR : BR = wbMerge W.bks R.bks := by
    apply GMap.ext; intro id
    show BR !! id = wbMerge W.bks R.bks !! id
    rw [HBR id]
    by_cases h : id ∈ keys
    · simp only [h, ↓reduceIte]
    · simp only [h, ↓reduceIte]
      rw [wbMerge_lookup_none (hWnone id h)]
  have hreset : ({ bks := BW, seq := W.seq } : WBuf).reset = writebackW W R := by
    unfold writebackW
    refine WBuf.reset_congr ?_ rfl
    apply bksReset_congr; intro id
    by_cases h : id ∈ keys
    · exact HBW' id h
    · show (BW !! id).map List.isEmpty = ((W.bks.filter _) !! id).map List.isEmpty
      rw [HBW id h, GMap.lookup_filter, hWnone id h]; rfl
  subst hBR
  wp_auto
  wp_apply (hReset txw { bks := BW, seq := W.seq }) $$ [HbkW Hseq Hs HW HmW] as HWb
  · unfold ownWB
    iexists mW, s
    iframe HbkW Hseq Hs
    iapply ownBks_close
    iframe HmW HW
  rw [hreset]
  iapply HΦ
  iunfold ownWB at HWb
  iframe HWb
  iexists mR
  simp only [writebackR]
  iframe HbkR Hver
  iapply ownBks_close
  iframe HmR HR

end proof

end EtcdGrove
end Perennial
