/-
Package `proxy`: executing a decided slot (`proxysmrhandler.go`'s `executeClientBatches`,
`applySMRLogic`).
-/
module

public import Dsverify.Proof.raxos.Proxy.Kv
public import Dsverify.Proof.raxos.Proxy.Store
public import Dsverify.Proof.raxos.Smr.Laws

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Perennial.raxos


open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open Perennial.raxos.pure Perennial.raxos.msg
open raxos.replica.src

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [π : NetProtoGS] [qv : hyp.QpVocab GF]
variable [raxos.replica.src.Assumptions] [raxos.proto.client.Assumptions]

attribute [local instance] HeapGS.goose_globalGS

theorem wp_applySMRLogic (pr bm : Loc) (st : pure.Store) (cs : GoSlice)
    (cbs : List raxos.proto.client.ClientBatch) (bs : List Batch)
    (hok : ∀ b ∈ bs, ∀ c ∈ b.cmds, cmdOk c) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.replica.src ∗ pr.[Proxy, go!"benchmark"] ↦□ bm ∗
        kvOwn bm st ∗ cs ↦*□ cbs ∗ cbsRep cbs bs }}
      (App (Val (pr @!! go.GoType.PointerType Proxy.ty @!! go!"applySMRLogic")) (Val #cs))
    {{ (rs : GoSlice) (outs : List raxos.proto.client.ClientBatch), RET #rs;
        kvOwn bm (runBatches st (bs.map Batch.cmds)).1 ∗ rs ↦* outs ∗
        [∗list] k ↦ o ∈ outs, ∃ b r, ⌜bs[k]? = some b ∧ (runBatches st (bs.map Batch.cmds)).2[k]? = some r⌝ ∗
          repCBVal o (DFrac.own 1) ⟨b.id, b.sender, r⟩ }} := by
  wp_start as ⟨#Hbm, Hkv, #Hcs, Hrep⟩
  wp_auto
  wp_apply wp_Execute bm st cs cbs bs hok $$ [Hkv Hrep] as %rs %outs H
  · iframe Hkv Hrep Hcs
  wp_end

theorem wp_executeClientBatches (γ : QNames) (γs : GName) (pr cb bm ebm : Loc) (sl : GoSlice)
    (ids : List GoString) (Bm : GMap GoString Batch) (es : ExecSt) (E : GMap GoString Bool)
    (hE : doneRel E es.done) (hB : ∀ x ∈ ids, (Bm !! x).isSome)
    (hcmd : ∀ x b, Bm !! x = some b → ∀ c ∈ b.cmds, cmdOk c)
    (hid : ∀ x b, Bm !! x = some b → b.id = x) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.replica.src ∗
        pr.[Proxy, go!"clientBatchStore"] ↦□ cb ∗ isStore γ γs cb ∗
        pr.[Proxy, go!"benchmark"] ↦□ bm ∗ pr.[Proxy, go!"executedBatches"] ↦□ ebm ∗
        ebm ↦$ E ∗ kvOwn bm es.store ∗ sl ↦*□ ids ∗ ([∗list] x ∈ ids, storeHas γs x) ∗
        knownP γ Bm }}
      (App (Val (pr @!! go.GoType.PointerType Proxy.ty @!! go!"executeClientBatches")) (Val #sl))
    {{ (rs : GoSlice) (outs : List raxos.proto.client.ClientBatch), RET #rs;
        ∃ E', ebm ↦$ E' ∗ ⌜doneRel E' (execIds (fun x => Bm !! x) es ids).done⌝ ∗
        kvOwn bm (execIds (fun x => Bm !! x) es ids).store ∗ rs ↦* outs ∗
        [∗list] k ↦ o ∈ outs, ∃ x b r, ⌜(freshIds es.done ids)[k]? = some x ∧ Bm !! x = some b ∧
          (execIds (fun x => Bm !! x) es ids).results x = some r⌝ ∗
          repCBVal o (DFrac.own 1) ⟨x, b.sender, r⟩ }} := by
  wp_start as ⟨#Hcb, #Hst, #Hbm, #Hebm, Hm, Hkv, #Hsl, #Hhas, #Hknown⟩
  wp_auto
  ihave %Hsllen := ownSlice_len $$ Hsl
  wp_apply (wp_slice_make2 (V := raxos.proto.client.ClientBatch)) as %bsl0 ⟨Hbsl, Hbcap⟩
  · ipureintro; word
  ihave HI : (∃ (i : w64) (bsl : GoSlice) (cbv : List raxos.proto.client.ClientBatch)
      (E' : GMap GoString Bool),
      "i" ∷ i_ptr ↦ i ∗ "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z sl.len⌝ ∗
      "batches" ∷ batches_ptr ↦ bsl ∗ "Hbsl" ∷ bsl ↦* cbv ∗
      "Hbcap" ∷ ownSliceCap raxos.proto.client.ClientBatch bsl (DFrac.own 1) ∗
      "Hrep" ∷ cbsRep cbv ((freshIds es.done (ids.take (sint.nat i))).map (fun x => (Bm !! x).getD default)) ∗
      "Hm" ∷ ebm ↦$ E' ∗
      "%HE'" ∷ ⌜doneRel E' (es.done ++ freshIds es.done (ids.take (sint.nat i)))⌝ : IProp GF)
      $$ [i batches Hbsl Hbcap Hm]
  · iexists W64 0, bsl0, [], E
    rw [show sint.nat (W64 0) = 0 from rfl]
    simp only [List.take_zero, freshIds, List.map_nil, List.append_nil, List.replicate_zero]
    iframe
    isplitr
    · ipureintro; exact ⟨by word, by word⟩
    isplitr
    · iunfold cbsRep; isplitr
      · ipureintro; rfl
      iapply BigSepL.bigSepL_nil.2; iempintro
    ipureintro; exact hE
  wp_for HI
  wp_if_destruct
  · have Hilt : sint.nat i < ids.length := by word
    list_elem ids (sint.nat i) as x
    ihave #Hx := BigSepL.bigSepL_lookup (Φ := fun _ y => storeHas (GF := GF) γs y) Hx_lookup $$ Hhas
    have Hb : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z sl.len := ⟨Hi.1, Hif⟩
    repeat' (first | wp_auto | simp only [Hb, _root_.and_self, ↓reduceIte])
    wp_apply wp_load_slice_index sl (sint.Z i) ids _ x Hi.1 $$ [Hsl] as -
    · iframe Hsl; ipureintro; simpa using Hx_lookup
    wp_apply (store_get_proof γ γs cb x true) $$ [Hst Hx] as %v %ok ⟨%Hok, Hv⟩
    · iframe Hst; simp only [↓reduceIte]; iexact Hx
    obtain rfl : ok = true := Hok rfl
    simp only [↓reduceIte]
    icases Hv with ⟨%b, %Hb', #Hrepv, #Hregx, #Hhasx⟩
    simp only [Bool.not_true]
    repeat' (first | wp_auto | simp only [Hb, _root_.and_self, ↓reduceIte])
    wp_apply wp_load_slice_index sl (sint.Z i) ids _ x Hi.1 $$ [Hsl] as -
    · iframe Hsl; ipureintro; simpa using Hx_lookup
    wp_apply wp_map_lookup1 $$ Hm as Hm
    -- the registry's batch for `x`
    obtain ⟨b', Hb'⟩ := Option.isSome_iff_exists.1 (hB x (List.mem_of_getElem? Hx_lookup))
    iunfold knownP at Hknown
    ihave Hkb := BigSepM.bigSepM_lookup (Φ := fun y c => iprop(batchReg (GF := GF) γ y c ∗ ⌜batchFit c⌝))
      (show PartialMap.get? Bm x = some b' from Hb') $$ Hknown
    icases Hkb with ⟨#Hregx', -⟩
    ihave %Hbb := batchReg_agree γ x b b' $$ Hregx Hregx'
    subst Hbb
    have Htake : ids.take (sint.nat i + 1) = ids.take (sint.nat i) ++ [x] :=
      take_succ_of_getElem? _ _ _ Hx_lookup
    have Hin : sint.nat (i + W64 1) = sint.nat i + 1 := by word
    by_cases Hif : (E' !! x).getD (zero_val Bool) = true
    · -- executed before: skipped
      rw [Hif]
      wp_auto
      have Hdone : x ∈ es.done ++ freshIds es.done (ids.take (sint.nat i)) := by
        have := (HE' x).1; rw [← this]
        revert Hif; cases E' !! x <;> simp [zero_val]
      wp_for_post
      iframe
      iexists i + W64 1, bsl, cbv, E'
      rw [Hin, Htake, freshIds_snoc, ite_eq_left_of_eq_true _ _ (eq_true Hdone), List.append_nil]
      iframe
      ipureintro; exact ⟨⟨by word, by word⟩, HE'⟩
    · -- executed now
      have Hnd : x ∉ es.done ++ freshIds es.done (ids.take (sint.nat i)) := by
        intro h; have := ((HE' x).1).2 h; rw [this] at Hif; simp at Hif
      rw [show (E' !! x).getD (zero_val Bool) = false by simpa using Hif]
      repeat' (first | wp_auto | simp only [Hb, _root_.and_self, ↓reduceIte])
      wp_apply wp_load_slice_index sl (sint.Z i) ids _ x Hi.1 $$ [Hsl] as -
      · iframe Hsl; ipureintro; simpa using Hx_lookup
      wp_apply wp_mapInsert $$ Hm as Hm
      wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType raxos.proto.client.ClientBatch.ty))))
        (Val (LiteralValueV _)))
      iapply wp_slice_literal (V := raxos.proto.client.ClientBatch) (t := raxos.proto.client.ClientBatch.ty) [v]
      wp_auto
      isplitl []
      · ipureintro; rfl
      iintro %lit_ptr ⟨Hlit, -⟩
      wp_apply wp_slice_append (V := raxos.proto.client.ClientBatch) _ _ _ _ _ $$ [$Hbsl $Hbcap $Hlit]
        as %bsl' ⟨Hbsl, Hbcap, -⟩
      wp_for_post
      iframe
      iexists i + W64 1, bsl', cbv ++ [v], E'.insert x true
      rw [Hin, Htake, freshIds_snoc, ite_eq_right_of_eq_false _ _ (eq_false Hnd)]
      iframe
      isplitr
      · ipureintro; exact ⟨by word, by word⟩
      isplitl [Hrep]
      · iunfold cbsRep at Hrep
        icases Hrep with ⟨%Hlen, #Hrep⟩
        iunfold cbsRep
        isplitr
        · ipureintro; simp [Hlen]
        iapply BigSepL.bigSepL_append.2
        isplitl []
        · iapply BigSepL.bigSepL_impl $$ Hrep
          imodintro
          iintro %k %o %hk ⟨%b0, %Hb0, Hr⟩
          iexists b0
          iframe Hr
          ipureintro
          rw [List.map_append, List.getElem?_append_left (by simp [← Hlen]; exact (List.getElem?_eq_some_iff.1 hk).1)]
          exact Hb0
        iapply BigSepL.bigSepL_singleton.2
        iexists b
        iframe Hrepv
        ipureintro
        simp [Hlen, Hb']
      ipureintro
      intro y
      by_cases hy : y = x
      · subst hy; simp
      · rw [GMap.lookup_insert_ne _ _ (Ne.symm hy)]
        have := HE' y
        simp only [List.mem_append, List.mem_singleton, hy, _root_.or_false] at this ⊢
        simpa [List.append_assoc] using this
  · -- the loop's exit: execute the batches
    have Hin : sint.nat i = ids.length := by word
    rw [Hin, List.take_length] at HE'
    rw [Hin, List.take_length]
    ipersist Hbsl
    have hok : ∀ b ∈ (freshIds es.done ids).map (fun x => (Bm !! x).getD default),
        ∀ c ∈ b.cmds, cmdOk c := by
      intro b hb c hc
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hb
      have hxi := ((freshIds_nodup ids es.done).2 x hx).2
      obtain ⟨b', hb'⟩ := Option.isSome_iff_exists.1 (hB x hxi)
      rw [hb'] at hc
      exact hcmd x b' hb' c hc
    wp_apply wp_applySMRLogic pr bm es.store bsl cbv _ hok $$ [Hkv Hrep] as %rs %outs ⟨Hkv, Hrs, Houts⟩
    · iframe Hbm Hkv Hbsl Hrep
    -- the slot's execution, as the Go code did it
    have Hcm : ((freshIds es.done ids).map (fun x => (Bm !! x).getD default)).map Batch.cmds =
        (freshIds es.done ids).map (cmdsOf (fun x => Bm !! x)) := by
      simp only [List.map_map]
      apply List.map_congr_left
      intro x hx
      have hxi := ((freshIds_nodup ids es.done).2 x hx).2
      obtain ⟨b', hb'⟩ := Option.isSome_iff_exists.1 (hB x hxi)
      simp [cmdsOf, hb']
    rw [Hcm]
    have Heq := execIds_eq_execSeq (fun x => Bm !! x) ids es
    wp_end
    iexists E'
    rw [Heq, execSeq_store, execSeq_done]
    iframe Hm Hkv Hrs
    isplitr
    · ipureintro; exact HE'
    iapply BigSepL.bigSepL_impl $$ Houts
    imodintro
    iintro %k %o %hk ⟨%b0, %r, %Hbr, Hr⟩
    obtain ⟨x, hx, rfl⟩ : ∃ x, (freshIds es.done ids)[k]? = some x ∧ b0 = (Bm !! x).getD default := by
      rw [List.getElem?_map] at Hbr
      cases h : (freshIds es.done ids)[k]? with
      | none => rw [h] at Hbr; simp at Hbr
      | some x => rw [h] at Hbr; simp at Hbr; exact ⟨x, rfl, Hbr.1.symm⟩
    have hxi := ((freshIds_nodup ids es.done).2 x (List.mem_of_getElem? hx)).2
    obtain ⟨b', hb'⟩ := Option.isSome_iff_exists.1 (hB x hxi)
    iexists x, b', r
    simp only [hb', Option.getD_some]
    isplitr
    · ipureintro
      refine ⟨hx, trivial, ?_⟩
      rw [execSeq_results _ _ (freshIds_nodup ids es.done).1 es k x hx]
      exact Hbr.2
    rw [hid x b' hb']
    iexact Hr

end proofs
end Perennial.raxos
