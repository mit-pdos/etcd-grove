/-
Package `proxy`: the resident key-value store (`kvStore.go`, mode 0): `residentExecute`,
`Execute`.
-/
module

public import Dsverify.Proof.raxos.Replica
public import Dsverify.Proof.raxos.Proxy.Pure
public import Dsverify.Proof.raxos.Proxy.StateDefs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Perennial.raxos


open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open Perennial.raxos.pure Perennial.raxos.msg
open raxos.replica.src

theorem set_append_replicate {A : Type} (qs : List A) (n : Nat) (z q : A) (h : 0 < n) :
    (qs ++ List.replicate n z).set qs.length q = (qs ++ [q]) ++ List.replicate (n - 1) z := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp [List.set_append, List.replicate_succ]

theorem take_succ_of_getElem? {A : Type} (l : List A) (n : Nat) (x : A) (h : l[n]? = some x) :
    l.take (n + 1) = l.take n ++ [x] := by
  rw [List.take_succ, h]; rfl

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [π : NetProtoGS] [qv : hyp.QpVocab GF]

end defs

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [π : NetProtoGS] [qv : hyp.QpVocab GF]
variable [raxos.replica.src.Assumptions]

theorem wp_residentExecute (bm : Loc) (st : pure.Store) (cs : GoSlice)
    (cbs : List raxos.proto.client.ClientBatch) (bs : List Batch)
    (hok : ∀ b ∈ bs, ∀ c ∈ b.cmds, cmdOk c) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.replica.src ∗ kvOwn bm st ∗ cs ↦*□ cbs ∗
        cbsRep cbs bs }}
      (App (Val (bm @!! go.GoType.PointerType Benchmark.ty @!! go!"residentExecute")) (Val #cs))
    {{ (rs : GoSlice) (outs : List raxos.proto.client.ClientBatch), RET #rs;
        kvOwn bm (runBatches st (bs.map Batch.cmds)).1 ∗ rs ↦* outs ∗
        [∗list] k ↦ o ∈ outs, ∃ b r, ⌜bs[k]? = some b ∧ (runBatches st (bs.map Batch.cmds)).2[k]? = some r⌝ ∗
          repCBVal o (DFrac.own 1) ⟨b.id, b.sender, r⟩ }} := by
  wp_start as ⟨Hkv, #Hcs, Hrep⟩
  iunfold kvOwn at Hkv
  icases Hkv with ⟨%kvm, %M, #Hmode, #Hkl, #Hkvf, Hm, %HM⟩
  wp_auto
  ihave %Hcslen := ownSlice_len $$ Hcs
  iunfold cbsRep at Hrep
  icases Hrep with ⟨%Hlenb, #Hreps⟩
  wp_apply (wp_slice_make2 (V := raxos.proto.client.ClientBatch)) as %rs ⟨Hrs, Hrscap⟩
  · ipureintro; exact Hcslen.2
  ihave HI : (∃ (i : w64) (outs : List raxos.proto.client.ClientBatch) (M' : GMap GoString GoString),
      "i" ∷ clientBatchIndex_ptr ↦ i ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z cs.len ∧ outs.length = sint.nat i⌝ ∗
      "Hrs" ∷ rs ↦* (outs ++ List.replicate (sint.nat cs.len - sint.nat i) (zero_val raxos.proto.client.ClientBatch)) ∗
      "Hm" ∷ kvm ↦$ M' ∗
      "%HM'" ∷ ⌜storeRel M' (runBatches st ((bs.take (sint.nat i)).map Batch.cmds)).1⌝ ∗
      "Houts" ∷ ([∗list] k ↦ o ∈ outs, ∃ b r, ⌜bs[k]? = some b ∧
          (runBatches st ((bs.take (sint.nat i)).map Batch.cmds)).2[k]? = some r⌝ ∗
          repCBVal o (DFrac.own 1) ⟨b.id, b.sender, r⟩) : IProp GF) $$ [clientBatchIndex Hrs Hm]
  · iexists W64 0, [], M
    rw [show sint.nat (W64 0) = 0 from rfl]
    simp only [Nat.sub_zero, List.nil_append, List.take_zero, List.map_nil]
    iframe
    isplitr
    · ipureintro; refine ⟨by word, by word, rfl⟩
    isplitr
    · ipureintro; simpa [runBatches] using HM
    iapply BigSepL.bigSepL_nil.2; iempintro
  wp_for HI
  wp_if_destruct
  · -- the loop body: batch `i`
    have Hilt : sint.nat i < cbs.length := by word
    list_elem cbs (sint.nat i) as cb
    list_elem bs (sint.nat i) as bb
    ihave Hcb := BigSepL.bigSepL_lookup (Φ := fun k v => iprop(∃ b, ⌜bs[k]? = some b⌝ ∗ repCBVal (GF := GF) v DFrac.discard b))
      Hcb_lookup $$ Hreps
    icases Hcb with ⟨%bb', %Hbb', #Hcbrep⟩
    rw [Hbb_lookup] at Hbb'
    cases Hbb'
    icases ownSlice_elem_acc (sint.Z i) cb cs DFrac.discard cbs (by word) (by simpa using Hcb_lookup) $$ Hcs with ⟨#Hel, -⟩
    have Hb : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z cs.len := ⟨Hi.1, Hif⟩
    simp only [Hb, _root_.and_self, ↓reduceIte]
    iStructNamedPrefix Hel "c"
    iunfold repCBVal at Hcbrep
    icases Hcbrep with ⟨%ps, %Hsid, #Hps, #Hpsl⟩
    iunfold repList at Hpsl
    icases Hpsl with ⟨%Hpslen, #Hpsl⟩
    ihave %Hpslen' := ownSlice_len $$ Hps
    repeat' (first | wp_auto | simp only [Hb, _root_.and_self, ↓reduceIte])
    wp_apply (wp_slice_make2 (V := Loc)) as %msl ⟨Hmsl, Hmslcap⟩
    · ipureintro; word
    ihave %Hrslen := ownSlice_len $$ Hrs
    have Hb2 : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z rs.len := by
      simp only [List.length_append, List.length_replicate] at Hrslen; exact ⟨Hi.1, by word⟩
    repeat' (first | wp_auto | simp only [Hb, Hb2, _root_.and_self, ↓reduceIte])
    wp_apply wp_store_slice_index $$ [Hrs] as Hrs
    · iframe; ipureintro; simp; word
    -- the result batch `i`, kept apart during the inner loop
    obtain ⟨outi, Houti⟩ : Exists fun (o : raxos.proto.client.ClientBatch) =>
      o = ⟨zeroValDef, 0, slice.nil, cb.Sender', msl, cb.Id'⟩ := ⟨_, rfl⟩
    rw [← Houti]
    have Hset : ((outs ++ List.replicate (sint.nat cs.len - sint.nat i)
        (zero_val raxos.proto.client.ClientBatch)).set (sint.Z i).toNat outi)[(sint.Z i).toNat]? = some outi := by
      rw [List.getElem?_set_self]; simp at Hrslen ⊢; word
    icases ownSlice_elem_acc (sint.Z i) outi rs _ _ Hb2.1 Hset $$ Hrs with ⟨Hout, Hrs⟩
    -- (Hout kept whole)
    subst Houti
    obtain ⟨sti, Hsti⟩ : Exists fun (s0 : pure.Store) =>
      s0 = (runBatches st ((bs.take (sint.nat i)).map Batch.cmds)).1 := ⟨_, rfl⟩
    rw [← Hsti] at HM'
    ihave %Hmsllen := ownSlice_len $$ Hmsl
    ihave HJ : (∃ (j : w64) (qs : List Loc) (M'' : GMap GoString GoString),
        "j" ∷ clientRequestIndex_ptr ↦ j ∗
        "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z cb.Messages'.len ∧ qs.length = sint.nat j⌝ ∗
        "Hmsl" ∷ msl ↦* (qs ++ List.replicate (sint.nat cb.Messages'.len - sint.nat j) (zero_val Loc)) ∗
        "Hqs" ∷ ([∗list] k ↦ q ∈ qs, ∃ r, ⌜(execBatch sti (bb.cmds.take (sint.nat j))).2[k]? = some r⌝ ∗
          repCSingle q (DFrac.own 1) r) ∗
        "Hm" ∷ kvm ↦$ M'' ∗
        "%HM''" ∷ ⌜storeRel M'' (execBatch sti (bb.cmds.take (sint.nat j))).1⌝ : IProp GF)
        $$ [clientRequestIndex Hmsl Hm]
    · iexists W64 0, [], M'
      rw [show sint.nat (W64 0) = 0 from rfl]
      simp only [Nat.sub_zero, List.nil_append, List.take_zero]
      iframe
      isplitr
      · ipureintro; refine ⟨by word, by word, rfl⟩
      isplitl []
      · iapply BigSepL.bigSepL_nil.2; iempintro
      ipureintro; simpa [execBatch] using HM'
    wp_for HJ
    repeat' (first | wp_auto | simp only [Hb, Hb2, _root_.and_self, ↓reduceIte])
    cleanup_bool_decide
    wp_if_destruct
    · -- the inner body: command `j`
      have Hjlt : sint.nat j < bb.cmds.length := by word
      list_elem bb.cmds (sint.nat j) as c
      list_elem ps (sint.nat j) as p
      have Hb3 : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z cb.Messages'.len := ⟨Hj.1, Hif⟩
      ihave %Hmsllen2 := ownSlice_len $$ Hmsl
      have Hb4 : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z msl.len := by
        simp only [List.length_append, List.length_replicate] at Hmsllen2; exact ⟨Hj.1, by word⟩
      wp_pures
      irename «$r0» => Hq
      repeat' (first | wp_auto | simp only [Hb, Hb2, Hb3, Hb4, _root_.and_self, ↓reduceIte])
      wp_apply wp_store_slice_index $$ [Hmsl] as Hmsl
      · iframe; ipureintro; simp at Hmsllen2 ⊢; word
      repeat' (first | wp_auto | simp only [Hb, Hb2, Hb3, Hb4, _root_.and_self, ↓reduceIte])
      wp_apply wp_load_slice_index _ _ ps _ p Hb3.1 $$ [Hps] as Hps'
      · iframe Hps; ipureintro; simpa using Hp_lookup
      ihave Hpc := BigSepL.bigSepL_lookup (Φ := fun k p => iprop(∃ x, ⌜bb.cmds[k]? = some x⌝ ∗ repCSingle (GF := GF) p DFrac.discard x))
        Hp_lookup $$ Hpsl
      icases Hpc with ⟨%c', %Hc', #Hpc⟩
      rw [Hc_lookup] at Hc'; cases Hc'
      iunfold repCSingle at Hpc
      icases Hpc with ⟨%pv, #Hpv, %Hpvu, %Hpvm⟩
      repeat' (first | wp_auto | simp only [Hb, Hb2, Hb3, Hb4, _root_.and_self, ↓reduceIte])
      rw [Hpvm]
      have hc9 : 1 + keyLen ≤ c.length := hok bb (List.mem_of_getElem? Hbb_lookup) c
        (List.mem_of_getElem? Hc_lookup)
      simp only [keyLen] at hc9
      repeat' (first | wp_auto | simp only [Hb, Hb2, Hb3, Hb4, _root_.and_self, ↓reduceIte] |
        (rw [ite_cond_eq_true _ _ (eq_true (by word))]))
      wp_func_call
      wp_call
      by_cases hclen : ((c).length : Int) ≤ maxAddr
      case neg =>
        simp only [hclen, ↓reduceIte]
        wp_bind (AngelicExit _)
        iapply wp_AngelicExit
      simp only [hclen, ↓reduceIte]
      have hclen_lt : (c).length < 2 ^ 63 := by unfold maxAddr at hclen; omega
      repeat' (first | wp_auto | simp only [Hb, Hb2, Hb3, Hb4, _root_.and_self, ↓reduceIte] |
        (rw [ite_cond_eq_true _ _ (eq_true (by word))]))
      -- iStructNamedPrefix Hq "q"
      have Hkey : List.take (sint.nat (W64 1 + W64 8) - 1) (List.drop 1 c) = (c.drop 1).take keyLen := by
        simp [keyLen]; rfl
      have Hval : List.take (sint.nat (W64 c.length) - sint.nat (W64 1 + W64 8)) (List.drop (sint.nat (W64 1 + W64 8)) c) =
          c.drop (1 + keyLen) := by
        rw [List.take_of_length_le]
        · simp [keyLen]; rfl
        · simp; word
      simp only [Nat.sub_zero, List.drop_zero]
      rw [Hkey, Hval]
      ihave %Hmsllen3 := ownSlice_len $$ Hmsl
      have Hqj : ((qs ++ List.replicate (sint.nat cb.Messages'.len - sint.nat j) (zero_val Loc)).set
          (sint.Z j).toNat «$r0_ptr»)[(sint.Z j).toNat]? = some «$r0_ptr» := by
        rw [List.getElem?_set_self]; simp at Hmsllen3 ⊢; word
      wp_if_destruct
      · -- a write
        wp_apply wp_mapInsert $$ Hm as Hm
        repeat' (first | wp_auto | simp only [Hb, Hb2, Hb3, Hb4, _root_.and_self, ↓reduceIte])
        wp_apply wp_load_slice_index _ _ _ _ _ Hb3.1 $$ [Hmsl] as Hmsl
        · iframe; ipureintro; exact Hqj
        wp_for_post
        iframe
        have Hjn : sint.nat (j + W64 1) = sint.nat j + 1 := by word
        iexists j + W64 1, qs ++ [«$r0_ptr»],
          (M''.insert (List.take keyLen (List.drop 1 c)) (List.drop (1 + keyLen) c))
        rw [Hjn, take_succ_of_getElem? _ _ _ Hc_lookup, execBatch_snoc]
        have Hjq : (sint.Z j).toNat = qs.length := by word
        rw [Hjq, set_append_replicate _ _ _ _ (by word),
          show sint.nat cb.Messages'.len - sint.nat j - 1 = sint.nat cb.Messages'.len - (sint.nat j + 1) by omega]
        iframe
        isplitr
        · ipureintro; refine ⟨by word, by word, by simp; word⟩
        isplitl [Hqs Hq]
        · iapply BigSepL.bigSepL_append.2
          isplitl [Hqs]
          · iapply BigSepL.bigSepL_impl $$ Hqs
            imodintro
            iintro %k %q %hk ⟨%r, %Hr, Hr⟩
            iexists r
            iframe Hr
            ipureintro
            rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 Hr).1]
            exact Hr
          · iapply BigSepL.bigSepL_singleton.2
            iexists _
            isplitr
            · ipureintro
              rw [List.getElem?_append_right (by rw [execBatch_length]; simp; word)]
              rw [execBatch_length, List.length_take,
                show 0 + qs.length - min (sint.nat j) bb.cmds.length = 0 by omega]
              rfl
            iunfold repCSingle
            iexists _
            rw [ptCSingle_own]
            iframe Hq
            ipureintro; refine ⟨rfl, ?_⟩
            simp [execCmd, Hif, List.append_assoc]
        ipureintro
        intro k
        simp only [execCmd, Hif, ↓reduceIte]
        by_cases hk : k = List.take keyLen (List.drop 1 c)
        · subst hk; simp
        · rw [GMap.lookup_insert_ne _ _ (Ne.symm hk)]
          rw [ite_eq_right_of_eq_false _ _ (eq_false (by simpa using hk))]
          exact HM'' k
      · -- a read
        have HMk := HM'' (List.take keyLen (List.drop 1 c))
        have Htyp := Hif
        wp_apply wp_map_lookup2 $$ Hm as Hm
        repeat' (first | wp_auto | simp only [Hb, Hb2, Hb3, Hb4, _root_.and_self, ↓reduceIte])
        wp_if_destruct
        · repeat' (first | wp_auto | simp only [Hb, Hb2, Hb3, Hb4, _root_.and_self, ↓reduceIte])
          wp_apply wp_load_slice_index _ _ _ _ _ Hb3.1 $$ [Hmsl] as Hmsl
          · iframe; ipureintro; exact Hqj
          wp_for_post
          iframe
          have Hjn : sint.nat (j + W64 1) = sint.nat j + 1 := by word
          iexists j + W64 1, qs ++ [«$r0_ptr»],
            M''
          rw [Hjn, take_succ_of_getElem? _ _ _ Hc_lookup, execBatch_snoc]
          have Hjq : (sint.Z j).toNat = qs.length := by word
          rw [Hjq, set_append_replicate _ _ _ _ (by word),
            show sint.nat cb.Messages'.len - sint.nat j - 1 = sint.nat cb.Messages'.len - (sint.nat j + 1) by omega]
          iframe
          isplitr
          · ipureintro; refine ⟨by word, by word, by simp; word⟩
          isplitl [Hqs Hq]
          · iapply BigSepL.bigSepL_append.2
            isplitl [Hqs]
            · iapply BigSepL.bigSepL_impl $$ Hqs
              imodintro
              iintro %k %q %hk ⟨%r, %Hr, Hr⟩
              iexists r
              iframe Hr
              ipureintro
              rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 Hr).1]
              exact Hr
            · iapply BigSepL.bigSepL_singleton.2
              iexists _
              isplitr
              · ipureintro
                rw [List.getElem?_append_right (by rw [execBatch_length]; simp; word)]
                rw [execBatch_length, List.length_take,
                  show 0 + qs.length - min (sint.nat j) bb.cmds.length = 0 by omega]
                rfl
              iunfold repCSingle
              iexists _
              rw [ptCSingle_own]
              iframe Hq
              ipureintro; refine ⟨rfl, ?_⟩
              simp only [execCmd, Htyp, ↓reduceIte, List.append_assoc]
              rw [← HMk]
              revert Hif; cases M'' !! List.take keyLen (List.drop 1 c) <;> simp
          ipureintro
          simp only [execCmd, Htyp, ↓reduceIte]
          exact HM''
        · repeat' (first | wp_auto | simp only [Hb, Hb2, Hb3, Hb4, _root_.and_self, ↓reduceIte])
          wp_apply wp_load_slice_index _ _ _ _ _ Hb3.1 $$ [Hmsl] as Hmsl
          · iframe; ipureintro; exact Hqj
          wp_for_post
          iframe
          have Hjn : sint.nat (j + W64 1) = sint.nat j + 1 := by word
          iexists j + W64 1, qs ++ [«$r0_ptr»],
            M''
          rw [Hjn, take_succ_of_getElem? _ _ _ Hc_lookup, execBatch_snoc]
          have Hjq : (sint.Z j).toNat = qs.length := by word
          rw [Hjq, set_append_replicate _ _ _ _ (by word),
            show sint.nat cb.Messages'.len - sint.nat j - 1 = sint.nat cb.Messages'.len - (sint.nat j + 1) by omega]
          iframe
          isplitr
          · ipureintro; refine ⟨by word, by word, by simp; word⟩
          isplitl [Hqs Hq]
          · iapply BigSepL.bigSepL_append.2
            isplitl [Hqs]
            · iapply BigSepL.bigSepL_impl $$ Hqs
              imodintro
              iintro %k %q %hk ⟨%r, %Hr, Hr⟩
              iexists r
              iframe Hr
              ipureintro
              rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 Hr).1]
              exact Hr
            · iapply BigSepL.bigSepL_singleton.2
              iexists _
              isplitr
              · ipureintro
                rw [List.getElem?_append_right (by rw [execBatch_length]; simp; word)]
                rw [execBatch_length, List.length_take,
                  show 0 + qs.length - min (sint.nat j) bb.cmds.length = 0 by omega]
                rfl
              iunfold repCSingle
              iexists _
              rw [ptCSingle_own]
              iframe Hq
              ipureintro; refine ⟨rfl, ?_⟩
              simp only [execCmd, Htyp, ↓reduceIte, List.append_assoc]
              rw [← HMk]
              revert Hif; cases M'' !! List.take keyLen (List.drop 1 c) <;> simp
          ipureintro
          simp only [execCmd, Htyp, ↓reduceIte]
          exact HM''
    · -- the inner loop's exit: batch `i` executed
      have Hjm : sint.nat j = bb.cmds.length := by word
      ihave Hrs := Hrs $$ Hout
      wp_for_post
      iframe
      have Hin : sint.nat (i + W64 1) = sint.nat i + 1 := by word
      iexists i + W64 1, outs ++ [⟨zeroValDef, 0, slice.nil, cb.Sender', msl, cb.Id'⟩], M''
      have Hio : (sint.Z i).toNat = outs.length := by word
      rw [List.set_set, Hin, Hio, set_append_replicate _ _ _ _ (by word),
        show sint.nat cs.len - sint.nat i - 1 = sint.nat cs.len - (sint.nat i + 1) by omega]
      rw [take_succ_of_getElem? _ _ _ Hbb_lookup]
      simp only [List.map_append, List.map_cons, List.map_nil]
      rw [runBatches_snoc]
      rw [Hjm, List.take_length] at HM''
      have Hml : sint.nat cb.Messages'.len = bb.cmds.length := by omega
      rw [Hjm, List.take_length, Hml, Nat.sub_self, List.replicate_zero, List.append_nil]
      rw [← Hsti]
      iframe
      isplitr
      · ipureintro; refine ⟨by word, by word, by simp; word⟩
      isplitr
      · ipureintro; exact HM''
      iapply BigSepL.bigSepL_append.2
      isplitl [Houts]
      · iapply BigSepL.bigSepL_impl $$ Houts
        imodintro
        iintro %k %o %hk ⟨%b0, %r, %Hbr, Hr⟩
        iexists b0, r
        iframe Hr
        ipureintro
        refine ⟨Hbr.1, ?_⟩
        rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 Hbr.2).1]
        exact Hbr.2
      iapply BigSepL.bigSepL_singleton.2
      iexists bb, (execBatch sti bb.cmds).2
      isplitr
      · ipureintro
        refine ⟨?_, ?_⟩
        · rw [show 0 + outs.length = sint.nat i by omega]; exact Hbb_lookup
        · rw [List.getElem?_append_right (by rw [runBatches_length]; simp; omega)]
          rw [runBatches_length, List.length_map, List.length_take,
            show 0 + outs.length - min (sint.nat i) bs.length = 0 by omega]
          rfl
      iunfold repCBVal
      iexists qs
      iframe Hmsl
      isplitr
      · ipureintro; exact ⟨by simpa using Hsid.1, Hsid.2.1, rfl⟩
      iunfold repList
      isplitr
      · ipureintro; rw [execBatch_length]; omega
      iexact Hqs
  · -- the outer loop's exit
    have Hin : sint.nat i = bs.length := by word
    rw [Hin, List.take_length] at HM'
    rw [Hin, List.take_length, show sint.nat cs.len - bs.length = 0 by word, List.replicate_zero,
      List.append_nil]
    iapply HΦ
    iframe Hrs Houts
    iunfold kvOwn
    iexists kvm, M'
    iframe Hmode Hkl Hkvf Hm
    ipureintro; exact HM'

theorem wp_Execute (bm : Loc) (st : pure.Store) (cs : GoSlice)
    (cbs : List raxos.proto.client.ClientBatch) (bs : List Batch)
    (hok : ∀ b ∈ bs, ∀ c ∈ b.cmds, cmdOk c) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.replica.src ∗ kvOwn bm st ∗ cs ↦*□ cbs ∗
        cbsRep cbs bs }}
      (App (Val (bm @!! go.GoType.PointerType Benchmark.ty @!! go!"Execute")) (Val #cs))
    {{ (rs : GoSlice) (outs : List raxos.proto.client.ClientBatch), RET #rs;
        kvOwn bm (runBatches st (bs.map Batch.cmds)).1 ∗ rs ↦* outs ∗
        [∗list] k ↦ o ∈ outs, ∃ b r, ⌜bs[k]? = some b ∧ (runBatches st (bs.map Batch.cmds)).2[k]? = some r⌝ ∗
          repCBVal o (DFrac.own 1) ⟨b.id, b.sender, r⟩ }} := by
  wp_start as ⟨Hkv, #Hcs, Hrep⟩
  ihave #Hmode : bm.[Benchmark, go!"mode"] ↦□ W64 0 $$ [Hkv]
  · iunfold kvOwn at Hkv
    icases Hkv with ⟨%kvm, %M, #Hmode, -⟩
    iexact Hmode
  wp_auto
  wp_apply wp_residentExecute bm st cs cbs bs hok $$ [Hkv Hrep] as %rs %outs H
  · iframe Hkv Hrep Hcs
  wp_end

end proofs
end Perennial.raxos
