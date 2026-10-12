/-
Proof of `Spec/.../mvcc/storeTxnCommon__rangeKeys.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.storeTxnCommon__rangeKeys
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.treeIndex__CountRevisions
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.treeIndex__Range
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.treeIndex__Revisions
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.sliceCapWithLimit
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.NewRevBytes
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.RevToBytes
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.Trace__Step
public import Spec.google_golang_org.protobuf.proto.Unmarshal
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.BucketLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

-- (the unused-variables linter walks the whole info tree of this long proof: 10-15s of
-- the build of this module, which is on the build's critical path)
set_option linter.unusedVariables false in
set_option maxHeartbeats 4000000 in
theorem mvcc.storeTxnCommon.rangeKeys.wp_proof
    (hCount : mvcc.treeIndex.CountRevisions.spec (GF := GF) (hG := hG))
    (hRange : mvcc.treeIndex.Range.spec (GF := GF) (hG := hG))
    (hRevs : mvcc.treeIndex.Revisions.spec (GF := GF) (hG := hG))
    (hCap : mvcc.sliceCapWithLimit.spec (GF := GF) (hG := hG))
    (hNew : mvcc.NewRevBytes.spec (GF := GF) (hG := hG))
    (hRevTo : mvcc.RevToBytes.spec (GF := GF) (hG := hG))
    (hStep : traceutil.Trace.Step.spec (GF := GF) (hG := hG))
    (hUnm : proto.Unmarshal.spec (GF := GF) (hG := hG)) :
    mvcc.storeTxnCommon.rangeKeys.spec (GF := GF) (hG := hG) := by
  intro txc s trace ti rt dq m R γ kn log rev ctx cd todo key endk k e ro Htrnn
  wp_start as ⟨#Hs, HsT, HtxcT, HtraceT, #Hrdr, HRr, %HsubT, Hkn, %Hklog, %HneT, %Hrv, #Hidx0, Hti0,
    #Hctx, #Hkey, #Hend⟩
  iunfold mvcc.isStore at Hs
  icases Hs with ⟨%b, %ti', %lg, Hs⟩
  iNamed Hs
  icombine Hidx0 Hidx gives %Hti'
  have hti := mvcc.mkOk_loc_inj _ Hti'
  subst hti
  ihave Hinit : (mvccInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hinit with ⟨⟨%e0, #Herr⟩, -, ⟨%ef, #Hfut⟩, -, -, -, -, -, -⟩
  (try wp_auto)
  -- a future revision
  wp_if_destruct
  · wp_alloc r as Hr
    ihave %Hrnn := typedPointsto_not_null _ _ _ $$ Hr
    (try wp_auto)
    iapply HΦ
    isplitl []
    · ipureintro; intro _; exact Hrnn
    iframe Hti0 HsT HtxcT HtraceT HRr Hkn
    iunfold mvcc.rangeOutcome
    ileft
    isplitl []
    · ipureintro; exact Hif
    isplitl []
    · iexists ef; iframe #; ipureintro; rfl
    iexact Hr
  · (try wp_auto)
    have hle : sint.Z ro.Rev' ≤ sint.Z rev := by omega
    have h0z : sint.Z (W64 0) = 0 := by decide
    have hm1 : sint.Z (W64 (-1)) = -1 := by decide
    icases mvcc.idxKnows_wf γ.idx kn $$ Hkn with ⟨Hkn, %Hcwf⟩
    rw [Hklog] at Hcwf
    obtain ⟨Hwf', Hlen, Hcs⟩ := Hcwf
    have hne : 0 < log.length := by
      cases log with
      | nil => exact absurd rfl HneT
      | cons _ _ => simp
    -- `rev <= 0`: the transaction's revision; the rest of the function is proved once
    wp_join iprop(rev_ptr ↦ mvcc.rangeRev rev ro.Rev' ∗ curRev_ptr ↦ rev) with [rev curRev]
      as ⟨Hrevp, curRev⟩
    · have hRR : mvcc.rangeRev rev ro.Rev' = rev := by
        unfold mvcc.rangeRev; rw [ite_eq_left (by omega)]
      rw [hRR]
      iframe rev curRev
    · have hRR : mvcc.rangeRev rev ro.Rev' = ro.Rev' := by
        unfold mvcc.rangeRev; rw [ite_eq_right (by omega)]
      rw [hRR]
      iframe rev curRev
    have hR0 : 0 ≤ sint.Z (mvcc.rangeRev rev ro.Rev') := by
      unfold mvcc.rangeRev; split <;> omega
    have hRlt : sint.Z (mvcc.rangeRev rev ro.Rev') < log.length := by
      unfold mvcc.rangeRev; split <;> omega
    -- `rev < compactMainRev` never holds (`-1`)
    (try simp only [h0z] at *)
    wp_if_destruct
    · exfalso; rw [hm1] at Hif; omega
    (try wp_auto)
    cases hco : ro.CountOnly' with
    | true =>
      -- `CountOnly`: the index's count
      (try wp_auto)
      wp_apply (hCount ti γ.idx kn key endk k e (mvcc.rangeRev rev ro.Rev') e0)
        $$ [$Hti $Hti0 $Hkn $Hkey $Hend $Herr] as ⟨Hti0, Hkn⟩
      · ipureintro; rw [Hklog]; exact ⟨hR0, hRlt⟩
      rw [Hklog]
      (try wp_auto)
      wp_apply (hStep trace _ _)
      · ipureintro; exact Htrnn
      (try wp_auto)
      wp_alloc r as Hr
      ihave %Hrnn := typedPointsto_not_null _ _ _ $$ Hr
      (try wp_auto)
      iapply HΦ
      isplitl []
      · ipureintro; intro _; exact Hrnn
      iframe Hti0 HsT HtxcT HtraceT HRr Hkn
      iunfold mvcc.rangeOutcome
      iright; iright
      isplitl []
      · ipureintro; exact hle
      isplitl []
      · ipureintro; rfl
      rw [hco]
      simp only [↓reduceIte]
      iexact Hr
    | false =>
      (try wp_auto)
      cases hfk : ro.FastKeysOnly' with
      | true =>
        -- `FastKeysOnly`: the index's keys, revisions and versions
        (try wp_auto)
        wp_apply (hRange ti γ.idx kn key endk k e (mvcc.rangeRev rev ro.Rev') ro.Limit'
          ro.WithTotalCount' e0) $$ [$Hti $Hti0 $Hkn $Hkey $Hend $Herr]
          as %keys %modifies %creates %vers %total
            ⟨Hti0, Hkn, Hkeys, Hmod, Hmodcap, Hcre, Hcrecap, Hvers, Hverscap, %Htotal⟩
        · ipureintro; rw [Hklog]; exact ⟨hR0, hRlt⟩
        rw [Hklog]
        rw [Hklog] at Htotal
        (try wp_auto)
        wp_apply (hStep trace _ _)
        · ipureintro; exact Htrnn
        (try wp_auto)
        generalize hT : mvcc.rangeTaken log (decide (endk = slice.nil)) k e
          (mvcc.rangeRev rev ro.Rev') ro.Limit' = taken at *
        iunfold mvcc.ownKeys at Hkeys
        icases Hkeys with ⟨%kss, Hksl, Hkcap, %Hkslen, Hzip⟩
        ihave %Hklen := ownSlice_len _ _ _ $$ Hksl
        rw [List.length_map] at Hkslen
        wp_if_destruct
        · -- no key: no answer
          have hkss : kss = [] := by
            rw [← List.length_eq_zero_iff, Hklen.1, Hif]; decide
          have htaken : taken = [] := by
            rw [hkss] at Hkslen; exact (List.length_eq_zero_iff.1 Hkslen.symm)
          wp_alloc r as Hr
          ihave %Hrnn := typedPointsto_not_null _ _ _ $$ Hr
          (try wp_auto)
          iapply HΦ
          isplitl []
          · ipureintro; intro _; exact Hrnn
          iframe Hti0 HsT HtxcT HtraceT HRr Hkn
          iunfold mvcc.rangeOutcome
          rw [hT]
          iright; iright
          isplitl []
          · ipureintro; exact hle
          isplitl []
          · ipureintro; rfl
          rw [hco]
          simp only [Bool.false_eq_true, ↓reduceIte]
          iexists slice.nil
          rw [mvcc.rangeTotal_of_taken_nil _ _ _ _ _ _ _ (hT.trans htaken),
            show ((0 : Nat) : Int) = 0 from rfl]
          iframe Hr
          iunfold mvcc.rangeKvs
          iexists []
          rw [htaken]
          isplitl []
          · iapply ownSlice_nil
          isplitl []
          · ipureintro; rfl
          rw [show ([] : List Loc).zip ([] : List (GoString × mvcc.Rev × mvcc.Rev × w64)) = []
            from rfl]
          iapply BigSepL.bigSepL_nil_intro; iempintro
        · -- the key-values of the answers, one per key
          (try wp_auto)
          wp_apply wp_slice_make2 (V := Loc) keys.len as %kvs ⟨Hkvs, Hkvscap⟩
          · ipureintro; exact Hklen.2
          (try wp_auto)
          ihave %Hkvlen := ownSlice_len _ _ _ $$ Hkvs
          simp only [List.length_replicate] at Hkvlen
          ipersist Hksl
          ipersist Hmod
          ipersist Hcre
          ipersist Hvers
          irename «$range_i» => Hri
          irename «end» => Hend0
          -- the loop: the first `i` key-values built
          ihave HI : (∃ (i : Nat) (ps : List Loc) (iv : w64),
              "Hri" ∷ «$range_i_ptr» ↦ W64 i ∗ "Hi" ∷ i_ptr ↦ iv ∗
              "%Hbnd" ∷ ⌜i ≤ sint.nat keys.len ∧ ps.length = i⌝ ∗
              "Hkvs" ∷ kvs ↦* (ps ++ List.replicate (sint.nat keys.len - i) (zero_val Loc)) ∗
              "Hps" ∷ [∗list] pa ∈ ps.zip (taken.take i), ∃ kv : EtcdKv,
                ⌜mvcc.findKey pa.2.1 (mvcc.stateAt log (sint.nat (mvcc.rangeRev rev ro.Rev'))) =
                  some kv⌝ ∗ mvcc.kvPtrIs false pa.1 kv) $$ [Hri i Hkvs]
          · iexists 0, [], (zero_val w64)
            simp only [named, List.nil_append, Nat.sub_zero, List.take_zero, List.zip_nil_left]
            rw [show (W64 ((0 : Nat) : Int) : w64) = zero_val w64 from rfl]
            iframe Hkvs i
            isplitl [Hri]
            · iexact Hri
            isplitl []
            · ipureintro; exact ⟨Nat.zero_le _, rfl⟩
            iapply BigSepL.bigSepL_nil_intro; iempintro
          wp_for HI
          have hkl : sint.nat keys.len < 2 ^ 63 := by
            unfold sint.nat; have := BitVec.toInt_lt (x := keys.len); omega
          have hi : sint.Z (W64 (i : Int)) = i := by
            unfold sint.Z W64
            rw [BitVec.toInt_ofInt_eq_self (by decide)
              (by rw [show (64 - 1 : Nat) = 63 from rfl]; omega)
              (by rw [show (64 - 1 : Nat) = 63 from rfl]; omega)]
          have hiN : (sint.Z (W64 (i : Int))).toNat = i := by rw [hi]; rfl
          wp_if_destruct
          · -- the `i`th key-value
            have hlt : sint.Z (W64 (i : Int)) < sint.Z kvs.len := by
              first | exact Hif | (have := go.intoVal_inj Hif; simpa using this)
            have hlt' : (i : Int) < sint.Z kvs.len := by rw [← hi]; exact hlt
            have hilt : i < sint.nat keys.len := by
              have h1 := Hkvlen.1; have h2 := Hkvlen.2; unfold sint.nat sint.Z at *; omega
            have hit : i < taken.length := by omega
            have hik : i < kss.length := by omega
            obtain ⟨a, ha⟩ : ∃ a, taken[i]? = some a := ⟨_, List.getElem?_eq_getElem hit⟩
            obtain ⟨ksi, hksi⟩ : ∃ x, kss[i]? = some x := ⟨_, List.getElem?_eq_getElem hik⟩
            -- the answer's key-value (the model)
            have hRnat : sint.nat (mvcc.rangeRev rev ro.Rev') < 2 ^ 63 := by
              have h1 := hRlt; have h2 := hR0; unfold sint.nat; unfold sint.Z at *; omega
            have hRW : mvcc.rangeRev rev ro.Rev' =
                W64 ((sint.nat (mvcc.rangeRev rev ro.Rev') : Nat) : Int) := by
              unfold sint.nat; rw [Int.toNat_of_nonneg hR0]; exact BitVec.ofInt_toInt.symm
            have hmem : a ∈ mvcc.rangeAnswers log (decide (endk = slice.nil)) k e
                (W64 ((sint.nat (mvcc.rangeRev rev ro.Rev') : Nat) : Int)) := by
              rw [← hRW]
              exact mvcc.mem_rangeAnswers_of_taken _ _ _ _ _ _ a
                (hT.symm ▸ List.mem_of_getElem? ha)
            obtain ⟨kv, hfind, hmod, hcr, hver, -⟩ := mvcc.rangeAnswers_kv log
              (mvcc.LogWf.of_wf' Hwf' HneT) Hlen Hcs _ k e _ hRnat a hmem
            have hz : (ksi, a.1) ∈ kss.zip (taken.map Prod.fst) :=
              List.mem_iff_getElem?.2 ⟨i, List.getElem?_zip_eq_some.2
                ⟨hksi, by rw [List.getElem?_map, ha]; rfl⟩⟩
            icases BigSepL.bigSepL_mem_acc hz $$ Hzip with ⟨#Hks, Hzip⟩
            ihave Hzip := Hzip $$ Hks
            have Hbk : 0 ≤ sint.Z (W64 (i : Int)) ∧ sint.Z (W64 (i : Int)) < sint.Z keys.len := by
              rw [hi]; constructor; · omega
              have := Hklen.1; unfold sint.nat at this; have := Hklen.2; unfold sint.Z at *; omega
            simp only [Hbk, _root_.and_self, ite_true]
            -- `keys[i]`
            wp_apply wp_load_slice_index keys (sint.Z (W64 (i : Int))) kss DFrac.discard ksi
              (by omega) $$ [$Hksl] as -
            · ipureintro; rw [hiN]; exact hksi
            (try wp_auto)
            -- `modifies[i].Main`, `creates[i].Main`, `versions[i]`
            ihave %Hmlen := ownSlice_len _ _ _ $$ Hmod
            ihave %Hclen := ownSlice_len _ _ _ $$ Hcre
            ihave %Hvlen := ownSlice_len _ _ _ $$ Hvers
            simp only [List.length_map] at Hmlen Hclen Hvlen
            have hml : (taken.length : Int) = sint.Z modifies.len := by
              have h1 := Hmlen.1; have h2 := Hmlen.2; unfold sint.nat at h1; unfold sint.Z at *; omega
            have hcl : (taken.length : Int) = sint.Z creates.len := by
              have h1 := Hclen.1; have h2 := Hclen.2; unfold sint.nat at h1; unfold sint.Z at *; omega
            have hvl : (taken.length : Int) = sint.Z vers.len := by
              have h1 := Hvlen.1; have h2 := Hvlen.2; unfold sint.nat at h1; unfold sint.Z at *; omega
            have Hbm : 0 ≤ sint.Z (W64 (i : Int)) ∧ sint.Z (W64 (i : Int)) < sint.Z modifies.len := by
              rw [hi]; omega
            simp only [Hbm, _root_.and_self, ite_true]
            icases ownSlice_elem_acc (sint.Z (W64 (i : Int))) (mvcc.revVal a.2.1) modifies
              DFrac.discard _ (by omega) (by rw [hiN, List.getElem?_map, ha]; rfl) $$ Hmod
              with ⟨#HelM, -⟩
            icases mvcc.rev_split _ _ _ $$ HelM with ⟨#HMm, -, -⟩
            (try wp_auto)
            have Hbc : 0 ≤ sint.Z (W64 (i : Int)) ∧ sint.Z (W64 (i : Int)) < sint.Z creates.len := by
              rw [hi]; omega
            simp only [Hbc, _root_.and_self, ite_true]
            icases ownSlice_elem_acc (sint.Z (W64 (i : Int))) (mvcc.revVal a.2.2.1) creates
              DFrac.discard _ (by omega) (by rw [hiN, List.getElem?_map, ha]; rfl) $$ Hcre
              with ⟨#HelC, -⟩
            icases mvcc.rev_split _ _ _ $$ HelC with ⟨#HCm, -, -⟩
            (try wp_auto)
            have Hbv : 0 ≤ sint.Z (W64 (i : Int)) ∧ sint.Z (W64 (i : Int)) < sint.Z vers.len := by
              rw [hi]; omega
            simp only [Hbv, _root_.and_self, ite_true]
            wp_apply wp_load_slice_index vers (sint.Z (W64 (i : Int))) _ DFrac.discard a.2.2.2
              (by omega) $$ [$Hvers] as -
            · ipureintro; rw [hiN, List.getElem?_map, ha]; rfl
            (try wp_auto)
            irename «$r0» => Hp
            -- `kvs[i] = kv`
            have Hbkv : 0 ≤ sint.Z (W64 (i : Int)) ∧ sint.Z (W64 (i : Int)) < sint.Z kvs.len :=
              ⟨by omega, hlt⟩
            simp only [Hbkv, _root_.and_self, ite_true]
            wp_apply wp_store_slice_index (V := Loc)
              (t := go.GoType.PointerType go_etcd_io.etcd.api.v3.mvccpb.KeyValue.ty) kvs _ _ «$r0_ptr»
              $$ [$Hkvs] as Hkvs
            · ipureintro; rw [hi]; simp only [List.length_append, List.length_replicate]; omega
            (try wp_auto)
            wp_for_post
            (try wp_auto)
            (try simp only [named])
            iframe HΦ tr ro curRev Hend0 key ctx Hrevp Hti0 Hmodcap Hcrecap Hverscap keys modifies
              creates versions total Hkcap Hzip Hkvscap kvs HsT HtxcT HtraceT HRr Hkn
            iexists (i + 1), (ps ++ [«$r0_ptr»]), (W64 (i : Int))
            (try simp only [named])
            have hsucc : (W64 ((i + 1 : Nat) : Int)) = W64 (i : Int) + W64 1 := by
              first | word | (unfold W64; simp [BitVec.ofInt_add]) | (unfold W64; push_cast; rfl)
            rw [hsucc, hiN, mvcc.set_filled Hbnd.2 hilt]
            iframe Hri Hi Hkvs
            isplitl []
            · ipureintro; exact ⟨by omega, by simp [Hbnd.2]⟩
            rw [List.take_add_one, ha, Option.toList_some,
              List.zip_append (by rw [Hbnd.2, List.length_take_of_le (by omega)])]
            iapply BigSepL.bigSepL_append.2
            isplitl [Hps]
            · iexact Hps
            rw [show [«$r0_ptr»].zip [a] = [(«$r0_ptr», a)] from rfl]
            iapply BigSepL.bigSepL_singleton.2
            iexists kv
            isplitl []
            · ipureintro; exact hfind
            iunfold mvcc.kvPtrIs
            iexists ksi, zeroValDef, slice.nil, 0
            isplitl []
            · rw [mvcc.findKey_key hfind]; iexact Hks
            simp only [Bool.false_eq_true, ↓reduceIte]
            rw [hmod, hcr, hver, show (W64 0 : w64) = 0 from rfl]
            iexact Hp
          · -- all the key-values built
            have hge : ¬ sint.Z (W64 (i : Int)) < sint.Z kvs.len := by
              first | exact Hif | exact fun h => Hif (by rw [decide_eq_true h])
            (try rw [decide_eq_false hge, if_pos (by simp)])
            (try wp_auto)
            have hin : i = sint.nat keys.len := by
              have h1 := Hkvlen.1; have h2 := Hkvlen.2; have h3 := Hbnd.1
              rw [hi] at hge; unfold sint.nat at *; unfold sint.Z at *; omega
            subst hin
            rw [Nat.sub_self, List.replicate_zero, List.append_nil]
            wp_alloc r as Hr
            ihave %Hrnn := typedPointsto_not_null _ _ _ $$ Hr
            (try wp_auto)
            iapply HΦ
            isplitl []
            · ipureintro; intro _; exact Hrnn
            iframe Hti0 HsT HtxcT HtraceT HRr Hkn
            iunfold mvcc.rangeOutcome
            rw [hT]
            iright; iright
            isplitl []
            · ipureintro; exact hle
            isplitl []
            · ipureintro; rfl
            rw [hco]
            simp only [Bool.false_eq_true, ↓reduceIte]
            iexists kvs
            rw [hfk]
            simp only [Bool.not_true]
            subst Htotal
            iframe Hr
            iunfold mvcc.rangeKvs
            iexists ps
            iframe Hkvs
            isplitl []
            · ipureintro; rw [Hbnd.2]; omega
            rw [List.take_of_length_le (by omega)]
            iexact Hps
      | false =>
        -- the full read: the index's revisions, then the bucket's key-values
        (try wp_auto)
        wp_apply (hRevs ti γ.idx kn key endk k e (mvcc.rangeRev rev ro.Rev') ro.Limit'
          ro.WithTotalCount' e0) $$ [$Hti $Hti0 $Hkn $Hkey $Hend $Herr]
          as %revs %total ⟨Hti0, Hkn, Hrevs, Hrevscap, %Htotal⟩
        · ipureintro; rw [Hklog]; exact ⟨hR0, hRlt⟩
        rw [Hklog]
        rw [Hklog] at Htotal
        (try wp_auto)
        wp_apply (hStep trace _ _)
        · ipureintro; exact Htrnn
        (try wp_auto)
        generalize hT : mvcc.rangeTaken log (decide (endk = slice.nil)) k e
          (mvcc.rangeRev rev ro.Rev') ro.Limit' = taken at *
        ihave %Hrlen := ownSlice_len _ _ _ $$ Hrevs
        rw [List.length_map] at Hrlen
        wp_if_destruct
        · -- no revision: no key-value
          have htaken : taken = [] := by
            rw [← List.length_eq_zero_iff, Hrlen.1, Hif]; decide
          wp_alloc r as Hr
          ihave %Hrnn := typedPointsto_not_null _ _ _ $$ Hr
          (try wp_auto)
          subst Htotal
          iapply HΦ
          isplitl []
          · ipureintro; intro _; exact Hrnn
          iframe Hti0 HsT HtxcT HtraceT HRr Hkn
          iunfold mvcc.rangeOutcome
          rw [hT]
          iright; iright
          isplitl []
          · ipureintro; exact hle
          isplitl []
          · ipureintro; rfl
          rw [hco]
          simp only [Bool.false_eq_true, ↓reduceIte]
          iexists slice.nil
          rw [hfk]
          simp only [Bool.not_false]
          iframe Hr
          iunfold mvcc.rangeKvs
          iexists []
          rw [htaken]
          isplitl []
          · iapply ownSlice_nil
          isplitl []
          · ipureintro; rfl
          rw [show ([] : List Loc).zip ([] : List (GoString × mvcc.Rev × mvcc.Rev × w64)) = []
            from rfl]
          iapply BigSepL.bigSepL_nil_intro; iempintro
        · -- the key-values from the bucket
          (try wp_auto)
          wp_apply (hCap Revision.ty ro.Limit' revs _ (DFrac.own 1)) $$ [$Hrevs] as Hrevs
          (try wp_auto)
          have hcap := mvcc.capWithLimit_rangeTaken log (decide (endk = slice.nil)) k e
            (mvcc.rangeRev rev ro.Rev') ro.Limit'
          rw [hT] at hcap
          rw [List.length_map, hcap]
          -- the package facts the loop needs: the `Key` bucket, `fmt`, the context's methods
          ihave #Hsch : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema $$ []
          · iPkgInit
          ihave Hsi : (go_etcd_io.etcd.server.v3.storage.schema.schemaInit : IProp GF) $$ []
          · iapply isPkgInit_access $$ Hsch
          icases Hsi with ⟨-, -, -, ⟨%bK, #HKeyG⟩⟩
          ihave #Hfmt : isPkgInit (PROP := IProp GF) pkg_id.fmt $$ []
          · iPkgInit
          ihave #HD := mvcc.rangeCtx_Done todo ctx cd $$ Hctx
          have hn : taken.length < 2 ^ 63 := by
            have h1 := Hrlen.1; have h2 := Hrlen.2; have h3 := BitVec.toInt_lt (x := revs.len)
            unfold sint.nat at h1; unfold sint.Z at *; omega
          -- `kvs := make([]*mvccpb.KeyValue, n)`, `revBytes := NewRevBytes()`
          wp_apply wp_slice_make2 (V := Loc) (W64 (taken.length : Int)) as %kvs ⟨Hkvs, Hkvscap⟩
          · ipureintro; unfold sint.Z W64
            rw [BitVec.toInt_ofInt_eq_self (by decide)
              (by rw [show (64 - 1 : Nat) = 63 from rfl]; omega)
              (by rw [show (64 - 1 : Nat) = 63 from rfl]; omega)]; omega
          (try wp_auto)
          wp_apply hNew as %rb ⟨Hrb, Hrbcap, %Hrbc⟩
          (try wp_auto)
          -- `revpairs[:len(kvs)]` is `revpairs`
          have hnZ : sint.Z (W64 (taken.length : Int)) = taken.length := by
            unfold sint.Z W64
            rw [BitVec.toInt_ofInt_eq_self (by decide)
              (by rw [show (64 - 1 : Nat) = 63 from rfl]; omega)
              (by rw [show (64 - 1 : Nat) = 63 from rfl]; omega)]
          have hnZ' : (W64 (taken.length : Int)).toInt = taken.length := hnZ
          have hnN : sint.nat (W64 (taken.length : Int)) = taken.length := by
            unfold sint.nat; rw [hnZ']; rfl
          ihave %Hkvlen := ownSlice_len _ _ _ $$ Hkvs
          rw [List.length_replicate, hnN] at Hkvlen
          have hkvl : sint.Z kvs.len = taken.length := by
            have h1 := Hkvlen.1; have h2 := Hkvlen.2; unfold sint.nat at h1; unfold sint.Z at *; omega
          have h0z' : sint.Z (W64 0) = 0 := by decide
          have hrvl : sint.Z revs.len = taken.length := by
            have h1 := Hrlen.1; have h2 := Hrlen.2; unfold sint.nat at h1; unfold sint.Z at *; omega
          have hkr : kvs.len = revs.len := by
            apply BitVec.eq_of_toInt_eq; unfold sint.Z at hkvl hrvl; omega
          ihave %Hrwf := ownSlice_wf _ _ _ $$ Hrevs
          have Hsb : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z kvs.len ∧ sint.Z kvs.len ≤ sint.Z revs.cap :=
            ⟨by decide, by rw [h0z']; omega, by rw [hkvl, ← hrvl]; exact Hrwf.2⟩
          (try simp only [Hsb, _root_.and_self, ite_true])
          rw [hkr]
          ipersist Hrevs
          ihave #Hsub := (ownSlice_trivial_slice revs DFrac.discard _).1 $$ Hrevs
          (try wp_pures)
          wp_alloc rp as Hrp
          (try wp_pures)
          wp_alloc igo as Hgo
          (try wp_auto)
          irename «end» => Hend0
          -- the loop: the first `i` key-values read from the bucket
          ihave HI : (∃ (i : Nat) (ps : List Loc) (iv : w64) (rpv : Revision) (rbuf : GoSlice)
              (bs : List w8),
              "Hi" ∷ i_ptr ↦ W64 i ∗ "Hgo" ∷ igo ↦ iv ∗ "Hrp" ∷ rp ↦ rpv ∗
              "revBytes" ∷ revBytes_ptr ↦ rbuf ∗ "Hrb" ∷ rbuf ↦* bs ∗
              "Hrbcap" ∷ ownSliceCap w8 rbuf (DFrac.own 1) ∗ "%Hbs" ∷ ⌜bs.length = 17⌝ ∗
              "%Hbnd" ∷ ⌜i ≤ taken.length ∧ ps.length = i⌝ ∗
              "Hkvs" ∷ kvs ↦* (ps ++ List.replicate (taken.length - i) (zero_val Loc)) ∗
              "Hps" ∷ [∗list] pa ∈ ps.zip (taken.take i), ∃ kv : EtcdKv,
                ⌜mvcc.findKey pa.2.1 (mvcc.stateAt log (sint.nat (mvcc.rangeRev rev ro.Rev'))) =
                  some kv⌝ ∗ mvcc.kvPtrIs true pa.1 kv) $$ [i Hgo Hrp revBytes Hrb Hrbcap Hkvs]
          · iexists 0, [], (zero_val w64), (zero_val Revision), rb, (List.replicate 17 (W8 0))
            simp only [named, List.nil_append, Nat.sub_zero, List.take_zero, List.zip_nil_left, hnN]
            rw [show (W64 ((0 : Nat) : Int) : w64) = W64 0 from rfl]
            iframe i Hgo Hrp revBytes Hrb Hrbcap Hkvs
            isplitl []
            · ipureintro; simp
            isplitl []
            · ipureintro; exact ⟨Nat.zero_le _, rfl⟩
            iapply BigSepL.bigSepL_nil_intro; iempintro
          wp_for HI
          have hi : sint.Z (W64 (i : Int)) = i := by
            unfold sint.Z W64
            rw [BitVec.toInt_ofInt_eq_self (by decide)
              (by rw [show (64 - 1 : Nat) = 63 from rfl]; omega)
              (by rw [show (64 - 1 : Nat) = 63 from rfl]; omega)]
          have hiN : (sint.Z (W64 (i : Int))).toNat = i := by rw [hi]; rfl
          have hsub0 : revs.len - W64 0 = revs.len := by first | simp | (unfold W64; simp)
          wp_if_destruct
          · -- the `i`th revision pair: its key-value from the bucket
            have hlt0 : sint.Z (W64 (i : Int)) < sint.Z (revs.len - W64 0) := by
              first | exact Hif | (have := go.intoVal_inj Hif; simpa using this)
            rw [hsub0] at hlt0
            have hlt : (i : Int) < sint.Z revs.len := by rw [← hi]; exact hlt0
            have hit : i < taken.length := by omega
            obtain ⟨a, ha⟩ : ∃ a, taken[i]? = some a := ⟨_, List.getElem?_eq_getElem hit⟩
            have Hbr : 0 ≤ sint.Z (W64 (i : Int)) ∧ sint.Z (W64 (i : Int)) < sint.Z (revs.len - W64 0) := by
              rw [hsub0, hi]; omega
            simp only [Hbr, _root_.and_self, ite_true]
            wp_apply wp_load_slice_index (slice.slice revs Revision (W64 0) revs.len)
              (sint.Z (W64 (i : Int))) _ DFrac.discard (mvcc.revVal a.2.1) (by omega) $$ [$Hsub] as -
            · ipureintro; rw [hiN, List.getElem?_map, ha]; rfl
            (try wp_auto)
            -- `select { case <-ctx.Done(): ...; default: }`
            wp_apply HD as %dch #Hdone
            (try wp_auto)
            wp_apply_core mvcc.wp_select1_alt_or_nil _
                iprop((∀ r err, ⌜todo = true → r ≠ null⌝ ∗ txc.[storeTxnCommon, go!"s"] ↦{dq} s ∗
                    txc.[storeTxnCommon, go!"tx"] ↦{dq} (GoInterface.ok rt : GoInterface) ∗
                    txc.[storeTxnCommon, go!"trace"] ↦{dq} trace ∗
                    R ∗ mvcc.idxKnows γ.idx kn ∗ mvcc.idxReader ti γ.idx ∗
                    mvcc.rangeOutcome r err log rev (decide (endk = slice.nil)) k e ro -∗
                    Φ (PairV #r #err)) ∗
                  txc.[storeTxnCommon, go!"s"] ↦{dq} s ∗
                  txc.[storeTxnCommon, go!"tx"] ↦{dq} (GoInterface.ok rt : GoInterface) ∗
                  txc.[storeTxnCommon, go!"trace"] ↦{dq} trace ∗ R ∗ mvcc.idxKnows γ.idx kn ∗
                  tr_ptr ↦ txc ∗ ro_ptr ↦ ro ∗ curRev_ptr ↦ rev ∗ end_ptr ↦ endk ∗
                  key_ptr ↦ key ∗ ctx_ptr ↦ (GoInterface.ok ctx : GoInterface) ∗
                  mvcc.idxReader ti γ.idx ∗ ownSliceCap Revision revs (DFrac.own 1) ∗
                  revpairs_ptr ↦ revs ∗ total_ptr ↦ total ∗ ownSliceCap Loc kvs (DFrac.own 1) ∗
                  kvs_ptr ↦ kvs ∗ i_ptr ↦ W64 (i : Int) ∗ igo ↦ W64 (i : Int) ∗
                  rp ↦ mvcc.revVal a.2.1 ∗ revBytes_ptr ↦ rbuf ∗ rbuf ↦* bs ∗
                  ownSliceCap w8 rbuf (DFrac.own 1) ∗
                  kvs ↦* (ps ++ List.replicate (taken.length - i) (zero_val Loc)) ∗
                  [∗list] pa ∈ ps.zip (taken.take i), ∃ kv : EtcdKv,
                    ⌜mvcc.findKey pa.2.1 (mvcc.stateAt log (sint.nat (mvcc.rangeRev rev ro.Rev'))) =
                      some kv⌝ ∗ mvcc.kvPtrIs true pa.1 kv)
                $$ [] [HΦ HsT HtxcT HtraceT HRr Hkn tr ro curRev Hend0 key ctx Hti0 Hrevscap revpairs total Hkvscap kvs Hi Hgo
                  Hrp revBytes Hrb Hrbcap Hkvs Hps] []
            · cases todo
              case true =>
                simp only [mvcc.rangeDone, ↓reduceIte]
                icases Hdone with (%Hnil | ⟨⟨%γd, #Hdone⟩, #Hnd⟩)
                · -- `context.TODO()`: `Done()` is `nil`, the case never fires
                  iright
                  iapply chan.nilClausePre_recv Unit dch _ Hnil
                -- a context never canceled: the case never fires (it would give `PDone`)
                ileft
                iintro ⟨HΦ, HsT, HtxcT, HtraceT, HRr, Hkn, tr, ro, curRev, Hend0, key, ctx, Hti0,
                  Hrevscap, revpairs, total, Hkvscap, kvs, Hi, Hgo, Hrp, revBytes, Hrb, Hrbcap, Hkvs,
                  Hps⟩
                simp only [chan.nonblockingAltClausePre]
                iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, dch, γd
                isplitr
                · ipureintro; rfl
                isplitr
                · iapply context.isContextDone_is_chan $$ Hdone
                iapply context.isContextDone_nonblocking_receive _ _ _ _ _ $$ Hdone
                isplit
                · iintro ⟨#Hp, -⟩
                  iexfalso
                  iunfold mvcc.neverDone at Hnd
                  iapply Hnd $$ Hp
                · iframe
              ileft
              simp only [mvcc.rangeDone, mvcc.rangeCtx, Bool.false_eq_true, ↓reduceIte]
              icases Hdone with ⟨%γd, #Hdone⟩
              ihave #Hctx2 := Hctx
              iNamed Hctx2
              iintro ⟨HΦ, HsT, HtxcT, HtraceT, HRr, Hkn, tr, ro, curRev, Hend0, key, ctx, Hti0, Hrevscap,
                revpairs, total, Hkvscap,
                kvs, Hi, Hgo, Hrp, revBytes, Hrb, Hrbcap, Hkvs, Hps⟩
              simp only [chan.nonblockingAltClausePre]
              iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, dch, γd
              isplitr
              · ipureintro; rfl
              isplitr
              · iapply context.isContextDone_is_chan $$ Hdone
              iapply context.isContextDone_nonblocking_receive _ _ _ _ _ $$ Hdone
              isplit
              · -- the context is done: no result, an error
                iintro ⟨-, #Hclosed⟩
                (try wp_auto)
                ihave #HE := HErr $$ %Broadcast.Done
                wp_apply HE $$ [$Hclosed] as %cerr %Hne
                (try wp_auto)
                wp_apply wp_slice_literal
                isplitr
                · ipureintro; rfl
                iintro %asl ⟨Hasl, -⟩
                (try wp_auto)
                wp_apply fmt.wp_Errorf $$ [$Hasl] as %e' -
                (try wp_auto)
                wp_for_post
                (try wp_auto)
                iapply HΦ
                isplitl []
                · ipureintro; intro h; cases h
                iframe Hti0 HsT HtxcT HtraceT HRr Hkn
                iunfold mvcc.rangeOutcome
                iright; ileft
                isplitl []
                · ipureintro; exact hle
                isplitl []
                · ipureintro; exact ⟨hco, hfk⟩
                isplitl []
                · ipureintro; rfl
                ipureintro; intro h; cases h
              · iframe
            · iframe
            · iintro ⟨HΦ, HsT, HtxcT, HtraceT, HRr, Hkn, tr, ro, curRev, Hend0, key, ctx, Hti0, Hrevscap,
                revpairs, total, Hkvscap,
                kvs, Hi, Hgo, Hrp, revBytes, Hrb, Hrbcap, Hkvs, Hps⟩ -
              (try wp_auto)
              -- `revBytes = RevToBytes(revpair, revBytes)`
              wp_apply (hRevTo (mvcc.revVal a.2.1) rbuf bs (Or.inl Hbs)) $$ [$Hrb $Hrbcap]
                as %rb' ⟨Hrb, Hrbcap⟩
              (try wp_auto)
              rw [mvcc.revOf_revVal, List.drop_of_length_le (by omega), List.append_nil]
              -- the bucket's entry (the model)
              have hRnat : sint.nat (mvcc.rangeRev rev ro.Rev') < 2 ^ 63 := by
                have h1 := hRlt; have h2 := hR0; unfold sint.nat; unfold sint.Z at *; omega
              have hRW : mvcc.rangeRev rev ro.Rev' =
                  W64 ((sint.nat (mvcc.rangeRev rev ro.Rev') : Nat) : Int) := by
                unfold sint.nat; rw [Int.toNat_of_nonneg hR0]; exact BitVec.ofInt_toInt.symm
              have hmem : a ∈ mvcc.rangeAnswers log (decide (endk = slice.nil)) k e
                  (W64 ((sint.nat (mvcc.rangeRev rev ro.Rev') : Nat) : Int)) := by
                rw [← hRW]
                exact mvcc.mem_rangeAnswers_of_taken _ _ _ _ _ _ a
                  (hT.symm ▸ List.mem_of_getElem? ha)
              obtain ⟨kv, hfind, hmod, hcr, hver, hlook⟩ := mvcc.rangeAnswers_kv log
                (mvcc.LogWf.of_wf' Hwf' HneT) Hlen Hcs _ k e _ hRnat a hmem
              have hlookm : m.lookup (mvcc.revBytes a.2.1 false) = some (mvcc.kvEncode kv) :=
                HsubT _ _ hlook
              -- `tr.tx.UnsafeRange(schema.Key, revBytes, nil, 0)`
              iunfold mvcc.keyReader at Hrdr
              ihave HR := Hrdr $$ %bK %rb' %(mvcc.revBytes a.2.1 false) %(DFrac.own 1)
              wp_apply HR $$ [$HKeyG $HRr $Hrb] as %ks %vs ⟨HRr, Hrb, #Hkv⟩
              iunfold mvcc.keyVals at Hkv
              rw [hlookm]
              icases Hkv with ⟨%ksl, %vsl, #Hks, #Hksl, #Hvs, #Hvsl⟩
              (try wp_auto)
              -- one value: `len(vs) == 1`
              ihave %Hvlen := ownSlice_len _ _ _ $$ Hvs
              simp only [List.length_singleton] at Hvlen
              have hv1 : vs.len = W64 1 := by
                have h1 := Hvlen.1; have h2 := Hvlen.2
                unfold sint.nat at h1; unfold sint.Z at *
                apply BitVec.eq_of_toInt_eq
                rw [show (W64 1 : w64).toInt = 1 by decide]; omega
              rw [hv1, decide_eq_true (rfl : (W64 1 : w64) = W64 1)]
              simp only [Bool.not_true]
              (try wp_auto)
              -- `kv := &mvccpb.KeyValue{}`, `proto.Unmarshal(vs[0], kv)`
              have Hb0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z vs.len :=
                ⟨by decide, by rw [hv1]; decide⟩
              simp only [Hb0, _root_.and_self, ite_true]
              wp_apply wp_load_slice_index vs (sint.Z (W64 0)) [vsl] DFrac.discard vsl (by decide)
                $$ [$Hvs] as -
              · ipureintro; rfl
              (try wp_auto)
              irename «$r0» => Hkvp
              wp_apply (hUnm vsl kv «$r0_ptr» _ DFrac.discard) $$ [$Hvsl $Hkvp]
                as ⟨-, %ks', %vs', %st, %uf, %sc, Hp, #Hks', #Hvs'⟩
              (try wp_auto)
              -- `kvs[i] = kv`
              have Hbkv : 0 ≤ sint.Z (W64 (i : Int)) ∧ sint.Z (W64 (i : Int)) < sint.Z kvs.len := by
                rw [hi, hkvl]; omega
              (try simp only [Hbkv, _root_.and_self, ite_true])
              wp_apply wp_store_slice_index (V := Loc)
                (t := go.GoType.PointerType go_etcd_io.etcd.api.v3.mvccpb.KeyValue.ty) kvs _ _ «$r0_ptr»
                $$ [$Hkvs] as Hkvs
              · ipureintro; rw [hi]; simp only [List.length_append, List.length_replicate]; omega
              (try wp_auto)
              wp_for_post
              (try wp_auto)
              (try simp only [named])
              iframe HΦ tr ro curRev Hend0 key ctx Hti0 Hrevscap revpairs total Hkvscap kvs
                HsT HtxcT HtraceT HRr Hkn
              iexists (i + 1), (ps ++ [«$r0_ptr»]), (W64 (i : Int)), (mvcc.revVal a.2.1), rb',
                (mvcc.revBytes a.2.1 false)
              (try simp only [named])
              have hsucc : (W64 ((i + 1 : Nat) : Int)) = W64 (i : Int) + W64 1 := by
                first | word | (unfold W64; simp [BitVec.ofInt_add]) | (unfold W64; push_cast; rfl)
              rw [hsucc, hiN, mvcc.set_filled Hbnd.2 hit]
              iframe Hi Hgo Hrp revBytes Hrb Hrbcap Hkvs
              isplitl []
              · ipureintro; exact mvcc.revBytes_false_length _
              isplitl []
              · ipureintro; exact ⟨by omega, by simp [Hbnd.2]⟩
              rw [List.take_add_one, ha, Option.toList_some,
                List.zip_append (by rw [Hbnd.2, List.length_take_of_le (by omega)])]
              iapply BigSepL.bigSepL_append.2
              isplitl [Hps]
              · iexact Hps
              rw [show [«$r0_ptr»].zip [a] = [(«$r0_ptr», a)] from rfl]
              iapply BigSepL.bigSepL_singleton.2
              iexists kv
              isplitl []
              · ipureintro; exact hfind
              iunfold mvcc.kvPtrIs
              iexists ks', st, uf, sc
              isplitl []
              · iexact Hks'
              simp only [↓reduceIte]
              iexists vs'
              iframe Hvs' Hp
          · -- all the key-values read
            have hge : ¬ sint.Z (W64 (i : Int)) < sint.Z (revs.len - W64 0) := by
              first | exact Hif | exact fun h => Hif (by rw [decide_eq_true h])
            (try rw [decide_eq_false hge, if_pos (by simp)])
            rw [hsub0, hi] at hge
            have hin : i = taken.length := by omega
            subst hin
            rw [Nat.sub_self, List.replicate_zero, List.append_nil]
            (try wp_auto)
            wp_apply (hStep trace _ _)
            · ipureintro; exact Htrnn
            (try wp_auto)
            wp_alloc r as Hr
            ihave %Hrnn := typedPointsto_not_null _ _ _ $$ Hr
            (try wp_auto)
            subst Htotal
            iapply HΦ
            isplitl []
            · ipureintro; intro _; exact Hrnn
            iframe Hti0 HsT HtxcT HtraceT HRr Hkn
            iunfold mvcc.rangeOutcome
            rw [hT]
            iright; iright
            isplitl []
            · ipureintro; exact hle
            isplitl []
            · ipureintro; rfl
            rw [hco]
            simp only [Bool.false_eq_true, ↓reduceIte]
            iexists kvs
            rw [hfk]
            simp only [Bool.not_false]
            iframe Hr
            iunfold mvcc.rangeKvs
            iexists ps
            iframe Hkvs
            isplitl []
            · ipureintro; exact Hbnd.2
            rw [List.take_of_length_le (by omega)]
            iexact Hps

end proof

end EtcdGrove
end Perennial
