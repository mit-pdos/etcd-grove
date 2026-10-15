/-
Proof of `Spec/go_etcd_io/etcd/client/v3/leasing/txnLeasing__guardRanges.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.leasing.txnLeasing__guardRanges
public import Spec.go_etcd_io.etcd.client.v3.leasing.leasingKV__revokeRange
public import Spec.go_etcd_io.etcd.client.v3.Op__IsGet
public import Spec.go_etcd_io.etcd.client.v3.Op__KeyBytes
public import Spec.go_etcd_io.etcd.client.v3.Op__RangeBytes
public import Spec.go_etcd_io.etcd.client.v3.WithLastRev
public import Spec.go_etcd_io.etcd.client.v3.WithRange
public import Spec.go_etcd_io.etcd.client.v3.ModRevision
public import Spec.go_etcd_io.etcd.client.v3.Cmp__WithRange
public import Spec.go_etcd_io.etcd.client.v3.Compare
public import Spec.go_etcd_io.etcd.client.v3.CreateRevision
public import Proof.go_etcd_io.etcd.client.v3.leasing.InvLeasingTxnLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace leasing

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.leasing go_etcd_io.etcd.api.v3

/-- The get of `guardRanges`: `OpGet(key, WithLastRev(), WithRange(end))`. -/
abbrev lastRevGs (e : GoString) : List (OpFull → OpFull) := withTopM (W64 3) (W64 2) ++ [withRangeM e]

theorem lastRevOp_facts (key e : GoString) :
    ¬ opGetPanics (lastRevGs e) ∧ (opGetModel key (lastRevGs e)).t = W64 1 ∧
      (opGetModel key (lastRevGs e)).isPrefixGet [] = false ∧
      (opGetModel key (lastRevGs e)).base.rev = W64 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  by_cases hk : key = [] <;>
  simp [opGetPanics, opGetModel, opFold, lastRevGs, withTopM, withPrefixM, withSortM, withLimitM,
    withRangeM, OpFull.getInit, OpFull.newOp, OpModel.zero, OpFull.isPrefixGet, hk]

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

theorem txnLeasing.guardRanges.wp_proof
    (hIsGet : EtcdGrove.Op.IsGet.spec (GF := GF) (hG := hG))
    (hRange : EtcdGrove.Op.RangeBytes.spec (GF := GF) (hG := hG))
    (hKey : EtcdGrove.Op.KeyBytes.spec (GF := GF) (hG := hG))
    (hRR : leasingKV.revokeRange.spec (GF := GF) (hG := hG))
    (hWLR : EtcdGrove.WithLastRev.spec (GF := GF) (hG := hG))
    (hWR : EtcdGrove.WithRange.spec (GF := GF) (hG := hG))
    (hMR : EtcdGrove.ModRevision.spec (GF := GF) (hG := hG))
    (hCWR : EtcdGrove.Cmp.WithRange.spec (GF := GF) (hG := hG))
    (hCmp : EtcdGrove.Compare.spec (GF := GF) (hG := hG))
    (hCR : EtcdGrove.CreateRevision.spec (GF := GF) (hG := hG)) :
    txnLeasing.guardRanges.spec (GF := GF) (hG := hG) := by
  intro txn lkv γ pfx ctx cs dq sl os
  wp_start as ⟨Hlkvf, Hctxf, #HLKV, Hrd, #Hsr, #Hctx, #Hcc, #Hops⟩
  ihave #HLKV' := HLKV
  iunfold isLeasingKV at HLKV'
  icases HLKV' with ⟨%cl, %kv, %lctx, %lcs, %cancel, %osl, %Hpfx, -, #Hkvf, #Hpfxf, -, -, -,
    #HKV, -⟩
  ihave #Hops' := (opsAt_listRel sl os).1 $$ Hops
  icases Hops' with ⟨%vs, #Hvs, #Hrel⟩
  ihave #Hrel' := Hrel
  iunfold listRel at Hrel'
  icases Hrel' with ⟨%Hlen, #Hv⟩
  ihave %Hsl := ownSlice_len _ _ _ $$ Hvs
  ihave #Hcv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  wp_auto
  ihave IH : iprop(∃ (n : w64) (opv : go_etcd_io.etcd.client.v3.Op) (csl : GoSlice)
      (cvs : List go_etcd_io.etcd.client.v3.Cmp) (ms : List CmpModel),
      "i" ∷ i_ptr ↦ n ∗ "op" ∷ op_ptr ↦ opv ∗ "cmps" ∷ cmps_ptr ↦ csl ∗ "#Hcsl" ∷ csl ↦*□ cvs ∗
      "Hcap" ∷ ownSliceCap go_etcd_io.etcd.client.v3.Cmp csl (DFrac.own 1) ∗
      "#Hrelc" ∷ listRel cmpAt cvs ms ∗ "Hrd" ∷ lkvReader lkv γ pfx ∗
      "Hlkvf" ∷ structFieldRef txnLeasing go!"lkv" txn ↦{dq} lkv ∗
      "Hctxf" ∷ structFieldRef txnLeasing go!"ctx" txn ↦{dq} GoInterface.ok ctx ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (vs.length : Int)⌝) $$ [i op cmps Hrd Hlkvf Hctxf]
  · iexists W64 0, _, slice.nil, [], []
    simp only [named]
    iframe
    isplitl []
    · iapply ownSlice_nil
    isplitl []
    · iapply ownSliceCap_nil
    isplitl []
    · iapply listRel_nil
    ipureintro; constructor <;> word
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.nat n < vs.length := by word
    obtain ⟨v, Hvi⟩ : ∃ v, vs[sint.nat n]? = some v := ⟨_, List.getElem?_eq_getElem Hlt⟩
    obtain ⟨o, Hoi⟩ : ∃ o, os[sint.nat n]? = some o :=
      ⟨_, List.getElem?_eq_getElem (by rw [← Hlen]; exact Hlt)⟩
    have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len := ⟨Hn.1, by word⟩
    simp only [Hbnd, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index sl (sint.Z n) vs DFrac.discard v Hn.1 $$ [Hvs] as -
    · iframe #; ipureintro; exact Hvi
    ihave #Hat := Hv $$ %(sint.nat n) %v %o %Hvi %Hoi
    ihave #Hat' := Hat
    iunfold opFullAt at Hat'
    icases Hat' with ⟨#Hbase, -⟩
    wp_apply hIsGet $$ [$op $Hat] as op
    wp_if_destruct
    · (try wp_auto)
      wp_for_post
      iframe
      iexists (n + W64 1), v, csl, cvs, ms
      simp only [named]
      iframe
      iframe #
      ipureintro; constructor <;> word
    · wp_apply hRange $$ [$op $Hbase] as %esl ⟨op, #He⟩
      ihave %Hel := ownSlice_len _ _ _ $$ He
      (try wp_auto)
      wp_if_destruct
      · (try wp_auto)
        wp_for_post
        iframe
        iexists (n + W64 1), v, csl, cvs, ms
        simp only [named]
        iframe
        iframe #
        ipureintro; constructor <;> word
      · (try wp_auto)
        wp_apply hKey $$ [$op $Hat] as %ksl ⟨op, #Hk⟩
        wp_apply wp_bytes_to_string ksl o.key DFrac.discard $$ [$Hk] as -
        wp_apply hRange $$ [$op $Hbase] as %esl2 ⟨op, #He2⟩
        wp_apply wp_bytes_to_string esl2 o.base.rangeEnd DFrac.discard $$ [$He2] as -
        (try wp_auto)
        wp_apply (hRR lkv γ pfx ctx cs o.key o.base.rangeEnd) $$ [$HLKV $Hrd $Hsr $Hctx $Hcc]
          as %maxRev %err Hrd
        cases err with
        | ok e =>
          (try wp_auto)
          wp_for_post
          iapply HΦ
          iframe
          ileft; ipureintro; exact ⟨by simp, rfl⟩
        | nil =>
          (try wp_auto)
          wp_apply hWLR $$ [$Hcv] as %sl1 ⟨#Hsl1, Hcap1⟩
          wp_apply hWR $$ [$Hcv] as %f #Hf
          wp_apply wp_slice_literal
          isplitr
          · ipureintro; rfl
          iintro %lsl ⟨Hlsl, -⟩
          ipersist Hlsl
          generalize hlsl : slice.mk lsl _ _ = litSl
          ihave #Hsl1' := Hsl1
          iunfold optsAt at Hsl1'
          icases Hsl1' with ⟨%fs1, #Hfs1, %Hlen1, #Hf1⟩
          (try wp_auto)
          wp_apply wp_slice_append_persistent sl1 fs1 litSl [f] DFrac.discard $$ [$Hfs1 $Hcap1 $Hlsl]
            as %gsl ⟨#Hgsl, -, -⟩
          ihave #Hopts : optsAt gsl (lastRevGs o.base.rangeEnd) $$ []
          · iunfold optsAt
            iexists fs1 ++ [f]
            iframe Hgsl
            isplitr
            · ipureintro; simp [Hlen1]
            imodintro
            iintro %j %f' %g %Hf' %Hg
            rcases Nat.lt_or_ge j fs1.length with h | h
            · rw [List.getElem?_append_left h] at Hf'
              rw [List.getElem?_append_left (by rw [← Hlen1]; exact h)] at Hg
              iapply Hf1 $$ %j %f' %g %Hf' %Hg
            · rw [List.getElem?_append_right h] at Hf'
              rw [List.getElem?_append_right (by rw [← Hlen1]; exact h)] at Hg
              rw [← Hlen1] at Hg
              rcases Nat.lt_or_ge (j - fs1.length) 1 with h' | h'
              · have h0 : j - fs1.length = 0 := by omega
                rw [h0] at Hf' Hg
                cases Hf'; cases Hg; iexact Hf
              · rw [List.getElem?_eq_none (by simp; omega)] at Hf'
                cases Hf'
          (try wp_auto)
          ihave #HKV' := HKV
          iunfold isEtcdKV at HKV'
          ihave #HG := HKV' $$ %ctx %cs %o.key %gsl %(lastRevGs o.base.rangeEnd) %(W64 0)
          ihave #H0 := etcdReached_zero (GF := GF)
          obtain ⟨Hnp, Ht1, HnP, Hrev0⟩ := lastRevOp_facts o.key o.base.rangeEnd
          wp_apply HG $$ [] as %gresp %gerr #Hgres
          · iframe Hctx Hopts H0
            ipureintro; exact ⟨Hnp, Ht1⟩
          iunfold kvGetResult at Hgres
          icases Hgres with (%Hgne | ⟨%Hgnil, %R, %gm, -, -, -, -, Hgr⟩)
          · obtain ⟨ge, rfl⟩ : ∃ ge, gerr = GoInterface.ok ge := by
              cases gerr with
              | nil => exact absurd rfl Hgne
              | ok ge => exact ⟨ge, rfl⟩
            (try wp_auto)
            wp_for_post
            iapply HΦ
            iframe
            ileft; ipureintro; exact ⟨by simp, rfl⟩
          subst Hgnil
          rw [ite_eq_right (c := (opGetModel o.key (lastRevGs o.base.rangeEnd)).isPrefixGet [] = true)
            (by rw [HnP]; simp)]
          unfold getRespRange
          rw [ite_eq_left (show (opGetModel o.key (lastRevGs o.base.rangeEnd)).base.rev = W64 0 ∧
            KeyRangeUnder [] (opGetModel o.key (lastRevGs o.base.rangeEnd)).key
              (opGetModel o.key (lastRevGs o.base.rangeEnd)).base.rangeEnd from
            ⟨Hrev0, fun _ _ => List.nil_prefix⟩)]
          icases Hgr with ⟨%s', %gsl', %gps, %gkvs, -, -, #Hgsl', #Hgps, #Hgkvs, -⟩
          iunfold kvPtrsAt at Hgkvs
          icases Hgkvs with ⟨%Hgl, #Hgkv⟩
          ihave %Hgsl := ownSlice_len $$ Hgps
          (try wp_auto)
          wp_join iprop(∃ mm : w64, maxModRev_ptr ↦ mm ∗ getResp_ptr ↦ gresp) with [maxModRev getResp]
            as ⟨%mm, maxModRev, getResp⟩
          · obtain ⟨kp, Hkp⟩ : ∃ kp, gps[0]? = some kp := by
              cases gps with
              | nil => exfalso; simp at Hgsl; word
              | cons kp _ => exact ⟨kp, rfl⟩
            obtain ⟨w, Hw⟩ : ∃ w, gkvs[0]? = some w := by
              cases gkvs with
              | nil => cases gps with
                | nil => cases Hkp
                | cons _ _ => simp at Hgl
              | cons w _ => exact ⟨w, rfl⟩
            (try wp_auto)
            rw [ite_eq_left (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z gsl'.len by
              constructor
              · word
              · have : gps.length ≠ 0 := by intro h; rw [List.length_eq_zero_iff] at h; subst h; cases Hkp
                have := Hgsl.1
                word)]
            icases ownSlice_elem_acc (sint.Z (W64 0)) kp gsl' DFrac.discard gps (by word)
              (by simpa using Hkp) $$ Hgps with ⟨#Hkpe, -⟩
            ihave #Hwv := Hgkv $$ %0 %kp %w %Hkp %Hw
            iunfold kvValAt at Hwv
            icases Hwv with ⟨%keySl, %valSl, -, -, -, #Hmod, -⟩
            (try wp_auto)
            wp_join_done
          (try wp_auto)
          wp_apply hMR $$ [$Hcv] as %c0 #Hc0
          wp_apply hCWR $$ [$Hcv $Hc0] as %c1 #Hc1
          (try wp_auto)
          wp_apply (hCmp c1 _ go!"<" .lt _ (.num (mm + W64 1))) $$ [$Hcv $Hc1] as %c2 #Hc2
          · ipureintro
            refine ⟨by simp [cmpOpOf], ?_⟩
            simp [cmpWithRangeM, cmpKeyM, cmpArgOf]
          (try wp_auto)
          wp_apply hCR $$ [$Hcv] as %d0 #Hd0
          wp_apply hCWR $$ [$Hcv $Hd0] as %d1 #Hd1
          (try wp_auto)
          wp_apply (hCmp d1 _ go!"<" .lt _ (.num (maxRev + W64 1))) $$ [$Hcv $Hd1] as %d2 #Hd2
          · ipureintro
            refine ⟨by simp [cmpOpOf], ?_⟩
            simp [cmpWithRangeM, cmpKeyM, cmpArgOf]
          (try wp_auto)
          wp_apply wp_slice_literal (l := [c2, d2])
          isplitr
          · ipureintro; rfl
          iintro %zsl ⟨Hz, -⟩
          (try wp_auto)
          wp_apply (wp_slice_append_persistent csl cvs _ [c2, d2] (DFrac.own 1)) $$ [$Hcsl $Hcap $Hz]
            as %csl' ⟨#Hcsl', Hcap, -⟩
          (try wp_auto)
          wp_for_post
          iframe
          iexists (n + W64 1), v, csl', cvs ++ [c2, d2], ms ++
            [compareM (cmpWithRangeM o.base.rangeEnd (cmpKeyM .mod o.key)) .lt (.num (mm + W64 1)),
             compareM (cmpWithRangeM (pfx ++ o.base.rangeEnd) (cmpKeyM .create (pfx ++ o.key))) .lt
               (.num (maxRev + W64 1))]
          simp only [named]
          iframe
          iframe #
          isplitr
          · iapply listRel_app
            iframe #
            iapply listRel_cons
            iframe Hc2
            iapply listRel_single; iexact Hd2
          ipureintro; constructor <;> word
  · (try wp_auto)
    iapply HΦ
    iframe
    iright
    isplitr
    · ipureintro; rfl
    iexists ms
    iapply (cmpsAt_listRel _ _).2
    iexists cvs
    iframe #

end proof

end leasing
end EtcdGrove
end Perennial
