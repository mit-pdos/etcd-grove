/-
Proof of `Spec/go_etcd_io/etcd/client/v3/leasing/txnLeasing__guardKeys.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.leasing.txnLeasing__guardKeys
public import Spec.go_etcd_io.etcd.client.v3.leasing.leaseCache__Rev
public import Spec.go_etcd_io.etcd.client.v3.Op__IsGet
public import Spec.go_etcd_io.etcd.client.v3.Op__KeyBytes
public import Spec.go_etcd_io.etcd.client.v3.Op__RangeBytes
public import Spec.go_etcd_io.etcd.client.v3.CreateRevision
public import Spec.go_etcd_io.etcd.client.v3.Compare
public import Proof.go_etcd_io.etcd.client.v3.leasing.InvLeasingTxnLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace leasing

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.leasing go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

theorem txnLeasing.guardKeys.wp_proof
    (hKey : EtcdGrove.Op.KeyBytes.spec (GF := GF) (hG := hG))
    (hIsGet : EtcdGrove.Op.IsGet.spec (GF := GF) (hG := hG))
    (hRange : EtcdGrove.Op.RangeBytes.spec (GF := GF) (hG := hG))
    (hRev : leaseCache.Rev.spec (GF := GF) (hG := hG))
    (hCR : EtcdGrove.CreateRevision.spec (GF := GF) (hG := hG))
    (hCmp : EtcdGrove.Compare.spec (GF := GF) (hG := hG)) :
    txnLeasing.guardKeys.spec (GF := GF) (hG := hG) := by
  intro txn lkv γ pfx dq sl os
  wp_start as ⟨Hlkvf, #HLKV, Hrd, #Hops⟩
  ihave #HLKV' := HLKV
  unfold isLeasingKV
  icases HLKV' with ⟨%cl, %kv, %ctx, %cs, %cancel, %osl, %Hpfx, -, -, #Hpfxf, -, -, -, -, -, -, -, -,
    -, #Hcache, -⟩
  ihave #Hops' := (opsAt_listRel sl os).1 $$ Hops
  icases Hops' with ⟨%vs, #Hvs, #Hrel⟩
  ihave #Hrel' := Hrel
  unfold listRel
  icases Hrel' with ⟨%Hlen, #Hv⟩
  ihave %Hsl := ownSlice_len _ _ _ $$ Hvs
  ihave #Hcv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  ihave #Hpeek : lcPeek (GF := GF) (leasingX lkv γ) (fun _ => iprop(True)) $$ []
  · unfold lcPeek
    imodintro
    iintro %st %q HX
    iframe HX
    imodintro
    itrivial
  wp_auto
  wp_apply (wp_map_make1 (K := GoString) (V := Bool) go.string go.bool) as %mref Hm
  (try wp_auto)
  ihave IH : iprop(∃ (n : w64) (opv : go_etcd_io.etcd.client.v3.Op) (csl : GoSlice)
      (cvs : List go_etcd_io.etcd.client.v3.Cmp) (ms : List CmpModel) (m : GMap GoString Bool),
      "i" ∷ i_ptr ↦ n ∗ "op" ∷ op_ptr ↦ opv ∗ "cmps" ∷ cmps_ptr ↦ csl ∗ "#Hcsl" ∷ csl ↦*□ cvs ∗
      "Hcap" ∷ ownSliceCap go_etcd_io.etcd.client.v3.Cmp csl (DFrac.own 1) ∗
      "#Hrelc" ∷ listRel cmpAt cvs ms ∗ "Hm" ∷ mref ↦$ m ∗ "Hrd" ∷ lkvReader lkv γ pfx ∗
      "Hlkvf" ∷ structFieldRef txnLeasing go!"lkv" txn ↦{dq} lkv ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (vs.length : Int)⌝) $$ [i op cmps Hm Hrd Hlkvf]
  · iexists W64 0, _, slice.nil, [], [], ∅
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
    wp_apply hKey $$ [$op $Hat] as %ksl ⟨op, #Hk⟩
    wp_apply wp_bytes_to_string ksl o.key DFrac.discard $$ [$Hk] as -
    (try wp_auto)
    wp_apply hIsGet $$ [$op $Hat] as op
    wp_if_destruct
    · (try wp_auto)
      wp_for_post
      iframe
      iexists (n + W64 1), v, csl, cvs, ms, m
      simp only [named]
      iframe
      iframe #
      ipureintro; constructor <;> word
    · wp_apply hRange $$ [$op $Hbase] as %esl ⟨op, #He⟩
      ihave %Hel := ownSlice_len _ _ _ $$ He
      (try wp_auto)
      wp_if_destruct
      · (try wp_auto)
        wp_apply (wp_map_lookup1 go.string go.bool mref m o.key (DFrac.own 1)) $$ [$Hm] as Hm
        generalize (m !! o.key).getD (zero_val Bool) = bs
        cases bs
        · (try wp_auto)
          wp_apply (hRev (lkvLeases lkv) γ.lc pfx (leasingX lkv γ) (fun _ => iprop(True)) o.key)
            $$ [$Hcache $Hrd $Hpeek] as %r ⟨Hrd, -⟩
          (try wp_auto)
          wp_apply hCR $$ [$Hcv] as %c0 #Hc0
          (try wp_auto)
          wp_apply (hCmp c0 _ go!"<" .lt _ (.num (r + W64 1))) $$ [$Hcv $Hc0] as %c1 #Hc1
          · ipureintro
            refine ⟨by simp [cmpOpOf], ?_⟩
            simp [cmpKeyM, cmpArgOf]
          wp_apply wp_slice_literal (l := [c1])
          isplitr
          · ipureintro; rfl
          iintro %zsl ⟨Hz, -⟩
          (try wp_auto)
          wp_apply (wp_slice_append_persistent csl cvs _ [c1] (DFrac.own 1)) $$ [$Hcsl $Hcap $Hz]
            as %csl' ⟨#Hcsl', Hcap, -⟩
          (try wp_auto)
          wp_apply (wp_mapInsert go.string mref m o.key true) $$ [$Hm] as Hm
          (try wp_auto)
          wp_for_post
          iframe
          iexists (n + W64 1), v, csl', cvs ++ [c1], ms ++ [compareM (cmpKeyM .create (pfx ++ o.key)) .lt (.num (r + W64 1))], _
          simp only [named]
          iframe
          iframe #
          isplitr
          · iapply listRel_app
            iframe #
            iapply listRel_single
            iexact Hc1
          ipureintro; constructor <;> word
        · (try wp_auto)
          wp_for_post
          iframe
          iexists (n + W64 1), v, csl, cvs, ms, m
          simp only [named]
          iframe
          iframe #
          ipureintro; constructor <;> word
      · (try wp_auto)
        wp_for_post
        iframe
        iexists (n + W64 1), v, csl, cvs, ms, m
        simp only [named]
        iframe
        iframe #
        ipureintro; constructor <;> word
  · (try wp_auto)
    iapply HΦ
    iframe
    iexists ms
    iapply (cmpsAt_listRel _ _).2
    iexists cvs
    iframe #

end proof

end leasing
end EtcdGrove
end Perennial
