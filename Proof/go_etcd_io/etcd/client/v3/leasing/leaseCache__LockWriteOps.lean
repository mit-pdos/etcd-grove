/-
Proof of `Spec/go_etcd_io/etcd/client/v3/leasing/leaseCache__LockWriteOps.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.leasing.leaseCache__LockWriteOps
public import Spec.go_etcd_io.etcd.client.v3.leasing.leaseCache__Lock
public import Spec.go_etcd_io.etcd.client.v3.leasing.leaseCache__LockRange
public import Spec.go_etcd_io.etcd.client.v3.Op__IsGet
public import Spec.go_etcd_io.etcd.client.v3.Op__KeyBytes
public import Spec.go_etcd_io.etcd.client.v3.Op__RangeBytes

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace leasing

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.leasing go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

theorem leaseCache.LockWriteOps.wp_proof
    (hLock : leaseCache.Lock.spec (GF := GF) (hG := hG))
    (hLockRange : leaseCache.LockRange.spec (GF := GF) (hG := hG))
    (hIsGet : Op.IsGet.spec (GF := GF) (hG := hG))
    (hKey : Op.KeyBytes.spec (GF := GF) (hG := hG))
    (hRange : Op.RangeBytes.spec (GF := GF) (hG := hG)) :
    leaseCache.LockWriteOps.spec (GF := GF) (hG := hG) := by
  intro lc γ pfx X sl os
  wp_start as ⟨#Hlc, #Hstep, #Hops⟩
  unfold opsAt
  icases Hops with ⟨%vs, #Hvs, %Hlen, #Hv⟩
  ihave %Hsl := ownSlice_len _ _ _ $$ Hvs
  wp_auto
  ihave #Hpeek : lcPeek (GF := GF) X (fun _ => iprop(True)) $$ []
  · unfold lcPeek
    imodintro
    iintro %st %q HX
    iframe HX
    imodintro
    itrivial
  ihave IH : iprop(∃ (n : w64) (opv : go_etcd_io.etcd.client.v3.Op) (rsl : GoSlice)
      (cs : List GoChan),
      "i" ∷ i_ptr ↦ n ∗ "op" ∷ op_ptr ↦ opv ∗ "ret" ∷ ret_ptr ↦ rsl ∗ "Hrsl" ∷ rsl ↦* cs ∗
      "Hcap" ∷ ownSliceCap GoChan rsl (DFrac.own 1) ∗ "Hcs" ∷ ([∗list] c ∈ cs, waitcClose c) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (vs.length : Int)⌝) $$ [i op ret]
  · iexists W64 0, _, slice.nil, []
    simp only [named]
    iframe
    isplitl []
    · iapply ownSlice_nil
    isplitl []
    · iapply ownSliceCap_nil
    isplitl []
    · iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2; iempintro
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
    wp_apply hIsGet $$ [$op $Hat] as op
    wp_if_destruct
    · wp_for_post
      iframe
      iexists (n + W64 1), v, rsl, cs
      simp only [named]
      iframe
      ipureintro; constructor <;> word
    · wp_apply hKey $$ [$op $Hat] as %ksl ⟨op, #Hk⟩
      wp_apply wp_bytes_to_string ksl o.key DFrac.discard $$ [$Hk] as -
      ihave #Hat' := Hat
      unfold opFullAt
      icases Hat' with ⟨#Hbase, -⟩
      wp_apply hRange $$ [$op $Hbase] as %esl ⟨op, #He⟩
      wp_apply wp_bytes_to_string esl o.base.rangeEnd DFrac.discard $$ [$He] as -
      wp_if_destruct
      · wp_apply (hLock lc γ pfx X (fun _ => iprop(True)) o.key) $$ [$Hlc $Hpeek $Hstep]
          as %wc %r ⟨%st, -, -, -, Hres⟩
        wp_if_destruct
        · wp_for_post
          iframe
          iexists (n + W64 1), v, rsl, cs
          simp only [named]
          iframe
          ipureintro; constructor <;> word
        · icases Hres with (⟨%Hnone, %Hwc⟩ | ⟨%Hsome, Hwc⟩)
          · exact absurd Hwc ‹_›
          wp_apply wp_slice_literal (l := [wc])
          isplitr
          · ipureintro; rfl
          iintro %zsl ⟨Hz, -⟩
          wp_auto
          wp_apply wp_slice_append $$ [$Hrsl $Hcap $Hz] as %rsl' ⟨Hrsl, Hcap, -⟩
          wp_for_post
          iframe
          iexists (n + W64 1), v, rsl', cs ++ [wc]
          simp only [named]
          iframe
          isplitl []
          · iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2; iempintro
          ipureintro; constructor <;> word
      · wp_apply (hLockRange lc γ pfx X (fun _ => iprop(True)) o.key o.base.rangeEnd)
          $$ [$Hlc $Hpeek $Hstep] as %lsl ⟨%st, %ks, %cs2, Hlsl, Hlcap, Hcs2, -, -⟩
        wp_apply wp_slice_append $$ [$Hrsl $Hcap $Hlsl] as %rsl' ⟨Hrsl, Hcap, -⟩
        wp_for_post
        iframe
        iexists (n + W64 1), v, rsl', cs ++ cs2
        simp only [named]
        iframe
        ipureintro; constructor <;> word
  · iapply HΦ
    iframe

end proof

end leasing
end EtcdGrove
end Perennial
