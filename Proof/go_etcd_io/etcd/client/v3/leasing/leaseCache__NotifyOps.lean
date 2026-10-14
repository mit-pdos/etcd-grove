/-
Proof of `Spec/go_etcd_io/etcd/client/v3/leasing/leaseCache__NotifyOps.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.leasing.leaseCache__NotifyOps
public import Spec.go_etcd_io.etcd.client.v3.leasing.leaseCache__notify
public import Spec.go_etcd_io.etcd.client.v3.Op__IsGet
public import Spec.go_etcd_io.etcd.client.v3.Op__KeyBytes

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

theorem leaseCache.NotifyOps.wp_proof
    (hIsGet : Op.IsGet.spec (GF := GF) (hG := hG))
    (hKey : Op.KeyBytes.spec (GF := GF) (hG := hG))
    (hnotify : leaseCache.notify.spec (GF := GF) (hG := hG)) :
    leaseCache.NotifyOps.spec (GF := GF) (hG := hG) := by
  intro lc γ pfx X sl os
  wp_start as ⟨#Hlc, Hrd, #Hops⟩
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
  ihave IH : iprop(∃ (n : w64) (opv : go_etcd_io.etcd.client.v3.Op) (wsl : GoSlice)
      (cs : List GoChan),
      "i" ∷ i_ptr ↦ n ∗ "op" ∷ op_ptr ↦ opv ∗ "wcs" ∷ wcs_ptr ↦ wsl ∗ "Hwsl" ∷ wsl ↦* cs ∗
      "Hcap" ∷ ownSliceCap GoChan wsl (DFrac.own 1) ∗ "#Hcs" ∷ ([∗list] c ∈ cs, waitcOk c) ∗
      "Hrd" ∷ leaseCacheReader lc γ pfx X ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (vs.length : Int)⌝) $$ [i op wcs Hrd]
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
    · wp_apply hKey $$ [$op $Hat] as %ksl ⟨op, #Hk⟩
      wp_apply wp_bytes_to_string ksl o.key DFrac.discard $$ [$Hk] as -
      wp_apply (hnotify lc γ pfx X (fun _ => iprop(True)) o.key) $$ [$Hrd $Hlc $Hpeek] as %li %wc ⟨Hrd, %st, -, Hres⟩
      icases Hres with (⟨%Hnone, %Hli, %Hwc⟩ | ⟨%ent, %Hent, #Hw, -, -⟩)
      · subst Hwc
        wp_auto
        wp_for_post
        iframe
        iexists (n + W64 1), v, wsl, cs
        simp only [named]
        iframe
        iframe #
        ipureintro; constructor <;> word
      · wp_if_destruct
        · wp_for_post
          iframe
          iexists (n + W64 1), v, wsl, cs
          simp only [named]
          iframe
          iframe #
          ipureintro; constructor <;> word
        · wp_apply wp_slice_literal (l := [wc])
          isplitr
          · ipureintro; rfl
          iintro %zsl ⟨Hz, -⟩
          wp_auto
          wp_apply wp_slice_append $$ [$Hwsl $Hcap $Hz] as %wsl' ⟨Hwsl, Hcap, -⟩
          wp_for_post
          iframe
          iexists (n + W64 1), v, wsl', cs ++ [wc]
          simp only [named]
          iframe
          isplitl []
          · iapply (BigSepL.bigSepL_snoc (PROP := IProp GF)).2
            iframe #
          ipureintro; constructor <;> word
    · wp_for_post
      iframe
      iexists (n + W64 1), v, wsl, cs
      simp only [named]
      iframe
      iframe #
      ipureintro; constructor <;> word
  · iapply HΦ
    iframe
    iframe #

end proof

end leasing
end EtcdGrove
end Perennial
