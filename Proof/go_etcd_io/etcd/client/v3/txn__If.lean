/-
Proof of `Spec/go_etcd_io/etcd/client/v3/txn__If.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.txn__If
public import Spec.go_etcd_io.etcd.client.v3.Cmp__Clone
public import Spec.go_etcd_io.etcd.client.v3.Cmp__GetCompare
public import Perennial.Proof.sync.Link

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

theorem txn.If.wp_proof (wp_Clone : Cmp.Clone.spec (GF := GF) (hG := hG))
    (wp_GetCompare : Cmp.GetCompare.spec (GF := GF) (hG := hG)) :
    txn.If.spec (GF := GF) (hG := hG) := by
  intro tp addr ci cd b sl ms
  wp_start as ⟨Htx, #Hcs, %Hb⟩
  obtain ⟨hif, hthen, helse⟩ := Hb
  iunfold txnObjAt at Htx
  icases Htx with ⟨%Htpn, %api, %cosl, %csl, %ssl, %fsl, %cps, %sps, %fps, %iw, #Hkvf, #Hkv, #Hctxf,
    #Hctx, #Hce, #Hmu, Hcif, Hcthen, Hcelse, Hiw, Hcmps, Hcsl, Hccap, #Hcpa, Hsus, Hssl, Hscap,
    #Hspa, Hfas, Hfsl, Hfcap, #Hfpa, #Hcof, #Hco⟩
  wp_apply wp_with_defer as %defer defer
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, -⟩
  rw [hif]
  wp_auto
  rw [hthen]
  wp_auto
  rw [helse]
  wp_auto
  iunfold cmpsAt at Hcs
  icases Hcs with ⟨%cs, #Hcss, %Hcl, #Hcsa⟩
  ihave %Hsll := ownSlice_len $$ Hcss
  rename_i ig
  irename : (ig ↦ zero_val w64 : IProp GF) => gi
  ihave IH : iprop(∃ (n gv : w64) (csl' : GoSlice) (cps' : List Loc),
      "i" ∷ i_ptr ↦ n ∗ "gi" ∷ ig ↦ gv ∗
      "Hcmps" ∷ structFieldRef go_etcd_io.etcd.client.v3.txn go!"cmps" tp ↦ csl' ∗
      "Hcsl" ∷ csl' ↦* cps' ∗ "Hccap" ∷ ownSliceCap Loc csl' (DFrac.own 1) ∗
      "#Hcpa" ∷ comparesAt cps' (b.model.cmps ++ ms.take (sint.nat n)) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (cs.length : Int)⌝) $$ [i gi Hcmps Hcsl Hccap]
  · iexists W64 0, _, csl, cps
    simp only [named]
    iframe
    simp only [show sint.nat (W64 0) = 0 by rfl, List.take_zero, List.append_nil]
    iframe #
    ipureintro; constructor <;> word
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.nat n < cs.length := by word
    obtain ⟨c, Hci⟩ : ∃ c, cs[sint.nat n]? = some c := ⟨_, List.getElem?_eq_getElem Hlt⟩
    obtain ⟨m, Hmi⟩ : ∃ m, ms[sint.nat n]? = some m :=
      ⟨_, List.getElem?_eq_getElem (by rw [← Hcl]; exact Hlt)⟩
    have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len := ⟨Hn.1, by word⟩
    icases ownSlice_elem_acc (sint.Z n) c sl DFrac.discard cs Hn.1 Hci $$ Hcss
      with ⟨#Hce0, -⟩
    ihave #Hcm := Hcsa $$ %(sint.nat n) %c %m %Hci %Hmi
    simp only [Hbnd, and_self, ↓reduceIte]
    wp_auto
    simp only [Hbnd, and_self, ↓reduceIte]
    wp_auto
    wp_apply wp_Clone $$ [$Hce0 $Hcm] as %c' ⟨-, %Hc'n, Hcown⟩
    iunfold compareOwn at Hcown
    icases Hcown with ⟨%ksl, %esl, %u, Hres, #Htgt, #Hkey, #Hks, Hre, #Hes, Htu, #Hu⟩
    ipersist Hres; ipersist Hre; ipersist Htu
    wp_apply wp_GetCompare $$ [$cmp]
    · ipureintro; exact Hc'n
    iintro -
    wp_apply wp_slice_literal (V := Loc) [c'.c']
    isplitr
    · ipureintro; rfl
    iintro %sl2 ⟨Hsl2, -⟩
    (try wp_auto)
    wp_apply wp_slice_append $$ [Hcsl Hccap Hsl2] as %sl' ⟨Hcsl, Hccap, -⟩
    · iframe
    (try wp_auto)
    wp_for_post
    iframe
    iexists n + W64 1, _, sl', cps' ++ [c'.c']
    simp only [named]
    iframe
    ihave #Hcmp : compareAt (GF := GF) c'.c' m $$ []
    · unfold compareAt
      iexists ksl, esl, u
      iframe #
    isplitl []
    · rw [show sint.nat (n + W64 1) = sint.nat n + 1 by word, List.take_add_one, Hmi]
      simp only [Option.toList_some, ← List.append_assoc]
      iapply comparesAt_snoc
      iframe #
      ipureintro; exact Hc'n
    ipureintro; constructor <;> word
  · have Hge : sint.nat n = ms.length := by rw [← Hcl]; word
    rw [show ms.take (sint.nat n) = ms by rw [Hge, List.take_length]]
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked]
    · inext; itrivial
    iapply HΦ
    unfold txnObjAt
    isplitl []
    · ipureintro; exact Htpn
    iexists api, cosl, csl', ssl, fsl, cps', sps, fps, iw
    iframe
    iframe #

end proof

end EtcdGrove
end Perennial
