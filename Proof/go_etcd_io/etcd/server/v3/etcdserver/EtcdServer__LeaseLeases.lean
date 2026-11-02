/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__LeaseLeases.lean`. Lean-first
(no Rocq counterpart); the lease-read plan (2026-10-31).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__LeaseLeases
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__checkLeaseLeases
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__newHeader
public import Spec.go_etcd_io.etcd.server.v3.lease.lessor__Leases
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.LeaseCheckLemmas

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `leaseCheckFrom` is monotone in its keys' verdict `K`. -/
theorem leaseCheckFrom_mono (s : Loc) (E : apply.AEnv GF) (ctx : GoInterface) (n : Nat)
    (K K' : go_etcd_io.etcd.server.v3.auth.AuthInfo → IProp GF) (h : ∀ info, K info ⊢ K' info) :
    leaseCheckFrom s E ctx n K ⊢ leaseCheckFrom s E ctx n K' := by
  unfold leaseCheckFrom
  iintro (H | ⟨%info, Hb, (Ha | Hk)⟩)
  · ileft; iexact H
  · iright; iexists info; iframe Hb; ileft; iexact Ha
  · iright; iexists info; iframe Hb; iright; iapply (h info); iexact Hk

set_option maxHeartbeats 4000000 in
theorem EtcdServer.LeaseLeases.wp_proof
    (hLs : lease.lessor.Leases.spec (GF := GF) (hG := hG))
    (hChk : EtcdServer.checkLeaseLeases.spec (GF := GF) (hG := hG))
    (hHdr : EtcdServer.newHeader.spec (GF := GF) (hG := hG)) :
    EtcdServer.LeaseLeases.spec (GF := GF) (hG := hG) := by
  intro s E γr γl ctx cd r mid cid n m
  wp_start as ⟨#Hsr, #Hhf, Hst, #Hau, #Hlb, #Hlr, #Hpub, #Hmlb, #Hctx, HRD, #Hpool, Htok, %Hb1, %Hb2⟩
  ihave #Htx : mvcc.txnCtx (GF := GF) ctx cd $$ []
  · iunfold mvcc.txnCtx; iright; iexact Hctx
  ihave #Hlr' := Hlr
  iunfold srvLessorRd at Hlr'
  icases Hlr' with ⟨%lp, #Hlf, #Hinv⟩
  ihave #Hlp : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply (hLs lp γl m) $$ [$Htok] as %sl %ls ⟨Htok, Hsl, ⟨%li, %Hmi, #Hmap⟩, #Hls⟩
  · iframe Hinv Hpool Hmlb; ipureintro; exact ⟨Hb1, Hb2⟩
  ihave #Hlive := lease.leaseMapAt_live γl li ls $$ Hmap
  ihave ⟨#Hobj, #Hid⟩ := BigSepL.bigSepL_sep_eqv.1 $$ Hls
  (try wp_auto)
  -- `if err := s.checkLeaseLeases(ctx, ls); err != nil { return nil, err }`
  wp_apply (hChk s E γl ctx cd sl ls (DFrac.own 1) n li) $$ [$HRD $Htok $Hsl]
      as %err ⟨HRD, Htok, Hsl, #Herr, Hok⟩
  · iframe #
    isplitr
    · ipureintro; exact Hb1
    iapply BigSepL.bigSepL_sep_eqv.2
    iframe Hobj Hlive
  (try wp_auto)
  rcases err with ei | _
  · (try wp_auto)
    iapply HΦ
    iframe HRD Htok Hst
    iright
    iframe Herr
    ipureintro; exact ⟨rfl, by intro h; cases h⟩
  ihave %Hsll := ownSlice_len _ _ _ $$ Hsl
  (try wp_auto)
  wp_apply (wp_slice_make2 (V := Loc) sl.len) as %lsl ⟨Hlsl, -⟩
  · ipureintro; have := Hsll.2; word
  (try wp_auto)
  ihave %Hlsll := ownSlice_len _ _ _ $$ Hlsl
  simp only [List.length_replicate, List.length_map] at Hsll Hlsll
  rename_i gptr
  irename : (gptr ↦ zero_val w64 : IProp GF) => gi
  ihave IH : iprop(∃ (j : w64) (g : w64) (ps : List Loc),
      "i" ∷ i_ptr ↦ j ∗ "gi" ∷ gptr ↦ g ∗ "Hlsl" ∷ lsl ↦* ps ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z sl.len ∧ ps.length = ls.length⌝ ∗
      "Hps" ∷ [∗list] k ↦ p ∈ ps.take (sint.nat j), ∃ (st : etcdserverpb.LeaseStatus) (id : w64),
        ⌜(ls.map Prod.snd)[k]? = some id ∧ st.ID' = id⌝ ∗ p ↦ st) $$ [i gi Hlsl]
  · iexists W64 0, _, _
    iframe i gi Hlsl
    isplitl []
    · ipureintro
      refine ⟨by decide, by word, ?_⟩
      simp only [List.length_replicate]; omega
    · rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero]
      iapply BigSepL.bigSepL_nil.2; itrivial
  wp_for IH
  wp_if_destruct
  · have hjl : (sint.Z j).toNat < ls.length := by unfold sint.nat at Hsll; word
    obtain ⟨x, Hx⟩ : ∃ x, ls[(sint.Z j).toNat]? = some x := ⟨_, List.getElem?_eq_getElem hjl⟩
    have Hbnd : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z sl.len := ⟨Hj.1, Hif⟩
    simp only [Hbnd, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index sl (sint.Z j) _ _ x.1 Hj.1 $$ [Hsl] as Hsl
    · iframe; ipureintro; simp only [List.getElem?_map, Hx, Option.map_some]
    (try wp_auto)
    simp only [Hbnd, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index sl (sint.Z j) _ _ x.1 Hj.1 $$ [Hsl] as Hsl
    · iframe; ipureintro; simp only [List.getElem?_map, Hx, Option.map_some]
    ihave #HidX := BigSepL.bigSepL_lookup Hx $$ Hid
    (try wp_auto)
    have Hbl : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z lsl.len := ⟨Hj.1, by unfold sint.nat at Hlsll; word⟩
    simp only [Hbl, _root_.and_self, ↓reduceIte]
    wp_apply wp_store_slice_index lsl (sint.Z j) ps _ $$ [Hlsl] as Hlsl
    · iframe; ipureintro; refine ⟨Hj.1, ?_⟩; rw [Hj.2.2]; unfold sint.nat at Hsll; word
    wp_for_post
    iframe
    iexists j + W64 1, j, ps.set (sint.Z j).toNat _
    iframe
    isplitl []
    · ipureintro; refine ⟨by word, by word, by rw [List.length_set]; exact Hj.2.2⟩
    have hsn : sint.nat (j + W64 1) = (sint.Z j).toNat + 1 := by unfold sint.nat; word
    have hjp : (sint.Z j).toNat < ps.length := by rw [Hj.2.2]; exact hjl
    rw [hsn, List.take_add_one, List.take_set_of_le (Nat.le_refl _),
      List.getElem?_set_self hjp, Option.toList_some]
    iapply BigSepL.bigSepL_snoc.2
    unfold sint.nat
    iframe Hps
    iexists _, x.2
    iframe
    ipureintro
    simp only [List.length_take, List.getElem?_map, and_true]
    rw [Nat.min_eq_left (Nat.le_of_lt hjp), Hx]; rfl
  have hall : ps.take (sint.nat j) = ps := by
    apply List.take_of_length_le; rw [Hj.2.2]; unfold sint.nat at *; word
  rw [hall] at *
  ihave #Hhf' := Hhf
  iunfold srvHeaderFacts at Hhf'
  icases Hhf' with ⟨%cl, #Hcl, #Hcid, #Hmid, #Hlead⟩
  (try wp_auto)
  wp_apply (hHdr E.authOn s E γr cl mid cid) $$ [$Hst] as %h ⟨Hst, Hh⟩
  · iframe #
  (try wp_auto)
  ihave #Hc := Hok $$ %rfl
  iapply HΦ
  iframe HRD Htok Hst
  ileft
  isplitr
  · ipureintro; rfl
  iexists li, ls.map Prod.snd
  isplitr
  · ipureintro; exact Hmi
  isplitr
  · iapply lease.leaseMapAt_ids; iexact Hmap
  isplitr [Hc]
  · iunfold leasesRespIs
    iexists _
    iframe
    isplitl [Hh]
    · iunfold srvHeaderAt; iexact Hh
    iunfold leasesListIs
    iexists ps
    iframe
    ipureintro; rw [List.length_map]; exact Hj.2.2
  iapply leaseCheckFrom_mono _ _ _ _ _ _ ?_
  rotate_left
  · iexact Hc
  intro info
  rw [BigSepL.bigSepL_map]
  apply BigSepL.bigSepL_mono
  intro k x _
  unfold leaseKeysVerdictFrom
  iintro H
  iright; iexists x.1; iexact H

end proof

end EtcdGrove
end Perennial
