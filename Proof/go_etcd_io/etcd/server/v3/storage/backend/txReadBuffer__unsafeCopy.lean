/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/backend/txReadBuffer__unsafeCopy.lean`. Lean-first (no
Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.txReadBuffer__unsafeCopy
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.bucketBuffer__CopyUsed
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.BksLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.backend backend

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]


theorem backend.txReadBuffer.unsafeCopy.wp_proof
    (hCopy : backend.bucketBuffer.CopyUsed.spec (GF := GF) (hG := hG)) :
    backend.txReadBuffer.unsafeCopy.spec (GF := GF) (hG := hG) := by
  intro txr dq m P R
  wp_start as Hrb
  unfold rbAt bksAt
  icases Hrb with ⟨Htb, Hver, Hm, Hbbs⟩
  ihave %Hiff := bbs_lookup_iff P R.bks dq $$ Hbbs
  icases txBuffer_buckets_acc _ _ _ $$ Htb with ⟨Hbk, Htb⟩
  wp_auto
  wp_apply wp_map_len $$ Hm as Hm
  wp_apply (wp_map_make2 (K := w64) (V := Loc)) as %nm Hnm
  ihave Htb := Htb $$ Hbk
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  wp_func_lits
  iapply wp_map_for_range (K := w64) (V := Loc) (fun (keys : List w64) (i : Int) =>
      iprop(∃ (P' : BksPhys) (bv : Loc) (bn : w64),
        "Hnm" ∷ nm ↦$ P'.fmap Prod.fst ∗
        "Hnew" ∷ ([∗map] _id ↦ x;es ∈ P';R.bks.filter (fun j _ => decide (j ∈ keys.take i.toNat)),
          bbAt (GF := GF) x.1 (DFrac.own 1) x.2 es) ∗
        "Hbbs" ∷ ([∗map] _id ↦ x;es ∈ P;R.bks, bbAt (GF := GF) x.1 dq x.2 es) ∗
        "txrCopy" ∷ txrCopy_ptr ↦ ({ txBuffer' := { buckets' := nm }, bufVersion' := W64 0 } : txReadBuffer) ∗
        "bucket" ∷ bucket_ptr ↦ bv ∗ "bucketName" ∷ bucketName_ptr ↦ bn ∗
        "%Hi" ∷ ⌜0 ≤ i⌝))
    _ BucketID.ty (go.GoType.PointerType bucketBuffer.ty) m (P.fmap Prod.fst) dq $$ Hm
  iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
  isplitl [Hnm Hbbs txrCopy bucket bucketName]
  · iexists ∅, _, _
    simp only [named]
    rw [show Int.toNat 0 = 0 from rfl, gmap_filter_take_zero, GMap.fmap_empty]
    iframe
    isplitl
    · iapply bbs_empty
    · ipureintro; omega
  isplitr
  · imodintro
    iintro %i %k %v ⟨%Hki, %Hmv⟩ HP
    iNamed HP
    obtain ⟨x, hPk, rfl⟩ : ∃ x, P !! k = some x ∧ x.1 = v := by
      simp only [GMap.lookup_fmap, Option.map_eq_some_iff] at Hmv
      exact Hmv
    have hnotin : k ∉ keys.take i.toNat := not_mem_take_of_getElem? Hknodup Hki
    have hBi : (R.bks.filter (fun j _ => decide (j ∈ keys.take i.toNat))) !! k = none := by
      simp [GMap.lookup_filter, hnotin]
    ihave %hP'k := bbs_lookup_none_r P' _ (DFrac.own 1) k hBi $$ Hnew
    icases bbs_lookup_acc P R.bks dq k x hPk $$ Hbbs with ⟨%es, %hB, Hbb, Hbbs⟩
    wp_auto
    wp_apply hCopy x.1 dq x.2 es $$ [$Hbb] as %c ⟨Hbb, %p', Hc, %Hlen⟩
    ihave Hbbs := Hbbs $$ Hbb
    wp_apply wp_mapInsert $$ Hnm as Hnm
    unfold forMapPostcondition
    iright; ileft
    isplitr
    · ipureintro; rfl
    iexists <[k := (c, p')]> P', x.1, k
    simp only [named]
    rw [GMap.fmap_insert, show (i + 1).toNat = i.toNat + 1 by omega,
      gmap_filter_take_succ R.bks keys i.toNat k es Hki hB]
    iframe
    isplitl
    · iapply (bbs_insert P' _ (DFrac.own 1) k (c, p') es hP'k hBi).2
      iframe
    · ipureintro; omega
  iintro HP Hm
  iNamed HP
  have hlen : (((GMap.fmap Prod.fst P).size : Nat) : Int).toNat = keys.length := by
    rw [Hklen]; rfl
  rw [hlen, gmap_filter_take_length R.bks keys (fun j hj => by
    rw [Hkset j, GMap.lookup_fmap]
    have := (Hiff j).2 hj
    cases h : P !! j <;> simp_all)]
  wp_auto
  iapply HΦ
  iframe
  ipureintro; rfl

end proof

end EtcdGrove
end Perennial
