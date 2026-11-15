/-
The proof of `Spec/go_etcd_io/bbolt/Bucket__openBucket_w.lean` (U6e, `notes/bbolt-proof-plan.md`):
`newBucket` (a writer: its two maps), the alignment test (`uintptr` of a pointer is an arbitrary
word: both branches); aligned, the header copied from the value into a fresh `InBucket`;
misaligned, the value cloned, the clone's first 16 bytes its header (owned whole), the rest
persisted; the inline page after the header.
-/
module

public import Spec.go_etcd_io.bbolt.Bucket__openBucket_w
public import Spec.go_etcd_io.bbolt.cloneBytes
public import Spec.go_etcd_io.bbolt.internal.common.InBucket__RootPage
public import Proof.go_etcd_io.bbolt.internal.common.Lemmas.Bytes

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

theorem Bucket.openBucket_w.wp_proof (hcl : cloneBytes.spec (GF := GF) (hG := hG))
    (hRP : internal.common.InBucket.RootPage.spec (GF := GF) (hG := hG)) :
    Bucket.openBucket_w.spec (GF := GF) (hG := hG) := by
  intro K tx r m X bl B value vsr cv hB hwr hvs h16 hinl
  wp_start as ⟨Hw, #Hv⟩
  icases wtxW_pkgInit K tx r m X $$ Hw with ⟨Hw, #Hpkg⟩
  ihave #Hcom : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common $$ []
  · iPkgInit
  icases wtxW_cells_acc K tx r m X $$ Hw with ⟨%Hbase, Hcells, Hwb⟩
  ihave Hw := Hwb $$ Hcells
  icases src_openParts X.v Hbase value vsr cv hvs h16 $$ Hv with ⟨#Hop, %Hvp⟩
  ihave %Hvl := srcOwn_len_r X.v value vsr cv hvs $$ Hv
  have hvlen : 16 ≤ sint.Z value.len := by
    have h1 := Hvl.1; have h2 := Hvl.2; simp only [sint.nat] at h1; unfold sint.Z at *; omega
  icases wtxW_bkt_tx_acc K tx r m X bl B hB $$ Hw with ⟨%dt, Htx, Htxb⟩
  wp_auto
  ihave Hw := Htxb $$ Htx
  icases wtxW_writable_acc K tx r m X $$ Hw with ⟨Hwr, Hwrb⟩
  wp_func_call; wp_call
  wp_auto
  rw [hwr]
  wp_auto
  wp_apply (wp_map_make1 (K := GoString) (V := Loc)) as %bm Hbm
  wp_apply (wp_map_make1 (K := w64) (V := Loc)) as %nm Hnm
  ihave %Hnmn := ownMap_not_nil _ _ _ $$ Hnm
  have Hnmn' : nm ≠ null := Hnmn
  try wp_auto
  ihave Hw := Hwrb $$ Hwr
  rw [if_pos (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z value.len from
    ⟨by decide, by rw [show sint.Z (W64 0) = 0 from rfl]; omega⟩)]
  unfold sliceIndexRef
  rw [show sint.Z (W64 0) = 0 by rfl, go.arrayIndexRef_0]
  wp_auto
  wp_apply wp_ArbitraryInt as %x -
  icases (persistent_entails_left (typedPointsto_not_null _ _ _)) $$ child with ⟨child, %Hcn⟩
  iStructNamed child
  by_cases hal : x &&& W64 7 = W64 0
  · rw [decide_eq_true hal]
    icases wtxW_bkt_tx_acc K tx r m X bl B hB $$ Hw with ⟨%dt2, Htx, Htxb⟩
    wp_auto
    ihave Hw := Htxb $$ Htx
    icases wtxW_writable_acc K tx r m X $$ Hw with ⟨Hwr, Hwrb⟩
    rw [hwr]
    wp_auto
    ihave Hw := Hwrb $$ Hwr
    rw [if_pos (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z value.len from
      ⟨by decide, by rw [show sint.Z (W64 0) = 0 from rfl]; omega⟩)]
    unfold sliceIndexRef
    rw [show sint.Z (W64 0) = 0 by rfl, go.arrayIndexRef_0]
    icases wtxW_src_hdr K tx r m X value vsr cv hvs h16 $$ [Hw] with ⟨%dh, Hh, Hhb⟩
    · iframe; iframe #
    wp_auto
    ihave Hw := Hhb $$ Hh
    wp_method_call; wp_call
    wp_auto
    irename InBucket => HIB
    irename : («$r0_ptr» ↦ inBucketOf cv : IProp GF) => Hib
    wp_apply hRP _ (inBucketOf cv) (DFrac.own 1) $$ [Hib] as Hib
    · iexact Hib
    icases wtxW_fill_fresh K tx r m X child_ptr _ $$ [Hw FillPercent] with ⟨Hw, FillPercent, %Hfr⟩
    · iframe
    have hrt : child_ptr ≠ tx.[Tx, go!"root"] := Hfr.2
    rw [show (decode (List.take 8 (bytesAt cv 0 16)) : w64) = (inBucketOf cv).root' from rfl]
    have hroot : inBucketRoot cv = (inBucketOf cv).root'.toNat := rfl
    iapply wp_fupd
    by_cases hr0 : (inBucketOf cv).root' = W64 0
    · rw [decide_eq_true hr0]
      have hi : inBucketRoot cv = 0 := by rw [hroot, hr0]; rfl
      have hgt := hinl hi
      wp_auto
      have h16v : 16 < sint.Z value.len := by
        have h1 := Hvl.1; have h2 := Hvl.2; simp only [sint.nat] at h1; unfold sint.Z at *; omega
      rw [if_pos (show 0 ≤ sint.Z (W64 16) ∧ sint.Z (W64 16) < sint.Z value.len from
        ⟨by decide, by rw [show sint.Z (W64 16) = 16 from rfl]; omega⟩)]
      rw [sliceIndexRef_byte _ _ Hvp (by decide), show sint.Z (W64 16) = 16 from rfl]
      wp_auto
      ipersist tx
      have hpp : value.ptr +ₗ (16 : Int) ≠ null := by
        intro h; have := congrArg Loc.addr h; simp [Loc.add, null] at this; omega
      cases vsr with
      | stale => exact absurd rfl hvs
      | view =>
        ihave %Hil := src_inl_view X.v value cv h16 $$ Hv
        imodintro
        iapply HΦ
        iexists (⟨⟨«$r0_ptr», tx, bm, value.ptr +ₗ (16 : Int), null, nm, W64 4602678819172646912⟩,
          inBucketOf cv, ∅, ∅, ∅, inlinePage cv, Src.view, PageSt.view⟩ : BRec)
        iframe Hw
        isplitl [HIB tx buckets page rootNode nodes Hib Hbm Hnm]
        · simp only [objOwn, pageOwn]
          rw [if_neg hrt, if_pos trivial, if_neg Hnmn']
          iframe; iframe #
          ipureintro; exact Hil
        isplitl [FillPercent]
        · iexists _; iframe; ipureintro; decide
        ipureintro
        exact ⟨Hcn, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => ⟨hpp, rfl, Or.inl ⟨rfl, rfl, rfl⟩⟩,
          fun h => absurd hi h, Hnmn'⟩
      | own d =>
        ihave #Hil := src_inl_own X.v value d cv h16 $$ Hv
        imodintro
        iapply HΦ
        iexists (⟨⟨«$r0_ptr», tx, bm, value.ptr +ₗ (16 : Int), null, nm, W64 4602678819172646912⟩,
          inBucketOf cv, ∅, ∅, ∅, inlinePage cv, Src.own DFrac.discard, PageSt.none⟩ : BRec)
        iframe Hw
        isplitl [HIB tx buckets page rootNode nodes Hib Hbm Hnm]
        · simp only [objOwn, pageOwn]
          rw [if_neg hrt, if_pos trivial, if_neg hpp, if_neg Hnmn']
          iframe; iframe #
        isplitl [FillPercent]
        · iexists _; iframe; ipureintro; decide
        ipureintro
        exact ⟨Hcn, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => ⟨hpp, rfl, Or.inr ⟨rfl, rfl⟩⟩,
          fun h => absurd hi h, Hnmn'⟩
    · rw [decide_eq_false hr0]
      have hi : inBucketRoot cv ≠ 0 := by
        rw [hroot]; intro h; apply hr0; apply BitVec.eq_of_toNat_eq; simpa using h
      wp_auto
      ipersist tx
      imodintro
      iapply HΦ
      iexists (⟨⟨«$r0_ptr», tx, bm, null, null, nm, W64 4602678819172646912⟩,
        inBucketOf cv, ∅, ∅, ∅, inlinePage cv, Src.own DFrac.discard, PageSt.none⟩ : BRec)
      iframe Hw
      isplitl [HIB tx buckets page rootNode nodes Hib Hbm Hnm]
      · simp only [objOwn, pageOwn]
        rw [if_neg hrt, if_pos trivial, if_pos trivial, if_neg Hnmn']
        iframe; iframe #
      isplitl [FillPercent]
      · iexists _; iframe; ipureintro; decide
      ipureintro
      exact ⟨Hcn, rfl, rfl, rfl, rfl, rfl, rfl, fun h => absurd h hi, fun _ => ⟨rfl, rfl⟩, Hnmn'⟩
  · rw [decide_eq_false hal]
    wp_auto
    icases wtxW_cells_acc K tx r m X $$ Hw with ⟨-, Hc, Hwb⟩
    icases viewCells_src_acc wq X.v Hbase value vsr cv hvs $$ [Hc] with ⟨%dvq, Hvs, Hcb⟩
    · iframe; iframe #
    wp_apply hcl value cv dvq $$ [Hvs] as %cl ⟨Hcl, -, Hvs⟩
    · iframe
    ihave Hc := Hcb $$ Hvs
    ihave Hw := Hwb $$ Hc
    try wp_auto
    ihave %Hcll := ownSlice_len _ _ _ $$ Hcl
    have hne : cv ≠ [] := by intro h; simp [h] at h16
    ihave %Hcp := ownSlice_ptr_pos cl cv (DFrac.own 1) hne $$ Hcl
    icases wtxW_bkt_tx_acc K tx r m X bl B hB $$ Hw with ⟨%dt2, Htx, Htxb⟩
    wp_auto
    ihave Hw := Htxb $$ Htx
    icases wtxW_writable_acc K tx r m X $$ Hw with ⟨Hwr, Hwrb⟩
    rw [hwr]
    wp_auto
    ihave Hw := Hwrb $$ Hwr
    have hclen : 16 ≤ sint.Z cl.len := by
      have h1 := Hcll.1; have h2 := Hcll.2; simp only [sint.nat] at h1; unfold sint.Z at *; omega
    rw [if_pos (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z cl.len from
      ⟨by decide, by rw [show sint.Z (W64 0) = 0 from rfl]; omega⟩)]
    unfold sliceIndexRef
    rw [show sint.Z (W64 0) = 0 by rfl, go.arrayIndexRef_0]
    wp_auto
    -- the clone's bytes: its header owned whole, the rest persisted
    icases ownSlice_bytes_acc go.uint8 (.scalar _ _ .isPlainScalar_uint8) cl cv (DFrac.own 1) Hcp
      $$ Hcl with ⟨Hb, -⟩
    rw [flatMap_encode_w8]
    have hsplit : cv = cv.take 16 ++ cv.drop 16 := (List.take_append_drop _ _).symm
    have ht16 : (cv.take 16).length = 16 := by simp; omega
    have happ := (bytesPointsto_app (GF := GF) cl.ptr (DFrac.own 1) (cv.take 16) (cv.drop 16)).1
    rw [← hsplit, ht16] at happ
    icases happ $$ Hb with ⟨Hh, Hil⟩
    icases (bytesPointsto_typed (V := InBucket) cl.ptr (DFrac.own 1) (cv.take 16) ht16 Hcp).1 $$ Hh
      with Hib
    rw [show (decode (cv.take 16) : InBucket) = inBucketOf cv by
      unfold inBucketOf bytesAt; simp only [List.drop_zero]]
    imod internal.common.bytesPointsto_persist _ _ _ $$ Hil with #Hil
    wp_method_call; wp_call
    wp_auto
    wp_apply hRP _ (inBucketOf cv) (DFrac.own 1) $$ [Hib] as Hib
    · iexact Hib
    icases wtxW_fill_fresh K tx r m X child_ptr _ $$ [Hw FillPercent] with ⟨Hw, FillPercent, %Hfr⟩
    · iframe
    have hrt : child_ptr ≠ tx.[Tx, go!"root"] := Hfr.2
    rw [show (decode (List.take 8 (bytesAt cv 0 16)) : w64) = (inBucketOf cv).root' from rfl]
    have hroot : inBucketRoot cv = (inBucketOf cv).root'.toNat := rfl
    iapply wp_fupd
    by_cases hr0 : (inBucketOf cv).root' = W64 0
    · rw [decide_eq_true hr0]
      have hi : inBucketRoot cv = 0 := by rw [hroot, hr0]; rfl
      have hgt := hinl hi
      wp_auto
      have h16v : 16 < sint.Z cl.len := by
        have h1 := Hcll.1; have h2 := Hcll.2; simp only [sint.nat] at h1; unfold sint.Z at *; omega
      rw [if_pos (show 0 ≤ sint.Z (W64 16) ∧ sint.Z (W64 16) < sint.Z cl.len from
        ⟨by decide, by rw [show sint.Z (W64 16) = 16 from rfl]; omega⟩)]
      rw [sliceIndexRef_byte _ _ Hcp (by decide), show sint.Z (W64 16) = 16 from rfl]
      wp_auto
      ipersist tx
      have hpp : cl.ptr +ₗ (16 : Int) ≠ null := by
        intro h; have := congrArg Loc.addr h; simp [Loc.add, null] at this; omega
      imodintro
      iapply HΦ
      iexists (⟨⟨cl.ptr, tx, bm, cl.ptr +ₗ (16 : Int), null, nm, W64 4602678819172646912⟩,
        inBucketOf cv, ∅, ∅, ∅, inlinePage cv, Src.own DFrac.discard, PageSt.none⟩ : BRec)
      iframe Hw
      isplitl [InBucket tx buckets page rootNode nodes Hib Hbm Hnm]
      · simp only [objOwn, pageOwn]
        rw [if_neg hrt, if_pos trivial, if_neg hpp, if_neg Hnmn']
        iframe; iframe #
        unfold inlinePage bucketHeaderSize
        iexact Hil
      isplitl [FillPercent]
      · iexists _; iframe; ipureintro; decide
      ipureintro
      exact ⟨Hcn, rfl, rfl, rfl, rfl, rfl, rfl, fun _ => ⟨hpp, rfl, Or.inr ⟨rfl, rfl⟩⟩,
        fun h => absurd hi h, Hnmn'⟩
    · rw [decide_eq_false hr0]
      have hi : inBucketRoot cv ≠ 0 := by
        rw [hroot]; intro h; apply hr0; apply BitVec.eq_of_toNat_eq; simpa using h
      wp_auto
      ipersist tx
      imodintro
      iapply HΦ
      iexists (⟨⟨cl.ptr, tx, bm, null, null, nm, W64 4602678819172646912⟩,
        inBucketOf cv, ∅, ∅, ∅, inlinePage cv, Src.own DFrac.discard, PageSt.none⟩ : BRec)
      iframe Hw
      isplitl [InBucket tx buckets page rootNode nodes Hib Hbm Hnm]
      · simp only [objOwn, pageOwn]
        rw [if_neg hrt, if_pos trivial, if_pos trivial, if_neg Hnmn']
        iframe; iframe #
      isplitl [FillPercent]
      · iexists _; iframe; ipureintro; decide
      ipureintro
      exact ⟨Hcn, rfl, rfl, rfl, rfl, rfl, rfl, fun h => absurd h hi, fun _ => ⟨rfl, rfl⟩, Hnmn'⟩

end proof

end bbolt
end EtcdGrove
end Perennial
