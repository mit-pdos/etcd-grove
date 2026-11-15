/-
The proof of `Spec/go_etcd_io/bbolt/Bucket__openBucket_r.lean` (U6, `notes/bbolt-proof-plan.md`):
`newBucket` (a reader: no caches), the alignment test (`uintptr` of a pointer is an arbitrary
word: both branches; a misaligned value is cloned, its copy persistent), the header pointing
into the value, the inline page after it; the new bucket's fields made persistent.
-/
module

public import Spec.go_etcd_io.bbolt.Bucket__openBucket_r
public import Spec.go_etcd_io.bbolt.cloneBytes
public import Proof.go_etcd_io.bbolt.Read.Root

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

theorem Bucket.openBucket_r.wp_proof (hcl : cloneBytes.spec (GF := GF) (hG := hG))
    (hRP : internal.common.InBucket.RootPage.spec (GF := GF) (hG := hG)) :
    Bucket.openBucket_r.spec (GF := GF) (hG := hG) := by
  intro K tx src q T v b dq bv ibp pp value vsr cv hvs h16 hinl
  wp_start as ⟨Hk, Hb, #Hv⟩
  ihave %Hbase := rdTxK_base_pos K tx src q T v $$ Hk
  unfold rBktP
  icases Hb with ⟨HIB, Htx, Hbks, Hpage, Hroot, Hnodes, Hhdr, Hil⟩
  icases rdTxK_writable_acc K tx src q T v $$ Hk with ⟨%dw, Hw, Hwb⟩
  icases src_openParts v Hbase value vsr cv hvs h16 $$ Hv with ⟨#Hop, %Hvp⟩
  wp_auto
  ihave %Hvl := srcOwn_len_r v value vsr cv hvs $$ Hv
  wp_func_call; wp_call
  wp_auto
  have hvlen : 16 ≤ sint.Z value.len := by
    have h1 := Hvl.1; have h2 := Hvl.2; simp only [sint.nat] at h1; unfold sint.Z at *; omega
  rw [if_pos (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z value.len from
    ⟨by decide, by rw [show sint.Z (W64 0) = 0 from rfl]; omega⟩)]
  unfold sliceIndexRef
  rw [show sint.Z (W64 0) = 0 by rfl, go.arrayIndexRef_0]
  wp_auto
  wp_apply wp_ArbitraryInt as %x -
  ihave Hk := Hwb $$ Hw
  -- after the alignment test: the value (cloned when misaligned), its parts and its length
  by_cases hal : x &&& W64 7 = W64 0
  case' pos =>
    rw [decide_eq_true hal]
    wp_auto
  case' neg =>
    rw [decide_eq_false hal]
    wp_auto
    icases rdTxK_cells_acc K tx src q T v $$ Hk with ⟨%qc, Hc, Hkb⟩
    icases viewCells_src_acc qc v Hbase value vsr cv hvs $$ [Hc] with ⟨%dvq, Hvs, Hcb⟩
    · iframe; iframe #
    wp_apply hcl value cv dvq $$ [Hvs] as %cl ⟨Hcl, -, Hvs⟩
    · iframe
    ihave Hc := Hcb $$ Hvs
    ihave Hk := Hkb $$ Hc
    ipersist Hcl
    try wp_auto
    ihave %Hcll := ownSlice_len _ _ _ $$ Hcl
    icases src_openParts v Hbase cl (Src.own DFrac.discard) cv (by intro h; cases h) h16 $$ [Hcl]
      with ⟨#Hop, %Hvp⟩
    · unfold srcOwn; iexact Hcl
    clear hvlen Hvl
    have hvlen : 16 ≤ sint.Z cl.len := by
      have h1 := Hcll.1; have h2 := Hcll.2; simp only [sint.nat] at h1; unfold sint.Z at *; omega
    have Hvl : cv.length = sint.nat cl.len ∧ 0 ≤ sint.Z cl.len := Hcll
    generalize cl = value at *
  all_goals
    icases rdTxK_writable_acc K tx src q T v $$ Hk with ⟨%dw, Hw, Hwb⟩
    wp_auto
    rw [if_pos (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z value.len from
      ⟨by decide, by rw [show sint.Z (W64 0) = 0 from rfl]; omega⟩)]
    unfold sliceIndexRef
    rw [show sint.Z (W64 0) = 0 by rfl, go.arrayIndexRef_0]
    wp_auto
    ihave Hk := Hwb $$ Hw
    unfold openParts
    icases Hop with ⟨#Hh, #Hl⟩
    wp_method_call; wp_call
    wp_auto
    wp_apply wp_rd_rootPage hRP K tx src q T v cv value.ptr h16 $$ [Hk] as ⟨Hk, -⟩
    · iframe; iframe #
    rw [show (decode (List.take 8 (bytesAt cv 0 16)) : w64) = (inBucketOf cv).root' from rfl]
    have hroot : inBucketRoot cv = (inBucketOf cv).root'.toNat := rfl
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
      iapply wp_fupd
      wp_auto
      icases (persistent_entails_left (typedPointsto_not_null _ _ _)) $$ child with ⟨child, %Hcn⟩
      iStructNamed child
      ipersist InBucket; ipersist tx; ipersist buckets; ipersist page; ipersist rootNode
      ipersist nodes
      imodintro
      iapply HΦ
      iframe
      isplitr
      · ipureintro; exact Hcn
      unfold rBkt
      iexists value.ptr, (value.ptr +ₗ 16)
      iframe; iframe #
      rw [if_pos hi]
      iframe #
      ipureintro
      intro h; have := congrArg Loc.addr h; simp [Loc.add, null] at this; omega
    · rw [decide_eq_false hr0]
      have hi : inBucketRoot cv ≠ 0 := by
        rw [hroot]; intro h; apply hr0; apply BitVec.eq_of_toNat_eq; simpa using h
      iapply wp_fupd
      wp_auto
      icases (persistent_entails_left (typedPointsto_not_null _ _ _)) $$ child with ⟨child, %Hcn⟩
      iStructNamed child
      ipersist InBucket; ipersist tx; ipersist buckets; ipersist page; ipersist rootNode
      ipersist nodes
      imodintro
      iapply HΦ
      iframe
      isplitr
      · ipureintro; exact Hcn
      unfold rBkt
      iexists value.ptr, null
      iframe; iframe #
      rw [if_neg hi]
      ipureintro; rfl
end proof

end bbolt
end EtcdGrove
end Perennial
