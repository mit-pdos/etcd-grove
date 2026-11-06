/-
The proof of `Spec/go_etcd_io/bbolt/Bucket__Bucket_r.lean` (U6, `notes/bbolt-proof-plan.md`): no
cache (a reader's `buckets` is nil); a cursor, `seek(name)` (the leaf where the name lands,
`rRoute_bkt`), the key compared with `bytes.Equal`, the flags tested, then `openBucket` on the
value; a miss is no nested bucket (`not_bktNames`).
-/
module

public import Spec.go_etcd_io.bbolt.Bucket__Bucket_r
public import Spec.go_etcd_io.bbolt.Bucket__Cursor_i
public import Spec.go_etcd_io.bbolt.Cursor__seek_r
public import Spec.go_etcd_io.bbolt.Bucket__openBucket_r
public import Perennial.Spec.bytes.Equal
public import Proof.go_etcd_io.bbolt.Read.BktOK
public import Proof.go_etcd_io.bbolt.Read.Pub

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

theorem Bucket.Bucket_r.wp_proof
    (hcur : Bucket.Cursor_i.spec (GF := GF) (hG := hG))
    (hseek : Cursor.seek_r.spec (GF := GF) (hG := hG))
    (hopen : Bucket.openBucket_r.spec (GF := GF) (hG := hG))
    (hEq : bytes.Equal.spec (GF := GF) (hG := hG)) :
    Bucket.Bucket_r.spec (GF := GF) (hG := hG) := by
  intro K tx src q T v b dq bv ibp pp name kr nb hbv
  wp_start as ⟨Hk, Hb, Hn⟩
  icases (persistent_entails_left (rdTxK_view K tx src q T v)) $$ Hk with ⟨Hk, %Hvw⟩
  have hok := rBktOK_of v Hvw.2 bv hbv
  ihave #Hpkg := (rdTxK_pkgInit K tx src q T v) $$ Hk
  unfold rBktP
  icases Hb with ⟨HIB, Htx, Hbks, Hpage, Hroot, Hnodes, Hhdr, Hil⟩
  wp_auto
  icases rdTxK_stats_acc K tx src q T v $$ Hk with ⟨%r, #Hcore, #Hreg, Hst, Hkb⟩
  wp_apply hcur K tx r true q b dq $$ [Hst Htx] as %c ⟨%stk, Hc, Hs, Hcap, Hst, Htx⟩
  · iframe; iframe #
  ihave Hk := Hkb $$ Hst
  wp_apply hseek K tx src q T v b dq bv ibp pp c stk [] name kr nb hok.1 hok.2.1
    $$ [Hk HIB Htx Hbks Hpage Hroot Hnodes Hhdr Hil Hc Hs Hcap Hn]
    as %k %vl %fl ⟨%stk', %els', %e, %pid, %pg, Hk, Hb, Hc, Hs, Hcap, Hn, %Hr, Hkv⟩
  · iframe; iframe #; unfold rBktP; iframe
  obtain ⟨hrt, hpa, hfl, hidx⟩ := Hr
  obtain ⟨els2, e2, pid2, pg2, hp2, hpa2, -, -, hwf2, h162, -, hmem, hfound⟩ :=
    rRoute_bkt v Hvw.2 bv hok pp nb _ hrt
  have he2 := (List.append_inj' hp2 rfl).2
  simp only [List.cons.injEq, and_true] at he2
  subst he2
  have hpg := rPageAt_det v bv pp pid2 pid _ pg2 pg hpa2 hpa
  subst hpg
  ihave %Hbase := rdTxK_base_pos K tx src q T v $$ Hk
  have hand : ∀ f : w32, f &&& W32 1 = W32 0 ↔ f.toNat % 2 = 0 := by
    intro f; rw [BitVec.toNat_eq]; simp [BitVec.toNat_and, Nat.and_one_is_mod]
  unfold rKV
  by_cases hic : pageSeekIdx pg2 nb < pageCount pg2
  · rw [if_pos hic]
    icases Hkv with ⟨%ks', %vs', ⟨-, %hks', %hvs', %hfl'⟩, #Hks, #Hvs⟩
    icases rd_keyR_src_acc K tx src q T v name kr nb k ks' (leafKey pg2 (pageSeekIdx pg2 nb))
      hks' $$ [Hk Hn] with ⟨%d1, %d2, Hnm, Hkk, Hback⟩
    · iframe; iframe #
    wp_apply hEq name k d1 d2 nb _ $$ [Hnm Hkk] as ⟨Hnm, Hkk⟩
    · iframe
    icases Hback $$ Hnm Hkk with ⟨Hk, Hn⟩
    by_cases hk : nb = leafKey pg2 (pageSeekIdx pg2 nb)
    · rw [decide_eq_true hk]
      simp only [Bool.not_true]
      wp_auto
      have hfb : leafFlags pg2 (pageSeekIdx pg2 nb) = fl.toNat := by unfold leafFlags; rw [hfl']
      by_cases hb : fl &&& W32 1 = W32 0
      · rw [decide_eq_true hb]
        wp_auto
        iapply HΦ
        unfold rBkt
        iframe
        isplitl
        · unfold rBktP
          iframe
        ileft
        ipureintro
        refine ⟨rfl, not_bktNames v.pages bv pg2 nb hfound hwf2 ?_⟩
        rintro ⟨-, -, h3⟩
        rw [hfb, (hand fl).1 hb] at h3; simp [bucketLeafFlag] at h3
      · rw [decide_eq_false hb]
        have hf : leafFlags pg2 (pageSeekIdx pg2 nb) % 2 = bucketLeafFlag := by
          rw [hfb]; have := (not_congr (hand fl)).1 hb; simp [bucketLeafFlag]; omega
        obtain ⟨hcv16, hcvi⟩ := bktLeaf_bucket_value v Hvw.2 bv hbv pg2 hmem _ hic hf
        wp_auto
        wp_apply hopen K tx src q T v b dq bv ibp pp vl vs' (leafValue pg2 (pageSeekIdx pg2 nb))
          hvs' hcv16 hcvi $$ [Hk Hb]
          as %cb ⟨Hk, Hb, %Hcb, Hcbb⟩
        · iframe; iframe #
        unfold rBktP
        icases Hb with ⟨HIB, Htx, Hbks, Hpage, Hroot, Hnodes, Hhdr, Hil⟩
        wp_auto
        iapply HΦ
        unfold rBkt
        iframe
        iright
        iexists (leafValue pg2 (pageSeekIdx pg2 nb))
        iframe Hcbb
        ipureintro
        exact ⟨Hcb, pg2, _, hmem, hic, hk.symm, hf, rfl⟩
    · rw [decide_eq_false hk]
      simp only [Bool.not_false]
      wp_auto
      iapply HΦ
      unfold rBkt
      iframe
      isplitl
      · unfold rBktP
        iframe
      ileft
      ipureintro
      refine ⟨rfl, not_bktNames v.pages bv pg2 nb hfound hwf2 ?_⟩
      rintro ⟨-, h2, -⟩; exact hk h2.symm
  · rw [if_neg hic]
    icases Hkv with %Hnil
    obtain ⟨rfl, rfl, rfl⟩ := Hnil
    icases rd_keyR_acc K tx src q T v name kr nb $$ [Hk Hn] with ⟨%d1, Hnm, Hback⟩
    · iframe
    wp_apply hEq name slice.nil d1 DFrac.discard nb [] $$ [Hnm] as ⟨Hnm, -⟩
    · iframe; iframe #; iapply ownSlice_nil
    icases Hback $$ Hnm with ⟨Hk, Hn⟩
    by_cases hk : nb = []
    · rw [decide_eq_true hk]
      simp only [Bool.not_true]
      wp_auto
      iapply HΦ
      unfold rBkt
      iframe
      isplitl
      · unfold rBktP
        iframe
      ileft
      ipureintro
      refine ⟨rfl, not_bktNames v.pages bv pg2 nb hfound hwf2 ?_⟩
      rintro ⟨h1, -⟩; exact hic h1
    · rw [decide_eq_false hk]
      simp only [Bool.not_false]
      wp_auto
      iapply HΦ
      unfold rBkt
      iframe
      isplitl
      · unfold rBktP
        iframe
      ileft
      ipureintro
      refine ⟨rfl, not_bktNames v.pages bv pg2 nb hfound hwf2 ?_⟩
      rintro ⟨h1, -⟩; exact hic h1

end proof

end bbolt
end EtcdGrove
end Perennial
