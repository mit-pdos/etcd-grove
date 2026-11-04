/-
The proof of `Spec/go_etcd_io/bbolt/Bucket__Bucket_w.lean` (U6e, `notes/bbolt-proof-plan.md`): the
bucket cache looked up (a hit returns the cached child); a cursor, `seek(name)` (`seek_w`), the
key compared with `bytes.Equal`, the flags tested (a miss: no nested bucket of that name,
`route_found_at`); then `openBucket_w` on the value and the child cached and registered
(`wtxW_bktOpen`).
The transaction is writable (`openBucket` reads `tx.writable`; batch 37's premise, from
`txClean`'s first clause), and the cached children are non-nil (a nil entry of `b.buckets` is a
miss for the code, which then opens over it; batch 37: `bktClean`'s last clause, through
`bktLocalOK`).
-/
module

public import Spec.go_etcd_io.bbolt.Bucket__Bucket_w
public import Spec.go_etcd_io.bbolt.Bucket__Cursor_i
public import Spec.go_etcd_io.bbolt.Cursor__seek_w
public import Spec.go_etcd_io.bbolt.Bucket__openBucket_w
public import Perennial.Spec.bytes.Equal
public import Proof.go_etcd_io.bbolt.Read.WOpenH
public import Proof.go_etcd_io.bbolt.Read.WOpenWOK

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

omit hos in
theorem ownMap_nonnull_s (l : Loc) (dq : DFrac) (m : GMap GoString Loc) :
    (l ↦${dq} m : IProp GF) ⊢ ⌜l ≠ null⌝ := by
  rw [ownMap_unseal]
  iintro H
  iNamed H
  ihave %Hp := heapPointsto_pos _ _ _ $$ Hown
  ipureintro
  intro h; subst h; simp [null] at Hp

theorem Bucket.Bucket_w.wp_proof
    (hcur : Bucket.Cursor_i.spec (GF := GF) (hG := hG))
    (hseek : Cursor.seek_w.spec (GF := GF) (hG := hG))
    (hopen : Bucket.openBucket_w.spec (GF := GF) (hG := hG))
    (hEq : bytes.Equal.spec (GF := GF) (hG := hG)) :
    Bucket.Bucket_w.spec (GF := GF) (hG := hG) := by
  intro K tx r m X bl B name nb ks g hB hloc hks hpm hwr
  have hbmn : ∀ c, B.bm !! nb = some c → c ≠ null := by
    obtain ⟨-, B', hB', hc, -⟩ := hloc
    rw [hB] at hB'; cases hB'
    exact fun c h => hc.2.2.2.2.2.2.2.2.2.2 nb c h
  wp_start as ⟨Hw, #Hn⟩
  icases wtxW_pkgInit K tx r m X $$ Hw with ⟨Hw, #Hpkg⟩
  icases wtxW_buckets_fld K tx r m X bl B hB $$ Hw with ⟨Hbf, Hwb⟩
  wp_auto
  ihave Hw := Hwb $$ Hbf
  icases wtxW_bm_acc K tx r m X bl B hB _ _ rfl rfl $$ Hw with ⟨Hbm, Hwb⟩
  ihave %Hbmn := ownMap_nonnull_s _ _ _ $$ Hbm
  ihave Hw := Hwb $$ Hbm
  rw [show (map.nil : Loc) = null from rfl, decide_eq_false Hbmn]
  wp_auto
  icases wtxW_cells_acc K tx r m X $$ Hw with ⟨%Hbase, Hc, Hwb⟩
  icases viewCells_src_acc wq X.v Hbase name ks nb hks $$ [Hc] with ⟨%dn, Hnb, Hcb⟩
  · iframe; iframe #
  wp_apply wp_bytes_to_string $$ [Hnb] as Hnb
  · iexact Hnb
  ihave Hc := Hcb $$ Hnb
  ihave Hw := Hwb $$ Hc
  icases wtxW_bkt_acc K tx r m X bl B hB $$ Hw with ⟨Ho, Hwb⟩
  isimp only [objOwn] at Ho
  icases Ho with ⟨H1, H2, H3, H4, H5, H6, H7, H8, H9, H10⟩
  wp_auto
  wp_apply wp_map_lookup1 $$ [H9] as H9
  · iexact H9
  ihave Hw := Hwb $$ [H1 H2 H3 H4 H5 H6 H7 H8 H9 H10]
  · isimp only [objOwn]; iframe
  try wp_auto
  cases hbmc : B.bm !! nb with
  | some c =>
    have hcn := hbmn c hbmc
    simp only [Option.getD_some]
    rw [decide_eq_false hcn]
    wp_auto
    iapply HΦ
    iexists X
    iframe
    ipureintro
    exact Or.inr ⟨hcn, Or.inl ⟨rfl, rfl⟩, fun h => ⟨h, rfl⟩⟩
  | none =>
    simp only [Option.getD_none]
    rw [decide_eq_true (show (zero_val Loc : Loc) = null from rfl)]
    wp_auto
    icases wtxW_cursor_acc K tx r m X bl B hB $$ Hw with ⟨#Hcore, #Hreg, Hst, %dt, Htx, Hwb⟩
    wp_apply hcur K tx r m 1 bl dt $$ [Hst Htx] as %c ⟨%stk, Hc, Hs, Hcap, Hst, Htx⟩
    · iframe; iframe #
    ihave Hw := Hwb $$ Hst Htx
    try wp_auto
    wp_apply hseek K tx r m X bl c stk [] name nb ks hloc hks hpm $$ [Hw Hc Hs Hcap]
      as %k %vl %fl ⟨%stk', %els, %pids, Hw, Hc, Hs, Hcap, %Hrt, Hkv⟩
    · iframe; iframe #
    obtain ⟨Hp, Hr⟩ := Hrt
    obtain ⟨p, ws, ⟨j, hpj⟩, hL, hle⟩ := WOpen.lPath_leaf X bl B hB hloc els pids Hp
    have hI := WOpen.lPath_posI X bl B hB hloc els pids Hp j p hpj
    have hfa := WOpen.route_found_at X bl els pids nb hloc Hp Hr
    rw [hle] at hfa
    rw [hle]
    cases hw : ws[wsIdx ws nb]? with
    | none =>
      icases Hkv with %Hnil
      obtain ⟨rfl, rfl, rfl⟩ := Hnil
      icases wtxW_cells_acc K tx r m X $$ Hw with ⟨%Hbase, Hc, Hwb⟩
      icases viewCells_src_acc wq X.v Hbase name ks nb hks $$ [Hc] with ⟨%d1, Hnm, Hcb⟩
      · iframe; iframe #
      wp_apply hEq name slice.nil d1 DFrac.discard nb [] $$ [Hnm] as ⟨Hnm, -⟩
      · iframe; iframe #; iapply ownSlice_nil
      ihave Hc := Hcb $$ Hnm
      ihave Hw := Hwb $$ Hc
      have hnone : ¬ ∃ w ∈ X.allEnts bl, w.key = nb ∧ isBktFlag w.flags := by
        rintro ⟨w', hw', hk', -⟩; rw [hfa w' hw' hk'] at hw; cases hw
      by_cases hk : nb = []
      · rw [decide_eq_true hk]
        simp only [Bool.not_true]
        wp_auto
        iapply HΦ
        iexists X; iframe
        ipureintro; exact Or.inl ⟨rfl, rfl, hnone⟩
      · rw [decide_eq_false hk]
        simp only [Bool.not_false]
        wp_auto
        iapply HΦ
        iexists X; iframe
        ipureintro; exact Or.inl ⟨rfl, rfl, hnone⟩
    | some w =>
      icases Hkv with ⟨%Hkw, #Hks, #Hvs⟩
      have hwm : w ∈ ws := List.mem_of_getElem? hw
      obtain ⟨hlk, hlv⟩ := WOpen.leaf_live X bl B hB hloc p hI ws hL w hwm
      icases wtxW_src2_acc K tx r m X name k ks _ nb w.key hks
        (WOpen.leafSrc_live X bl B hB hloc _ hlk) $$ [Hw] with ⟨%d1, %d2, Hnm, Hkk, Hback⟩
      · iframe; iframe #
      wp_apply hEq name k d1 d2 nb w.key $$ [Hnm Hkk] as ⟨Hnm, Hkk⟩
      · iframe
      ihave Hw := Hback $$ Hnm Hkk
      have hand : ∀ f : w32, f &&& W32 1 = W32 0 ↔ ¬ isBktFlag f := by
        intro f; unfold isBktFlag; simp
      by_cases hk : nb = w.key
      · rw [decide_eq_true hk]
        simp only [Bool.not_true]
        wp_auto
        by_cases hbf : fl &&& W32 1 = W32 0
        · rw [decide_eq_true hbf]
          wp_auto
          iapply HΦ
          iexists X; iframe
          ipureintro
          refine Or.inl ⟨rfl, rfl, ?_⟩
          rintro ⟨w', hw', hk', hf'⟩
          have := hfa w' hw' hk'
          rw [hw] at this; cases this
          exact (hand _).1 (Hkw.2 ▸ hbf) hf'
        · rw [decide_eq_false hbf]
          have hflag : isBktFlag w.flags := by
            rw [← Hkw.2]; intro h; exact hbf h
          have hbmw : B.bm !! w.key = none := hk ▸ hbmc
          obtain ⟨hbv, hvs', hent, htk, hninl⟩ :=
            WOpen.leafBkt X bl B hB hloc p hI ws hL w hwm hflag hbmw
          have hsrc : leafSrc X bl w.vs = w.vs := by
            unfold leafSrc; rw [hB]; simp only; rw [if_neg hninl]
          rw [hsrc]
          have h16 : 16 ≤ w.value.length := by cases hbv.1 <;> assumption
          have hinl : inBucketRoot w.value = 0 → 16 < w.value.length := by
            intro h0
            have h1 := (hbv.2.1 h0).1.2.2.2.1
            have h2 : (inlinePage w.value).length = w.value.length - 16 := by
              unfold inlinePage bucketHeaderSize; simp
            omega
          icases wtxW_cells_acc K tx r m X $$ Hw with ⟨%Hbase, Hc0, Hwb⟩
          ihave Hw := Hwb $$ Hc0
          icases wtxW_heapOK' K tx r m X $$ Hw with ⟨Hw, %Hok⟩
          have htxB : B.bv.tx' = tx := Hok.2.2.1 bl B hB
          wp_auto
          wp_apply hopen K tx r m X bl B vl w.vs w.value hB hwr hlv h16 hinl $$ [Hw]
            as %c ⟨%C, Hw, Hco, Hfill, %Hcr⟩
          · iframe; iframe #
          obtain ⟨hcn, hrec⟩ := Hcr
          icases Hfill with ⟨%f, %Hnan, Hfp⟩
          icases wtxW_fill_fresh K tx r m X c f $$ [Hw Hfp] with ⟨Hw, Hfp, %Hfr⟩
          · iframe
          isimp only [objOwn] at Hco
          icases Hco with ⟨C1, C2, C3, C4, C5, C6, C7, C8, C9, C10⟩
          icases wtxW_bkt_fresh K tx r m X c _ $$ [Hw C1] with ⟨Hw, C1, %Hbo⟩
          · iframe
          ihave Hco : objOwn X.v c (DFrac.own 1) true (.bkt C) $$ [C1 C2 C3 C4 C5 C6 C7 C8 C9 C10]
          · isimp only [objOwn]; iframe
          icases wtxW_bktOpen K tx r m X bl B hB hloc.1 $$ Hw with ⟨Hbf, Hbm, Hcells, Hback⟩
          wp_auto
          rw [show (map.nil : Loc) = null from rfl, decide_eq_false Hbmn]
          wp_auto
          icases viewCells_src_acc wq X.v Hbase name ks nb hks $$ [Hcells] with ⟨%d3, Hnm, Hcb⟩
          · iframe; iframe #
          wp_apply wp_bytes_to_string $$ [Hnm] as Hnm
          · iexact Hnm
          ihave Hcells := Hcb $$ Hnm
          wp_apply wp_mapInsert $$ [Hbm] as Hbm
          · iexact Hbm
          imod Hback $$ %nb %c %C %g Hbf Hcells Hbm Hco [Hfp] [] with Hw
          · iexists f; iframe; ipureintro; exact Hnan
          · ipureintro; exact ⟨Hbo, Hfr.1, hrec.2.1, hrec.2.2.2.2.2.1⟩
          wp_auto
          iapply HΦ
          iexists _
          iframe Hw
          ipureintro
          have hwa : w ∈ X.allEnts bl := by
            obtain ⟨w', hw', hk'⟩ := (lRoutes_found' X bl els pids nb hloc Hp Hr).2 (by
              unfold wsFound; rw [hle, hw]; simp [hk])
            have := hfa w' hw' hk'
            rw [hw] at this; cases this; exact hw'
          have hrec' : openedRec B.bv.tx' w.value w.vs C := by rw [htxB]; exact hrec
          obtain ⟨hib, htx, hrn, hnm, hbm', hns, hil, hni⟩ := hrec
          refine Or.inr ⟨hcn, Or.inr ⟨B, C, w, hB, hwa, hk.symm, hflag, hbmc, hcn,
            by rw [Hbo]; rfl, hib, by rw [htx, htxB], hrn, hnm, hbm', hns, ?_, hni, rfl⟩, ?_⟩
          · intro h0
            obtain ⟨h1, h2, h3⟩ := hil h0
            refine ⟨h1, h2, ?_⟩
            rcases h3 with ⟨-, a, b⟩ | ⟨a, b⟩
            · exact Or.inl ⟨by rcases hvs' with e | e <;> simp_all, a, b⟩
            · exact Or.inr ⟨a, b⟩
          · intro hok
            have hplain : ∀ pg, bktLeafPg X.v.pages w.value pg → ∀ j < pageCount pg,
                leafFlags pg j % 2 = 0 := by
              intro pg hpg j hj
              by_cases h0 : inBucketRoot w.value = 0
              · rcases hpg with ⟨-, rfl⟩ | ⟨h0', -⟩
                · exact ((hbv.2.1 h0).1.2.2.2.2 j hj).2
                · exact absurd h0 h0'
              · exact (hbv.2.2 h0 pg hpg j hj).1
            exact WOpen.wOK_bktOpened X bl c B C w nb g hok Hok.2.1 hB hwa hk.symm hflag hbmc Hbo
              hrec' hbv (hk ▸ hent) htk hplain hcn
      · rw [decide_eq_false hk]
        simp only [Bool.not_false]
        wp_auto
        iapply HΦ
        iexists X; iframe
        ipureintro
        refine Or.inl ⟨rfl, rfl, ?_⟩
        rintro ⟨w', hw', hk', -⟩
        have := hfa w' hw' hk'
        rw [hw] at this; cases this
        exact hk hk'.symm

end proof

end bbolt
end EtcdGrove
end Perennial
