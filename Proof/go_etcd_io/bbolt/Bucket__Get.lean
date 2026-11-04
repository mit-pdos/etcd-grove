/-
The proof of `Spec/go_etcd_io/bbolt/Bucket__Get.lean` (U6g, `notes/bbolt-proof-plan.md`).
A reader (`wp_reader`): `Bucket.Cursor_i`, `seek_r` on the handle's bucket (`boltBktDef`'s `rBkt`,
at the reader's view by `ViewOfRdAgree`), the flags (a top-level bucket's entries are plain,
`rd_top_plain`), `bytes.Equal`; the key's lookup is the entry at its search index of the only leaf
that can hold it (`rd_get_lookup`). A writer (`wp_writer`): OPEN, at a fraction `q < 1` the writer's
internal read specs (`Cursor.seek_w`, over `wtxW`, the whole writer) do not apply.
-/
module

public import Spec.go_etcd_io.bbolt.Bucket__Get
public import Spec.go_etcd_io.bbolt.Bucket__Cursor_i
public import Spec.go_etcd_io.bbolt.Cursor__seek_r
public import Perennial.Spec.bytes.Equal
public import Proof.go_etcd_io.bbolt.Read.Pub
public import Proof.go_etcd_io.bbolt.Read.GetFacts
import all Spec.go_etcd_io.bbolt.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

theorem Bucket.Get.wp_reader [HasExt osFsExt] (hagree : ViewOfRdAgree (GF := GF))
    (hcur : Bucket.Cursor_i.spec (GF := GF) (hG := hG))
    (hseek : Cursor.seek_r.spec (GF := GF) (hG := hG))
    (hEq : bytes.Equal.spec (GF := GF) (hG := hG))
    (tx : Loc) (γ : BoltName) (q : Qp) (T : TxView) (b : Loc) (n : GoString) (m : BktData)
    (key : GoSlice) (kb : GoString) (dk : DFrac) (hro : T.rw = false) :
  {{ boltTx (GF := GF) tx γ q T ∗ boltBkt tx γ b n (T.gen n) ∗ key ↦*{dk} kb ∗ ⌜T.cur.lookup n = some m⌝ }}
    (App (Val (b @!! go.GoType.PointerType Bucket.ty @!! go!"Get")) (Val #key))
  {{ (v : GoSlice), RET #v; boltTx tx γ q T ∗ key ↦*{dk} kb ∗
      (match m.lookup kb with
       | none => iprop(⌜v = slice.nil⌝)
       | some vb => txBytes tx γ v vb) }} := by
  wp_start as ⟨Ht, #Hb, Hkey, %Hm⟩
  unfold boltTx boltBkt txBytes at *
  ihave Ht := (boltTx_rdTx _ _ tx q T hro).1 $$ Ht
  icases Ht with ⟨%db, Hr, #Hdb⟩
  ihave Hr := (rdTx_rdTxK _ _ tx .loan q T).1 $$ Hr
  icases Hr with ⟨%K, %v, %HK, Hk⟩
  obtain ⟨KB, KN, Kdb, Kp, Ksp, Kt0⟩ := K
  obtain ⟨hKB, hKN⟩ := HK
  simp only at hKB hKN
  subst hKB hKN
  unfold boltBktDef
  icases Hb with ⟨%r', #Hreg', #Hbtx, #Hh, Hrb⟩
  icases (persistent_entails_left (rdTxK_view _ tx .loan q T v)) $$ Hk with ⟨Hk, %Hvw⟩
  ihave #Hpkg := (rdTxK_pkgInit _ tx .loan q T v) $$ Hk
  icases rdTxK_cur_acc _ tx .loan q T v $$ Hk with ⟨%r, #Hcore, #Hreg, #Hvo, %Hro, Hst, Hkb⟩
  iunfold reg at Hreg Hreg'
  icombine Hreg Hreg' gives %hr
  obtain ⟨-, rfl⟩ := hr
  simp only [Hro, Bool.false_eq_true, ite_false]
  icases Hrb with ⟨%v', %bv, #Hvo', #Hrbk, %Hbe⟩
  ihave %Hvv := hagree r v v' Hro $$ [Hvo Hvo']
  · iframe #
  subst Hvv
  obtain ⟨hT, hvwf⟩ := Hvw
  have hm' : v.data !! n = some m := by rw [hT] at Hm; exact Hm
  obtain ⟨hn, hmeq, hS⟩ := rd_bkt_data v hvwf n bv m Hbe hm'
  have hok := rBktOK_of v hvwf bv (Or.inr ⟨n, hn⟩)
  unfold rBkt
  icases Hrbk with ⟨%ibp, %pp, #HIB, #Htx, #Hbks, #Hpage, #Hroot, #Hnodes, #Hhdr, #Hil⟩
  wp_auto
  wp_apply hcur _ tx r true q b DFrac.discard $$ [Hst] as %c ⟨%stk, Hc, Hs, Hcap, Hst, -⟩
  · iframe; iframe #; unfold reg; iframe #
  ihave Hk := Hkb $$ Hst
  try wp_auto
  wp_apply hseek _ tx .loan q T v b DFrac.discard bv ibp pp c stk [] key (KeyR.heap dk) kb hok.1
    hok.2.1 $$ [Hk Hc Hs Hcap Hkey]
    as %k %vl %fl ⟨%stk', %els', %e, %pid, %pg, Hk, -, Hc, Hs, Hcap, Hkey, %Hr, Hkv⟩
  · iframe; iframe #; unfold rBktP keyR; iframe; iframe #
  obtain ⟨hrt, hpa, hfl, hidx⟩ := Hr
  obtain ⟨els2, e2, pid2, pg2, hp2, hpa2, -, -, hwf2, h162, -, hmem, hfound⟩ :=
    rRoute_bkt v hvwf bv hok pp kb _ hrt
  have he2 := (List.append_inj' hp2 rfl).2
  simp only [List.cons.injEq, and_true] at he2
  subst he2
  have hpg := rPageAt_det v bv pp pid2 pid _ pg2 pg hpa2 hpa
  subst hpg
  have hlk := rd_get_lookup v.pages bv hS kb pg2 hmem hfound hwf2
  rw [← hmeq] at hlk
  ihave %Hbase := rdTxK_base_pos _ tx .loan q T v $$ Hk
  have hand : ∀ f : w32, f &&& W32 1 = W32 0 ↔ f.toNat % 2 = 0 := by
    intro f; rw [BitVec.toNat_eq]; simp [BitVec.toNat_and, Nat.and_one_is_mod]
  unfold rKV keyR
  by_cases hic : pageSeekIdx pg2 kb < pageCount pg2
  · rw [if_pos hic]
    icases Hkv with ⟨%ks', %vs', ⟨-, %hks', %hvs', %hfl'⟩, #Hks, #Hvs⟩
    have hfb : leafFlags pg2 (pageSeekIdx pg2 kb) = fl.toNat := by unfold leafFlags; rw [hfl']
    have hplain := rd_top_plain v hvwf n bv hn pg2 hmem _ hic
    have hb : fl &&& W32 1 = W32 0 := (hand fl).2 (by rw [← hfb]; exact hplain)
    rw [decide_eq_true hb]
    wp_auto
    icases rdTxK_cells_acc _ tx .loan q T v $$ Hk with ⟨%qc, Hcl, Hkb⟩
    icases viewCells_src_acc qc v Hbase k ks' (leafKey pg2 (pageSeekIdx pg2 kb)) hks' $$ [Hcl]
      with ⟨%d1, Hkk, Hcb⟩
    · iframe; iframe #
    wp_apply hEq key k dk d1 kb _ $$ [Hkey Hkk] as ⟨Hkey, Hkk⟩
    · iframe
    ihave Hcl := Hcb $$ Hkk
    ihave Hk := Hkb $$ Hcl
    by_cases hk : kb = leafKey pg2 (pageSeekIdx pg2 kb)
    · rw [decide_eq_true hk]
      simp only [Bool.not_true]
      wp_auto
      iapply HΦ
      iframe Hkey
      isplitl [Hk]
      · iapply (boltTx_rdTx _ _ tx q T hro).2
        iexists db; iframe #
        iapply (rdTx_rdTxK _ _ tx .loan q T).2
        iexists _, v; iframe; ipureintro; exact ⟨rfl, rfl⟩
      have hsome : m !! kb = some (leafValue pg2 (pageSeekIdx pg2 kb)) := by
        rw [hlk]; exact if_pos (And.intro hic hk.symm)
      rw [hsome]
      unfold txBytesDef
      cases vs' with
      | stale => exact absurd rfl hvs'
      | own d => unfold srcOwn; ileft; iexact Hvs
      | view =>
        unfold srcOwn
        icases Hvs with %Hin
        iright; iexists r, v; unfold reg; iframe #; ipureintro; exact Hin
    · rw [decide_eq_false hk]
      simp only [Bool.not_false]
      wp_auto
      iapply HΦ
      iframe Hkey
      isplitl [Hk]
      · iapply (boltTx_rdTx _ _ tx q T hro).2
        iexists db; iframe #
        iapply (rdTx_rdTxK _ _ tx .loan q T).2
        iexists _, v; iframe; ipureintro; exact ⟨rfl, rfl⟩
      have hnone : m !! kb = none := by
        rw [hlk]; exact if_neg (show ¬ (_ ∧ _) from fun h => hk h.2.symm)
      rw [hnone]
      ipureintro; rfl
  · rw [if_neg hic]
    icases Hkv with %Hnil
    obtain ⟨rfl, rfl, rfl⟩ := Hnil
    rw [decide_eq_true (show (W32 0 : w32) &&& W32 1 = W32 0 by decide)]
    wp_auto
    wp_apply hEq key slice.nil dk DFrac.discard kb [] $$ [Hkey] as ⟨Hkey, -⟩
    · iframe; iframe #; iapply ownSlice_nil
    have hnone : m !! kb = none := by
      rw [hlk]; exact if_neg (show ¬ (_ ∧ _) from fun h => hic h.1)
    by_cases hk : kb = []
    · rw [decide_eq_true hk]
      simp only [Bool.not_true]
      wp_auto
      iapply HΦ
      iframe Hkey
      isplitl [Hk]
      · iapply (boltTx_rdTx _ _ tx q T hro).2
        iexists db; iframe #
        iapply (rdTx_rdTxK _ _ tx .loan q T).2
        iexists _, v; iframe; ipureintro; exact ⟨rfl, rfl⟩
      rw [show m !! kb = none from hnone]
      ipureintro; rfl
    · rw [decide_eq_false hk]
      simp only [Bool.not_false]
      wp_auto
      iapply HΦ
      iframe Hkey
      isplitl [Hk]
      · iapply (boltTx_rdTx _ _ tx q T hro).2
        iexists db; iframe #
        iapply (rdTx_rdTxK _ _ tx .loan q T).2
        iexists _, v; iframe; ipureintro; exact ⟨rfl, rfl⟩
      rw [show m !! kb = none from hnone]
      ipureintro; rfl

/-- **A writer's `Get`** at any fraction: OPEN. The writer's read specs (`Cursor.seek_w`,
`Cursor.keyValue_w`, `Bucket.pageNode_w`) are over `wtxW`, the whole writer (`boltTxDef_wtxW` at
`q = 1`); at `q < 1` the writer holds `wtxFrac` at `q` (its heap at `q`), and they do not apply. -/
theorem Bucket.Get.wp_writer [HasExt osFsExt]
    (tx : Loc) (γ : BoltName) (q : Qp) (T : TxView) (b : Loc) (n : GoString) (m : BktData)
    (key : GoSlice) (kb : GoString) (dk : DFrac) (hrw : T.rw = true) :
  {{ boltTx (GF := GF) tx γ q T ∗ boltBkt tx γ b n (T.gen n) ∗ key ↦*{dk} kb ∗ ⌜T.cur.lookup n = some m⌝ }}
    (App (Val (b @!! go.GoType.PointerType Bucket.ty @!! go!"Get")) (Val #key))
  {{ (v : GoSlice), RET #v; boltTx tx γ q T ∗ key ↦*{dk} kb ∗
      (match m.lookup kb with
       | none => iprop(⌜v = slice.nil⌝)
       | some vb => txBytes tx γ v vb) }} := by
  sorry

theorem Bucket.Get.wp_proof (hcur : ∀ [HasExt osFsExt], Bucket.Cursor_i.spec (GF := GF) (hG := hG))
    (hseek : ∀ [HasExt osFsExt], Cursor.seek_r.spec (GF := GF) (hG := hG))
    (hEq : bytes.Equal.spec (GF := GF) (hG := hG)) :
    Bucket.Get.spec (GF := GF) (hG := hG) := by
  intro _ tx γ q T b n m key kb dk
  by_cases hrw : T.rw = true
  · exact Bucket.Get.wp_writer tx γ q T b n m key kb dk hrw
  · exact Bucket.Get.wp_reader viewOfRdAgree_holds hcur hseek hEq tx γ q T b n m key kb dk
      (Bool.eq_false_iff.2 hrw)

end proof

end bbolt
end EtcdGrove
end Perennial
