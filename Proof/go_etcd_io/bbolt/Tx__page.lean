/-
The proof of `Spec/go_etcd_io/bbolt/Tx__page.lean` (U4, `notes/bbolt-proof-plan.md`): over
`DB.page` and `Page.FastCheck`.

`Tx.page.wp_proof'` is the spec with the mapping's base at a positive address (`0 < data.addr`)
in place of `data ≠ null`: `db.page`'s `&db.data[i]` is `data + i` only at a positive base
(`arrayIndexRef_plain`), so the frozen premise does not determine the page's address (U4 finding,
`notes/bbolt-proof-plan.md`). `Tx.page.wp_proof` waits for that premise.
-/
module

public import Spec.go_etcd_io.bbolt.Tx__page
public import Spec.go_etcd_io.bbolt.internal.common.Page__FastCheck
public import Proof.go_etcd_io.bbolt.DB__page

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

/-- `FastCheck`'s premises of a page's bytes. -/
theorem pageHdr_fastCheck (pg : List w8) (id : w64) (hid : pageId pg = id.toNat)
    (hfl : pageFlags pg = branchPageFlag ∨ pageFlags pg = leafPageFlag ∨
      pageFlags pg = metaPageFlag ∨ pageFlags pg = freelistPageFlag) :
    (pageHdr pg).id' = id ∧ ((pageHdr pg).flags' = W16 1 ∨ (pageHdr pg).flags' = W16 2 ∨
      (pageHdr pg).flags' = W16 4 ∨ (pageHdr pg).flags' = W16 16) := by
  unfold pageId at hid
  unfold pageFlags branchPageFlag leafPageFlag metaPageFlag freelistPageFlag at hfl
  refine ⟨BitVec.eq_of_toNat_eq hid, ?_⟩
  rcases hfl with h | h | h | h
  · exact Or.inl (BitVec.eq_of_toNat_eq h)
  · exact Or.inr (Or.inl (BitVec.eq_of_toNat_eq h))
  · exact Or.inr (Or.inr (Or.inl (BitVec.eq_of_toNat_eq h)))
  · exact Or.inr (Or.inr (Or.inr (BitVec.eq_of_toNat_eq h)))

/-- `p.FastCheck(id)` on a page's bytes. -/
theorem wp_fastCheck_bytes (hFast : internal.common.Page.FastCheck.spec (GF := GF) (hG := hG))
    (p : Loc) (pg : List w8) (dq : DFrac) (id : w64) (hlen : 16 ≤ pg.length)
    (hid : pageId pg = id.toNat)
    (hfl : pageFlags pg = branchPageFlag ∨ pageFlags pg = leafPageFlag ∨
      pageFlags pg = metaPageFlag ∨ pageFlags pg = freelistPageFlag) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ bytesPointsto p dq pg }}
      (App (Val (p @!! go.GoType.PointerType Page.ty @!! go!"FastCheck")) (Val #id))
    {{ RET #(); bytesPointsto p dq pg }} := by
  iintro %Φ ⟨#Hpkg, Hpg⟩ HΦ
  have hpgne : pg ≠ [] := by intro h; rw [h] at hlen; simp at hlen
  ihave %Hpos := bytesPointsto_pos _ _ _ hpgne $$ Hpg
  icases bytesPointsto_view_read (V := Page) p dq pg 0 p (by simp [loc_add_0]) (by omega) Hpos
    $$ Hpg with ⟨Hhdr, Hclose⟩
  rw [show (decode ((pg.drop 0).take 16) : Page) = pageHdr pg from rfl]
  obtain ⟨h1, h2⟩ := pageHdr_fastCheck pg id hid hfl
  wp_apply hFast p (pageHdr pg) dq id h1 h2 $$ [Hhdr] as Hhdr
  · iframe
  iapply HΦ
  iapply Hclose $$ Hhdr

theorem Tx.page.wp_proof' (hFast : internal.common.Page.FastCheck.spec (GF := GF) (hG := hG))
    (tx db : Loc) (pmv : GoMap) (pm : GMap w64 Loc) (data : Loc) (id : w64) (p : Loc)
    (pg : List w8) (dqt dqm dqd dq : DFrac)
    (hcase : pm !! id = some p ∨
      (pm !! id = none ∧ 0 < data.addr ∧ id.toNat * 4096 < 0xFFFFFFFFFFFF ∧
        p = data +ₗ ((id.toNat * 4096 : Nat) : Int)))
    (hlen : 16 ≤ pg.length) (hid : pageId pg = id.toNat)
    (hfl : pageFlags pg = branchPageFlag ∨ pageFlags pg = leafPageFlag ∨
      pageFlags pg = metaPageFlag ∨ pageFlags pg = freelistPageFlag) :
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗
      tx.[Tx, go!"pages"] ↦{dqt} pmv ∗
      (if pmv = null then iprop(⌜pm = ∅⌝) else iprop(pmv ↦${dqm} pm)) ∗
      tx.[Tx, go!"db"] ↦{dqt} db ∗ db.[DB, go!"data"] ↦{dqd} data ∗
      db.[DB, go!"pageSize"] ↦□ W64 4096 ∗ bytesPointsto p dq pg }}
    (App (Val (tx @!! go.GoType.PointerType Tx.ty @!! go!"page")) (Val #id))
  {{ RET #p; tx.[Tx, go!"pages"] ↦{dqt} pmv ∗
      (if pmv = null then iprop(⌜pm = ∅⌝) else iprop(pmv ↦${dqm} pm)) ∗
      tx.[Tx, go!"db"] ↦{dqt} db ∗ db.[DB, go!"data"] ↦{dqd} data ∗ bytesPointsto p dq pg }} := by
  wp_start as ⟨Hpages, Hpm, Hdb, Hd, #Hps, Hpg⟩
  wp_auto
  by_cases hnil : pmv = null
  · have e : decide (pmv = map.nil) = true := decide_eq_true hnil
    rw [e]
    simp only [hnil, ↓reduceIte]
    icases Hpm with %hpm
    have hc : pm !! id = none ∧ 0 < data.addr ∧ id.toNat * 4096 < 0xFFFFFFFFFFFF ∧
        p = data +ₗ ((id.toNat * 4096 : Nat) : Int) := by
      rcases hcase with h | h
      · rw [hpm] at h; simp at h
      · exact h
    obtain ⟨-, hpos, hlt, rfl⟩ := hc
    try wp_auto
    wp_apply DB.page.wp_proof' db data id dqd hpos hlt $$ [Hd] as Hd
    · iframe; iframe #
    try wp_auto
    wp_apply wp_fastCheck_bytes hFast _ pg dq id hlen hid hfl $$ [Hpg] as Hpg
    · iframe
    try wp_auto
    iapply HΦ; iframe
    ipureintro; exact hpm
  · have e : decide (pmv = map.nil) = false := decide_eq_false hnil
    rw [e]
    simp only [hnil, ↓reduceIte]
    wp_auto
    wp_apply wp_map_lookup2 _ _ pmv pm id dqm $$ Hpm as Hpm
    rcases hcase with hc | ⟨hc, hpos, hlt, rfl⟩
    · rw [hc]
      simp only [Option.isSome_some, decide_true, Option.getD_some]
      wp_auto
      wp_apply wp_fastCheck_bytes hFast _ pg dq id hlen hid hfl $$ [Hpg] as Hpg
      · iframe
      try wp_auto
      iapply HΦ; iframe
    · rw [hc]
      simp only [Option.isSome_none, Bool.false_eq_true, decide_false]
      wp_auto
      wp_apply DB.page.wp_proof' db data id dqd hpos hlt $$ [Hd] as Hd
      · iframe; iframe #
      try wp_auto
      wp_apply wp_fastCheck_bytes hFast _ pg dq id hlen hid hfl $$ [Hpg] as Hpg
      · iframe
      try wp_auto
      iapply HΦ; iframe

theorem Tx.page.wp_proof (hFast : internal.common.Page.FastCheck.spec (GF := GF) (hG := hG)) :
    Tx.page.spec (GF := GF) (hG := hG) := Tx.page.wp_proof' hFast

end proof

end bbolt
end EtcdGrove
end Perennial
