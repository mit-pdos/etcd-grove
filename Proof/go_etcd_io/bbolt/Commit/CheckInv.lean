/-
`tx.checkInvariantProperties(r, reachable, freed, HexKVStringer(), ch)` of a reader on a root
`r` of its view's tree (U10e of `notes/bbolt-proof-plan.md`): the walk of `r`'s own pages
(`forEachPage`, `verifyPageReachable` on each) adds their slots to `reachable`; the key-order
check (`recursivelyCheckPageKeyOrder`) reports nothing.
-/
module

public import Proof.go_etcd_io.bbolt.Commit.CheckReach
public import Proof.go_etcd_io.bbolt.Commit.CheckPure
public import Proof.go_etcd_io.bbolt.Inv.RdMeta
public import Proof.go_etcd_io.bbolt.Read.Walk
public import Proof.go_etcd_io.bbolt.Read.Open
public import Spec.go_etcd_io.bbolt.Tx__forEachPage_r
public import Spec.go_etcd_io.bbolt.internal.common.Meta__Pgid

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- **`tx.recursivelyCheckPageKeyOrder(r, keyToString, ch)`** of a reader on a root of its
view's tree: the keys are a B+tree's (`treeKeys`), nothing is reported. -/
abbrev Tx.recursivelyCheckPageKeyOrder_ok.spec : Prop :=
  ∀ (K : BC) (tx : Loc) (src : PairSrc) (q : Qp) (T : TxView) (v : View) (r : w64) (f : val)
    (ch : Loc) (hwm : Nat),
  treeWF v.pages hwm r.toNat → treeKeys v.pages r.toNat none none →
  {{ rdTxK (GF := GF) K tx src q T v }}
    (App (App (App (Val (tx @!! go.GoType.PointerType Tx.ty @!! go!"recursivelyCheckPageKeyOrder"))
      (Val #r)) (Val f)) (Val #ch))
  {{ RET #(); rdTxK K tx src q T v }}

/-- **`tx.checkInvariantProperties(r, reachable, freed, HexKVStringer(), ch)`** of a reader on a
root `r` of its view's tree whose own pages' slots are not yet reachable: they become
reachable; nothing is reported. -/
abbrev Tx.checkInvariantProperties_ok.spec : Prop :=
  ∀ (K : BC) (tx : Loc) (src : PairSrc) (q : Qp) (T : TxView) (v : View) (r : w64)
    (rm fm ch : Loc) (M : GMap w64 Loc),
  ownRootOK v.pages r.toNat →
  (∀ x : w64, (M !! x).isSome = true → ¬ ownSlot v.pages r.toNat x.toNat) →
  {{ rdTxK (GF := GF) K tx src q T v ∗ rm ↦$ M ∗ fm ↦$ (∅ : GMap w64 Bool) }}
    (App (App (App (App (App (Val (tx @!! go.GoType.PointerType Tx.ty @!!
      go!"checkInvariantProperties")) (Val #r)) (Val #rm)) (Val #fm)) (Val #hexKV)) (Val #ch))
  {{ RET #(); rdTxK K tx src q T v ∗ fm ↦$ (∅ : GMap w64 Bool) ∗ ∃ M' : GMap w64 Loc, rm ↦$ M' ∗
      ⌜∀ x : w64, (M' !! x).isSome = true ↔
        ((M !! x).isSome = true ∨ ownSlot v.pages r.toNat x.toNat)⌝ }}

theorem Tx.checkInvariantProperties_ok.wp_proof
    (wp_fep : Tx.forEachPage_r.spec (GF := GF) (hG := hG))
    (wp_vpr : verifyPageReachable_ok.spec (GF := GF) (hG := hG))
    (wp_Pgid : internal.common.Meta.Pgid.spec (GF := GF) (hG := hG))
    (wp_ko : Tx.recursivelyCheckPageKeyOrder_ok.spec (GF := GF) (hG := hG)) :
    Tx.checkInvariantProperties_ok.spec (GF := GF) (hG := hG) := by
  intro K tx src q T v r rm fm ch M hroot hdis
  wp_start as ⟨Hk, Hrm, Hfm⟩
  wp_auto
  ihave #Hpkg := rdTxK_pkgInit K tx src q T v $$ Hk
  ipersist tx
  ipersist reachable
  ipersist freed
  ipersist ch
  have hroot' := hroot
  obtain ⟨C, hok, hCP, hwf, hkeys⟩ := hroot'
  rw [recv_eq_func_mk]
  wp_apply (wp_fep K tx src q T v r _
    (fun i => iprop(fm ↦$ (∅ : GMap w64 Bool) ∗ ∃ M' : GMap w64 Loc, rm ↦$ M' ∗
      ⌜∀ x : w64, (M' !! x).isSome = true ↔
        ((M !! x).isSome = true ∨ walkSlot v.pages r.toNat i x.toNat)⌝))
    ⟨C.hwm, hwf⟩) $$ [Hk Hrm Hfm] as ⟨Hk, Hfm, %M', Hrm, %HM'⟩
  · iframe
    isplitr
    · ipureintro
      intro x
      constructor
      · intro h; exact .inl h
      · rintro (h | ⟨j, hj, -⟩)
        · exact h
        · omega
    iintro !> %i %id %ids %stk %dq
    wp_start as ⟨Hk, ⟨Hfm, %M1, Hrm, %HM1⟩, Hstk, %Hi⟩
    wp_auto
    icases rdTxK_meta_pgid_acc K tx src q T v $$ Hk with ⟨%mp, %mv, Hmf, Hmv, %Hmeta, Hmb⟩
    wp_auto
    wp_apply wp_Pgid mp mv (DFrac.own q) $$ [Hmv] as Hmv
    · iframe
    ihave Hk := Hmb $$ Hmf Hmv
    obtain ⟨pg, hpg, hown, hid, h16, hfl⟩ := walk_entry v.pages r.toNat hroot i id ids Hi
    icases rdTxK_hdr_acc K tx src q T v id pg hpg h16 $$ Hk with ⟨%dqh, Hh, Hhb⟩
    have hidz : (pageHdr pg).id'.toNat = id := hid
    have hovz : (pageHdr pg).overflow'.toNat = pageOverflow pg := rfl
    have hpm := Hmeta.2 id pg hpg
    have hpl := mv.pgid'.isLt
    have hdisj : ∀ x : w64, (M1 !! x).isSome = true → ¬ hdSlot (pageHdr pg) x.toNat := by
      intro x hx hs
      unfold hdSlot at hs
      rw [hidz, hovz] at hs
      rcases (HM1 x).1 hx with h | h
      · exact hdis x h ⟨id, pg, hown, hpg, hs.1, hs.2⟩
      · exact walkSlot_disj v.pages r.toNat hroot i id ids pg Hi hpg _ h hs
    have hflg : (pageHdr pg).flags' = W16 1 ∨ (pageHdr pg).flags' = W16 2 := by
      have hf : pageFlags pg = (pageHdr pg).flags'.toNat := rfl
      rcases hfl with h | h
      · left; apply BitVec.eq_of_toNat_eq; rw [← hf, h]; rfl
      · right; apply BitVec.eq_of_toNat_eq; rw [← hf, h]; rfl
    wp_apply wp_vpr (pageLoc v id) (pageHdr pg) dqh mv.pgid' stk rm fm ch M1 (by omega) (by omega)
      hdisj hflg $$ [Hh Hrm Hfm] as ⟨Hh, Hfm, %M2, Hrm, %HM2⟩
    · iframe
    ihave Hk := Hhb $$ Hh
    try wp_auto
    iapply HΦ
    iframe
    ipureintro
    intro x
    rw [HM2 x, HM1 x]
    unfold hdSlot
    rw [hidz, hovz]
    constructor
    · rintro ((h | ⟨j, hj, h⟩) | h)
      · exact .inl h
      · exact .inr ⟨j, by omega, h⟩
      · exact .inr ⟨i, by omega, id, ids, pg, Hi, hpg, h.1, h.2⟩
    · rintro (h | ⟨j, hj, id', ids', pg', hj', hpg', h1, h2⟩)
      · exact .inl (.inl h)
      · by_cases hji : j = i
        · subst hji
          rw [Hi] at hj'
          simp only [Option.some.injEq, Prod.mk.injEq] at hj'
          obtain ⟨rfl, rfl⟩ := hj'
          rw [hpg] at hpg'; cases hpg'
          exact .inr ⟨h1, h2⟩
        · exact .inl (.inr ⟨j, by omega, id', ids', pg', hj', hpg', h1, h2⟩)
  try wp_auto
  wp_apply wp_ko K tx src q T v r _ ch C.hwm hwf
    (by exact hkeys) $$ [Hk] as Hk
  · iframe
  try wp_auto
  iapply HΦ
  iframe
  ipureintro
  intro x
  rw [HM' x, walkSlot_all v.pages r.toNat hroot]

end spec

end bbolt
end EtcdGrove
end Perennial
