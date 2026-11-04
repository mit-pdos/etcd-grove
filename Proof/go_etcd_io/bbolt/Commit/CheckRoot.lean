/-
`tx.recursivelyCheckBucket(b, reachable, freed, HexKVStringer(), ch)` of a reader (U10e of
`notes/bbolt-proof-plan.md`): on a top-level bucket (`Tx.recursivelyCheckBucket_child`: its own
pages, if stored in pages; it has no nested bucket), and on the root bucket
(`Tx.recursivelyCheckBucket_root`, `Commit/CheckSpec`: the root's own pages, then each top-level
bucket's in `ForEachBucket`'s order, which together cover the view's slots once).
-/
module

public import Proof.go_etcd_io.bbolt.Commit.CheckInv
public import Proof.go_etcd_io.bbolt.Commit.CheckSplit
public import Proof.go_etcd_io.bbolt.Commit.CheckPureRoot
public import Proof.go_etcd_io.bbolt.Read.Root
public import Spec.go_etcd_io.bbolt.Bucket__ForEachBucket_r
public import Spec.go_etcd_io.bbolt.Bucket__Bucket_r

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

/-- **`tx.recursivelyCheckBucket(c, …)` on a top-level bucket** `c` of value `cv` (a reader's):
its own pages' slots (if stored in pages) become reachable; nothing is reported. -/
abbrev Tx.recursivelyCheckBucket_child.spec : Prop :=
  ∀ (K : BC) (tx : Loc) (src : PairSrc) (q : Qp) (T : TxView) (v : View) (c : Loc)
    (kb cv : List w8) (rm fm ch : Loc) (M : GMap w64 Loc),
  viewWF v → bktEntry v.pages (rootVal v) kb cv →
  (inBucketRoot cv ≠ 0 → ∀ x : w64, (M !! x).isSome = true →
    ¬ ownSlot v.pages (inBucketRoot cv) x.toNat) →
  {{ rdTxK (GF := GF) K tx src q T v ∗ rBkt v tx c DFrac.discard cv ∗ rm ↦$ M ∗
      fm ↦$ (∅ : GMap w64 Bool) }}
    (App (App (App (App (App (Val (tx @!! go.GoType.PointerType Tx.ty @!!
      go!"recursivelyCheckBucket")) (Val #c)) (Val #rm)) (Val #fm)) (Val #hexKV)) (Val #ch))
  {{ RET #(); rdTxK K tx src q T v ∗ fm ↦$ (∅ : GMap w64 Bool) ∗ ∃ M' : GMap w64 Loc, rm ↦$ M' ∗
      ⌜∀ x : w64, (M' !! x).isSome = true ↔ ((M !! x).isSome = true ∨
        (inBucketRoot cv ≠ 0 ∧ ownSlot v.pages (inBucketRoot cv) x.toNat))⌝ }}

theorem Tx.recursivelyCheckBucket_child.wp_proof
    (hRP : internal.common.InBucket.RootPage.spec (GF := GF) (hG := hG))
    (wp_cip : Tx.checkInvariantProperties_ok.spec (GF := GF) (hG := hG))
    (wp_feb : Bucket.ForEachBucket_r.spec (GF := GF) (hG := hG)) :
    Tx.recursivelyCheckBucket_child.spec (GF := GF) (hG := hG) := by
  intro K tx src q T v c kb cv rm fm ch M hvw he hdis
  wp_start as ⟨Hk, Hb, Hrm, Hfm⟩
  ihave #Hpkg := rdTxK_pkgInit K tx src q T v $$ Hk
  rw [rBkt_eq]
  icases Hb with ⟨%ibp, %pp, Hb⟩
  have hlen := top_len v hvw kb cv he
  wp_auto
  unfold rBktP
  icases Hb with ⟨HIB, Htx, Hbks, Hpage, Hroot, Hnodes, Hhdr, Hil⟩
  wp_method_call; wp_call
  wp_auto
  wp_apply wp_rd_rootPage hRP K tx src q T v cv ibp hlen $$ [Hk Hhdr] as ⟨Hk, Hhdr⟩
  · iframe
  rw [show (decode (List.take 8 (bytesAt cv 0 16)) : w64) = (inBucketOf cv).root' from rfl]
  by_cases h0 : inBucketRoot cv = 0
  · have hr0 : (inBucketOf cv).root' = W64 0 := by
      apply BitVec.eq_of_toNat_eq; rw [show (inBucketOf cv).root'.toNat = inBucketRoot cv from rfl, h0]
      rfl
    rw [hr0]
    wp_auto
    iapply HΦ
    iframe
    ipureintro
    intro x
    constructor
    · intro h; exact .inl h
    · rintro (h | ⟨h1, -⟩)
      · exact h
      · exact absurd h0 h1
  · have hr0 : (inBucketOf cv).root' ≠ W64 0 := by
      intro e; apply h0; rw [show inBucketRoot cv = (inBucketOf cv).root'.toNat from rfl, e]; rfl
    rw [decide_eq_false hr0]
    wp_auto
    wp_method_call; wp_call
    wp_auto
    wp_apply wp_rd_rootPage hRP K tx src q T v cv ibp hlen $$ [Hk Hhdr] as ⟨Hk, Hhdr⟩
    · iframe
    rw [show (decode (List.take 8 (bytesAt cv 0 16)) : w64) = (inBucketOf cv).root' from rfl]
    wp_apply wp_cip K tx src q T v (inBucketOf cv).root' rm fm ch M
      (top_ownRootOK v hvw kb cv he h0) (hdis h0) $$ [Hk Hrm Hfm] as ⟨Hk, Hfm, %M', Hrm, %HM'⟩
    · iframe
    try wp_auto
    have hnil := top_names_nil v hvw kb cv he
    rw [recv_eq_func_mk]
    wp_apply (wp_feb K tx src q T v c DFrac.discard cv ibp pp _ (fun _ => iprop(emp))
      (.inr (top_entries v hvw kb cv he))) $$ [Hk HIB Htx Hbks Hpage Hroot Hnodes Hhdr Hil]
      as %err ⟨%i, Hk, Hb, -, -⟩
    · unfold rBktP
      iframe
      isplitr
      · iempintro
      iintro !> %i %k %kb' %ks
      wp_start as ⟨-, -, -, -, %Hi⟩
      rw [hnil] at Hi
      simp at Hi
    try wp_auto
    iapply HΦ
    iframe
    ipureintro
    intro x
    rw [HM' x]
    constructor
    · rintro (h | h)
      · exact .inl h
      · exact .inr ⟨h0, h⟩
    · rintro (h | ⟨-, h⟩)
      · exact .inl h
      · exact .inr h

end spec

end bbolt
end EtcdGrove
end Perennial
