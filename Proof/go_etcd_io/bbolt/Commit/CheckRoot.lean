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
public import Proof.go_etcd_io.bbolt.Inv.RdMeta
public import Spec.go_etcd_io.bbolt.Bucket__ForEachBucket_r
public import Spec.go_etcd_io.bbolt.Bucket__Bucket_r

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
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
      (fun _ => iprop(emp))
      (.inr (top_entries v hvw kb cv he))) $$ [Hk HIB Htx Hbks Hpage Hroot Hnodes Hhdr Hil]
      as %err ⟨Hk, Hb, -⟩
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

theorem Tx.recursivelyCheckBucket_root.wp_proof
    (hRP : internal.common.InBucket.RootPage.spec (GF := GF) (hG := hG))
    (wp_cip : Tx.checkInvariantProperties_ok.spec (GF := GF) (hG := hG))
    (wp_feb : Bucket.ForEachBucket_r.spec (GF := GF) (hG := hG))
    (wp_bkt : Bucket.Bucket_r.spec (GF := GF) (hG := hG))
    (wp_child : Tx.recursivelyCheckBucket_child.spec (GF := GF) (hG := hG)) :
    Tx.recursivelyCheckBucket_root.spec (GF := GF) (hG := hG) := by
  intro K tx src q T v rm fm ch
  wp_start as ⟨Hk, Hrm, Hfm⟩
  ihave #Hpkg := rdTxK_pkgInit K tx src q T v $$ Hk
  icases (persistent_entails_left (rdTxK_view K tx src q T v)) $$ Hk with ⟨Hk, %Hvw⟩
  have hvw := Hvw.2
  have hrok := root_ownRootOK v hvw
  obtain ⟨pgr, hpgr⟩ : ∃ pg, v.pages !! v.root = some pg := by
    obtain ⟨C, -, -, ⟨hwm, hwf⟩, -⟩ := hrok
    cases hwf with | page _ pg _ _ hpg _ _ _ => exact ⟨pg, hpg⟩
  icases rdTxK_meta_pgid_acc K tx src q T v $$ Hk with ⟨%mp, %mv, Hmf, Hmv, %Hmeta, Hmb⟩
  have h64 : v.root < 2 ^ 64 := by
    have := Hmeta.2 v.root pgr hpgr; have := mv.pgid'.isLt; omega
  ihave Hk := Hmb $$ Hmf Hmv
  obtain ⟨hrr, hlen⟩ := rootVal_root v h64
  icases rdTxK_root_split K tx src q T v $$ Hk with ⟨%ibp, %pp, Hk, Hb, Hback⟩
  wp_auto
  unfold rBktP
  icases Hb with ⟨HIB, Htx, Hbks, Hpage, Hroot, Hnodes, Hhdr, Hil⟩
  wp_method_call; wp_call
  wp_auto
  wp_apply wp_rd_rootPage hRP K tx src q.half T v (rootVal v) ibp hlen $$ [Hk Hhdr] as ⟨Hk, Hhdr⟩
  · iframe
  rw [show (decode (List.take 8 (bytesAt (rootVal v) 0 16)) : w64) = (inBucketOf (rootVal v)).root'
    from rfl]
  have hr2 : 2 ≤ v.root := by
    obtain ⟨C, -, -, ⟨hwm, hwf⟩, -⟩ := hrok
    cases hwf with | page _ _ h2 _ _ _ _ _ => exact h2
  have hrt : (inBucketOf (rootVal v)).root'.toNat = v.root := hrr
  have hr0 : (inBucketOf (rootVal v)).root' ≠ W64 0 := by
    intro e; rw [e] at hrt; simp at hrt; omega
  rw [decide_eq_false hr0]
  wp_auto
  wp_method_call; wp_call
  wp_auto
  wp_apply wp_rd_rootPage hRP K tx src q.half T v (rootVal v) ibp hlen $$ [Hk Hhdr] as ⟨Hk, Hhdr⟩
  · iframe
  rw [show (decode (List.take 8 (bytesAt (rootVal v) 0 16)) : w64) = (inBucketOf (rootVal v)).root'
    from rfl]
  wp_apply wp_cip K tx src q.half T v (inBucketOf (rootVal v)).root' rm fm ch ∅
    (by rw [hrt]; exact hrok) (fun x hx => by simp at hx) $$ [Hk Hrm Hfm]
    as ⟨Hk, Hfm, %M0, Hrm, %HM0⟩
  · iframe
  try wp_auto
  ipersist tx
  ipersist b
  ipersist reachable
  ipersist freed
  ipersist kvStringer
  ipersist ch
  rw [recv_eq_func_mk]
  wp_apply (wp_feb K tx src q.half T v (txRoot (GF := GF) tx) (DFrac.own q.half) (rootVal v) ibp pp _
    (fun i => iprop(fm ↦$ (∅ : GMap w64 Bool) ∗ ∃ M' : GMap w64 Loc, rm ↦$ M' ∗
      ⌜∀ x : w64, (M' !! x).isSome = true ↔
        (ownSlot v.pages v.root x.toNat ∨ chSlot v i x.toNat)⌝))
    (fun _ => iprop(False)) (.inl rfl))
    $$ [Hk HIB Htx Hbks Hpage Hroot Hnodes Hhdr Hil Hfm Hrm] as %err ⟨Hk, Hb, HIE⟩
  · unfold rBktP
    iframe
    isplitr
    · ipureintro
      intro x
      rw [HM0 x, hrt]
      simp only [GMap.lookup_empty, Option.isSome_none, Bool.false_eq_true, false_or]
      constructor
      · intro h; exact .inl h
      · rintro (h | ⟨j, hj, -⟩)
        · exact h
        · omega
    iintro !> %i %k %kb %ks
    wp_start as ⟨Hk, Hb, ⟨Hfm, %M1, Hrm, %HM1⟩, Hks, %Hc⟩
    ihave Hb : rBktP v tx (txRoot (GF := GF) tx) (DFrac.own q.half) (rootVal v) ibp pp $$ [Hb]
    · unfold rBktP; iexact Hb
    wp_auto
    icases srcOwn_keyR v k ks kb Hc.1 $$ Hks with ⟨%kr, Hkr⟩
    wp_apply wp_bkt K tx src q.half T v (txRoot (GF := GF) tx) (DFrac.own q.half) (rootVal v) ibp pp
      k kr kb (.inl rfl) $$ [Hk Hb Hkr] as %c ⟨Hk, Hb, -, Hres⟩
    · iframe
    icases Hres with (%Hnil | ⟨%cv, %Hce, Hcb⟩)
    · exact absurd (List.mem_of_getElem? Hc.2) Hnil.2
    have he := Hce.2
    rw [decide_eq_false Hce.1]
    wp_auto
    have hdis : inBucketRoot cv ≠ 0 → ∀ x : w64, (M1 !! x).isSome = true →
        ¬ ownSlot v.pages (inBucketRoot cv) x.toNat := by
      intro hf x hx ho
      rcases (HM1 x).1 hx with h | h
      · exact top_disj_root v hvw kb cv he hf _ ho h
      · exact top_disj_prev v hvw i kb cv Hc.2 he hf _ ho h
    wp_apply wp_child K tx src q.half T v c kb cv rm fm ch M1 hvw he hdis $$ [Hk Hcb Hrm Hfm]
      as ⟨Hk, Hfm, %M2, Hrm, %HM2⟩
    · iframe
    try wp_auto
    iapply HΦ
    unfold rBktP
    iframe
    ileft
    isplitr
    · ipureintro; rfl
    iframe
    ipureintro
    intro x
    rw [HM2 x, HM1 x]
    constructor
    · rintro ((h | ⟨j, hj, h⟩) | ⟨hf, h⟩)
      · exact .inl h
      · exact .inr ⟨j, by omega, h⟩
      · exact .inr ⟨i, by omega, kb, cv, Hc.2, he, hf, h⟩
    · rintro (h | ⟨j, hj, kb', cv', hj', he', hf', h⟩)
      · exact .inl (.inl h)
      · by_cases hji : j = i
        · subst hji
          rw [Hc.2] at hj'; cases hj'
          have := top_entry_unique v hvw kb cv cv' he he'
          subst this
          exact .inr ⟨hf', h⟩
        · exact .inl (.inr ⟨j, by omega, kb', cv', hj', he', hf', h⟩)
  icases HIE with (⟨-, Hfm, %M3, Hrm, %HM3⟩ | ⟨-, %Hf⟩)
  rotate_left
  · exact Hf.elim
  try wp_auto
  ihave Hk := Hback $$ Hk [Hb]
  · unfold rBktP; iframe
  iapply HΦ
  iframe
  ipureintro
  intro x
  rw [HM3 x]
  exact root_cover v hvw x.toNat

end spec

end bbolt
end EtcdGrove
end Perennial
