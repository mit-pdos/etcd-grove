/-
The read path's (U6, `notes/bbolt-proof-plan.md`) sources of the slices a reader returns: a
sub-range of a reader bucket's page is, as a byte slice, bytes of the view or persistent heap
bytes (`srcOwn` at a source other than `stale`).
-/
module

public import Proof.go_etcd_io.bbolt.Read.RCtx

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section facts
theorem bytesAt_bytesAt (pg : List w8) (o L off n : Nat) (h : off + n ≤ L) :
    bytesAt (bytesAt pg o L) off n = bytesAt pg (o + off) n := by
  unfold bytesAt
  rw [List.drop_take, List.take_take, List.drop_drop, Nat.min_eq_left (by omega)]

theorem bytesAt_length (pg : List w8) (off n : Nat) (h : off + n ≤ pg.length) :
    (bytesAt pg off n).length = n := by
  unfold bytesAt; simp; omega

variable [GooseExts]

/-- A sub-range of bytes of the view is bytes of the view. -/
theorem inViewLoc_sub (v : View) (p : Loc) (bs : List w8) (h : inViewLoc v p bs) (off n : Nat)
    (hn : off + n ≤ bs.length) :
    inViewLoc v (p +ₗ ((off : Nat) : Int)) (bytesAt bs off n) := by
  obtain ⟨id, pg, o, hpg, hle, hbs, rfl⟩ := h
  have hl := bytesAt_length bs off n hn
  refine ⟨id, pg, o + off, hpg, by rw [hl]; omega, ?_, ?_⟩
  · rw [hl, ← hbs, bytesAt_bytesAt pg o bs.length off n hn]
  · rw [loc_add_assoc]; exact congrArg (fun z => v.base +ₗ z) (by omega)

/-- A sub-range of a page of the view is bytes of the view. -/
theorem inViewLoc_page (v : View) (id : Nat) (pg : List w8) (h : v.pages !! id = some pg)
    (off n : Nat) (hn : off + n ≤ pg.length) :
    inViewLoc v (pageLoc v id +ₗ ((off : Nat) : Int)) (bytesAt pg off n) := by
  have hl := bytesAt_length pg off n hn
  refine ⟨id, pg, off, h, by rw [hl]; omega, by rw [hl], ?_⟩
  unfold pageLoc; rw [loc_add_assoc]; exact congrArg (fun z => v.base +ₗ z) (by omega)

end facts

section src
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

instance srcOwn_persistent (v : View) (s : GoSlice) (src : Src) (bs : List w8) :
    Persistent (srcOwn (GF := GF) v s src bs) := by
  cases src <;> unfold srcOwn <;> infer_instance

/-- **A sub-range of a reader bucket's page, as a byte slice, has a source** (the view's bytes,
or persistent heap bytes of a cloned inline page). -/
theorem rd_src (K : BC) (tx : Loc) (src : PairSrc) (q : Qp) (T : TxView) (v : View)
    (b : Loc) (dqb : DFrac) (bv : List w8) (ibp pp : Loc) (pid : Nat) (l : Loc) (pg : List w8)
    (h : rPageAt v bv pp pid = some (l, pg)) (hne : pg ≠ []) (off n : Nat)
    (hn : off + n ≤ pg.length) (hn32 : n < 2 ^ 32) :
    rdTxK (GF := GF) K tx src q T v ∗ rBktP v tx b dqb bv ibp pp ⊢
      (rdTxK K tx src q T v ∗ rBktP v tx b dqb bv ibp pp) ∗
      ∃ s : Src, ⌜s ≠ Src.stale⌝ ∗
        srcOwn v (slice.mk (l +ₗ ((off : Nat) : Int)) (W64 (n : Int)) (W64 (n : Int))) s
          (bytesAt pg off n) := by
  have hl := bytesAt_length pg off n hn
  iintro H
  icases rd_page_bounds K tx src q T v b dqb bv ibp pp pid l pg h hne $$ H with ⟨H, %Hbd⟩
  unfold rPageAt at h
  by_cases hi : inBucketRoot bv = 0
  · rw [if_pos hi] at h
    by_cases h0 : pid = 0
    · rw [if_pos h0] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      unfold rBktP
      rw [if_pos hi]
      icases H with ⟨Hk, H1, H2, H3, H4, H5, H6, H7, %Hpp, Hlo⟩
      unfold locOwn
      icases Hlo with (%Hv | #Hb)
      · isplitl
        · iframe; isplitr
          · ipureintro; exact Hpp
          ileft; ipureintro; exact Hv
        iexists Src.view
        isplitr
        · ipureintro; intro e; cases e
        unfold srcOwn
        ipureintro
        exact ⟨inViewLoc_sub v pp _ Hv off n hn, by rw [hl]; exact hn32, by rw [hl], by rw [hl]⟩
      · isplitl
        · iframe; isplitr
          · ipureintro; exact Hpp
          iright; iexact Hb
        iexists (Src.own DFrac.discard)
        isplitr
        · ipureintro; intro e; cases e
        unfold srcOwn
        icases Read.bytesPointsto_sub_acc pp DFrac.discard (inlinePage bv) (bytesAt (inlinePage bv) off n)
          off (by rw [hl]; exact hn) (by rw [hl]) $$ Hb with ⟨Hs, -⟩
        have Ho := Read.bytesPointsto_ownSlice (GF := GF) (pp +ₗ ((off : Nat) : Int)) DFrac.discard
          (bytesAt (inlinePage bv) off n) (by simp [Loc.add]; omega) (by rw [hl]; omega)
        rw [hl] at Ho
        iapply Ho.1
        iexact Hs
    · rw [if_neg h0] at h; cases h
  · rw [if_neg hi] at h
    obtain ⟨pg', hpg, he⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    iframe H
    iexists Src.view
    isplitr
    · ipureintro; intro e; cases e
    unfold srcOwn
    ipureintro
    exact ⟨inViewLoc_page v pid pg' hpg off n hn, by rw [hl]; exact hn32, by rw [hl], by rw [hl]⟩

end src

end bbolt
end EtcdGrove
end Perennial
