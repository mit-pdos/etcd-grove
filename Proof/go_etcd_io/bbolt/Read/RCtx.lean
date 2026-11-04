/-
The reader's read path context (U6, `notes/bbolt-proof-plan.md`): a reader bucket with its
header and inline page locations exposed (`rBktP`, of which `rBkt` is the existential), the page a
bucket position names (`rPageAt`), and the bytes of such a page read out of the reader's
resources (`rd_page_acc`).
-/
module

public import Proof.go_etcd_io.bbolt.Read.Base
public import Proof.go_etcd_io.bbolt.Read.Bytes

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section rctx
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- A reader's bucket with its header at `ibp` and its inline page at `pp` (`rBkt`'s body). -/
def rBktP (v : View) (tx b : Loc) (dq : DFrac) (bv : List w8) (ibp pp : Loc) : IProp GF :=
  iprop(b.[Bucket, go!"InBucket"] ↦{dq} ibp ∗ b.[Bucket, go!"tx"] ↦{dq} tx ∗
    b.[Bucket, go!"buckets"] ↦{dq} null ∗ b.[Bucket, go!"page"] ↦{dq} pp ∗
    b.[Bucket, go!"rootNode"] ↦{dq} null ∗ b.[Bucket, go!"nodes"] ↦{dq} null ∗
    ((∃ ib : InBucket, ibp ↦□ ib ∗ ⌜ib.root' = (inBucketOf bv).root'⌝) ∨
      ⌜inViewLoc v ibp (bytesAt bv 0 16)⌝) ∗
    (if inBucketRoot bv = 0 then iprop(⌜pp ≠ null⌝ ∗ locOwn v pp (inlinePage bv))
     else iprop(⌜pp = null⌝)))

theorem rBkt_eq (v : View) (tx b : Loc) (dq : DFrac) (bv : List w8) :
    rBkt (GF := GF) v tx b dq bv = iprop(∃ ibp pp, rBktP v tx b dq bv ibp pp) := rfl

/-- The page at position `pid` of the reader bucket whose value is `bv` (its inline page at `pp`):
where it is, its bytes. -/
def rPageAt (v : View) (bv : List w8) (pp : Loc) (pid : Nat) : Option (Loc × List w8) :=
  if inBucketRoot bv = 0 then (if pid = 0 then some (pp, inlinePage bv) else none)
  else (v.pages !! pid).map fun pg => (pageLoc v pid, pg)

/-- **A page of the reader's view, read** out of `rdTxK`, and back. -/
theorem rdTxK_page_acc (K : BC) (tx : Loc) (src : PairSrc) (q : Qp) (T : TxView) (v : View)
    (id : Nat) (pg : List w8) (h : v.pages !! id = some pg) :
    rdTxK (GF := GF) K tx src q T v ⊢ ∃ dq, bytesPointsto (pageLoc v id) dq pg ∗
      (bytesPointsto (pageLoc v id) dq pg -∗ rdTxK K tx src q T v) := by
  unfold rdTxK rtxFrac
  iintro ⟨%r, %c, %mv, %k, %Hc, #Hreg, #Hpk, #Hcore, Hv, Hex,
    ⟨%t, Hw, Hm, Hmeta, Hroot, Hfill, Hpages, Hch, Hwf, Hdb, Hmv, Hcells, Hmap, #Hvo, %Hf⟩, Hpool⟩
  icases viewCells_page_acc _ v id pg h $$ Hcells with ⟨Hpg, Hcells⟩
  iexists _
  iframe Hpg
  iintro Hpg
  iexists r, c, mv, k
  iframe; iframe #
  isplitr
  · ipureintro; exact Hc
  isplitl [Hcells Hpg]
  · iapply Hcells; iexact Hpg
  ipureintro; exact Hf

/-- **Bytes of the reader's view at a location, read** out of `rdTxK`, and back. -/
theorem rdTxK_loc_acc (K : BC) (tx : Loc) (src : PairSrc) (q : Qp) (T : TxView) (v : View)
    (l : Loc) (bs : List w8) (h : inViewLoc v l bs) :
    rdTxK (GF := GF) K tx src q T v ⊢ ∃ dq, bytesPointsto l dq bs ∗
      (bytesPointsto l dq bs -∗ rdTxK K tx src q T v) := by
  unfold rdTxK rtxFrac
  iintro ⟨%r, %c, %mv, %k, %Hc, #Hreg, #Hpk, #Hcore, Hv, Hex,
    ⟨%t, Hw, Hm, Hmeta, Hroot, Hfill, Hpages, Hch, Hwf, Hdb, Hmv, Hcells, Hmap, #Hvo, %Hf⟩, Hpool⟩
  icases viewCells_loc_acc _ v l bs h $$ Hcells with ⟨%dq, Hpg, Hcells⟩
  iexists dq
  iframe Hpg
  iintro Hpg
  iexists r, c, mv, k
  iframe; iframe #
  isplitr
  · ipureintro; exact Hc
  isplitl [Hcells Hpg]
  · iapply Hcells; iexact Hpg
  ipureintro; exact Hf

/-- **A page of a reader bucket, read** (a page of the view, or its inline page: bytes of the
view or persistent heap bytes), and back. -/
theorem rd_page_acc (K : BC) (tx : Loc) (src : PairSrc) (q : Qp) (T : TxView) (v : View)
    (b : Loc) (dqb : DFrac) (bv : List w8) (ibp pp : Loc) (pid : Nat) (l : Loc) (pg : List w8)
    (h : rPageAt v bv pp pid = some (l, pg)) :
    rdTxK (GF := GF) K tx src q T v ∗ rBktP v tx b dqb bv ibp pp ⊢ ∃ dq,
      bytesPointsto l dq pg ∗
      (bytesPointsto l dq pg -∗ rdTxK K tx src q T v ∗ rBktP v tx b dqb bv ibp pp) := by
  unfold rPageAt at h
  by_cases hi : inBucketRoot bv = 0
  · rw [if_pos hi] at h
    by_cases h0 : pid = 0
    · rw [if_pos h0] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      unfold rBktP
      rw [if_pos hi]
      iintro ⟨Hk, H1, H2, H3, H4, H5, H6, H7, %Hpp, Hlo⟩
      unfold locOwn
      icases Hlo with (%Hv | #Hb)
      · icases rdTxK_loc_acc K tx src q T v pp _ Hv $$ Hk with ⟨%dq, Hb, Hk⟩
        iexists dq
        iframe Hb
        iintro Hb
        ihave Hk := Hk $$ Hb
        iframe
        isplitr
        · ipureintro; exact Hpp
        ileft; ipureintro; exact Hv
      · iexists DFrac.discard
        iframe Hb
        iintro -
        iframe
        ipureintro; exact Hpp
    · rw [if_neg h0] at h; cases h
  · rw [if_neg hi] at h
    obtain ⟨pg', hpg, he⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    iintro ⟨Hk, Hb⟩
    icases rdTxK_page_acc K tx src q T v pid pg' hpg $$ Hk with ⟨%dq, Hp, Hk⟩
    iexists dq
    iframe Hp
    iintro Hp
    ihave Hk := Hk $$ Hp
    iframe

end rctx

end bbolt
end EtcdGrove
end Perennial
