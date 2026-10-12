/-
What `Commit`'s rebalance hands its spill (`txBalanced`, the stash of freed pages' tokens
`freedToks`), and what the spill writes (`wtree`, `wbkt`: a written tree's tokens and facts).

**Freed pages.** A page `Commit` frees (`node.free`, `Bucket.free`: `freelist.Free(txid, p)`, its
ids pending for the writer's transaction) gives its token to the stash `freedToks γ F` (`F`: the
freed pages, id ↦ bytes), so that the written tree, holding the tokens of all its pages, shares
none with them (`freedIn`: every slot of a freed page is pending for `txid`).

**Written trees.** `wtree γ P hwm x lo hi`: in the pages `P` (the view's pages and the dirty
pages), the tree under `x` is well-formed and strict, its keys within `[lo, hi)`, its pages'
slots disjoint, and the transaction holds the token of each of its pages. `wbkt γ P hwm v`: a
nested bucket's value: its tree's `wtree`, or a good inline page.
-/
module

public import Proof.go_etcd_io.bbolt.WriteTxShape
public import Proof.go_etcd_io.bbolt.internal.freelist.Iface

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pure
variable [ext : FfiSyntax]

/-- No node of the transaction is marked unbalanced (`rebalance` has run). -/
def txBalanced (T : WTx) : Prop :=
  ∀ bl B, T.bs !! bl = some B → ∀ l r, B.ns !! l = some r → r.nv.unbalanced' = false

/-- Every slot of a freed page (`F`) is pending for `txid` in the freelist `fl`. -/
def freedIn (fl : FLState) (txid : w64) (F : GMap Nat (List w8)) : Prop :=
  ∀ id pg, F !! id = some pg → ∀ k < 1 + pageOverflow pg,
    ∃ pd, fl.pending !! txid = some pd ∧ W64 ((id + k : Nat) : Int) ∈ pd.ids

/-- Every slot a pending entry of `txid` holds is a slot of a freed page (`F`): the converse
of `freedIn` (so that `Free` of another page does not panic). -/
def freedAll (fl : FLState) (txid : w64) (F : GMap Nat (List w8)) : Prop :=
  ∀ pd, fl.pending !! txid = some pd → ∀ x ∈ pd.ids, ∃ id pg k, F !! id = some pg ∧
    k < 1 + pageOverflow pg ∧ x = W64 ((id + k : Nat) : Int)

/-- The dirty pages, keyed by their ids as numbers. -/
def bufsN (bufs : GMap w64 (List w8)) : GMap Nat (List w8) :=
  ⟨fun n => if n < 2 ^ 64 then bufs !! W64 (n : Int) else none, by
    obtain ⟨l, hl⟩ := bufs.finite
    refine ⟨l.map (fun x => uint.nat x), fun n h => ?_⟩
    by_cases hn : n < 2 ^ 64
    · simp only [hn, if_true] at h
      refine List.mem_map.2 ⟨W64 (n : Int), hl _ h, ?_⟩
      simp; omega
    · simp [hn] at h⟩

/-- The pages a spilled tree is in: the view's and the dirty ones. -/
def spillPages (W : WView) (T : WTx) : GMap Nat (List w8) := W.pages ∪ bufsN T.bufs

/-- The upper bound `H` is at most `hi` (`none`: no bound). -/
def hiLe (H hi : Option (List w8)) : Prop :=
  ∀ h, hi = some h → ∃ h', H = some h' ∧ ¬ go.GoStringLt h h'

/-- The facts of a written tree whose pages are exactly `Q` (`wtreeQ`). -/
def wtreeF (Q : GMap Nat (List w8)) (x : Nat) (lo hi : Option (List w8)) : Prop :=
  (∀ id, (Q !! id).isSome ↔ treeHas Q x id) ∧ treeWF Q (2 ^ 64) x ∧ pagesStrict Q ∧
    treeKeys Q x lo hi

end pure

section own
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]

/-- The tokens of the freed pages `F`. -/
def freedToks (γ : GName) (F : GMap Nat (List w8)) : IProp GF := pgToks γ F

/-- A written tree (see the module doc). -/
def wtree (γ : GName) (P : GMap Nat (List w8)) (hwm x : Nat) (lo hi : Option (List w8)) :
    IProp GF :=
  iprop(pgToks γ (treePages P x) ∗
    ⌜treeWF P hwm x ∧ pagesStrict (treePages P x) ∧ treeKeys P x lo hi ∧
      pagesDisjoint (treePages P x)⌝)

/-- A written nested bucket's value (see the module doc). -/
def wbkt (γ : GName) (P : GMap Nat (List w8)) (hwm : Nat) (v : List w8) : IProp GF :=
  iprop(⌜16 ≤ v.length⌝ ∗
    if inBucketRoot v = 0 then ⌜inlineGood (inlinePage v)⌝
    else wtree γ P hwm (inBucketRoot v) none none)

/-- A written tree whose pages are exactly `Q`, independent of the other pages (see
`SpillTree.lean`'s `wtree_of_Q`). -/
def wtreeQ (γ : GName) (Q : GMap Nat (List w8)) (x : Nat) (lo hi : Option (List w8)) :
    IProp GF :=
  iprop(pgToks γ Q ∗ ⌜wtreeF Q x lo hi⌝)

/-- A written nested bucket's value, its tree's pages any (`wtreeQ`). -/
def wbktQ (γ : GName) (v : List w8) : IProp GF :=
  iprop(⌜16 ≤ v.length⌝ ∗
    if inBucketRoot v = 0 then ⌜inlineGood (inlinePage v)⌝
    else ∃ Q, wtreeQ γ Q (inBucketRoot v) none none)

end own

end bbolt
end EtcdGrove
end Perennial
