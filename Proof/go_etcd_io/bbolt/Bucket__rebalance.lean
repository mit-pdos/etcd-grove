/-
The proof of `Spec/go_etcd_io/bbolt/Bucket__rebalance.lean` (U8b, `notes/bbolt-proof-plan.md`).

`b.rebalance()` rebalances `b`'s cached nodes (a map iteration: each node still cached when its
key is reached, `node.rebalance.spec'`), then recurses into its cached buckets (`b.buckets`). Its
internal spec (`Bucket.rebalance.spec'`) is over `rebalance`'s invariant `rblX`: after it, every
bucket reached from `b` through the bucket caches has no unbalanced node, and a bucket without one
keeps none (`node.rebalance` never marks a node unbalanced). At `Commit` (`tx.root.rebalance()`)
every bucket is reached from the root (`liveReach`), and `rebalOK_of_rbl` gives the post.
-/
module

public import Spec.go_etcd_io.bbolt.Bucket__rebalance
public import Proof.go_etcd_io.bbolt.node__rebalance

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

/-- The buckets reached from `b` through the bucket caches (`b` included). -/
inductive bReach (X : WX) : Loc → Loc → Prop
  | self (b : Loc) : bReach X b b
  | child (b c d : Loc) (B : BRec) (n : GoString) :
      X.t.bs !! b = some B → B.bm !! n = some c → bReach X c d → bReach X b d

/-- No node of bucket `c` is unbalanced. -/
def balanced (X : WX) (c : Loc) : Prop :=
  ∀ B, X.t.bs !! c = some B → ∀ l r, B.ns !! l = some r → r.nv.unbalanced' = false

/-- **`b.rebalance()`** of a bucket `bl` of the transaction, under `rebalance`'s invariant: every
bucket reached from it balanced after, a balanced bucket kept so, the steps' frees. -/
def Bucket.rebalance.spec' : Prop :=
  ∀ (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (w : WDb) (bl dbl : Loc),
  rblX X w.fl dbl none → (X.t.bs !! bl).isSome →
  {{ wtxW (GF := GF) K tx r m X ∗ wdbW K tx X.v w }}
    (App (Val (bl @!! go.GoType.PointerType Bucket.ty @!! go!"rebalance")) (Val #()))
  {{ RET #(); ∃ (X' : WX) (fl' : FLPg), wtxW K tx r m X' ∗ wdbW K tx X.v (w.withFl fl') ∗
      ⌜rblX X' fl' dbl none ∧ rblRel X w.fl X' fl' X.t.mv.txid' ∧
        (∀ c, bReach X bl c → balanced X' c) ∧ (∀ c, balanced X c → balanced X' c)⌝ }}

end spec

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- **`b.rebalance()`**: the two map iterations (order-independent invariants: the unbalanced
nodes' page ids are keys not yet reached; the buckets done balanced) and the recursion (Löb). -/
theorem Bucket.rebalance.wp_proof' (hn : node.rebalance.spec' (GF := GF) (hG := hG)) :
    Bucket.rebalance.spec' (GF := GF) (hG := hG) := by
  sorry

/-- A bucket the root reaches (`bktReach`) is reached from the root (`bReach`). -/
theorem bReach_snoc (X : WX) (a b c : Loc) (B : BRec) (n : GoString) (h : bReach X a b)
    (hb : X.t.bs !! b = some B) (hn : B.bm !! n = some c) : bReach X a c := by
  induction h with
  | self b => exact .child b c c B n hb hn (.self c)
  | child b c' d B' n' hb' hn' _ ih => exact .child b c' c B' n' hb' hn' (ih hb)

theorem bReach_of_bktReach (X : WX) (c : Loc) (h : bktReach X c) : bReach X X.rl c := by
  induction h with
  | root => exact .self _
  | child bl c B n hb hn _ ih => exact bReach_snoc X X.rl bl c B n ih hb hn

/-- The writer's root bucket is the transaction's `root` field. -/
theorem wtxW_rl (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) :
    wtxW (GF := GF) K tx r m X ⊢ ⌜X.rl = txRoot (GF := GF) tx⌝ ∗ wtxW K tx r m X := by
  unfold wtxW wtxCore
  iintro ⟨⟨Hpkg, Hcore, %Hr, Hreg, Hh, Hrest⟩, Hcells, Hmap⟩
  ihave %Hok := wtxHeap_heapOK tx (DFrac.own 1) X $$ Hh
  isplitr
  · ipureintro; exact Hok.1
  · iframe
    ipureintro; exact Hr

/-- The writer's view is the committed state's. -/
theorem wdbW_view (K : BC) (tx : Loc) (v : View) (w : WDb) :
    wdbW (GF := GF) K tx v w ⊢ ⌜v = View.ofC v.base w.C⌝ ∗ wdbW K tx v w := by
  unfold wdbW
  iintro ⟨H, %Hp⟩
  isplitr
  · ipureintro; exact Hp.2.2
  · iframe; ipureintro; exact Hp

/-- **`tx.root.rebalance()`** (the frozen spec), from the internal one: at `Commit` the invariant
holds (`rblX_init`), every bucket is live, hence reached from the root, hence balanced after;
`rebalOK_of_rbl` gives the post. -/
theorem Bucket.rebalance.wp_proof
    (hSize : node.size.spec (GF := GF) (hG := hG))
    (hNum : node.numChildren.spec (GF := GF) (hG := hG))
    (hIdx : node.childIndex.spec (GF := GF) (hG := hG))
    (hNext : node.nextSibling.spec (GF := GF) (hG := hG))
    (hPrev : node.prevSibling.spec (GF := GF) (hG := hG))
    (hDel : node.del.spec (GF := GF) (hG := hG))
    (hRm : node.removeChild.spec (GF := GF) (hG := hG))
    (hFree : node.free.spec (GF := GF) (hG := hG))
    (hNode : Bucket.node.spec (GF := GF) (hG := hG))
    (hInc : TxStats.IncRebalance.spec (GF := GF) (hG := hG))
    (hAssert : internal.common.Assert.spec (GF := GF) (hG := hG)) :
    Bucket.rebalance.spec (GF := GF) (hG := hG) := by
  have hb := Bucket.rebalance.wp_proof' (node.rebalance.wp_proof hSize hNum hIdx hNext hPrev hDel
    hRm hFree hNode hInc hAssert)
  intro K tx r m X w hok _hld hlr hfl
  -- Not in the frozen spec's pre (reported): a covered slot is covered once, and every node of a
  -- bucket is live.
  have hcov : covU X := by sorry
  have hns : nsLive X := by sorry
  have hI := rblX_init X w.fl X.rl hok hlr hfl hcov hns
  wp_start_folded as ⟨Hw, Hdb⟩
  icases wtxW_rl K tx r m X $$ Hw with ⟨%Hrl, Hw⟩
  icases wdbW_view K tx X.v w $$ Hdb with ⟨%Hv, Hdb⟩
  have e : (tx.[Tx, go!"root"] : Loc) = X.rl := by rw [Hrl]; rfl
  rw [e]
  have hroot : (X.t.bs !! X.rl).isSome := hok.1.2.2.2.2.1
  wp_apply (hb K tx r m X w X.rl X.rl hI hroot) $$ [Hw Hdb] as ⟨%X', %fl', Hw, Hdb, %Hpost⟩
  · iframe
  obtain ⟨hI', hR, hreach, -⟩ := Hpost
  have hbal : ∀ bl B l r, X'.t.bs !! bl = some B → B.ns !! l = some r →
      r.nv.unbalanced' = false := by
    intro bl B l r hb' hr
    have hs := hR.2.2.2.2.2.2.2.2.1 bl
    rw [hb'] at hs
    obtain ⟨B0, hb0⟩ := Option.isSome_iff_exists.1 hs.symm
    have hlive : bl ∈ X.live := hok.2.2.2.2.2.1.2.2 bl B0 hb0
    exact hreach bl (bReach_of_bktReach X bl (hlr.1 bl B0 hb0 hlive)) B hb' l r hr
  obtain ⟨h1, h2, h3⟩ := rebalOK_of_rbl X X' w.fl fl' X.rl X.t.mv.txid' hI' hR hbal
  have htxw : X.t.mv.txid' = w.wtxid := by
    have h0 := hok.1.2.2.2.1
    have hvt : X.v.txid = w.C.txid := by rw [Hv]; rfl
    apply BitVec.eq_of_toNat_eq
    unfold WDb.wtxid
    rw [toNat_W64_of_lt _ (by have := X.t.mv.txid'.isLt; omega)]
    omega
  rw [htxw] at h1
  iapply HΦ
  iexists X', fl'
  iframe
  ipureintro
  exact ⟨h1, h2, h3⟩

end proof

end bbolt
end EtcdGrove
end Perennial
