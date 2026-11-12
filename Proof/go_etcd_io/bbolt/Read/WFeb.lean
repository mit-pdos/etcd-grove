/-
A writer's `Bucket.ForEachBucket` over `first_w`/`next_w`/`next_we` (final wave A,
`notes/bbolt-proof-plan.md`): the bucket's `tx.db` non-nil, a cursor, `first`, then `next` until
nil; a top-level bucket's leaf entries are plain (`wEntKV`), so the callback never runs.
`wp_proof'` is over `wCurCtx`, which `Bucket.ForEachBucket_w.spec`'s premises (`bktLocalOK`,
`pmFresh`, plain entries) do not give (no `wOK`, no `nlocCur`, the root allowed): the spec has to be
restated over `wCurCtx X n bl (X.rootPid bl).toNat` for `wp_proof` to be this.
-/
module

public import Spec.go_etcd_io.bbolt.Bucket__ForEachBucket_w
public import Spec.go_etcd_io.bbolt.Bucket__Cursor_i
public import Spec.go_etcd_io.bbolt.Cursor__first_w
public import Spec.go_etcd_io.bbolt.Cursor__next_w
public import Proof.go_etcd_io.bbolt.Read.PubWCur
public import Proof.go_etcd_io.bbolt.Read.PubWGet

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

set_option linter.unusedSectionVars false

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- Where a writer's cursor is between `ForEachBucket`'s moves: past the end (`k` nil), or on a
stack `next_w` (on an entry) or `next_we` (at the end) moves from, its flags plain. -/
def febAt (X : WX) (n : GoString) (bl : Loc) (rt : Nat) (nl : Loc → Option (Loc × Nat))
    (ipg : List w8) (els : List elemRef) (k : GoSlice) (fl : w32) : Prop :=
  k = slice.nil ∨ (¬ isBktFlag fl ∧ ∃ pids, sPathR nl X.v bl rt els pids ∧
    sLeafOK X.v ipg (wEs X n) pids els ∧
    (leafIdx els < leafCnt X.v (wEs X n) pids els ∨ wEndAt X.v (wEs X n) pids els))

theorem febAt_of_curAt (X : WX) (n : GoString) (bl : Loc) (rt : Nat) (nl : Loc → Option (Loc × Nat))
    (ipg : List w8) (els : List elemRef) (i : Nat) (k : GoSlice) (fl : w32)
    (hc : wCurAt nl X.v (wEs X n) bl rt ipg els (some i)) (hfl : k ≠ slice.nil → ¬ isBktFlag fl) :
    febAt X n bl rt nl ipg els k fl := by
  by_cases hk : k = slice.nil
  · exact Or.inl hk
  obtain ⟨pids, hp, hl, hs⟩ := hc
  refine Or.inr ⟨hfl hk, pids, hp, hl, ?_⟩
  rcases hs with ⟨h, -⟩ | ⟨h, -⟩
  · exact Or.inl h
  · exact Or.inr h

theorem febAt_of_nextPost (X : WX) (n : GoString) (bl : Loc) (rt : Nat)
    (_nl nl' : Loc → Option (Loc × Nat)) (ipg : List w8) (els els' : List elemRef) (pids : List Nat)
    (t : Nat) (k : GoSlice) (fl : w32)
    (hc : wNextPost nl' X.v (wEs X n) bl rt ipg els pids t els') (hfl : k ≠ slice.nil → ¬ isBktFlag fl) :
    febAt X n bl rt nl' ipg els' k fl := by
  by_cases hk : k = slice.nil
  · exact Or.inl hk
  obtain ⟨pids', hp, hl, hs⟩ := hc
  refine Or.inr ⟨hfl hk, pids', hp, hl, ?_⟩
  rcases hs with ⟨-, h, -⟩ | ⟨-, ⟨rfl, rfl, h⟩ | h⟩
  · exact Or.inl h
  · exact Or.inl h
  · exact Or.inr h

theorem wEntKV_plain (v : View) (es : List BoltEnt) (i : Nat) (k vl : GoSlice) (fl : w32) :
    wEntKV (GF := GF) v es i k vl fl ⊢ ⌜k ≠ slice.nil → ¬ isBktFlag fl⌝ := by
  unfold wEntKV
  split
  · iintro ⟨%h, -⟩; ipureintro; exact fun _ => h.2
  · iintro %h; ipureintro; exact fun hk => absurd h.1 hk

/-- **`ForEachBucket` of a writer's top-level bucket** (`wCurCtx`: not the root, so its leaves'
entries are plain, `wEntKV`): the callback never runs; nil, nothing changed. -/
theorem Bucket.ForEachBucket_w.wp_proof'
    (hcur : Bucket.Cursor_i.spec (GF := GF) (hG := hG))
    (hfst : Cursor.first_w.specQ (GF := GF) (hG := hG))
    (hnx : Cursor.next_w.specQ (GF := GF) (hG := hG))
    (hnxe : Cursor.next_we.specQ (GF := GF) (hG := hG)) :
    ∀ (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (n : GoString) (bl : Loc) (fn : GoFunc),
    wCurCtx X n bl (X.rootPid bl).toNat →
    {{ wtxW (GF := GF) K tx r m X }}
      (App (Val (bl @!! go.GoType.PointerType Bucket.ty @!! go!"ForEachBucket")) (Val #fn))
    {{ (err : GoInterface), RET #err; ⌜err = interface.nil⌝ ∗ wtxW K tx r m X }} := by
  intro K tx r m X n bl fn hctx
  wp_start as Hw
  ihave Hw : wtxWQ K tx r m 1 X $$ [Hw]
  · rw [wtxWQ_one]; iexact Hw
  icases wtxWQ_pkgInit K tx r m 1 X $$ Hw with ⟨Hw, #Hpkg⟩
  icases wtxWQ_heapOK K tx r m 1 X $$ Hw with ⟨Hw, %Hhok⟩
  obtain ⟨C, hC⟩ := PubW.bktLoc_rec X hctx.1 n bl hctx.2.1
  icases wtxWQ_child_tx K tx r m 1 X bl C hC hctx.2.2.2.2 Hhok $$ Hw with ⟨Hw, #Hbtx⟩
  icases wtxWQ_db_acc K tx r m 1 X $$ Hw with ⟨Hdb, %Hdbn, Hwdb⟩
  wp_auto
  rw [decide_eq_false Hdbn]
  wp_auto
  ihave Hw := Hwdb $$ Hdb
  icases wtxWQ_stats_acc K tx r m 1 X $$ Hw with ⟨#Hcore, #Hreg, Hst, Hwb⟩
  wp_apply hcur K tx r m 1 bl DFrac.discard $$ [Hst] as %c ⟨%stk, Hc, Hs, Hcap, Hst, -⟩
  · iframe; iframe #
  ihave Hw := Hwb $$ Hst
  try wp_auto
  wp_apply hfst K tx r m 1 X n bl _ c stk [] hctx $$ [Hw Hc Hs Hcap]
    as %k %vl %fl ⟨%stk1, %els1, %nl1, %ipg1, Hw, Hc, Hs, Hcap, #Hown, %Hcur, #Hkv⟩
  · iframe
  ihave %Hpl := wEntKV_plain X.v (wEs X n) 0 k vl fl $$ Hkv
  have hat := febAt_of_curAt X n bl _ nl1 ipg1 els1 0 k fl Hcur Hpl
  try wp_auto
  ihave IH : (∃ (k : GoSlice) (fl : w32) (stk1 : GoSlice) (els1 : List elemRef)
      (nl1 : Loc → Option (Loc × Nat)) (ipg1 : List w8),
      "k" ∷ k_ptr ↦ k ∗ "flags" ∷ flags_ptr ↦ fl ∗ "Hw" ∷ wtxWQ K tx r m 1 X ∗
      "Hc" ∷ c ↦ Cursor.mk bl stk1 ∗ "Hs" ∷ stk1 ↦* els1 ∗
      "Hcap" ∷ ownSliceCap elemRef stk1 (DFrac.own 1) ∗
      "Hown" ∷ wStkOwn r nl1 X.v (X.rootPid bl).toNat ipg1 els1 ∗
      "%Hat" ∷ ⌜febAt X n bl (X.rootPid bl).toNat nl1 ipg1 els1 k fl⌝ : IProp GF)
    $$ [k flags Hw Hc Hs Hcap Hown]
  · iexists k, fl, stk1, els1, nl1, ipg1
    simp only [named]
    iframe; iframe #
    ipureintro; exact hat
  wp_for IH
  cleanup_bool_decide
  by_cases hkn : k = slice.nil
  · simp only [hkn, _root_.decide_true, Bool.not_true, intoVal_eq_iff, Bool.false_eq_true,
      _root_.decide_false, ↓reduceIte]
    wp_auto
    iapply HΦ
    rw [← wtxWQ_one]
    iframe
    ipureintro; rfl
  · simp only [hkn, _root_.decide_false, Bool.not_false, _root_.decide_true, ↓reduceIte]
    rcases Hat with hk | ⟨hfl, pids, hp, hl, hs⟩
    · exact absurd hk hkn
    have hand : fl &&& W32 1 = W32 0 := by
      unfold isBktFlag at hfl; exact Classical.not_not.1 hfl
    wp_auto
    rw [decide_eq_true hand]
    simp only [Bool.not_true]
    wp_auto
    wp_for_post
    rcases hs with hli | hend
    · have hstk : wStk nl1 X.v (wEs X n) bl (X.rootPid bl).toNat ipg1 els1 pids :=
        ⟨hp, hl, Nat.le_of_lt hli⟩
      wp_apply hnx K tx r m 1 X n bl _ ipg1 nl1 c stk1 els1 pids hctx hstk
        $$ [Hw Hc Hs Hcap Hown] as %k' %vl' %fl' ⟨%stk2, %els2, %nl2, Hw, Hc, Hs, Hcap, #Hown', %Hpost, #Hkv'⟩
      · iframe
      ihave %Hpl' := wEntKV_plain X.v (wEs X n) _ k' vl' fl' $$ Hkv'
      try wp_auto
      iframe
      iexists k', fl', stk2, els2, nl2, ipg1
      simp only [named]
      iframe; iframe #
      ipureintro; exact febAt_of_nextPost X n bl _ nl1 nl2 ipg1 els1 els2 pids _ k' fl' Hpost Hpl'
    · wp_apply hnxe K tx r m 1 X n bl _ ipg1 nl1 c stk1 els1 pids hctx (Or.inr ⟨hp, hl, hend⟩)
        $$ [Hw Hc Hs Hown] as ⟨Hw, Hc, Hs, Hown⟩
      · iframe
      try wp_auto
      iframe
      iexists slice.nil, (W32 0), stk1, els1, nl1, ipg1
      simp only [named]
      iframe; iframe #
      ipureintro; exact Or.inl rfl

end proof

end bbolt
end EtcdGrove
end Perennial
