/-
`Cursor.keyValue_ws`'s (U6aa, `notes/bbolt-proof-plan.md`, "Writer reads at a fraction") facts:
the entries of a leaf's bounds are the contiguous block of a sorted entry list after the entries
below its lower bound (`entsIn_get`), so a stack's position names its leaf's entry; a view's leaf
pages are well-formed and its branches' children are not position `0`; a kept slice's source
gives `wEntKV`'s disjunct.
-/
module

public import Proof.go_etcd_io.bbolt.Read.WCur
public import Proof.go_etcd_io.bbolt.Read.Ents
public import Proof.go_etcd_io.bbolt.Read.TreeFacts

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

namespace WKVs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pure
variable [GooseExts]

open Classical in
/-- **A leaf's entries are the block after the entries below its lower bound** (in a sorted list). -/
theorem entsIn_get (bnd : Option (List w8) × Option (List w8)) :
    ∀ (es : List BoltEnt), Ents.esSorted es → ∀ i, i < (entsIn es bnd).length →
      es[(es.filter fun e => decide (¬ keyGe bnd.1 e.1)).length + i]? = (entsIn es bnd)[i]?
  | [], _, i, h => by simp [entsIn] at h
  | a :: t, hs, i, h => by
    have hst : Ents.esSorted t := (List.pairwise_cons.1 hs).2
    have hlt : ∀ b ∈ t, go.GoStringLt a.1 b.1 := (List.pairwise_cons.1 hs).1
    by_cases hg : keyGe bnd.1 a.1
    · -- every later entry is above the lower bound too
      have hgt : ∀ b ∈ t, keyGe bnd.1 b.1 := by
        intro b hb l hl hbl
        exact hg l hl (go.goStringLt_trans (hlt b hb) hbl)
      have hf0 : (t.filter fun e => decide (¬ keyGe bnd.1 e.1)) = [] := by
        rw [List.filter_eq_nil_iff]; intro b hb; simpa using hgt b hb
      have hfa : ((a :: t).filter fun e => decide (¬ keyGe bnd.1 e.1)) = [] := by
        rw [List.filter_cons, if_neg (by simpa using hg), hf0]
      rw [hfa, List.length_nil, Nat.zero_add]
      by_cases hk : keyLt a.1 bnd.2
      · have he : entsIn (a :: t) bnd = a :: entsIn t bnd := by
          unfold entsIn; rw [List.filter_cons, if_pos (decide_eq_true ⟨hg, hk⟩)]
        rw [he] at h ⊢
        cases i with
        | zero => rfl
        | succ j =>
          simp only [List.getElem?_cons_succ]
          have := entsIn_get bnd t hst j (by simp at h; omega)
          rw [hf0, List.length_nil, Nat.zero_add] at this
          exact this
      · -- no later entry is below the upper bound: the leaf is empty
        have hnt : ∀ b ∈ t, ¬ keyLt b.1 bnd.2 := by
          intro b hb hb'
          apply hk
          intro u hu
          exact go.goStringLt_trans (hlt b hb) (hb' u hu)
        have he : entsIn (a :: t) bnd = [] := by
          unfold entsIn
          rw [List.filter_eq_nil_iff]
          intro b hb
          intro hd
          have hk' := (of_decide_eq_true hd).2
          rcases List.mem_cons.1 hb with rfl | hb'
          · exact hk hk'
          · exact hnt b hb' hk'
        rw [he] at h; simp at h
    · have hfa : ((a :: t).filter fun e => decide (¬ keyGe bnd.1 e.1)) =
          a :: (t.filter fun e => decide (¬ keyGe bnd.1 e.1)) := by
        rw [List.filter_cons, if_pos (by simpa using hg)]
      have he : entsIn (a :: t) bnd = entsIn t bnd := by
        unfold entsIn; rw [List.filter_cons, if_neg (fun h' => hg (of_decide_eq_true h').1)]
      rw [hfa, he]
      rw [he] at h
      rw [List.length_cons, show (t.filter fun e => decide (¬ keyGe bnd.1 e.1)).length + 1 + i =
        ((t.filter fun e => decide (¬ keyGe bnd.1 e.1)).length + i) + 1 by omega,
        List.getElem?_cons_succ]
      exact entsIn_get bnd t hst i h

/-- **A stack's position names its leaf's entry** (over `bktEnts`, sorted). -/
theorem stackPos_get (v : View) (m : BktData) (pids : List Nat) (els : List elemRef)
    (h : leafIdx els < leafCnt v (bktEnts m) pids els) :
    (bktEnts m)[stackPos v (bktEnts m) pids els]? =
      (entsIn (bktEnts m) (pathBnd v pids els))[leafIdx els]? := by
  unfold stackPos
  exact entsIn_get _ _ (Ents.bktEnts_sorted m) _ h

/-- A stack's leaf index is its last element's. -/
theorem leafIdx_append (els : List elemRef) (e : elemRef) :
    leafIdx (els ++ [e]) = e.index'.toNat := by
  unfold leafIdx; simp

/-- The tree of a page of a well-formed view. -/
theorem viewWF_treeWF (v : View) (hv : viewWF v) (id : Nat) (pg : List w8)
    (hpg : v.pages !! id = some pg) : ∃ hwm, treeWF v.pages hwm id := by
  obtain ⟨C, hok, hvC⟩ := hv
  have hpv : v.pages = C.pages := by rw [← hvC]; rfl
  rw [hpv] at hpg ⊢
  have hin : treePages C.pages C.root !! id = some pg := by rw [hok.2.1]; exact hpg
  unfold treePages at hin
  rw [GMap.mapLookup_filter_Some] at hin
  have hhas : treeHas C.pages C.root id := by simpa using hin.2
  exact ⟨_, Read.treeHas_treeWF C.pages C.hwm hhas hok.1.1⟩

/-- A leaf page of a well-formed view is well-formed (`leafWF`). -/
theorem viewWF_leafWF (v : View) (hv : viewWF v) (id : Nat) (pg : List w8)
    (hpg : v.pages !! id = some pg) (hb : pageFlags pg = leafPageFlag) :
    leafWF pg pg.length := by
  obtain ⟨hwm, hw⟩ := viewWF_treeWF v hv id pg hpg
  cases hw with
  | page _ pg' _ _ hpg' _ _ hpt =>
    rw [hpg] at hpg'; cases hpg'
    cases hpt with
    | leaf _ _ _ hlw _ => exact hlw
    | branch _ _ hf _ _ => rw [hb] at hf; simp [branchPageFlag, leafPageFlag] at hf

/-- A branch page's children in a well-formed view are not position `0` (nor `1`). -/
theorem viewWF_branch_child (v : View) (hv : viewWF v) (id : Nat) (pg : List w8)
    (hpg : v.pages !! id = some pg) (hb : pageFlags pg = branchPageFlag) (i : Nat)
    (hi : i < pageCount pg) : 2 ≤ branchPgid pg i := by
  obtain ⟨hwm, hw⟩ := viewWF_treeWF v hv id pg hpg
  cases hw with
  | page _ pg' _ _ hpg' _ _ hpt =>
    rw [hpg] at hpg'; cases hpg'
    cases hpt with
    | leaf _ _ hf _ _ => rw [hb] at hf; simp [branchPageFlag, leafPageFlag] at hf
    | branch _ _ _ _ hch =>
      cases hch i hi with
      | page _ _ h2 _ _ _ _ _ => exact h2

/-- **A stack whose leaf is at position `0` is the root alone** (a branch's children are view
pages). -/
theorem sPathR_pid0 (nl : Loc → Option (Loc × Nat)) (v : View) (hv : viewWF v) (b : Loc)
    (rt : Nat) (els : List elemRef) (e : elemRef) (pids : List Nat)
    (hp : sPathR nl v b rt (els ++ [e]) pids) (hpid : pids.getLast? = some 0) :
    els = [] ∧ pids = [0] ∧ rt = 0 := by
  obtain ⟨-, hlen, hhd, hj⟩ := hp
  simp only [List.length_append, List.length_singleton] at hlen
  cases els with
  | nil =>
    refine ⟨rfl, ?_⟩
    match pids, hlen with
    | [p], _ =>
      simp at hpid hhd
      subst hpid; exact ⟨rfl, hhd.symm⟩
  | cons x t =>
    exfalso
    have hl : (x :: t).length - 1 < (x :: t ++ [e]).length := by simp; omega
    obtain ⟨p, hp⟩ : ∃ p, pids[(x :: t).length - 1]? = some p :=
      ⟨_, List.getElem?_eq_getElem (by simp at hlen ⊢; omega)⟩
    obtain ⟨y, hy⟩ : ∃ y, (x :: t ++ [e])[(x :: t).length - 1]? = some y :=
      ⟨_, List.getElem?_eq_getElem hl⟩
    obtain ⟨-, -, hbr, -⟩ := hj _ y p hy hp
    obtain ⟨pg, hpg, hf, hi, hnext⟩ := hbr (by simp)
    have hlast : pids[(x :: t).length - 1 + 1]? = some 0 := by
      rw [show (x :: t).length - 1 + 1 = pids.length - 1 by simp at hlen ⊢; omega,
        ← List.getLast?_eq_getElem?]
      exact hpid
    rw [hlast] at hnext
    have := viewWF_branch_child v hv p pg hpg hf _ hi
    simp only [Option.some.injEq] at hnext
    omega

/-- **The leaf index's facts** on a non-empty leaf (`count` entries, `count < 2^63`): at most
`count`, and its signed value is itself. -/
theorem leafIdx_sint (e : elemRef) (cnt : Nat) (hc : cnt < 2 ^ 63) (h0 : cnt ≠ 0)
    (h : e.index'.toNat ≤ cnt ∨ e.index' = W64 (cnt : Int) ∨ (cnt = 0 ∧ e.index' = W64 (-1))) :
    e.index'.toNat ≤ cnt ∧ sint.Z e.index' = (e.index'.toNat : Int) := by
  rcases h with h | h | ⟨h, -⟩
  · refine ⟨h, ?_⟩
    have : (e.index'.toNat : Int) = uint.Z e.index' := rfl
    rw [this]
    word
  · rw [h]
    have hn : (W64 (cnt : Int)).toNat = cnt := by simp; omega
    rw [hn]
    refine ⟨Nat.le_refl _, ?_⟩
    word
  · exact absurd h h0

/-- `wEndAt` or the leaf index at most the count: the disjunction `leafIdx_sint` takes. -/
theorem leafIdx_cases (v : View) (es : List BoltEnt) (pids : List Nat) (els : List elemRef)
    (e : elemRef)
    (h : leafIdx (els ++ [e]) ≤ leafCnt v es pids (els ++ [e]) ∨ wEndAt v es pids (els ++ [e])) :
    e.index'.toNat ≤ leafCnt v es pids (els ++ [e]) ∨
      e.index' = W64 (leafCnt v es pids (els ++ [e]) : Int) ∨
      (leafCnt v es pids (els ++ [e]) = 0 ∧ e.index' = W64 (-1)) := by
  rw [leafIdx_append] at h
  rcases h with h | ⟨-, e', he', h⟩
  · exact Or.inl h
  · simp at he'; subst he'; exact Or.inr h

end pure

section iprop
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- A kept slice's non-stale source: persistent bytes or bytes of the view (`wEntKV`'s). -/
theorem srcOwn_ent (v : View) (s : GoSlice) (src : Src) (bs : List w8) (h : src ≠ Src.stale) :
    srcOwn (GF := GF) v s src bs ⊢ s ↦*□ bs ∨ ⌜inViewAt v s bs⌝ := by
  cases src with
  | stale => exact absurd rfl h
  | view => unfold srcOwn; iintro %H; iright; ipureintro; exact H
  | own _ => unfold srcOwn; iintro #H; ileft; iexact H

/-- **The inline root page's bytes**, out of `wInlOwn` of a root-alone stack: a non-stale source. -/
theorem wInlOwn_src (v : View) (ipg : List w8) (e : elemRef) (hn : e.node' = null) :
    wInlOwn (GF := GF) v 0 ipg [e] ⊢ ∃ src, ⌜src ≠ Src.stale⌝ ∗ srcLoc v e.page' src ipg := by
  unfold wInlOwn locOwn
  simp only [hn, and_self, ↓reduceIte]
  iintro (%H | #H)
  · iexists Src.view; unfold srcLoc
    isplitr
    · ipureintro; intro h; cases h
    · ipureintro; exact H
  · iexists Src.own DFrac.discard; unfold srcLoc
    isplitr
    · ipureintro; intro h; cases h
    · iexact H

end iprop

end WKVs

end bbolt
end EtcdGrove
end Perennial
