/-
U7e's (`notes/bbolt-proof-plan.md`) walk of a bucket's logical tree, `Bucket._forEachPageNode`:
over a finite tree `t` of the logical tree (`ltIs`, `Rebalance/RTree`), the walk calls its
callback at each position of `t` in pre-order (`t.pos`), the callback running over an invariant
`I` of the visited positions. The walk reads the writer's state through `I`: an accessor gives a
state `Y` with what the walk reads as in `X` (`walkSame`: the view, the page cache, the bucket's
header, root node and node cache, each node's kind, entries and inodes).
-/
module

public import Spec.go_etcd_io.bbolt.Bucket__pageNode_w
public import Spec.go_etcd_io.bbolt.internal.common.Page__IsBranchPage
public import Spec.go_etcd_io.bbolt.internal.common.Page__Count
public import Spec.go_etcd_io.bbolt.internal.common.Page__BranchPageElement
public import Spec.go_etcd_io.bbolt.internal.common.branchPageElement__Pgid
public import Spec.go_etcd_io.bbolt.internal.common.Inode__Pgid
public import Spec.go_etcd_io.bbolt.internal.common.InBucket__RootPage
public import Proof.go_etcd_io.bbolt.Read.WCtx
public import Proof.go_etcd_io.bbolt.Read.Bytes
public import Proof.go_etcd_io.bbolt.Rebalance.RTree
public import Proof.go_etcd_io.bbolt.internal.common.Lemmas.Layout

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

namespace Write

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pure
variable [GooseExts]

/-- **What the walk reads stays as in `X`** (bucket `bl`, `B` its record in `X`). -/
def walkSame (X Y : WX) (bl : Loc) (B : BRec) : Prop :=
  Y.v = X.v ∧ Y.t.pm = X.t.pm ∧ bl ∈ Y.liveB ∧ ∃ B', Y.t.bs !! bl = some B' ∧ B'.ib = B.ib ∧
    B'.bv = B.bv ∧ B'.nm = B.nm ∧ B'.ipg = B.ipg ∧
    ∀ l r, B.ns !! l = some r → l ∈ Y.live ∧ ∃ r', B'.ns !! l = some r' ∧
      r'.nv.isLeaf' = r.nv.isLeaf' ∧ r'.ws = r.ws ∧ r'.ins = r.ins ∧ r'.nv.inodes' = r.nv.inodes'

/-- The callback's arguments at position `pid`: the materialized node (a nil page), else the
page (a nil node). -/
def posRef (X : WX) (B : BRec) (pid : w64) (p n : Loc) : Prop :=
  match resolve B pid with
  | some l => p = null ∧ n = l
  | none => n = null ∧ ∃ pg, wpageAt X.v B pid = some (p, pg)

theorem ltIsL_get (L : LTree) (bl : Loc) : ∀ (ws : List WEntry) (cs : List RTree),
    ltIsL L bl ws cs → ∀ (j : Nat) (c : RTree), cs[j]? = some c → ∃ w, ws[j]? = some w ∧ c.pid = w.pgid ∧ ltIs L bl c
  | [], [], _, j, c, h => by simp at h
  | w :: ws, t :: ts, h, j, c, hc => by
    simp only [ltIsL] at h
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hc
      subst hc
      exact ⟨w, rfl, h.1, h.2.1⟩
    | succ j =>
      simp only [List.getElem?_cons_succ] at hc ⊢
      exact ltIsL_get L bl ws ts h.2.2 j c hc
  | [], _ :: _, h, _, _, _ => by simp only [ltIsL] at h
  | _ :: _, [], h, _, _, _ => by simp only [ltIsL] at h

theorem ltIsL_len (L : LTree) (bl : Loc) : ∀ (ws : List WEntry) (cs : List RTree),
    ltIsL L bl ws cs → cs.length = ws.length
  | [], [], _ => rfl
  | _ :: ws, _ :: cs, h => by
    simp only [ltIsL] at h
    simp only [List.length_cons, ltIsL_len L bl ws cs h.2.2]
  | [], _ :: _, h => by simp only [ltIsL] at h
  | _ :: _, [], h => by simp only [ltIsL] at h

theorem posL_append (a b : List RTree) : RTree.posL (a ++ b) = RTree.posL a ++ RTree.posL b := by
  induction a with
  | nil => rfl
  | cons t ts ih => simp only [List.cons_append, RTree.posL, ih, List.append_assoc]

theorem posL_take_succ (cs : List RTree) (j : Nat) (c : RTree) (h : cs[j]? = some c) :
    RTree.posL (cs.take (j + 1)) = RTree.posL (cs.take j) ++ c.pos := by
  rw [List.take_succ, h, Option.toList_some, posL_append]
  simp [RTree.posL]

theorem walkSame_resolve {X Y : WX} {bl : Loc} {B B' : BRec} (h : walkSame X Y bl B)
    (hB' : Y.t.bs !! bl = some B') (pid : w64) : resolve B' pid = resolve B pid := by
  obtain ⟨-, -, -, B'', hb, hib, hbv, hnm, -, -⟩ := h
  rw [hB'] at hb; cases hb
  unfold resolve; rw [hib, hbv, hnm]

theorem walkSame_wpageAt {X Y : WX} {bl : Loc} {B B' : BRec} (h : walkSame X Y bl B)
    (hB' : Y.t.bs !! bl = some B') (pid : w64) : wpageAt Y.v B' pid = wpageAt X.v B pid := by
  obtain ⟨hv, -, -, B'', hb, hib, hbv, -, hipg, -⟩ := h
  rw [hB'] at hb; cases hb
  unfold wpageAt; rw [hib, hbv, hipg, hv]

theorem viewWF_branch (v : View) (hv : viewWF v) (id : Nat) (pg : List w8)
    (hpg : v.pages !! id = some pg) (hb : pageFlags pg = branchPageFlag) :
    ∃ hwm, branchWF pg pg.length hwm := by
  obtain ⟨C, hok, hvC⟩ := hv
  have hpv : v.pages = C.pages := by rw [← hvC]; rfl
  rw [hpv] at hpg
  have hin : treePages C.pages C.root !! id = some pg := by rw [hok.2.1]; exact hpg
  unfold treePages at hin
  rw [GMap.mapLookup_filter_Some] at hin
  have hhas : treeHas C.pages C.root id := by simpa using hin.2
  have hw := Read.treeHas_treeWF C.pages C.hwm hhas hok.1.1
  cases hw with
  | page _ pg' _ _ hpg' _ _ hpt =>
    rw [hpg] at hpg'; cases hpg'
    cases hpt with
    | leaf _ _ hf _ _ => rw [hb] at hf; exact absurd hf (by decide)
    | branch _ _ _ hbw _ => exact ⟨_, hbw⟩

/-- A page position of the walk: its page in the view, at its location. -/
theorem walk_page (X : WX) (bl : Loc) (B : BRec) (pid : w64) (x : Bool × List WEntry)
    (hB : X.t.bs !! bl = some B) (h0 : B.ib.root' ≠ W64 0) (hr : resolve B pid = none)
    (hl : ltree X bl pid = some x) :
    ∃ pg, X.v.pages !! pid.toNat = some pg ∧ wpageAt X.v B pid = some (pageLoc X.v pid.toNat, pg) ∧
      x = (decide (pageFlags pg = leafPageFlag), pageWs pg) := by
  unfold ltree at hl
  rw [hB] at hl
  simp only [hr] at hl
  unfold wpageAt at hl ⊢
  rw [if_neg h0] at hl ⊢
  cases hpg : X.v.pages !! pid.toNat with
  | none => rw [hpg] at hl; cases hl
  | some pg =>
    rw [hpg] at hl
    simp only [Option.map_some, Option.some.injEq] at hl
    exact ⟨pg, rfl, rfl, hl.symm⟩

/-- A node position of the walk: its node. -/
theorem walk_node (X : WX) (bl : Loc) (B : BRec) (pid : w64) (l : Loc) (x : Bool × List WEntry)
    (hB : X.t.bs !! bl = some B) (hc : bktClean X.v X.t.mv.pgid'.toNat bl B)
    (h0 : B.ib.root' ≠ W64 0) (hr : resolve B pid = some l)
    (hl : ltree X bl pid = some x) :
    ∃ rn, B.ns !! l = some rn ∧ l ≠ null ∧ rn.nv.pgid' = pid ∧ x = (rn.nv.isLeaf', rn.ws) := by
  have hnm : B.nm !! pid = some l := by unfold resolve at hr; rwa [if_neg h0] at hr
  obtain ⟨hnn, rn, hrn, hpid⟩ := hc.2.2.2.2.1 pid l hnm
  unfold ltree at hl
  rw [hB] at hl
  simp only [hr, hrn, Option.map_some, Option.some.injEq] at hl
  exact ⟨rn, hrn, hnn, hpid, hl.symm⟩

theorem walk_pn_pre (X Y : WX) (bl : Loc) (B B' : BRec) (pid : w64) (x : Bool × List WEntry)
    (hs : walkSame X Y bl B) (hB' : Y.t.bs !! bl = some B') (hB : X.t.bs !! bl = some B)
    (h0 : B.ib.root' ≠ W64 0) (hvw : viewWF X.v) (hl : ltree X bl pid = some x)
    (hpm : X.t.pm !! pid = none)
    (hmax : ∀ id pg, Y.v.pages !! id = some pg → id * 4096 < 0xFFFFFFFFFFFF) :
    resolve B' pid = none → ∃ pa pg, wpageAt Y.v B' pid = some (pa, pg) ∧
      (B'.ib.root' = W64 0 → B'.pst = PageSt.view ∨ ∃ dq, B'.isrc = Src.own dq) ∧
      (B'.ib.root' ≠ W64 0 → Y.t.pm !! pid = none ∧ 16 ≤ pg.length ∧ pageId pg = pid.toNat ∧
        (pageFlags pg = branchPageFlag ∨ pageFlags pg = leafPageFlag) ∧
        pid.toNat * 4096 < 0xFFFFFFFFFFFF) := by
  intro hr
  rw [walkSame_resolve hs hB'] at hr
  obtain ⟨pg, hpg, hw, -⟩ := walk_page X bl B pid x hB h0 hr hl
  have hib : B'.ib = B.ib := by
    obtain ⟨-, -, -, B'', hb, hib, -⟩ := hs; rw [hB'] at hb; cases hb; exact hib
  obtain ⟨-, hid, h4096, hfl⟩ := Read.viewWF_page X.v hvw _ pg hpg
  refine ⟨_, pg, by rw [walkSame_wpageAt hs hB']; exact hw, fun h => ?_,
    fun _ => ⟨?_, by omega, hid, hfl, ?_⟩⟩
  · rw [hib] at h; exact absurd h h0
  · rw [hs.2.1]; exact hpm
  · exact hmax _ pg (by rw [hs.1]; exact hpg)

theorem walk_posRef {X Y : WX} {bl : Loc} {B B' : BRec} (hs : walkSame X Y bl B)
    (hB' : Y.t.bs !! bl = some B') (pid : w64) (p n : Loc)
    (h : match resolve B' pid with
      | some l => p = null ∧ n = l
      | none => n = null ∧ ∃ pg, wpageAt Y.v B' pid = some (p, pg)) : posRef X B pid p n := by
  unfold posRef; rw [walkSame_resolve hs hB', walkSame_wpageAt hs hB'] at h; exact h

theorem prefix_cons_mono (ps : List w64) (pid : w64) {A C : List w64} (h : A <+: C) :
    (ps ++ pid :: A) <+: (ps ++ pid :: C) := by
  obtain ⟨u, rfl⟩ := h; exact ⟨u, by simp⟩

theorem walk_child_pre (ps : List w64) (pid : w64) (cs : List RTree) (Q : List w64) (j : Nat)
    (c : RTree) (hc : cs[j]? = some c) (h : (ps ++ pid :: RTree.posL cs) <+: Q) :
    ((ps ++ pid :: RTree.posL (cs.take j)) ++ c.pos) <+: Q ∧
    (ps ++ pid :: RTree.posL (cs.take j)) ++ c.pos = ps ++ pid :: RTree.posL (cs.take (j + 1)) := by
  have he : (ps ++ pid :: RTree.posL (cs.take j)) ++ c.pos =
      ps ++ pid :: RTree.posL (cs.take (j + 1)) := by
    rw [posL_take_succ cs j c hc]; simp
  refine ⟨?_, he⟩
  rw [he]
  refine List.IsPrefix.trans (prefix_cons_mono ps pid ?_) h
  have := congrArg RTree.posL (List.take_append_drop (j + 1) cs)
  rw [posL_append] at this
  exact ⟨_, this⟩

end pure

section walk
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- The walk's accessor: `I` holds a writer state that reads as `X`'s. -/
def walkAcc (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (bl : Loc) (B : BRec)
    (I : List w64 → IProp GF) : IProp GF :=
  iprop(□ ∀ ps, I ps -∗ ∃ Y, wtxW K tx r m Y ∗ ⌜walkSame X Y bl B⌝ ∗ (wtxW K tx r m Y -∗ I ps))

instance walkAcc_persistent (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (bl : Loc)
    (B : BRec) (I : List w64 → IProp GF) : Persistent (walkAcc K tx r m X bl B I) := by
  unfold walkAcc; infer_instance

/-- The walk's callback: at position `pid` (`ps ++ [pid]` a prefix of `Q`), from `I ps` to
`I (ps ++ [pid])`. -/
def walkCb (X : WX) (B : BRec) (I : List w64 → IProp GF) (Q : List w64) (fn : GoFunc) : IProp GF :=
  iprop(□ ∀ (ps : List w64) (pid : w64) (p n : Loc) (d : w64),
    {{ I ps ∗ ⌜(ps ++ [pid]) <+: Q ∧ posRef X B pid p n⌝ }}
      (App (App (App (Val #fn) (Val #p)) (Val #n)) (Val #d))
    {{ RET #(); I (ps ++ [pid]) }})

instance walkCb_persistent (X : WX) (B : BRec) (I : List w64 → IProp GF) (Q : List w64)
    (fn : GoFunc) : Persistent (walkCb X B I Q fn) := by
  unfold walkCb; infer_instance

theorem walk_open (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (bl : Loc) (B : BRec)
    (I : List w64 → IProp GF) (ps : List w64) :
    walkAcc K tx r m X bl B I ⊢ I ps -∗ ∃ Y, wtxW K tx r m Y ∗ ⌜walkSame X Y bl B⌝ ∗
      (wtxW K tx r m Y -∗ I ps) := by
  unfold walkAcc
  iintro #Hacc HI
  iapply Hacc $$ HI

theorem walk_bytes (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (bl : Loc) (B : BRec)
    (I : List w64 → IProp GF) (id : Nat) (pg : List w8) (hpg : X.v.pages !! id = some pg)
    (ps : List w64) :
    walkAcc K tx r m X bl B I ⊢ I ps -∗ ∃ dq : DFrac, bytesPointsto (pageLoc X.v id) dq pg ∗
      (bytesPointsto (pageLoc X.v id) dq pg -∗ I ps) := by
  iintro #Hacc HI
  icases walk_open K tx r m X bl B I _ $$ Hacc HI with ⟨%Y, Hw, %Hs, Hback⟩
  obtain ⟨hv, -⟩ := Hs
  icases wtxW_cells_acc K tx r m Y $$ Hw with ⟨-, Hc, Hwb⟩
  rw [hv]
  icases viewCells_page_acc wq X.v id pg hpg $$ Hc with ⟨Hp, Hcb⟩
  iexists DFrac.own wq
  iframe Hp
  iintro Hp
  iapply Hback
  iapply Hwb
  iapply Hcb $$ Hp

theorem walk_node_acc (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (bl : Loc) (B : BRec)
    (I : List w64 → IProp GF) (l : Loc) (rn : NRec) (hrn : B.ns !! l = some rn) (ps : List w64) :
    walkAcc K tx r m X bl B I ⊢ I ps -∗ ∃ r' : NRec, ⌜r'.nv.isLeaf' = rn.nv.isLeaf' ∧
      r'.ws = rn.ws ∧ r'.ins = rn.ins ∧ r'.nv.inodes' = rn.nv.inodes'⌝ ∗
      objOwn X.v l (DFrac.own 1) true (.node bl r') ∗
      (objOwn X.v l (DFrac.own 1) true (.node bl r') -∗ I ps) := by
  iintro #Hacc HI
  icases walk_open K tx r m X bl B I _ $$ Hacc HI with ⟨%Y, Hw, %Hs, Hback⟩
  obtain ⟨hv, -, -, B', hB', -, -, -, -, hns⟩ := Hs
  obtain ⟨hlv, r', hr', h1, h2, h3, h4⟩ := hns l rn hrn
  icases wtxW_node_cells_acc K tx r m Y bl B' l r' hB' hr' hlv $$ Hw with ⟨-, Ho, Hc, Hwb⟩
  rw [hv]
  iexists r'
  isplitl []
  · ipureintro; exact ⟨h1, h2, h3, h4⟩
  iframe Ho
  iintro Ho
  iapply Hback
  iapply Hwb $$ Ho Hc

theorem walk_aux (hpn : Bucket.pageNode_w.spec (GF := GF) (hG := hG))
    (hIB : internal.common.Page.IsBranchPage.spec (GF := GF) (hG := hG))
    (hCnt : internal.common.Page.Count.spec (GF := GF) (hG := hG))
    (hBE : internal.common.Page.BranchPageElement.spec (GF := GF) (hG := hG))
    (hBP : internal.common.branchPageElement.Pgid.spec (GF := GF) (hG := hG))
    (hIP : internal.common.Inode.Pgid.spec (GF := GF) (hG := hG))
    (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (bl : Loc) (B : BRec)
    (I : List w64 → IProp GF) (Q : List w64) (fn : GoFunc)
    (hB : X.t.bs !! bl = some B) (hloc : bktLocalOK X bl) (h0 : B.ib.root' ≠ W64 0)
    (hpm : ∀ pid ∈ Q, X.t.pm !! pid = none) :
    ⊢ (walkAcc K tx r m X bl B I -∗ walkCb X B I Q fn -∗
      ∀ (t : RTree) (ps : List w64) (d : w64), ⌜ltIs (ltree X) bl t ∧ (ps ++ t.pos) <+: Q⌝ -∗
        ∀ Φ, I ps -∗ ▷ (I (ps ++ t.pos) -∗ Φ #()) -∗
        WP (App (App (App (Val (bl @!! go.GoType.PointerType Bucket.ty @!! go!"_forEachPageNode"))
          (Val #t.pid)) (Val #d)) (Val #fn)) {{ Φ }} : IProp GF) := by
  obtain ⟨-, B0, hB0, hclean, -, -, hnsl, hvw⟩ := id hloc
  rw [hB] at hB0; cases hB0
  have hnmnn := bktLocalOK_nm_nonnull X bl B hloc hB
  iintro #Hacc #Hcb
  iloeb as IH
  iintro %t %ps %d %Ht %Φ HI HΦ
  obtain ⟨hlt, hpre⟩ := Ht
  rcases t with ⟨pid, lf, ws, cs⟩
  have hx : ltree X bl pid = some (lf, ws) := by
    cases lf <;> simp only [ltIs] at hlt <;> exact hlt.1
  have hpq : (ps ++ [pid]) <+: Q := by
    refine List.IsPrefix.trans ?_ hpre
    cases lf <;> simp [RTree.pos]
  have hpid : pid ∈ Q := hpq.subset (by simp)
  rw [show (RTree.mk pid lf ws cs).pid = pid from rfl]
  wp_method_call; wp_call
  wp_auto
  icases walk_open K tx r m X bl B I _ $$ Hacc HI with ⟨%Y, Hw, %Hs, Hback⟩
  icases wtxW_pkgInit K tx r m Y $$ Hw with ⟨Hw, #Hpkg⟩
  ihave #Hcom : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common $$ []
  · iPkgInit
  ihave %Hmax := wtxW_page_maxMap K tx r m Y $$ Hw
  obtain ⟨-, -, hlY, B', hB', hib', -, hnm', -⟩ := id Hs
  icases wtxW_nodes_nonnull K tx r m Y bl B' hB' $$ Hw with ⟨Hw, %Hnodes⟩
  wp_apply hpn K tx r m Y bl B' pid hB' hlY (fun h => by rw [hib'] at h; exact absurd h h0)
    (fun h => absurd h Hnodes) (by rw [hnm']; exact hnmnn)
    (walk_pn_pre X Y bl B B' pid _ Hs hB' hB h0 hvw hx (hpm pid hpid) Hmax) $$ [Hw]
    as %p %n ⟨Hw, %Hpn⟩
  · iexact Hw
  have hpr := walk_posRef Hs hB' pid p n Hpn
  ihave HI := Hback $$ Hw
  isimp only [walkCb] at Hcb
  ihave #Hf := Hcb $$ %ps %pid %p %n %d
  wp_apply Hf $$ [HI] as HI
  · iframe; ipureintro; exact ⟨hpq, hpr⟩
  unfold posRef at hpr
  cases hres : resolve B pid with
  | some l =>
    rw [hres] at hpr
    obtain ⟨rfl, rfl⟩ := hpr
    obtain ⟨rn, hrn, hlnn, -, hxe⟩ := walk_node X bl B pid n _ hB hclean h0 hres hx
    simp only [Prod.mk.injEq] at hxe
    obtain ⟨hlf, hws⟩ := hxe
    wp_auto
    icases walk_node_acc K tx r m X bl B I n rn hrn (ps ++ [pid]) $$ Hacc HI
      with ⟨%r', %Hr', Ho, Hob⟩
    obtain ⟨hr1, hr2, hr3, hr4⟩ := Hr'
    isimp only [objOwn] at Ho
    icases Ho with ⟨Hn, Hins, Hcapn, Hws, Hch, Hchcap, Hnk⟩
    icases typedPointsto_not_null_dup _ _ _ $$ Hn with ⟨Hn, %Hnn⟩
    ihave %Hinl := ownSlice_len _ _ _ $$ Hins
    ihave %Hwl := BigSepL2.bigSepL2_length $$ Hws
    icases typedPointsto_split _ _ _ $$ Hn with Hn
    isimp only [TypedPointsto.typedPointstoDef, named] at Hn
    icases Hn with ⟨bucket, isLeaf, unbalanced, spilled, key, pgid, parent, children, inodes, -⟩
    wp_auto
    rw [hr1, ← hlf]
    cases lf with
    | true =>
      wp_auto
      ihave Hn : (n ↦ r'.nv : IProp GF) $$ [bucket isLeaf unbalanced spilled key pgid parent children inodes]
      · iapply typedPointsto_combine _ _ _ Hnn
        simp only [TypedPointsto.typedPointstoDef]
        rw [hr1, hr4, ← hlf]
        iframe
      ihave HI := Hob $$ [Hn Hins Hcapn Hws Hch Hchcap Hnk]
      · simp only [objOwn]; iframe
      iapply HΦ
      simp only [RTree.pos]
      iexact HI
    | false =>
      simp only [ltIs] at hlt
      have hcl := ltIsL_len _ _ _ _ hlt.2
      wp_auto
      rw [hr4]
      ihave Hn : (n ↦ r'.nv : IProp GF) $$ [bucket isLeaf unbalanced spilled key pgid parent children inodes]
      · iapply typedPointsto_combine _ _ _ Hnn
        simp only [TypedPointsto.typedPointstoDef]
        rw [hr1, hr4, ← hlf]
        iframe
      ihave HI := Hob $$ [Hn Hins Hcapn Hws Hch Hchcap Hnk]
      · simp only [objOwn]; rw [hr4]; iframe
      rw [hr4, hr3] at Hinl
      rw [hr2, hr3] at Hwl
      simp only [RTree.pos] at hpre
      ihave HL : (∃ j : w64, "i" ∷ i_ptr ↦ j ∗
          "HI" ∷ I (ps ++ pid :: RTree.posL (cs.take (sint.nat j))) ∗
          "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z rn.nv.inodes'.len⌝ : IProp GF) $$ [i HI]
      · iexists W64 0
        simp only [named]
        rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero]
        simp only [RTree.posL]
        iframe
        ipureintro; constructor <;> word
      wp_for HL
      wp_if_destruct
      · have Hlt : sint.Z j < sint.Z rn.nv.inodes'.len := by
          refine Classical.byContradiction fun h => ?_; simp [h] at Hif
        have Hjn : (sint.Z j).toNat < rn.ins.length := by rw [Hinl.1]; word
        rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hj.1, Hlt⟩)]
        list_elem rn.ins (sint.Z j).toNat as it
        list_elem rn.ws (sint.Z j).toNat as w
        have Hcj : (sint.Z j).toNat < cs.length := by rw [hcl, hws, ← Hwl]; exact Hjn
        list_elem cs (sint.Z j).toNat as c
        icases walk_node_acc K tx r m X bl B I n rn hrn _ $$ Hacc HI with ⟨%r'', %Hr'', Ho, Hob⟩
        obtain ⟨-, hq2, hq3, hq4⟩ := Hr''
        isimp only [objOwn] at Ho
        icases Ho with ⟨Hn, Hins, Hcapn, Hws, Hch, Hchcap, Hnk⟩
        rw [hq2, hq3, hq4]
        icases ownSlice_elem_acc (sint.Z j) it _ _ rn.ins Hj.1 Hit_lookup $$ Hins with ⟨Hit, Hsb⟩
        icases BigSepL2.bigSepL2_lookup_acc Hit_lookup Hw_lookup $$ Hws with ⟨Hw1, Hwsback⟩
        isimp only [wOwn] at Hw1
        icases Hw1 with ⟨%Hfp, Hwr⟩
        ihave Hws := Hwsback $$ [Hwr]
        · isimp only [wOwn]; iframe; ipureintro; exact Hfp
        wp_auto
        ihave Hins := Hsb $$ Hit
        rw [list_set_lookup_self _ _ _ Hit_lookup]
        ihave HI := Hob $$ [Hn Hins Hcapn Hws Hch Hchcap Hnk]
        · simp only [objOwn]; rw [hq2, hq3, hq4]; iframe
        wp_apply hIP $$ [inode] as inode
        · iframe
        obtain ⟨w', hw', hcp, hcl'⟩ := ltIsL_get _ _ _ _ hlt.2 _ c Hc_lookup
        rw [hws, Hw_lookup] at hw'
        cases hw'
        have hcpid : it.pgid' = c.pid := by rw [Hfp.2, hcp]
        rw [hcpid]
        obtain ⟨hpre', heq⟩ := walk_child_pre ps pid cs Q _ c Hc_lookup hpre
        have hh : ltIs (ltree X) bl c ∧
            (ps ++ pid :: RTree.posL (cs.take (sint.Z j).toNat) ++ c.pos) <+: Q := ⟨hcl', hpre'⟩
        rw [method_unfold]
        wp_apply IH $$ %c %(ps ++ pid :: RTree.posL (cs.take (sint.Z j).toNat)) %(d + W64 1)
          %hh [HI] as HI
        · iexact HI
        wp_for_post
        iframe
        iexists j + W64 1
        simp only [named]
        rw [show sint.nat (j + W64 1) = (sint.Z j).toNat + 1 by word, ← heq]
        iframe
        ipureintro; constructor <;> word
      · have Hge : ¬ sint.Z j < sint.Z rn.nv.inodes'.len := by
          intro h; simp [h] at Hif
        have Heq : sint.nat j = cs.length := by rw [hcl, hws, ← Hwl, Hinl.1]; word
        try wp_auto
        rw [Heq, List.take_length]
        iapply HΦ
        simp only [RTree.pos]
        iexact HI
  | none =>
    rw [hres] at hpr
    obtain ⟨rfl, pg0, hw0⟩ := hpr
    obtain ⟨pg, hpg, hw, hxe⟩ := walk_page X bl B pid _ hB h0 hres hx
    rw [hw] at hw0
    simp only [Option.some.injEq, Prod.mk.injEq] at hw0
    obtain ⟨rfl, -⟩ := hw0
    simp only [Prod.mk.injEq] at hxe
    obtain ⟨hlf, hws⟩ := hxe
    subst hlf hws
    obtain ⟨-, -, h4096, hfl⟩ := Read.viewWF_page X.v hvw _ pg hpg
    icases walk_bytes K tx r m X bl B I pid.toNat pg hpg (ps ++ [pid]) $$ Hacc HI
      with ⟨%dq, Hp, Hpb⟩
    icases Read.bytesPointsto_bounds _ dq pg (by intro e; simp [e] at h4096) $$ Hp with ⟨Hp, %Hlb⟩
    have hlnn : pageLoc X.v pid.toNat ≠ null := by intro e; rw [e] at Hlb; simp [null] at Hlb
    rw [decide_eq_false hlnn]
    wp_auto
    icases bytesPointsto_view_read (V := Page) (pageLoc X.v pid.toNat) dq pg 0 (pageLoc X.v pid.toNat) (by simp [loc_add_0]) (by omega) Hlb.1 $$ Hp
      with ⟨Hh, Hhb⟩
    rw [show (decode (List.take 16 (List.drop 0 pg)) : Page) = pageHdr pg from rfl]
    wp_apply hIB $$ [Hh] as Hh
    · iframe #; iexact Hh
    ihave Hp := Hhb $$ Hh
    ihave HI := Hpb $$ Hp
    have hfz : pageFlags pg = (pageHdr pg).flags'.toNat := rfl
    rcases hfl with hbr | hlf
    · -- a branch page
      have hf1 : (pageHdr pg).flags' = W16 1 := by
        apply BitVec.eq_of_toNat_eq; rw [← hfz, hbr]; rfl
      have hnl : ¬ pageFlags pg = leafPageFlag := by rw [hbr]; decide
      rw [hf1]
      have hdf : decide (pageFlags pg = leafPageFlag) = false := decide_eq_false hnl
      rw [hdf] at hlt hpre
      rw [hdf]
      simp only [ltIs] at hlt
      simp only [RTree.pos] at hpre ⊢
      have hcl := ltIsL_len _ _ _ _ hlt.2
      rw [pageWs_length] at hcl
      obtain ⟨hwm, hbwf⟩ := viewWF_branch X.v hvw _ pg hpg hbr
      have hcnt := hbwf.2.2.1
      have hcz : uint.Z (pageHdr pg).count' = (pageCount pg : Int) := rfl
      have hcnt16 : pageCount pg < 2 ^ 16 := by unfold pageCount; exact BitVec.isLt _
      wp_auto
      ihave HL : (∃ j : w64, "i" ∷ i_ptr ↦ j ∗
          "HI" ∷ I (ps ++ pid :: RTree.posL (cs.take (sint.nat j))) ∗
          "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ (pageCount pg : Int)⌝ : IProp GF) $$ [i HI]
      · iexists W64 0
        simp only [named]
        rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero]
        simp only [RTree.posL]
        iframe
        ipureintro; constructor <;> word
      wp_for HL
      icases walk_bytes K tx r m X bl B I pid.toNat pg hpg _ $$ Hacc HI with ⟨%dq1, Hp, Hpb⟩
      icases bytesPointsto_view_read (V := Page) (pageLoc X.v pid.toNat) dq1 pg 0 (pageLoc X.v pid.toNat) (by simp [loc_add_0]) (by omega) Hlb.1 $$ Hp
        with ⟨Hh, Hhb⟩
      rw [show (decode (List.take 16 (List.drop 0 pg)) : Page) = pageHdr pg from rfl]
      wp_apply hCnt $$ [Hh] as Hh
      · iframe #; iexact Hh
      ihave Hp := Hhb $$ Hh
      ihave HI := Hpb $$ Hp
      have h1 : sint.Z (W64 (uint.Z (pageHdr pg).count')) = (pageCount pg : Int) := by
        rw [hcz]; word
      rw [h1]
      wp_if_destruct
      · have Hlt : sint.Z j < (pageCount pg : Int) := by
          refine Classical.byContradiction fun h => ?_
          simp [h, intoVal_eq_iff] at Hif
        obtain ⟨k, hk⟩ : ∃ k : Nat, sint.Z j = (k : Int) := ⟨(sint.Z j).toNat, by omega⟩
        have hkc : k < pageCount pg := by omega
        list_elem cs k as c
        have hw16 : uint.Z (W16 (sint.Z j)) = (k : Int) := by rw [hk]; word
        wp_apply hBE _ (W16 (sint.Z j)) Hlb.1 (by rw [hw16]; unfold elemOff at hcnt; omega)
        try wp_auto
        icases walk_bytes K tx r m X bl B I pid.toNat pg hpg _ $$ Hacc HI with ⟨%dq2, Hp, Hpb⟩
        have hloc : pageLoc X.v pid.toNat +ₗ (16 + 16 * uint.Z (W16 (sint.Z j))) =
            pageLoc X.v pid.toNat +ₗ ((elemOff k : Nat) : Int) := by
          rw [hw16]; unfold elemOff; push_cast; rfl
        icases bytesPointsto_view_read (V := branchPageElement) _ dq2 pg (elemOff k) _ hloc
          (by unfold elemOff at hcnt ⊢; omega) Hlb.1 $$ Hp with ⟨He, Heb⟩
        rw [show (decode (List.take 16 (List.drop (elemOff k) pg)) : branchPageElement) =
          branchElem pg k from rfl]
        wp_apply hBP $$ [He] as He
        · iframe #; iexact He
        ihave Hp := Heb $$ He
        ihave HI := Hpb $$ Hp
        obtain ⟨w', hw', hcp, hcl'⟩ := ltIsL_get _ _ _ _ hlt.2 _ c Hc_lookup
        rw [pageWs_get pg k hkc] at hw'
        cases hw'
        have hcpid : (branchElem pg k).pgid' = c.pid := by
          rw [hcp, (pageW_branch pg k hbr).2]
          apply BitVec.eq_of_toNat_eq; simp [branchPgid]
        rw [hcpid]
        have hjk : (sint.Z j).toNat = k := by omega
        obtain ⟨hpre', heq⟩ := walk_child_pre ps pid cs Q k c Hc_lookup hpre
        have hh : ltIs (ltree X) bl c ∧
            (ps ++ pid :: RTree.posL (cs.take k) ++ c.pos) <+: Q := ⟨hcl', hpre'⟩
        rw [method_unfold]
        wp_apply IH $$ %c %(ps ++ pid :: RTree.posL (cs.take k)) %(d + W64 1)
          %hh [HI] as HI
        · rw [show sint.nat j = k from hjk]; iexact HI
        wp_for_post
        iframe
        iexists j + W64 1
        simp only [named]
        rw [show sint.nat (j + W64 1) = k + 1 by word, ← heq]
        iframe
        ipureintro; constructor <;> word
      · have Heq : sint.nat j = cs.length := by
          have : ¬ sint.Z j < (pageCount pg : Int) := by intro h; simp [h] at Hif
          rw [hcl]; word
        have hge : ¬ sint.Z j < (pageCount pg : Int) := by intro h; simp [h] at Hif
        simp only [hge, decide_false, Bool.false_eq_true, ↓reduceIte]
        try wp_auto
        rw [Heq, List.take_length]
        iapply HΦ
        iexact HI
    · -- a leaf page
      have hf2 : (pageHdr pg).flags' = W16 2 := by
        apply BitVec.eq_of_toNat_eq; rw [← hfz, hlf]; rfl
      rw [hf2]
      wp_auto
      iapply HΦ
      rw [decide_eq_true hlf]
      simp only [RTree.pos]
      iexact HI

end walk

end Write

end bbolt
end EtcdGrove
end Perennial
