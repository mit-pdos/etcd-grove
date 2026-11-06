/-
**`Cursor.node`'s `matReady` premise along a search path** (U7i, `notes/bbolt-proof-plan.md`;
`Bucket.Put`'s and `Bucket.Delete`'s `c.node()`, on any bucket of a `wOK` writer): every
unmaterialized position of a logical stack can be materialized. A file bucket's positions are view
pages (`path_ready`, then `Spill/BktLoopHeap.wtxW_matReady_all`'s argument, `Inv/MatReady`); an
inline bucket's only position is its inline page (`matReady_inline`: `bktClean`'s `inlineGood`, and
its bytes' bounds from their source, `wtxW_inline_bounds`). `wtxW_matReady_path` combines them.
-/
module

public import Proof.go_etcd_io.bbolt.Inv.MatReady
public import Proof.go_etcd_io.bbolt.Read.WQ
public import Proof.go_etcd_io.bbolt.Read.WOpenOK

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

/-- **An inline bucket's page can be materialized** (pure): its page is good (`bktClean`), not in
the page cache, at a location whose bytes lie in `(0, maxAddr]`. -/
theorem matReady_inline (X : WX) (bl : Loc) (B : BRec) (hc : bktClean X.v X.t.mv.pgid'.toNat bl B)
    (h0 : B.ib.root' = W64 0) (hrn : B.bv.rootNode' = null) (hpm : X.t.pm !! W64 0 = none)
    (hbnd : 0 < B.bv.page'.addr ∧ B.bv.page'.addr + B.ipg.length ≤ maxAddr) :
    matReady X B (W64 0) := by
  obtain ⟨-, hsrc, hg, -⟩ := hc.1 h0 hrn
  obtain ⟨hid, hf, hl, -, hgood⟩ := hg
  refine ⟨B.bv.page', B.ipg, by simp [wpageAt, h0], ⟨?_, fun i hi => ⟨?_, ?_⟩⟩, Or.inl hf,
    leafWF_elemsIn _ _ hl hf, ?_, hpm, fun _ => ?_, hbnd.1, hbnd.2, fun i hi => ?_⟩
  · have := hl.1; have := hl.2.1; omega
  · simp only [hf, ite_true]; exact (hgood i hi).1
  · simp only [elemEnd, hf, ite_true]; exact (hl.2.2.1 i hi).2
  · apply BitVec.eq_of_toNat_eq; exact hid
  · rcases hsrc with ⟨-, h⟩ | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr ⟨_, h⟩
  · have := leafWF_elemsIn _ _ hl hf i hi; omega

/-- **A file bucket's unmaterialized path positions are view pages** (not in the empty page
cache). -/
theorem path_ready (X : WX) (bl : Loc) (B : BRec) (hok : wOK X) (hB : X.t.bs !! bl = some B)
    (hloc : bktLocalOK X bl) (els : List elemRef) (pids : List w64) (hp : lPath X bl els pids)
    (h0 : B.ib.root' ≠ W64 0) :
    ∀ pid ∈ pids, resolve B pid = none →
      ∃ pg, X.v.pages !! pid.toNat = some pg ∧ X.t.pm !! pid = none := by
  intro pid hpid hres
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hpid
  have hI := WOpen.lPath_posI X bl B hB hloc els pids hp j pid hj
  have hpm : X.t.pm !! pid = none := by rw [hok.1.2.1.1]; rfl
  rcases hI with ⟨l, rn, hr, -⟩ | ⟨h0', -, -⟩ | ⟨-, ht, -, -, -⟩
  · rw [hr] at hres; cases hres
  · exact absurd h0' h0
  · obtain ⟨pg, hpg, -⟩ := WOpen.treeWF_page ht
    exact ⟨pg, hpg, hpm⟩

/-- **A leaf of a non-root bucket's logical tree holds plain entries** (a node's by `leafShape`,
the inline page's by `inlineGood`, a view page's by `posShape`): `Put`'s and `Delete`'s
`ErrIncompatibleValue` branch is unreachable. -/
theorem leaf_plain_nonroot (X : WX) (bl : Loc) (B : BRec) (hok : wOK X)
    (hB : X.t.bs !! bl = some B) (hroot : bl ≠ X.rl) (p : w64) (hI : WOpen.posI X B p)
    (ws : List WEntry) (hL : ltree X bl p = some (true, ws)) (w : WEntry) (hw : w ∈ ws) :
    ¬ isBktFlag w.flags := by
  have hc := (hok.1.2.2.2.2.2 bl B hB).1
  intro hf
  rcases hI with ⟨l, rn, hres, hrn⟩ | ⟨h0, hrn, rfl⟩ | ⟨hi, ht, hnm, ⟨c, hpr, hown⟩, -⟩
  · rw [ltree_node X bl B p l rn hB hres hrn] at hL
    simp only [Option.some.injEq, Prod.mk.injEq] at hL
    obtain ⟨hlf, rfl⟩ := hL
    exact hroot ((hok.1.2.1.2.2.1 bl B hB l rn hrn hlf w hw).1 hf)
  · have hres : resolve B (W64 0) = none := by simp [resolve, h0, hrn]
    have hwp : wpageAt X.v B (W64 0) = some (B.bv.page', B.ipg) := by simp [wpageAt, h0]
    rw [ltree_page X bl B _ _ _ hB hres hwp] at hL
    simp only [Option.some.injEq, Prod.mk.injEq] at hL
    obtain ⟨-, rfl⟩ := hL
    obtain ⟨-, -, hg, -⟩ := hc.1 h0 hrn
    unfold pageWs at hw
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hw
    have hi' := List.mem_range.1 hi
    unfold pageW at hf
    rw [if_pos hg.2.1] at hf
    have := WOpen.isBktFlag_mod _ hf
    rw [(hg.2.2.2.2 i hi').2] at this; cases this
  · obtain ⟨hres, pg, hpg, hwp, -⟩ := posOK_tree_page X B p hi ht hnm
    rw [ltree_page X bl B _ _ _ hB hres hwp] at hL
    simp only [Option.some.injEq, Prod.mk.injEq] at hL
    obtain ⟨hfl, rfl⟩ := hL
    have hfl' : pageFlags pg = leafPageFlag := of_decide_eq_true hfl
    unfold pageWs at hw
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hw
    have hi' := List.mem_range.1 hi
    unfold pageW at hf
    rw [if_pos hfl'] at hf
    have h1 := WOpen.isBktFlag_mod _ hf
    have := ((hok.1.2.1.2.2.2.1 bl B hB c p.toNat pg hpr hown hpg hfl' i hi').1).1
    exact hroot (this (by rw [h1]; rfl))

end pure

section iris
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **An inline bucket's page lies in `(0, maxAddr]`** (its bytes, from their source: the view's
cells or persistent heap bytes). -/
theorem wtxW_inline_bounds (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (bl : Loc)
    (B : BRec) (hb : X.t.bs !! bl = some B) (hl : bl ∈ X.liveB)
    (hc : bktClean X.v X.t.mv.pgid'.toNat bl B) (h0 : B.ib.root' = W64 0)
    (hrn : B.bv.rootNode' = null) :
    wtxW (GF := GF) K tx r m X ⊢ wtxW K tx r m X ∗
      ⌜0 < B.bv.page'.addr ∧ B.bv.page'.addr + B.ipg.length ≤ maxAddr⌝ := by
  obtain ⟨hpa, hsrc, hg, -⟩ := hc.1 h0 hrn
  have hne : B.ipg ≠ [] := by
    intro e; have := hg.2.2.2.1; rw [e] at this; simp at this
  rw [← wtxWQ_one]
  iintro Hw
  icases wtxWQ_page_srcLoc K tx r m 1 X bl B (W64 0) B.bv.page' B.ipg hb hl
    (by simp [wpageAt, h0])
    (fun _ => by rcases hsrc with ⟨-, h⟩ | ⟨h, -⟩; exact Or.inl h; exact Or.inr ⟨_, h⟩)
    (fun _ => hpa) $$ Hw with ⟨Hw, #Hs⟩
  by_cases hv : B.pst = PageSt.view
  · have hps : pgSrc B = Src.view := by unfold pgSrc inlSrc; rw [if_pos h0, if_pos hv]
    isimp only [hps, srcLoc] at Hs
    icases Hs with %Hin
    icases wtxWQ_cells_acc K tx r m 1 X $$ Hw with ⟨-, Hc, Hback⟩
    icases viewCells_loc_acc _ X.v B.bv.page' B.ipg Hin $$ Hc with ⟨%dq, Hp, Hcb⟩
    ihave %Hbd := Read.bytesPointsto_in_bounds B.bv.page' dq B.ipg hne $$ Hp
    ihave Hc := Hcb $$ Hp
    ihave Hw := Hback $$ Hc
    iframe Hw
    ipureintro; exact Hbd
  · have hps : pgSrc B = Src.own DFrac.discard := by unfold pgSrc inlSrc; rw [if_pos h0, if_neg hv]
    isimp only [hps, srcLoc] at Hs
    ihave %Hbd := Read.bytesPointsto_in_bounds B.bv.page' DFrac.discard B.ipg hne $$ Hs
    iframe Hw
    ipureintro; exact Hbd

theorem keep_pure' {Q : IProp GF} {P : Prop} (h : Q ⊢ ⌜P⌝) : Q ⊢ Q ∗ ⌜P⌝ := by
  refine (BI.and_intro h .rfl).trans ?_
  refine persistent_and_affinely_sep_left_mp.trans ?_
  iintro ⟨%HP, HQ⟩
  iframe
  ipureintro; exact HP

/-- `Spill/BktLoopHeap.wtxW_matReady_all`, here (view pages of a file bucket). -/
theorem wtxW_matReady_all' (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (B : BRec)
    (pids : List w64) (hroot : B.ib.root' ≠ W64 0) (hv : viewWF X.v)
    (hp : ∀ pid ∈ pids, resolve B pid = none →
      ∃ pg, X.v.pages !! pid.toNat = some pg ∧ X.t.pm !! pid = none) :
    wtxW (GF := GF) K tx r m X ⊢ wtxW K tx r m X ∗
      ⌜∀ pid ∈ pids, resolve B pid = none → matReady X B pid⌝ := by
  apply keep_pure'
  refine (BI.forall_intro fun pid => ?_).trans BI.pure_forall.2
  by_cases hm : pid ∈ pids ∧ resolve B pid = none
  · obtain ⟨pg, hpg, hpm⟩ := hp pid hm.1 hm.2
    exact (wtxW_matReady K tx r m X B pid pg hroot hv hpg hpm).trans
      (BI.pure_mono fun h _ _ => h)
  · iintro -
    ipureintro
    intro h1 h2; exact absurd ⟨h1, h2⟩ hm

/-- **Every unmaterialized position of a search path of a `wOK` writer's bucket can be
materialized** (`Cursor.node`'s premise). -/
theorem wtxW_matReady_path (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (bl : Loc)
    (B : BRec) (hok : wOK X) (hB : X.t.bs !! bl = some B) (hloc : bktLocalOK X bl)
    (els : List elemRef) (pids : List w64) (hp : lPath X bl els pids) :
    wtxW (GF := GF) K tx r m X ⊢ wtxW K tx r m X ∗
      ⌜∀ pid ∈ pids, resolve B pid = none → matReady X B pid⌝ := by
  have hv : viewWF X.v := hok.2.2.2.2.2.2.2
  by_cases h0 : B.ib.root' = W64 0
  · have hc := (hok.1.2.2.2.2.2 bl B hB).1
    by_cases hrn : B.bv.rootNode' = null
    · iintro Hw
      icases wtxW_inline_bounds K tx r m X bl B hB hloc.1 hc h0 hrn $$ Hw with ⟨Hw, %Hbd⟩
      iframe Hw
      ipureintro
      intro pid hpid _
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hpid
      have hI := WOpen.lPath_posI X bl B hB hloc els pids hp j pid hj
      have hpid0 : pid = W64 0 := by
        rcases hI with ⟨l, rn, hr, -⟩ | ⟨-, -, e⟩ | ⟨h0', -⟩
        · unfold resolve at hr; rw [if_pos h0, if_pos hrn] at hr; cases hr
        · exact e
        · exact absurd h0 h0'
      subst hpid0
      exact matReady_inline X bl B hc h0 hrn (by rw [hok.1.2.1.1]; rfl) Hbd
    · iintro Hw
      iframe Hw
      ipureintro
      intro pid _ hres
      unfold resolve at hres; rw [if_pos h0, if_neg hrn] at hres; cases hres
  · exact wtxW_matReady_all' K tx r m X B pids h0 hv
      (path_ready X bl B hok hB hloc els pids hp h0)

end iris

end Write

end bbolt
end EtcdGrove
end Perennial
