/-
U7n (`notes/bbolt-proof-plan.md`): **the walk of a dead bucket**, `Bucket._forEachPageNode` and
`Bucket.forEachPageNode` of `DeleteBucket`'s child after `child.nodes = nil` and
`child.rootNode = nil` (in `X.t.deadB`, its record `B`, nil node cache, a root page): over a
finite tree `t` of the view's page tree (`pltree`), the walk calls its callback at each position of
`t` in pre-order with the position's page (a nil node), over an invariant `I` holding the
writer's state `X`, unchanged (`walkAccD`). The page branch of `Write/Walk.walk_aux`, with
`Bucket.pageNode_d` for `pageNode`.
-/
module

public import Proof.go_etcd_io.bbolt.Write.Walk
public import Proof.go_etcd_io.bbolt.Write.WalkDeadDefs
public import Spec.go_etcd_io.bbolt.Bucket__pageNode_d
public import Proof.go_etcd_io.bbolt.Rebalance.Heap
public import Proof.go_etcd_io.bbolt.Spill.DerefHeap

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

namespace Write

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section walkd
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- A dead bucket's object, out of `wtxW` and back unchanged. -/
theorem wtxW_dead_obj_acc (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (bl : Loc)
    (B : BRec) (hbs : X.t.bs !! bl = none) (hd : X.t.deadB !! bl = some B) :
    wtxW (GF := GF) K tx r m X ⊢
      objOwn X.v bl (DFrac.own 1) (decide (bl ∈ X.liveB)) (.bkt B) ∗
      (objOwn X.v bl (DFrac.own 1) (decide (bl ∈ X.liveB)) (.bkt B) -∗ wtxW K tx r m X) := by
  unfold wtxW wtxCore
  iintro ⟨⟨Hpkg, Hcore, %Hr, Hreg, Hh, Hfills, Hbk, Hnl, Hdb, Hview, Hst⟩, Hcells, Hmap⟩
  icases wtxHeap_bkt_obj_acc tx (DFrac.own 1) X bl B (bobjs_dead X.t bl B hbs hd) $$ Hh
    with ⟨Ho, Hback⟩
  iframe Ho
  iintro Ho
  ihave Hh := Hback $$ Ho
  iframe; ipureintro; exact Hr

/-- **A dead bucket's object, out and back with a new record** (`X.setDead`). -/
theorem wtxW_dead_acc (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (bl : Loc)
    (B : BRec) (hbs : X.t.bs !! bl = none) (hd : X.t.deadB !! bl = some B) :
    wtxW (GF := GF) K tx r m X ⊢
      objOwn X.v bl (DFrac.own 1) (decide (bl ∈ X.liveB)) (.bkt B) ∗
      (∀ B', objOwn X.v bl (DFrac.own 1) (decide (bl ∈ X.liveB)) (.bkt B') -∗
        wtxW K tx r m (X.setDead bl B')) := by
  iintro Hw
  icases wtxW_open K tx r m X $$ Hw with ⟨-, -, -, Hh, Hv, Hst, Hwback⟩
  unfold wtxHeap
  icases Hh with ⟨%Hok, Hf, Hrf, Hm, Hbk⟩
  have Ho := bobjs_dead X.t bl B hbs hd
  icases (BigSepM.bigSepM_delete (M := GMap Loc) Ho).1 $$ Hbk with ⟨Hb, Hbk⟩
  iframe Hb
  iintro %B' Hb
  iapply Hwback $$ %(X.setDead bl B') [] [Hf Hrf Hm Hbk Hb] Hv Hst
  · ipureintro; exact ⟨rfl, rfl, rfl⟩
  isplitr
  · ipureintro; exact Hok
  isplitl [Hf]
  · unfold txFields WX.setDead; iexact Hf
  isplitl [Hrf]
  · iexact Hrf
  rw [bobjs_setDead X bl B' hbs]
  have hv : (X.setDead bl B').v = X.v := rfl
  have hlv : (X.setDead bl B').live = X.live := rfl
  have hlvB : (X.setDead bl B').liveB = X.liveB := rfl
  have hob : (X.setDead bl B').t.objs = X.t.objs := rfl
  simp only [hv, hlv, hlvB, hob]
  isplitl [Hm]
  · iexact Hm
  iapply (BigSepM.bigSepM_insert_delete (M := GMap Loc)).2
  iframe

/-- The dead walk's accessor: `I` holds the writer's state `X`. -/
def walkAccD (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (I : List w64 → IProp GF) :
    IProp GF :=
  iprop(□ ∀ ps, I ps -∗ wtxW K tx r m X ∗ (wtxW K tx r m X -∗ I ps))

instance walkAccD_persistent (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX)
    (I : List w64 → IProp GF) : Persistent (walkAccD K tx r m X I) := by
  unfold walkAccD; infer_instance

/-- The dead walk's callback: at position `pid` (`ps ++ [pid]` a prefix of `Q`), with its page,
from `I ps` to `I (ps ++ [pid])`. -/
def walkCbD (X : WX) (I : List w64 → IProp GF) (Q : List w64) (fn : GoFunc) : IProp GF :=
  iprop(□ ∀ (ps : List w64) (pid : w64) (pg : List w8) (d : w64),
    {{ I ps ∗ ⌜(ps ++ [pid]) <+: Q ∧ X.v.pages !! pid.toNat = some pg⌝ }}
      (App (App (App (Val #fn) (Val #(pageLoc X.v pid.toNat))) (Val #null)) (Val #d))
    {{ RET #(); I (ps ++ [pid]) }})

instance walkCbD_persistent (X : WX) (I : List w64 → IProp GF) (Q : List w64) (fn : GoFunc) :
    Persistent (walkCbD X I Q fn) := by
  unfold walkCbD; infer_instance

theorem walkD_open (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX)
    (I : List w64 → IProp GF) (ps : List w64) :
    walkAccD K tx r m X I ⊢ I ps -∗ wtxW K tx r m X ∗ (wtxW K tx r m X -∗ I ps) := by
  unfold walkAccD
  iintro #Hacc HI
  iapply Hacc $$ HI

theorem walkD_bytes (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX)
    (I : List w64 → IProp GF) (id : Nat) (pg : List w8) (hpg : X.v.pages !! id = some pg)
    (ps : List w64) :
    walkAccD K tx r m X I ⊢ I ps -∗ ∃ dq : DFrac, bytesPointsto (pageLoc X.v id) dq pg ∗
      (bytesPointsto (pageLoc X.v id) dq pg -∗ I ps) := by
  unfold walkAccD
  iintro #Hacc HI
  icases Hacc $$ HI with ⟨Hw, Hback⟩
  icases wtxW_cells_acc K tx r m X $$ Hw with ⟨-, Hc, Hwb⟩
  icases viewCells_page_acc wq X.v id pg hpg $$ Hc with ⟨Hp, Hcb⟩
  iexists DFrac.own wq
  iframe Hp
  iintro Hp
  iapply Hback
  iapply Hwb
  iapply Hcb $$ Hp

theorem pltree_page (v : View) (bl : Loc) (pid : w64) (x : Bool × List WEntry)
    (h : pltree v bl pid = some x) :
    ∃ pg, v.pages !! pid.toNat = some pg ∧ x = (decide (pageFlags pg = leafPageFlag), pageWs pg) := by
  unfold pltree at h
  cases hpg : v.pages !! pid.toNat with
  | none => rw [hpg] at h; cases h
  | some pg => rw [hpg] at h; simp only [Option.map_some, Option.some.injEq] at h; exact ⟨pg, rfl, h.symm⟩

theorem walk_aux_dead (hpnd : Bucket.pageNode_d.spec (GF := GF) (hG := hG))
    (hIB : internal.common.Page.IsBranchPage.spec (GF := GF) (hG := hG))
    (hCnt : internal.common.Page.Count.spec (GF := GF) (hG := hG))
    (hBE : internal.common.Page.BranchPageElement.spec (GF := GF) (hG := hG))
    (hBP : internal.common.branchPageElement.Pgid.spec (GF := GF) (hG := hG))
    (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (bl : Loc) (B : BRec)
    (I : List w64 → IProp GF) (Q : List w64) (fn : GoFunc)
    (hbs : X.t.bs !! bl = none) (hd : X.t.deadB !! bl = some B) (hlive : bl ∉ X.liveB)
    (htx : B.bv.tx' = tx) (hnil : B.bv.nodes' = null) (h0 : B.ib.root' ≠ W64 0)
    (hvw : viewWF X.v) (hpm : ∀ pid ∈ Q, X.t.pm !! pid = none) :
    ⊢ (walkAccD K tx r m X I -∗ walkCbD X I Q fn -∗
      ∀ (t : RTree) (ps : List w64) (d : w64), ⌜ltIs (pltree X.v) bl t ∧ (ps ++ t.pos) <+: Q⌝ -∗
        ∀ Φ, I ps -∗ ▷ (I (ps ++ t.pos) -∗ Φ #()) -∗
        WP (App (App (App (Val (bl @!! go.GoType.PointerType Bucket.ty @!! go!"_forEachPageNode"))
          (Val #t.pid)) (Val #d)) (Val #fn)) {{ Φ }} : IProp GF) := by
  iintro #Hacc #Hcb
  iloeb as IH
  iintro %t %ps %d %Ht %Φ HI HΦ
  obtain ⟨hlt, hpre⟩ := Ht
  rcases t with ⟨pid, lf, ws, cs⟩
  have hx : pltree X.v bl pid = some (lf, ws) := by
    cases lf <;> simp only [ltIs] at hlt <;> exact hlt.1
  have hpq : (ps ++ [pid]) <+: Q := by
    refine List.IsPrefix.trans ?_ hpre
    cases lf <;> simp [RTree.pos]
  have hpid : pid ∈ Q := hpq.subset (by simp)
  obtain ⟨pg, hpg, hxe⟩ := pltree_page X.v bl pid _ hx
  simp only [Prod.mk.injEq] at hxe
  obtain ⟨hlf, hws⟩ := hxe
  subst hlf hws
  obtain ⟨-, hidp, h4096', hfl'⟩ := Read.viewWF_page X.v hvw _ pg hpg
  rw [show (RTree.mk pid _ _ cs).pid = pid from rfl]
  wp_method_call; wp_call
  wp_auto
  icases walkD_open K tx r m X I ps $$ Hacc HI with ⟨Hw, Hback⟩
  icases wtxW_pkgInit K tx r m X $$ Hw with ⟨Hw, #Hpkg⟩
  ihave #Hcom : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common $$ []
  · iPkgInit
  wp_apply hpnd K tx r m X bl B pid pg hbs hd hlive htx hnil h0 hpg (hpm pid hpid) (by omega)
    hidp hfl' $$ [Hw] as Hw
  · iexact Hw
  ihave HI := Hback $$ Hw
  isimp only [walkCbD] at Hcb
  ihave #Hf := Hcb $$ %ps %pid %pg %d
  wp_apply Hf $$ [HI] as HI
  · iframe; ipureintro; exact ⟨hpq, hpg⟩
  obtain ⟨-, -, h4096, hfl⟩ := Read.viewWF_page X.v hvw _ pg hpg
  icases walkD_bytes K tx r m X I pid.toNat pg hpg (ps ++ [pid]) $$ Hacc HI
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
    icases walkD_bytes K tx r m X I pid.toNat pg hpg _ $$ Hacc HI with ⟨%dq1, Hp, Hpb⟩
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
      icases walkD_bytes K tx r m X I pid.toNat pg hpg _ $$ Hacc HI with ⟨%dq2, Hp, Hpb⟩
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
      have hh : ltIs (pltree X.v) bl c ∧
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

/-- **`b.forEachPageNode(fn)` of a dead bucket with a root page**: its page field nil, the walk
from its root, over a finite tree `t` of the view's page tree. -/
theorem forEachPageNode_dead (hpnd : Bucket.pageNode_d.spec (GF := GF) (hG := hG))
    (hRP : internal.common.InBucket.RootPage.spec (GF := GF) (hG := hG))
    (hIB : internal.common.Page.IsBranchPage.spec (GF := GF) (hG := hG))
    (hCnt : internal.common.Page.Count.spec (GF := GF) (hG := hG))
    (hBE : internal.common.Page.BranchPageElement.spec (GF := GF) (hG := hG))
    (hBP : internal.common.branchPageElement.Pgid.spec (GF := GF) (hG := hG))
    (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (bl : Loc) (B : BRec)
    (I : List w64 → IProp GF) (Q : List w64) (fn : GoFunc) (t : RTree)
    (hbs : X.t.bs !! bl = none) (hd : X.t.deadB !! bl = some B) (hlive : bl ∉ X.liveB)
    (htx : B.bv.tx' = tx) (hnil : B.bv.nodes' = null) (h0 : B.ib.root' ≠ W64 0)
    (hpg0 : B.bv.page' = null) (hvw : viewWF X.v) (hpm : ∀ pid ∈ Q, X.t.pm !! pid = none)
    (ht : ltIs (pltree X.v) bl t) (htp : t.pid = B.ib.root') (hQ : t.pos <+: Q) :
    ⊢ walkAccD K tx r m X I -∗ walkCbD X I Q fn -∗
      ∀ Φ, I [] -∗ ▷ (I t.pos -∗ Φ #()) -∗
      WP (App (Val (bl @!! go.GoType.PointerType Bucket.ty @!! go!"forEachPageNode")) (Val #fn))
        {{ Φ }} := by
  iintro #Hacc #Hcb %Φ HI HΦ
  wp_method_call; wp_call
  wp_auto
  icases walkD_open K tx r m X I [] $$ Hacc HI with ⟨Hw, Hback⟩
  icases wtxW_pkgInit K tx r m X $$ Hw with ⟨Hw, #Hpkg⟩
  ihave #Hcom : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common $$ []
  · iPkgInit
  icases wtxW_dead_obj_acc K tx r m X bl B hbs hd $$ Hw with ⟨Ho, Hwb⟩
  rw [decide_eq_false hlive]
  isimp only [objOwn] at Ho
  icases Ho with ⟨HIB, Htx, Hbks, Hpage, Hroot, Hnodes, Hib, Hnm, Hbm, Hpo⟩
  wp_auto
  rw [decide_eq_true hpg0]
  wp_auto
  wp_method_call
  try wp_call
  try wp_auto
  wp_apply hRP $$ [Hib] as Hib
  · iframe
  ihave Hw := Hwb $$ [HIB Htx Hbks Hpage Hroot Hnodes Hib Hnm Hbm Hpo]
  · simp only [objOwn]; iframe
  ihave HI := Hback $$ Hw
  have hh : ltIs (pltree X.v) bl t ∧ ([] ++ t.pos) <+: Q := ⟨ht, by simpa using hQ⟩
  ihave #Hwk := walk_aux_dead hpnd hIB hCnt hBE hBP K tx r m X bl B I Q fn hbs hd hlive htx hnil
    h0 hvw hpm $$ Hacc Hcb
  rw [← htp]
  wp_apply Hwk $$ %t %([] : List w64) %(W64 0) %hh [HI] as HI
  · iexact HI
  iapply HΦ
  simp only [List.nil_append]
  iexact HI

end walkd

end Write

end bbolt
end EtcdGrove
end Perennial
