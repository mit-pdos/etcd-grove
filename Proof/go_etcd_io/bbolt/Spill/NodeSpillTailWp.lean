/-
`node.spill` after its children's loop (U9s, `notes/bbolt-proof-plan.md`): **`spillTail`'s WP over
an abstract invariant** of the pieces' loop (`spillTail_gen`). The heap steps: `n.children = nil`
(`wtxW_nilCh`), the split (`Spill/NodeSpillSplit.splitStep_wp`), the pieces' loop (each iteration
`pieceOne_wp`), the test `n.parent != nil && n.parent.pgid == 0` and, if so, the new root's spill
(Löb's hypothesis `spillIH`). The invariant `I xs pl i Xi wi st` (the split's pieces `xs` under
the parent `pl`, iteration `i`, the state `(Xi, wi)`, the steps `st` from the spill's start) is a
parameter, with the pure facts the steps need (`H1`-`H7`): its start after the split, each
piece's premises (`pcPre`), its step (`pcStep`), an error's facts, its end, and the post (no new
root: `spDone`; a new root: its spill's pre, and its `spDone` giving `n`'s).
`Spill/NodeSpillPieces.spillTail_wp` instantiates it with the pieces' loop's invariant.
-/
module

public import Proof.go_etcd_io.bbolt.Spill.NodeSpillTailDefs
public import Proof.go_etcd_io.bbolt.Spill.NodeSpillSplit
public import Proof.go_etcd_io.bbolt.Spill.NodeSpillPiecesOne
public import Proof.go_etcd_io.bbolt.Spill.NodeSpillPiecesKill
public import Proof.go_etcd_io.bbolt.Spill.DerefCopy

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

omit hos sem package_sem in
/-- A frame `R` given back to the post. -/
theorem wp_frame_wand' (e : Expr) (Φ : val → IProp GF) (R : IProp GF) :
    R ∗ WP e {{ v, R -∗ Φ v }} ⊢ WP e {{ Φ }} := by
  iintro ⟨HR, Hwp⟩
  iapply wp_wand $$ Hwp
  iintro %v Hv
  iapply Hv $$ HR

omit package_sem in
/-- **The inodes' slices have their entries' lengths** (the sources not stale). -/
theorem wOwns_lensEq (v : View) :
    ∀ (ins : List Inode) (ws : List WEntry), wsLive ws →
    ([∗list] it;w ∈ ins;ws, wOwn (GF := GF) v true it w) ⊢ ⌜insLens ins ws⌝
  | [], [], _ => by
    iintro -; ipureintro; intro k it w h; simp at h
  | [], _ :: _, _ => by
    iintro H
    icases BigSepL2.bigSepL2_nil_inv_left $$ H with %H
    cases H
  | _ :: _, [], _ => by
    iintro H
    icases BigSepL2.bigSepL2_nil_inv_right $$ H with %H
    cases H
  | it :: ins, w :: ws, hl => by
    have hw := hl w List.mem_cons_self
    have IH := wOwns_lensEq v ins ws (fun x hx => hl x (List.mem_cons_of_mem _ hx))
    iintro H
    icases BigSepL2.bigSepL2_cons.1 $$ H with ⟨Hw, H⟩
    icases (wOwn_true' v it w).1 $$ Hw with ⟨-, #Hks, #Hvs⟩
    ihave %Hk := srcOwn_len v it.key' w.ks w.key hw.1 $$ Hks
    ihave %Hv := srcOwn_len v it.value' w.vs w.value hw.2 $$ Hvs
    ihave %Hr := IH $$ H
    ipureintro
    intro k x y hx hy
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hx hy
      subst hx hy
      constructor
      · rw [Hk.1, show sint.nat it.key'.len = (sint.Z it.key'.len).toNat from rfl]
        have := Hk.2; unfold sint.Z at this ⊢; rw [BitVec.toInt_eq_toNat_cond] at this ⊢
        split <;> omega
      · rw [Hv.1, show sint.nat it.value'.len = (sint.Z it.value'.len).toNat from rfl]
        have := Hv.2; unfold sint.Z at this ⊢; rw [BitVec.toInt_eq_toNat_cond] at this ⊢
        split <;> omega
    | succ k =>
      simp only [List.getElem?_cons_succ] at hx hy
      exact Hr k x y hx hy

omit package_sem in
/-- **A live node's inodes' lengths**, out of `wtxW` (its entries not stale). -/
theorem wtxW_lens (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (bl n : Loc) (rn : NRec)
    (hn : X.node bl n = some rn) (hl : n ∈ X.live) (hwl : wsLive rn.ws) :
    wtxW (GF := GF) K tx r m X ⊢ wtxW K tx r m X ∗ ⌜insLens rn.ins rn.ws⌝ := by
  obtain ⟨B, HB, Hrn⟩ := node_bs_of hn
  iintro Hw
  icases wtxW_open K tx r m X $$ Hw with ⟨#Hpk, #Hcore, #Hreg, Hh, Hv, Hst, Hclose⟩
  ihave %Hok := wtxHeap_heapOK tx (DFrac.own 1) X $$ Hh
  icases wtxHeap_setNode tx (DFrac.own 1) X bl B n rn HB Hrn $$ Hh with ⟨Hno, Hback⟩
  rw [decide_eq_true hl]
  icases (objOwn_live_node _ _ _ _ _).1 $$ Hno with ⟨Hn, Hins, Hcap, Hws, Hch, Hchcap, Hkey⟩
  icases Hws with #Hws
  ihave %Hlens := wOwns_lensEq X.v rn.ins rn.ws hwl $$ Hws
  ihave Hno : objOwn X.v n (DFrac.own 1) true (.node bl rn) $$ [Hn Hins Hcap Hch Hchcap Hkey]
  · iapply (objOwn_live_node _ _ _ _ _).2; iframe; iexact Hws
  ihave Hh := Hback $$ %rn %(Hok.2.2.2.1 bl B n rn HB Hrn) [Hno]
  · iexact Hno
  rw [setNode_self X bl n B rn HB Hrn]
  isplitl
  · iapply Hclose $$ %X [] Hh Hv Hst
    ipureintro; exact ⟨rfl, rfl, rfl⟩
  · ipureintro; exact Hlens

/-- **The free ids are no pages of the view** (`wdbOK`'s: a free id is no tree slot; the view's
pages are the committed state's). -/
theorem free_notView {w : WDb} {v : View} (hok : wdbOK w) (hv : v = View.ofC v.base w.C) :
    ∀ y ∈ w.fl.free, v.pages !! y.toNat = none := by
  intro y hy
  have h5 := hok.2.2.2.2.1 y hy
  cases e : v.pages !! y.toNat with
  | none => rfl
  | some pg =>
    exfalso; apply h5
    unfold treeSlots
    rw [mem_pagesSlots_iff]
    have hp : w.C.pages = v.pages := by rw [hv]; rfl
    rw [hp]
    exact ⟨y.toNat, pg, e, Nat.le_refl _, by omega⟩

omit package_sem in
/-- `free_notView` out of `wdbW`. -/
theorem wdbW_freeView (K : BC) (tx : Loc) (v : View) (w : WDb) :
    wdbW (GF := GF) K tx v w ⊢ wdbW K tx v w ∗ ⌜∀ y ∈ w.fl.free, v.pages !! y.toNat = none⌝ := by
  unfold wdbW
  iintro ⟨H, %Hp⟩
  isplitl [H]
  · isplitl [H]
    · iexact H
    · ipureintro; exact Hp
  · ipureintro; exact free_notView Hp.1 Hp.2.2

/-- **`spillTail` over an invariant of the pieces' loop** (see the module doc). -/
theorem spillTail_gen
    (hAlloc : Tx.allocate.spec (GF := GF) (hG := hG))
    (hPage : Tx.page.spec (GF := GF) (hG := hG))
    (hSplit : node.split.spec (GF := GF) (hG := hG))
    (hWrite : node.write.spec (GF := GF) (hG := hG))
    (hPut : node.put.spec (GF := GF) (hG := hG))
    (hSize : node.size.spec (GF := GF) (hG := hG))
    (hInc : TxStats.IncSpill.spec (GF := GF) (hG := hG))
    (hTxid : internal.common.Meta.Txid.spec (GF := GF) (hG := hG))
    (hPgid : internal.common.Meta.Pgid.spec (GF := GF) (hG := hG))
    (hId : internal.common.Page.Id.spec (GF := GF) (hG := hG))
    (hKey : internal.common.Inode.Key.spec (GF := GF) (hG := hG))
    (hAssert : internal.common.Assert.spec (GF := GF) (hG := hG))
    (hFree : internal.freelist.Interface.Free.spec (GF := GF) (hG := hG))
    (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (w : WDb) (bl n : Loc) (rn : NRec)
    (O : List Nat) (lo hi : Option (List w8)) (h : Nat) (D : List Nat) (N : List Loc)
    (E : List El) (cs : SpCase) (X' : WX) (w' : WDb) (r' : NRec) (st0 : List FLStep)
    (np txp resp : Loc) (e0 : GoInterface)
    (I : List (Loc × node × List Inode) → Loc → Nat → WX → WDb → List FLStep → Prop)
    (hn' : X'.node bl n = some r') (hlv' : n ∈ X'.live) (hwl : wsLive r'.ws)
    (hS : (X'.nilCh bl n r').node bl n = some r'.nilCh ∧ n ∈ (X'.nilCh bl n r').live ∧
      r'.nilCh.nv.bucket' = bl ∧ r'.nilCh.capOwn = true ∧ r'.nilCh.nv.spilled' = false ∧
      r'.nilCh.ins.length = r'.nilCh.ws.length ∧ (insLens r'.ins r'.ws → insBnd r'.nilCh.ins) ∧
      (r'.nilCh.nv.parent' ≠ null → ∃ rp, (X'.nilCh bl n r').node bl r'.nilCh.nv.parent' = some rp ∧
        r'.nilCh.nv.parent' ∈ (X'.nilCh bl n r').live))
    (H1 : insLens r'.ins r'.ws → ∀ X2 xs wss pl rp', splitRel (X'.nilCh bl n r') X2 bl n r'.nilCh xs wss pl rp' →
      (∀ x ∈ xs, pieceFits 4096 x.2.2 ∧ (2 ≤ xs.length → 2 ≤ x.2.2.length)) →
      I xs pl 0 X2 w' st0)
    (H2 : ∀ xs pl i Xi wi sti x, I xs pl i Xi wi sti → xs[i]? = some x →
      ∃ rl, Xi.node bl x.1 = some rl ∧ x.1 ∈ Xi.live ∧ wsLive rl.ws ∧
        (insLens rl.ins rl.ws → pcPre Xi wi bl x.1 rl))
    (H3 : ∀ xs pl i Xi wi sti x rl X3 w2 st' id, I xs pl i Xi wi sti → xs[i]? = some x →
      Xi.node bl x.1 = some rl → pcStep Xi wi bl x.1 rl (pcCount (insSize rl.ins)) X3 w2 st' id →
      objsDisj Xi.t → (∀ y ∈ wi.fl.free, Xi.v.pages !! y.toNat = none) →
      insLens rl.ins rl.ws → I xs pl (i + 1) X3 w2 (sti ++ st'))
    (H4 : ∀ xs pl i Xi wi sti (X'' : WX) (w'' : WDb) st', I xs pl i Xi wi sti →
      spErr Xi X'' wi w'' st' → spErr X X'' w w'' (sti ++ st'))
    (H5 : ∀ xs pl Xf wf sti, I xs pl xs.length Xf wf sti → ∃ rf, Xf.node bl n = some rf ∧
      n ∈ Xf.live ∧ rf.nv.parent' = pl ∧ rf.nv.children' = slice.nil ∧ rf.cs = [] ∧
      (pl ≠ null → ∃ rp, Xf.node bl pl = some rp ∧ pl ∈ Xf.live))
    (H6 : ∀ xs pl Xf wf sti, I xs pl xs.length Xf wf sti →
      (pl = null ∨ ∃ rp, Xf.node bl pl = some rp ∧ rp.nv.pgid' ≠ W64 0) →
      spDone X Xf w wf bl n rn O lo hi h D N E cs sti)
    (H7 : ∀ xs pl Xf wf sti rp, I xs pl xs.length Xf wf sti → pl ≠ null →
      Xf.node bl pl = some rp → rp.nv.pgid' = W64 0 →
      ∃ h2 F2 D2 N2, spPre Xf wf bl pl rp O lo hi h2 F2 D2 N2 E .top ∧
        ∀ Xg wg st2, spDone Xf Xg wf wg bl pl rp O lo hi h2 D2 N2 E .top st2 →
          spDone X Xg w wg bl n rn O lo hi h D N E cs (sti ++ st2)) :
    ⊢ □ ▷ spillIH (GF := GF) (hG := hG) -∗ wtxW K tx r m X' -∗ wdbW K tx X'.v w' -∗
      np ↦ n -∗ txp ↦ tx -∗ resp ↦ e0 -∗
      WP (spillTail np txp resp) {{ v, ⌜v = returnVal #()⌝ ∗ ∃ err : GoInterface,
        resp ↦ err ∗ np ↦ n ∗ txp ↦ tx ∗ spPost K tx r m X w bl n rn O lo hi h D N E cs err }} := by
  unfold spillIH
  iintro #IH Hw Hdb Hnp Htxp Hres
  icases wtxW_lens K tx r m X' bl n r' hn' hlv' hwl $$ Hw with ⟨Hw, %Hlens⟩
  icases wtxW_nilCh K tx r m X' bl n r' hn' hlv' $$ Hw with ⟨Hch, Hwb⟩
  wp_pures
  wp_load
  wp_pures
  wp_store
  wp_pures
  ihave Hw := Hwb $$ Hch
  obtain ⟨hS1, hS2, hS3, hS4, hS8, hS5, hS6, hS7⟩ := hS
  wp_bind (Let "$a0" _ _)
  iapply (splitStep_wp hSplit K tx r m _ bl n r'.nilCh np txp hS1 hS2 hS3 hS4 hS8 hS5 (hS6 Hlens) hS7)
  iframe
  iintro %s %xs %wss %pl %rp' %X2 %Hsr Hw Hs Hnp Htxp
  have HI0 := H1 Hlens X2 xs wss pl rp' Hsr.1 Hsr.2
  have hv2 : X2.v = X'.v := by
    have := Hsr.1.same.2.2.2
    rw [this]; unfold WX.nilCh WX.killL; rw [WX.setNode_v]
  rw [← hv2]
  wp_auto
  ihave %Hsl := ownSlice_len _ _ _ $$ Hs
  ihave HI : iprop(∃ (j : w64) (Xi : WX) (wi : WDb) (sti : List FLStep) (l0 : Loc),
      "i" ∷ i_ptr ↦ j ∗ "node" ∷ node_ptr ↦ l0 ∗ "Hw" ∷ wtxW K tx r m Xi ∗
      "Hdb" ∷ wdbW K tx Xi.v wi ∗ "Hres" ∷ resp ↦ e0 ∗
      "%HI" ∷ ⌜I xs pl (sint.nat j) Xi wi (st0 ++ sti) ∧ 0 ≤ sint.Z j ∧
        sint.Z j ≤ sint.Z s.len⌝) $$ [i node Hw Hdb Hres]
  · iexists W64 0, X2, w', [], zero_val Loc
    iframe
    ipureintro
    refine ⟨?_, by word, by have := Hsl.2; word⟩
    rw [show sint.nat (W64 0) = 0 from rfl, List.append_nil]; exact HI0
  wp_for HI
  obtain ⟨HIj, Hj0, Hjl⟩ := HI
  by_cases hlt : sint.Z j < sint.Z s.len
  · simp only [decide_eq_true hlt, ite_true]
    have hjn : sint.nat j < xs.length := by
      have h2 := Hsl.1
      simp only [List.length_map] at h2
      rw [h2]; show (sint.Z j).toNat < (sint.Z s.len).toNat; omega
    obtain ⟨x, hx⟩ : ∃ x, xs[sint.nat j]? = some x := ⟨_, List.getElem?_eq_getElem hjn⟩
    obtain ⟨rl, hrl, hrlv, hrwl, hpre⟩ := H2 xs pl _ Xi wi _ x HIj hx
    icases wtxW_lens K tx r m Xi bl x.1 rl hrl hrlv hrwl $$ Hw with ⟨Hw, %Hrlens⟩
    obtain ⟨hp1, hp2, hp3, hp4, hp5, hp6, hp7, hp8, hp9, hp10, hp11, hp12, -⟩ := hpre Hrlens
    icases wtxW_heapOK K tx r m Xi $$ Hw with ⟨Hw, %Hok⟩
    icases wdbW_freeView K tx Xi.v wi $$ Hdb with ⟨Hdb, %Hfv⟩
    wp_pures
    wp_bind (App (Val (GoInstruction (GoLoad go.int))) _)
    wp_load
    wp_pures
    simp only [Hj0, hlt, _root_.and_self, ite_true]
    wp_pures
    wp_bind (App (Val (GoInstruction (GoLoad (go.GoType.PointerType node.ty)))) _)
    iapply (wp_load_slice_index (t := go.GoType.PointerType node.ty) s (sint.Z j) (xs.map (·.1))
      (DFrac.own 1) x.1 Hj0) $$ [Hs]
    · iframe; ipureintro; rw [List.getElem?_map, show (sint.Z j).toNat = sint.nat j from rfl, hx]; rfl
    inext
    iintro Hs
    wp_bind (App (Val (GoInstruction (GoLoad go.int))) _)
    wp_load
    iapply (wp_frame_wand' _ _ iprop(np ↦ n ∗ s ↦* xs.map (·.1) ∗ i_ptr ↦ j))
    isplitl [Hnp Hs i]
    · iframe
    iapply (pieceOne_wp hAlloc hPage hWrite hPut hSize hInc hTxid hPgid hId hKey hAssert hFree K tx r m
      Xi wi bl x.1 rl txp resp node_ptr l0 e0 j hrl hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12)
    iframe
    isplitl
    · iintro %X3 %w2 %st' %id %Hst Hw Hdb Htxp Hnode Hres ⟨Hnp, Hs, i⟩
      wp_for_post
      have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by
        have : sint.Z (j + W64 1) = sint.Z j + 1 := by
          have h2 := Hsl.1
          simp only [List.length_map] at h2
          have : sint.Z s.len < 2 ^ 63 := by word
          word
        show (sint.Z (j + W64 1)).toNat = (sint.Z j).toNat + 1
        omega
      iframe
      iexists j + W64 1, X3, w2, sti ++ st', x.1
      iframe
      ipureintro
      refine ⟨?_, by word, ?_⟩
      rotate_left
      · have h2 := Hsl.1
        simp only [List.length_map] at h2
        have : sint.Z s.len < 2 ^ 63 := by word
        word
      rw [hj1, ← List.append_assoc]
      exact H3 xs pl _ Xi wi _ x rl X3 w2 st' id HIj hx hrl Hst Hok.2.1 Hfv Hrlens
    · iintro %err %X'' %w'' %st' %He #Hok Hst Htxp Hnode Hres ⟨Hnp, Hs, i⟩
      wp_for_post
      isplitr
      · ipureintro; rfl
      iexists err
      iframe
      unfold spPost
      iright
      isplitr
      · ipureintro; exact He.1
      iframe Hok
      iexists X'', w'', (st0 ++ sti) ++ st'
      iframe Hst
      ipureintro
      exact H4 xs pl _ Xi wi _ X'' w'' st' HIj He.2
  · simp only [decide_eq_false hlt]
    cleanup_bool_decide
    have hje : sint.nat j = xs.length := by
      have h2 := Hsl.1
      simp only [List.length_map] at h2
      rw [h2]; show (sint.Z j).toNat = (sint.Z s.len).toNat; omega
    rw [hje] at HIj
    obtain ⟨rf, hrf, hlvf, hpar, hch, hcs, hplv⟩ := H5 xs pl Xi wi _ HIj
    icases wtxW_size_acc K tx r m Xi bl n rf hrf hlvf $$ Hw with ⟨Hn, Hins, Hdbf, #Hps, Hwb⟩
    icases typedPointsto_not_null_dup _ _ _ $$ Hn with ⟨Hn, %Hnn⟩
    iStructNamed Hn
    wp_auto
    ihave Hn : (n ↦ rf.nv : IProp GF)
      $$ [bucket isLeaf unbalanced spilled key pgid parent children inodes]
    · iapply typedPointsto_combine _ _ _ Hnn
      simp only [TypedPointsto.typedPointstoDef]
      iframe
    ihave Hw := Hwb $$ Hn Hins Hdbf
    by_cases hnull : pl = null
    · rw [hpar, decide_eq_true hnull]
      wp_auto
      isplitr
      · ipureintro; rfl
      iexists interface.nil
      iframe
      unfold spPost
      ileft
      isplitr
      · ipureintro; rfl
      iexists Xi, wi, st0 ++ sti
      iframe
      ipureintro
      exact H6 xs pl Xi wi _ HIj (Or.inl hnull)
    · rw [hpar, decide_eq_false hnull]
      obtain ⟨rp, hrp, hplv'⟩ := hplv hnull
      icases wtxW_size_acc K tx r m Xi bl n rf hrf hlvf $$ Hw with ⟨Hn, Hins, Hdbf, #-, Hwb⟩
      iStructNamed Hn
      wp_auto
      ihave Hn : (n ↦ rf.nv : IProp GF)
        $$ [bucket isLeaf unbalanced spilled key pgid parent children inodes]
      · iapply typedPointsto_combine _ _ _ Hnn
        simp only [TypedPointsto.typedPointstoDef]
        iframe
      ihave Hw := Hwb $$ Hn Hins Hdbf
      rw [hpar]
      icases wtxW_size_acc K tx r m Xi bl pl rp hrp hplv' $$ Hw with ⟨Hp, Hpins, Hdbf, #-, Hwb⟩
      icases typedPointsto_not_null_dup _ _ _ $$ Hp with ⟨Hp, %Hpnn⟩
      iStructNamed Hp
      wp_auto
      ihave Hp : (pl ↦ rp.nv : IProp GF)
        $$ [bucket isLeaf unbalanced spilled key pgid parent children inodes]
      · iapply typedPointsto_combine _ _ _ Hpnn
        simp only [TypedPointsto.typedPointstoDef]
        iframe
      ihave Hw := Hwb $$ Hp Hpins Hdbf
      by_cases hpg : rp.nv.pgid' = W64 0
      · rw [decide_eq_true hpg]
        have hnil : Xi.nilCh bl n rf = Xi := by
          obtain ⟨B, HB, Hr⟩ := node_bs_of hrf
          have hr : rf.nilCh = rf := by
            unfold NRec.nilCh; rw [← hch, ← hcs]
          unfold WX.nilCh; rw [hr, hcs]
          simp only [WX.killL, List.foldr_nil]
          exact setNode_self Xi bl n B rf HB Hr
        icases wtxW_nilCh K tx r m Xi bl n rf hrf hlvf $$ Hw with ⟨Hch, Hwb⟩
        wp_auto
        ihave Hw := Hwb $$ Hch
        rw [hnil]
        icases wtxW_size_acc K tx r m Xi bl n rf hrf hlvf $$ Hw with ⟨Hn, Hins, Hdbf, #-, Hwb⟩
        iStructNamed Hn
        wp_auto
        ihave Hn : (n ↦ rf.nv : IProp GF)
          $$ [bucket isLeaf unbalanced spilled key pgid parent children inodes]
        · iapply typedPointsto_combine _ _ _ Hnn
          simp only [TypedPointsto.typedPointstoDef]
          iframe
        ihave Hw := Hwb $$ Hn Hins Hdbf
        rw [hpar]
        obtain ⟨h2, F2, D2, N2, hpre2, hdone2⟩ := H7 xs pl Xi wi _ rp HIj hnull hrp hpg
        wp_apply IH $$ %K %tx %r %m %Xi %wi %bl %pl %rp %O %lo %hi %h2 %F2 %D2 %N2 %E %SpCase.top
          %hpre2 [Hw Hdb] as %err Hpost
        · iframe
        try wp_auto
        isplitr
        · ipureintro; rfl
        iexists err
        iframe
        unfold spPost
        icases Hpost with (⟨%Herr, %Xg, %wg, %st2, Hw, Hdb, %Hd⟩ |
          ⟨%Herr, #Hok, %Xg, %wg, %st2, %He, Hst⟩)
        · ileft
          isplitr
          · ipureintro; exact Herr
          iexists Xg, wg, (st0 ++ sti) ++ st2
          iframe
          ipureintro
          exact hdone2 Xg wg st2 Hd
        · iright
          isplitr
          · ipureintro; exact Herr
          iframe Hok
          iexists Xg, wg, (st0 ++ sti) ++ st2
          iframe Hst
          ipureintro
          exact H4 xs pl _ Xi wi _ Xg wg st2 HIj He
      · rw [decide_eq_false hpg]
        wp_auto
        isplitr
        · ipureintro; rfl
        iexists interface.nil
        iframe
        unfold spPost
        ileft
        isplitr
        · ipureintro; rfl
        iexists Xi, wi, st0 ++ sti
        iframe
        ipureintro
        exact H6 xs pl Xi wi _ HIj (Or.inr ⟨rp, hrp, hpg⟩)

end proof

end Spill

end bbolt
end EtcdGrove
end Perennial
