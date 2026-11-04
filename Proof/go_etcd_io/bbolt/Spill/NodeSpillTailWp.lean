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
    (hn' : X'.node bl n = some r') (hlv' : n ∈ X'.live)
    (hS : (X'.nilCh bl n r').node bl n = some r'.nilCh ∧ n ∈ (X'.nilCh bl n r').live ∧
      r'.nilCh.nv.bucket' = bl ∧ r'.nilCh.capOwn = true ∧
      r'.nilCh.ins.length = r'.nilCh.ws.length ∧ insSize r'.nilCh.ins < 2 ^ 63 ∧
      (r'.nilCh.nv.parent' ≠ null → ∃ rp, (X'.nilCh bl n r').node bl r'.nilCh.nv.parent' = some rp ∧
        r'.nilCh.nv.parent' ∈ (X'.nilCh bl n r').live))
    (H1 : ∀ X2 xs wss pl rp', splitRel (X'.nilCh bl n r') X2 bl n r'.nilCh xs wss pl rp' →
      (∀ x ∈ xs, pieceFits 4096 x.2.2 ∧ (2 ≤ xs.length → 2 ≤ x.2.2.length)) →
      I xs pl 0 X2 w' st0)
    (H2 : ∀ xs pl i Xi wi sti x, I xs pl i Xi wi sti → xs[i]? = some x →
      ∃ rl, Xi.node bl x.1 = some rl ∧ pcPre Xi wi bl x.1 rl)
    (H3 : ∀ xs pl i Xi wi sti x rl X3 w2 st' id, I xs pl i Xi wi sti → xs[i]? = some x →
      Xi.node bl x.1 = some rl → pcStep Xi wi bl x.1 rl (pcCount (insSize rl.ins)) X3 w2 st' id →
      I xs pl (i + 1) X3 w2 (sti ++ st'))
    (H4 : ∀ xs pl i Xi wi sti (X'' : WX) (w'' : WDb) st', I xs pl i Xi wi sti →
      (w''.C = wi.C ∧ w''.fl = wi.fl.applySteps wi.wtxid st' ∧ X''.v.pages = Xi.v.pages) →
      w''.C = w.C ∧ w''.fl = w.fl.applySteps w.wtxid (sti ++ st') ∧ X''.v.pages = X.v.pages)
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
  icases wtxW_nilCh K tx r m X' bl n r' hn' hlv' $$ Hw with ⟨Hch, Hwb⟩
  wp_pures
  wp_load
  wp_pures
  wp_store
  wp_pures
  ihave Hw := Hwb $$ Hch
  obtain ⟨hS1, hS2, hS3, hS4, hS5, hS6, hS7⟩ := hS
  wp_bind (Let "$a0" _ _)
  iapply (splitStep_wp hSplit K tx r m _ bl n r'.nilCh np txp hS1 hS2 hS3 hS4 hS5 hS6 hS7)
  iframe
  iintro %s %xs %wss %pl %rp' %X2 %Hsr Hw Hs Hnp Htxp
  have HI0 := H1 X2 xs wss pl rp' Hsr.1 Hsr.2
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
    obtain ⟨rl, hrl, hp1, hp2, hp3, hp4, hp5, hp6, hp7, hp8, hp9, hp10, hp11, hp12⟩ :=
      H2 xs pl _ Xi wi _ x HIj hx
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
      exact H3 xs pl _ Xi wi _ x rl X3 w2 st' id HIj hx hrl Hst
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
