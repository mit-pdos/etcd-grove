/-
`node.spill`'s split (U9v, `notes/bbolt-proof-plan.md`): the pieces' objects. The writer's state
around its heap (`splitFr`, `wtxW_frame`), the bucket's `FillPercent` out of the fills
(`fill_acc`), the entries' facts cut at the pieces (`bigSepL2_cut`), and the objects of the
pieces (`headObj`, `tailObjs`) and of a new parent (`newParObj`).
-/
module

public import Proof.go_etcd_io.bbolt.Spill.NodeSpillSplitRecs
public import Proof.go_etcd_io.bbolt.Spill.NodeSpillSplitHeap
public import Proof.go_etcd_io.bbolt.Spill.NodeSpillAsm
public import Proof.go_etcd_io.bbolt.Spill.NodeSpillHeap

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section objs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- The writer's state but its heap, fills, `tx.db` share and statistics' token. -/
def splitFr (K : BC) (tx : Loc) (r : TxReg) (X : WX) : IProp GF :=
  iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ K.core ∗
    ⌜r.db = K.db ∧ r.rw = true ∧ tx ≠ null ∧ X.t.t.managed' = false ∧
      txRoot (GF := GF) tx ≠ null ∧ 0 < X.t.t.meta'.addr⌝ ∗ reg tx K.B r ∗
    hdlAuth r 1 X.handles ∗ nlAuth r 1 X.nloc ∗ viewBase r X.v ∗
    viewCells wq X.v ∗
    ∃ l : Nat, mapFields r.db (DFrac.own (1 : Qp).half.half) (some (X.v.base, l) : MapSt) ∗
      ⌜∀ id pg, X.v.pages !! id = some pg → (id + 1) * 4096 ≤ l⌝)

theorem splitFr_splitX (K : BC) (tx : Loc) (r : TxReg) (X : WX) (bl : Loc) (B : BRec)
    (a b : List (Loc × NRec)) :
    splitFr (GF := GF) K tx r (splitX X bl B a b) = splitFr K tx r X := rfl

/-- **The writer's state around its heap.** -/
theorem wtxW_frame (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) :
    wtxW (GF := GF) K tx r m X ⊣⊢ iprop(wtxHeap tx (DFrac.own 1) X ∗ fills X.handles (DFrac.own 1) ∗
      tx.[Tx, go!"db"] ↦{DFrac.own (txDbQ 1)} r.db ∗ statsTok r m 1 ∗ splitFr K tx r X) := by
  unfold wtxW wtxCore splitFr
  constructor
  · iintro ⟨⟨Hp, Hc, %Hr, Hreg, Hh, Hf, Hbk, Hnl, Hdb, Hv, Hst⟩, Hcells, Hmap⟩
    iframe; ipureintro; exact Hr
  · iintro ⟨Hh, Hf, Hdb, Hst, Hp, Hc, %Hr, Hreg, Hbk, Hnl, Hv, Hcells, Hmap⟩
    iframe; ipureintro; exact Hr

/-- The frame's persistent part. -/
theorem splitFr_pers (K : BC) (tx : Loc) (r : TxReg) (X : WX) :
    splitFr (GF := GF) K tx r X ⊢ □ (isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ K.core ∗
      reg tx K.B r) ∗ ⌜r.db = K.db⌝ ∗ splitFr K tx r X := by
  unfold splitFr
  iintro ⟨#Hp, #Hc, %Hr, #Hreg, H⟩
  iframe; iframe #
  isplitl []
  · ipureintro; exact Hr.1
  ipureintro; exact Hr

omit hos in
/-- **A bucket's `FillPercent`**, out of the root bucket's or the handles' fills. -/
theorem fill_acc (tx : Loc) (X : WX) (bl : Loc) (hrl : X.rl = txRoot (GF := GF) tx)
    (hfp : bl = X.rl ∨ (X.handles !! bl).isSome) :
    rootFill (GF := GF) tx (DFrac.own 1) ∗ fills X.handles (DFrac.own 1) ⊢
      ∃ f : w64, ⌜¬ float64IsNaN f⌝ ∗ bl.[Bucket, go!"FillPercent"] ↦ f ∗
        (bl.[Bucket, go!"FillPercent"] ↦ f -∗ rootFill tx (DFrac.own 1) ∗
          fills X.handles (DFrac.own 1)) := by
  iintro ⟨Hrf, Hfills⟩
  rcases hfp with hroot | hh
  · have hbr : bl = tx.[Tx, go!"root"] := hroot.trans hrl
    unfold rootFill
    icases Hrf with ⟨%f, %Hnan, Hf⟩
    iexists f
    rw [hbr]
    iframe Hf
    isplitl []
    · ipureintro; exact Hnan
    iintro Hf
    iframe Hfills
    iexists f; iframe Hf; ipureintro; exact Hnan
  · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 hh
    unfold fills
    icases (BigSepM.bigSepM_lookup_acc hx).1 $$ Hfills with ⟨⟨%f, %Hnan, Hf⟩, Hfb⟩
    iexists f
    iframe Hf
    isplitl []
    · ipureintro; exact Hnan
    iintro Hf
    iframe Hrf
    iapply Hfb
    iexists f; iframe Hf; ipureintro; exact Hnan

omit hos in
/-- A pairwise big separating conjunction over a flattened list, cut. -/
theorem bigSepL2_cut {α : Type} (Φ : α → WEntry → IProp GF) (ps : List (List α))
    (ws : List WEntry) (h : ps.flatten.length = ws.length) :
    ([∗list] it;w ∈ ps.flatten;ws, Φ it w) ⊢
      [∗list] a;w ∈ ps;cutWs ps ws, [∗list] it;w' ∈ a;w, Φ it w' := by
  induction ps generalizing ws with
  | nil =>
    simp at h
    rw [List.length_eq_zero_iff.1 h.symm]
    simp only [List.flatten_nil, cutWs]
    exact .rfl
  | cons a ps ih =>
    simp only [List.flatten_cons, List.length_append] at h
    have e : ws = ws.take a.length ++ ws.drop a.length := (List.take_append_drop _ _).symm
    simp only [List.flatten_cons, cutWs]
    conv => lhs; rw [e]
    refine (BigSepL2.bigSepL2_app_same_length (Or.inl (by rw [List.length_take]; omega))).1.trans ?_
    refine BI.Entails.trans ?_ BigSepL2.bigSepL2_cons.2
    exact sep_mono .rfl (ih _ (by simp only [List.length_drop]; omega))

/-- **The first piece's object** (`n` itself: its children and key kept). -/
theorem headObj (v : View) (bl n : Loc) (rN : NRec) (x0 : Loc × node × List Inode)
    (w0 : List WEntry) (hc : x0.2.1.children' = rN.nv.children') (hk : x0.2.1.key' = rN.nv.key') :
    (n ↦ x0.2.1 : IProp GF) ∗ x0.2.1.inodes' ↦* x0.2.2 ∗
      ([∗list] it;w ∈ x0.2.2;w0, wOwn v true it w) ∗ rN.nv.children' ↦* rN.cs ∗
      ownSliceCap Loc rN.nv.children' (DFrac.own 1) ∗
      (if true ∧ rN.nv.key' ≠ slice.nil then srcOwn v rN.nv.key' rN.ksrc rN.key else emp) ⊢
      objOwn v n (DFrac.own 1) true (.node bl (splitRec rN x0 w0 true false)) := by
  refine BI.Entails.trans ?_ (objOwn_live_node (GF := GF) v n (DFrac.own 1) bl _).2
  iintro ⟨Hn, Hi, Hw, Hc, Hcc, Hk⟩
  simp only [splitRec, ↓reduceIte, Bool.false_eq_true]
  rw [hc, hk]
  iframe

/-- **A fresh piece's object** (no children, no key, not its inodes' capacity). -/
theorem freshObj (v : View) (bl : Loc) (rN : NRec) (x : Loc × node × List Inode)
    (w : List WEntry) (hc : x.2.1.children' = slice.nil) (hk : x.2.1.key' = slice.nil) :
    (x.1 ↦ x.2.1 : IProp GF) ∗ x.2.1.inodes' ↦* x.2.2 ∗
      ([∗list] it;w' ∈ x.2.2;w, wOwn v true it w') ⊢
      objOwn v x.1 (DFrac.own 1) true (.node bl (splitRec rN x w false false)) := by
  refine BI.Entails.trans ?_ (objOwn_live_node (GF := GF) v x.1 (DFrac.own 1) bl _).2
  iintro ⟨Hn, Hi, Hw⟩
  simp only [splitRec, Bool.false_eq_true, ↓reduceIte]
  rw [hc, hk]
  simp only [ne_eq, not_true_eq_false, _root_.and_false, ↓reduceIte]
  ihave Hnil := ownSlice_nil (V := Loc) (GF := GF) (DFrac.own 1)
  ihave Hnilc := ownSliceCap_nil (V := Loc) (GF := GF)
  iframe
  isplitl []
  · iexact Hnil
  isplitl []
  · iexact Hnilc
  iempintro

/-- **The fresh pieces' objects.** -/
theorem tailObjs (v : View) (bl : Loc) (rN : NRec) (rest : List (Loc × node × List Inode))
    (ws : List WEntry) (h : ∀ x ∈ rest, x.2.1.children' = slice.nil ∧ x.2.1.key' = slice.nil) :
    ([∗list] x ∈ rest, (x.1 ↦ x.2.1 : IProp GF) ∗ x.2.1.inodes' ↦* x.2.2) ∗
      ([∗list] a;w ∈ rest.map (·.2.2);cutWs (rest.map (·.2.2)) ws,
        [∗list] it;w' ∈ a;w, wOwn v true it w') ⊢
      [∗list] p ∈ pieceRecs rN false rest (cutWs (rest.map (·.2.2)) ws) false,
        objOwn v p.1 (DFrac.own 1) true (.node bl p.2) := by
  induction rest generalizing ws with
  | nil => iintro -; simp only [pieceRecs]; iempintro
  | cons y rest ih =>
    simp only [List.map_cons, cutWs, pieceRecs]
    iintro ⟨⟨⟨Hy, Hyi⟩, Hr⟩, Hw⟩
    icases BigSepL2.bigSepL2_cons.1 $$ Hw with ⟨Hyw, Hw⟩
    iapply BigSepL.bigSepL_cons.2
    isplitl [Hy Hyi Hyw]
    · iapply freshObj v bl rN y _ (h y (List.mem_cons_self ..)).1 (h y (List.mem_cons_self ..)).2
      iframe
    iapply ih (ws.drop y.2.2.length) (fun x hx => h x (List.mem_cons_of_mem _ hx))
    iframe

/-- **A new parent's object** (no inodes, no key; its children). -/
theorem newParObj (v : View) (bl pl : Loc) (pv : node) (ls : List Loc)
    (hi : pv.inodes' = slice.nil) (hk : pv.key' = slice.nil) :
    (pl ↦ pv : IProp GF) ∗ pv.children' ↦* ls ∗ ownSliceCap Loc pv.children' (DFrac.own 1) ⊢
      objOwn v pl (DFrac.own 1) true (.node bl (newParRec pv ls)) := by
  refine BI.Entails.trans ?_ (objOwn_live_node (GF := GF) v pl (DFrac.own 1) bl _).2
  iintro ⟨Hn, Hc, Hcc⟩
  simp only [newParRec, ↓reduceIte]
  rw [hi, hk]
  simp only [ne_eq, not_true_eq_false, _root_.and_false, ↓reduceIte]
  ihave Hnil := ownSlice_nil (V := Inode) (GF := GF) (DFrac.own 1)
  ihave Hnilc := ownSliceCap_nil (V := Inode) (GF := GF)
  iframe
  isplitl []
  · iexact Hnil
  isplitl []
  · iexact Hnilc
  iapply (BigSepL2.bigSepL2_nil (Φ := fun _ (it : Inode) (w : WEntry) => wOwn (GF := GF) v true it w)).2
  iempintro

end objs

end Spill

end bbolt
end EtcdGrove
end Perennial
