/-
`Bucket.dereference` (pure and resource lemmas): the view's bytes a node's entries and key are
lent at fractions fixed in advance (`srcFrac`, `borrowEs`), so that what `node.dereference` gives
back (`node.dereference.wspec`, the same entries) returns them to the view.
-/
module

public import Proof.go_etcd_io.bbolt.WriteTxAcc
public import Proof.go_etcd_io.bbolt.WriteTxDeref
public import Spec.go_etcd_io.bbolt.node__dereference_w

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pure
variable [ext : FfiSyntax]

/-- The fraction a slice of the source `s` is lent at: its own, or `q` of the view. -/
def srcFrac (s : Src) (q : Qp) : DFrac :=
  match s with
  | .own d => d
  | _ => DFrac.own q

/-- The entries `nodeBorrowD` lends the inodes as, from the fraction `q` of the view. -/
def borrowEs : List WEntry → Qp → List NodeEntry
  | [], _ => []
  | w :: ws, q => ⟨w.flags, w.pgid, w.key, w.value, srcFrac w.ks q.half.half, srcFrac w.vs q.half.half⟩ ::
      borrowEs ws q.half

theorem borrowEs_match : ∀ (ws : List WEntry) (q : Qp), wMatch ws (borrowEs ws q)
  | [], _ => List.Forall₂.nil
  | w :: ws, q => List.Forall₂.cons ⟨rfl, rfl, rfl, rfl, fun d h => by simp [srcFrac, h],
      fun d h => by simp [srcFrac, h]⟩ (borrowEs_match ws q.half)

theorem borrowEs_length : ∀ (ws : List WEntry) (q : Qp), (borrowEs ws q).length = ws.length
  | [], _ => rfl
  | _ :: ws, q => by simp [borrowEs, borrowEs_length ws q.half]

/-- What a node lends `dereference`, from the fraction `f` of the view. -/
def dIn (r : NRec) (f : Qp) : DerefIn :=
  ⟨r.nv, r.cs, r.ins, borrowEs r.ws f.half, r.key, srcFrac r.ksrc f.half⟩

/-- The node `r` dereferenced: its struct `nv'`, inodes `ins'`. -/
def derefRec (r : NRec) (nv' : node) (ins' : List Inode) : NRec :=
  ⟨nv', ins', r.ws.map ownFresh, r.cs, r.key, Src.own (DFrac.own 1)⟩

/-- The fractions of the view the nodes `S` are lent: halves, in order. -/
def fracOf : List Loc → Qp → Loc → Qp
  | [], q, _ => q
  | x :: xs, q, l => if l = x then q.half else fracOf xs q.half l

/-- What is left of `q` after them. -/
def restOf : List Loc → Qp → Qp
  | [], q => q
  | _ :: xs, q => restOf xs q.half

/-- The node of a chain, for `node.root`. -/
def chainList (ns : GMap Loc NRec) (p : List Loc) : List (Loc × node) :=
  p.map (fun x => (x, ((ns !! x).map NRec.nv).getD (zero_val node)))

theorem chain_parentPath (ns : GMap Loc NRec) :
    ∀ (l : Loc) (p : List Loc) (t : Loc), upPath ns l p t →
      parentPath (chainList ns p) ∧ ∃ rest, chainList ns p = (l, ((ns !! l).map NRec.nv).getD (zero_val node)) :: rest ∧
        ((l, ((ns !! l).map NRec.nv).getD (zero_val node)) :: rest).getLast (List.cons_ne_nil _ _) =
          (t, ((ns !! t).map NRec.nv).getD (zero_val node)) := by
  intro l p t h
  induction h with
  | self l r hr hp =>
    refine ⟨?_, [], rfl, rfl⟩
    simp [chainList, parentPath, hr, hp]
  | up l r p t hr hp hu ih =>
    obtain ⟨hpp, rest, hrest, hlast⟩ := ih
    refine ⟨?_, chainList ns p, by simp [chainList], ?_⟩
    · show parentPath ((l, ((ns !! l).map NRec.nv).getD (zero_val node)) :: chainList ns p)
      rw [hrest]
      refine ⟨by simp [hr], hp, ?_⟩
      rw [← hrest]; exact hpp
    · rw [hrest, List.getLast_cons (List.cons_ne_nil _ _)]
      exact hlast

/-- The default of what a node lends. -/
def dInDefault : DerefIn := ⟨zero_val node, [], [], [], [], DFrac.own 1⟩

/-- What the nodes `S` of `ns` lend, the view's fraction `q` shared among them. -/
def gOf (ns : GMap Loc NRec) (S : List Loc) (q : Qp) (l : Loc) : DerefIn :=
  match ns !! l with
  | some r => dIn r (fracOf S q l)
  | none => dInDefault

theorem kidsTree_nodup (ns : GMap Loc NRec) (t : Loc) (S : List Loc) (h : kidsTree ns t S) :
    S.Nodup := by
  cases h with
  | mk _ _ _ _ _ hnd => exact hnd

theorem kidsTree_head (ns : GMap Loc NRec) (t : Loc) (S : List Loc) (h : kidsTree ns t S) :
    t ∈ S := by
  cases h with
  | mk _ _ _ _ _ _ => exact List.mem_cons_self

end pure

section own
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `srcBorrow` at the fraction `srcFrac`. -/
theorem srcBorrowD (W : WView) (hc : W.data.locCar ≠ 0) (q : Qp) (s : GoSlice) (src : Src)
    (bs : List w8) (hns : src ≠ Src.stale) :
    pagesView (GF := GF) W.data W.ps q W.pages ∗ srcOwn W s src bs ⊢
      s ↦*{srcFrac src q} bs ∗
      (s ↦*{srcFrac src q} bs -∗ pagesView W.data W.ps q W.pages ∗ srcOwn W s src bs) := by
  iintro ⟨Hpv, Hs⟩
  cases src with
  | stale => exact absurd rfl hns
  | own d =>
    unfold srcOwn srcFrac
    iframe Hs
    iintro Hs
    iframe
  | view =>
    unfold srcOwn srcFrac
    icases Hs with %Hin
    have Hs := inViewAt_slice W s bs Hin
    obtain ⟨Hloc, Hn, -, -⟩ := Hin
    obtain ⟨id, PG, o, -, -, -, Hp⟩ := id Hloc
    have Hpc : s.ptr.locCar ≠ 0 := by rw [Hp]; simpa [Loc.add] using hc
    icases viewLoc_acc_q (GF := GF) W q s.ptr bs Hloc $$ Hpv with ⟨Hb, Hback⟩
    icases bytes_slice_acc (hG := hG) s.ptr (DFrac.own q) bs 0 bs.length (by omega) Hn Hpc $$ Hb
      with ⟨Hsl, Hsback⟩
    have Hba : bytesAt bs 0 bs.length = bs := by simp [bytesAt]
    rw [Hba, ← Hs]
    iframe Hsl
    iintro Hsl
    ihave Hb := Hsback $$ Hsl
    ihave Hpv := Hback $$ Hb
    iframe
    ipureintro; exact ⟨Hloc, Hn, by rw [Hs]; rfl, by rw [Hs]; rfl⟩

/-- `nodeBorrow` at the entries `borrowEs`. -/
theorem nodeBorrowD (W : WView) (hc : W.data.locCar ≠ 0) :
    ∀ (ws : List WEntry) (ins : List Inode) (q : Qp), wsLive ws →
    pagesView (GF := GF) W.data W.ps q W.pages ∗ ([∗list] it;w ∈ ins;ws, wOwn W it w) ⊢
      inodesOwn ins (borrowEs ws q) ∗
        (inodesOwn ins (borrowEs ws q) -∗ pagesView W.data W.ps q W.pages ∗
          [∗list] it;w ∈ ins;ws, wOwn W it w) := by
  intro ws
  induction ws with
  | nil =>
    intro ins q _
    iintro ⟨Hpv, Hl⟩
    ihave %Hlen := BigSepL2.bigSepL2_length $$ Hl
    have : ins = [] := List.eq_nil_of_length_eq_zero (by simpa using Hlen)
    subst this
    simp only [borrowEs]
    isplitl []
    · iapply inodesOwn_nil
    iintro -
    iframe
  | cons w ws ih =>
    intro ins q Hlive
    iintro ⟨Hpv, Hl⟩
    icases BigSepL2.bigSepL2_cons_inv_right.1 $$ Hl with ⟨%it, %ins', %Heq, Hw, Hl⟩
    subst Heq
    icases (pv_half W.data W.ps W.pages q).1 $$ Hpv with ⟨Hpv1, Hpv2⟩
    icases (pv_half W.data W.ps W.pages q.half).1 $$ Hpv1 with ⟨Hpk, Hpv1⟩
    have Hl1 : wsLive ws := fun x hx => Hlive x (List.mem_cons_of_mem _ hx)
    have Hw0 := Hlive w (List.mem_cons_self)
    icases ih ins' q.half Hl1 $$ [Hpv2 Hl] with ⟨Hes, Hback⟩
    · iframe
    unfold wOwn
    icases Hw with ⟨%Hfp, Hk, Hv⟩
    icases srcBorrowD W hc q.half.half it.key' w.ks w.key Hw0.1 $$ [Hpk Hk] with ⟨Hk, Hkb⟩
    · iframe
    icases srcBorrowD W hc q.half.half it.value' w.vs w.value Hw0.2 $$ [Hpv1 Hv] with ⟨Hv, Hvb⟩
    · iframe
    simp only [borrowEs]
    isplitl [Hk Hv Hes]
    · iapply (inodesOwn_cons _ _ _ _).2
      iframe
      unfold inodeIs
      iframe
      ipureintro; exact Hfp
    iintro Hall
    icases (inodesOwn_cons _ _ _ _).1 $$ Hall with ⟨Hi, Hes⟩
    unfold inodeIs
    icases Hi with ⟨-, Hk, Hv⟩
    ihave Hk := Hkb $$ Hk
    ihave Hv := Hvb $$ Hv
    ihave Hr := Hback $$ Hes
    icases Hk with ⟨Hpk, Hk⟩
    icases Hv with ⟨Hpv1, Hv⟩
    icases Hr with ⟨Hpv2, Hl⟩
    isplitl [Hpk Hpv1 Hpv2]
    · iapply (pv_half W.data W.ps W.pages q).2
      iframe Hpv2
      iapply (pv_half W.data W.ps W.pages q.half).2
      iframe
    iapply BigSepL2.bigSepL2_cons.2
    iframe
    ipureintro; exact Hfp

/-- Heap copies of the entries, as a writer's node holds them. -/
theorem fresh_wOwn (W : WView) :
    ∀ (ins : List Inode) (ws : List WEntry) (es : List NodeEntry), wMatch ws es →
    inodesOwn (GF := GF) ins (es.map freshEntry) ⊢
      [∗list] it;w ∈ ins;ws.map ownFresh, wOwn W it w := by
  intro ins ws es hm
  induction hm generalizing ins with
  | nil =>
    iintro H
    ihave %Hl := inodesOwn_length _ _ $$ H
    have : ins = [] := List.eq_nil_of_length_eq_zero (by simpa using Hl)
    subst this
    simp only [List.map_nil]
    iapply BigSepL2.bigSepL2_nil.2
    iempintro
  | cons h1 _ ih =>
    rename_i w e ws' es'
    iintro H
    ihave %Hl := inodesOwn_length _ _ $$ H
    cases ins with
    | nil => simp at Hl
    | cons it ins' =>
      simp only [List.map_cons]
      icases (inodesOwn_cons _ _ _ _).1 $$ H with ⟨Hi, H⟩
      iapply BigSepL2.bigSepL2_cons.2
      isplitl [Hi]
      · unfold inodeIs wOwn srcOwn freshEntry ownFresh
        obtain ⟨hf, hp, hk, hv, -, -⟩ := h1
        icases Hi with ⟨%Hfp, Hk, Hv⟩
        simp only
        rw [← hk, ← hv]
        iframe
        ipureintro; exact ⟨Hfp.1.trans hf, Hfp.2.trans hp⟩
      iapply ih ins'
      iexact H

/-- What `dereference` takes of a node of `g` (a node of its tree, but the children). -/
def qPre (g : Loc → DerefIn) (bl l : Loc) : IProp GF :=
  iprop(∃ (nv : node), l ↦ nv ∗ nv.children' ↦* (g l).cs ∗ derefPreW g bl l nv)

/-- What it gives back of it. -/
def qPost (g : Loc → DerefIn) (bl l : Loc) : IProp GF :=
  iprop(∃ (nv : node), l ↦ nv ∗ nv.children' ↦* (g l).cs ∗ derefPostW g bl l nv)

/-- A writer's node lent to `dereference` (its view bytes at the fraction `f`), and back
dereferenced. -/
theorem node_deref_acc (W : WView) (hc : W.data.locCar ≠ 0) (bl l : Loc) (r : NRec) (f : Qp)
    (g : Loc → DerefIn) (hg : g l = dIn r f) (hok : derefOK bl r) :
    nodeOwn (GF := GF) W l r ∗ pagesView W.data W.ps f W.pages ⊢
      qPre g bl l ∗ (qPost g bl l -∗ ∃ nv' ins', ⌜derefNode r (derefRec r nv' ins')⌝ ∗
        nodeOwn W l (derefRec r nv' ins') ∗ pagesView W.data W.ps f W.pages) := by
  obtain ⟨hbl, hlen, hws, hkey⟩ := hok
  have hlive : wsLive r.ws := fun w hw => ⟨(hws w hw).1, (hws w hw).2.1⟩
  have hkeys : ∀ i < (borrowEs r.ws f.half).length, 0 < (entryKey (borrowEs r.ws f.half) i).length := by
    intro i hi
    rw [wMatch_key _ _ (borrowEs_match r.ws f.half)]
    rw [borrowEs_length] at hi
    rw [wKey_get r.ws i hi]
    exact (hws _ (List.getElem_mem hi)).2.2
  iintro ⟨Hnd, Hpv⟩
  isimp only [nodeOwn] at Hnd
  icases Hnd with ⟨Hn, Hins, Hcap, Hents, Hch, Hchcap, Hkey⟩
  icases (pv_half W.data W.ps W.pages f).1 $$ Hpv with ⟨Hpk, Hpe⟩
  icases nodeBorrowD W hc r.ws r.ins f.half hlive $$ [Hpe Hents] with ⟨Hes, Hesback⟩
  · iframe
  unfold qPre qPost derefPreW derefPostW
  rw [hg]
  simp only [dIn]
  -- the new node's resources, from what `dereference` gives back
  have Hnew : ∀ (nv' : node) (insN : List Inode), nv' = { r.nv with key' := nv'.key' } →
      (l ↦ nv' ∗ nv'.children' ↦* r.cs ∗ nv'.inodes' ↦* insN ∗
        inodesOwn insN ((borrowEs r.ws f.half).map freshEntry) ∗
        ownSliceCap Inode r.nv.inodes' (DFrac.own 1) ∗ ownSliceCap Loc r.nv.children' (DFrac.own 1) ∗
        (⌜nv'.key' = slice.nil⌝ ∨ nv'.key' ↦* r.key) : IProp GF) ⊢
      nodeOwn W l (derefRec r nv' insN) := by
    intro nv' insN Hnv'
    have Hni : nv'.inodes' = r.nv.inodes' := by rw [Hnv']
    have Hnc : nv'.children' = r.nv.children' := by rw [Hnv']
    iintro ⟨Hn', Hch', HinsN, HesN, Hcap, Hchcap, Hk⟩
    unfold nodeOwn derefRec
    simp only
    rw [Hni, Hnc]
    rw [← Hni, ← Hnc]
    iframe
    isplitl [HesN]
    · iapply fresh_wOwn W insN r.ws _ (borrowEs_match r.ws f.half)
      iexact HesN
    icases Hk with (%Hkn | Hk)
    · rw [if_pos Hkn]; ipureintro; trivial
    · by_cases hkn : nv'.key' = slice.nil
      · rw [if_pos hkn]; ipureintro; trivial
      · rw [if_neg hkn]; unfold srcOwn; iexact Hk
  have Hrel : ∀ (nv' : node) (insN : List Inode), nv' = { r.nv with key' := nv'.key' } →
      (r.nv.key' = slice.nil → nv'.key' = slice.nil) → derefNode r (derefRec r nv' insN) := by
    intro nv' insN Hnv' Hkk
    refine ⟨?_, rfl, rfl, rfl, Hkk, rfl⟩
    simp only [derefRec]
    rw [Hnv']
  by_cases hk : r.nv.key' = slice.nil
  · rw [if_pos hk] at *
    isplitl [Hn Hch Hins Hes]
    · iexists r.nv
      iframe
      isplitl []
      · ipureintro; exact ⟨rfl, hbl, hkeys⟩
      ileft; ipureintro; exact hk
    iintro ⟨%nv', Hn', Hch', %Hnv', ⟨%insN, HinsN, HesN⟩, Hold, Hkd⟩
    ihave Hb := Hesback $$ Hold
    icases Hb with ⟨Hpe, -⟩
    iexists nv', insN
    icases Hkd with (%Hkn | ⟨%Hkn, -, -⟩)
    · isplitr
      · ipureintro; exact Hrel nv' insN Hnv' (fun _ => Hkn.2)
      isplitl [Hn' Hch' HinsN HesN Hcap Hchcap]
      · iapply Hnew nv' insN Hnv'
        iframe
        ileft; ipureintro; exact Hkn.2
      iapply (pv_half W.data W.ps W.pages f).2
      iframe
    · exact absurd hk Hkn
  · rw [if_neg hk]
    have hks : r.ksrc ≠ Src.stale := by
      rcases hkey with h | ⟨h, -⟩
      · exact absurd h hk
      · exact h
    have hkp : r.nv.pgid' = W64 0 ∨ 0 < r.key.length := by
      rcases hkey with h | ⟨-, h⟩
      · exact absurd h hk
      · exact h
    icases srcBorrowD W hc f.half r.nv.key' r.ksrc r.key hks $$ [Hpk Hkey] with ⟨Hk, Hkback⟩
    · iframe
    isplitl [Hn Hch Hins Hes Hk]
    · iexists r.nv
      iframe
      isplitl []
      · ipureintro; exact ⟨rfl, hbl, hkeys⟩
      iright
      iframe
      ipureintro; exact hkp
    iintro ⟨%nv', Hn', Hch', %Hnv', ⟨%insN, HinsN, HesN⟩, Hold, Hkd⟩
    ihave Hb := Hesback $$ Hold
    icases Hb with ⟨Hpe, -⟩
    iexists nv', insN
    icases Hkd with (%Hkn | ⟨-, Hko, Hkn⟩)
    · exact absurd Hkn.1 hk
    ihave Hb := Hkback $$ Hko
    icases Hb with ⟨Hpk, -⟩
    isplitr
    · ipureintro; exact Hrel nv' insN Hnv' (fun h => absurd h hk)
    isplitl [Hn' Hch' HinsN HesN Hcap Hchcap Hkn]
    · iapply Hnew nv' insN Hnv'
      iframe
    iapply (pv_half W.data W.ps W.pages f).2
    iframe

theorem pv_list (W : WView) : ∀ (S : List Loc) (q : Qp), S.Nodup →
    pagesView (GF := GF) W.data W.ps q W.pages ⊢
      ([∗list] l ∈ S, pagesView W.data W.ps (fracOf S q l) W.pages) ∗
      (([∗list] l ∈ S, pagesView W.data W.ps (fracOf S q l) W.pages) -∗
        pagesView W.data W.ps q W.pages)
  | [], q, _ => by
    iintro H
    isplitl []
    · iapply BigSepL.bigSepL_nil.2; iempintro
    iintro -; iexact H
  | x :: xs, q, hnd => by
    have hx : x ∉ xs := (List.nodup_cons.1 hnd).1
    have hf : ∀ l ∈ xs, fracOf (x :: xs) q l = fracOf xs q.half l := by
      intro l hl; simp only [fracOf]; rw [if_neg (fun (h : l = x) => hx (h ▸ hl))]
    have hfx : fracOf (x :: xs) q x = q.half := by simp [fracOf]
    have e1 : ([∗list] l ∈ xs, pagesView (GF := GF) W.data W.ps (fracOf xs q.half l) W.pages) ⊢
        [∗list] l ∈ xs, pagesView (GF := GF) W.data W.ps (fracOf (x :: xs) q l) W.pages :=
      BigSepL.bigSepL_mono (fun hk => by rw [hf _ (List.mem_of_getElem? hk)])
    have e2 : ([∗list] l ∈ xs, pagesView (GF := GF) W.data W.ps (fracOf (x :: xs) q l) W.pages) ⊢
        [∗list] l ∈ xs, pagesView (GF := GF) W.data W.ps (fracOf xs q.half l) W.pages :=
      BigSepL.bigSepL_mono (fun hk => by rw [hf _ (List.mem_of_getElem? hk)])
    iintro H
    icases (pv_half W.data W.ps W.pages q).1 $$ H with ⟨H1, H2⟩
    icases pv_list W xs q.half (List.nodup_cons.1 hnd).2 $$ H2 with ⟨Hl, Hback⟩
    isplitl [H1 Hl]
    · iapply BigSepL.bigSepL_cons.2
      rw [hfx]
      iframe H1
      iapply e1
      iexact Hl
    iintro Hall
    icases BigSepL.bigSepL_cons.1 $$ Hall with ⟨H1, Hl⟩
    rw [hfx]
    ihave Hl := e2 $$ Hl
    ihave H2 := Hback $$ Hl
    iapply (pv_half W.data W.ps W.pages q).2
    iframe

/-- Some entries of a map, as a list (the rest dropped). -/
theorem map_list {V : Type} (Φ : Loc → V → IProp GF) : ∀ (S : List Loc) (m : GMap Loc V), S.Nodup →
    (∀ l ∈ S, (m !! l).isSome) →
    ([∗map] l ↦ v ∈ m, Φ l v) ⊢ [∗list] l ∈ S, ∃ v, ⌜m !! l = some v⌝ ∗ Φ l v
  | [], m, _, _ => by
    iintro -; iapply BigSepL.bigSepL_nil.2; iempintro
  | x :: xs, m, hnd, hdom => by
    have hx : x ∉ xs := (List.nodup_cons.1 hnd).1
    cases h : m !! x with
    | none =>
      have := hdom x List.mem_cons_self; rw [h] at this; cases this
    | some v =>
      iintro H
      icases (BigSepM.bigSepM_delete (M := GMap Loc) (Φ := Φ) (show Std.get? m x = some v from h)).1 $$ H
        with ⟨Hx, H⟩
      isplitl [Hx]
      · iexists v; iframe; ipureintro; exact h
      have hdom' : ∀ l ∈ xs, ((Std.delete m x) !! l).isSome := by
        intro l hl
        have hne : x ≠ l := fun e => hx (e ▸ hl)
        change ((GMap.delete x m) !! l).isSome
        rw [GMap.lookup_delete_ne _ hne]; exact hdom l (List.mem_cons_of_mem _ hl)
      ihave H := map_list Φ xs (Std.delete m x) (List.nodup_cons.1 hnd).2 hdom' $$ H
      iapply (BigSepL.bigSepL_mono ?_) $$ H
      intro k l hl
      iintro ⟨%v', %hv', Hv⟩
      iexists v'; iframe; ipureintro
      have hne : x ≠ l := fun e => hx (e ▸ List.mem_of_getElem? hl)
      change (GMap.delete x m) !! l = some v' at hv'
      rw [GMap.lookup_delete_ne _ hne] at hv'; exact hv'

/-- Entries of a list, as a map. -/
theorem list_map {V : Type} (Φ : Loc → V → IProp GF) (P : Loc → V → Prop) :
    ∀ (S : List Loc), S.Nodup →
    ([∗list] l ∈ S, ∃ v, ⌜P l v⌝ ∗ Φ l v) ⊢ ∃ (M : GMap Loc V),
      ⌜(∀ l, (M !! l).isSome ↔ l ∈ S) ∧ ∀ l v, M !! l = some v → P l v⌝ ∗ [∗map] l ↦ v ∈ M, Φ l v
  | [], _ => by
    iintro -
    iexists ∅
    isplitr
    · ipureintro
      exact ⟨fun l => by simp, fun l v h => by simp at h⟩
    iapply BigSepM.bigSepM_empty.2; iempintro
  | x :: xs, hnd => by
    have hx : x ∉ xs := (List.nodup_cons.1 hnd).1
    iintro H
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨⟨%v, %hv, Hx⟩, H⟩
    ihave H := list_map Φ P xs (List.nodup_cons.1 hnd).2 $$ H
    icases H with ⟨%M, %HM, HM⟩
    obtain ⟨hdom, hP⟩ := HM
    have hnone : M !! x = none := by
      cases h : M !! x with
      | none => rfl
      | some _ => exact absurd ((hdom x).1 (by rw [h]; rfl)) hx
    iexists (<[x := v]> M)
    isplitr
    · ipureintro
      refine ⟨fun l => ?_, fun l v' h => ?_⟩
      · by_cases e : l = x
        · subst e; rw [GMap.lookup_insert]; simp
        · rw [GMap.lookup_insert_ne _ _ (Ne.symm e)]; rw [hdom l]; simp [e]
      · by_cases e : l = x
        · subst e; rw [GMap.lookup_insert] at h; cases h; exact hv
        · rw [GMap.lookup_insert_ne _ _ (Ne.symm e)] at h; exact hP l v' h
    iapply (BigSepM.bigSepM_insert (M := GMap Loc) (Φ := Φ) (show Std.get? M x = none from hnone)).2
    iframe

theorem nodeTreeW_mono (P : Loc → node → IProp GF) (g : Loc → DerefIn) :
    ∀ (d d' : Nat) (c : Loc), d ≤ d' → nodeTreeW P g d c ⊢ nodeTreeW P g d' c
  | 0, _, c, _ => by iintro H; icases (nodeTreeW_zero _ _ _).1 $$ H with %H; exact H.elim
  | d + 1, 0, c, h => by omega
  | d + 1, d' + 1, c, h => by
    iintro H
    icases (nodeTreeW_succ _ _ _ _).1 $$ H with ⟨%nv, Hn, Hcs, Hp, Hk⟩
    iapply (nodeTreeW_succ _ _ _ _).2
    iexists nv
    iframe
    iapply (BigSepL.bigSepL_mono (fun _ => nodeTreeW_mono P g d d' _ (by omega))) $$ Hk

/-- The nodes of a tree (its nodes `S`), as a tree of `g` (its children those of the records). -/
theorem tree_of_list (P : Loc → node → IProp GF) (g : Loc → DerefIn) (ns : GMap Loc NRec) :
    ∀ (n : Nat) (t : Loc) (S : List Loc), S.length ≤ n → kidsTree ns t S →
    (∀ l ∈ S, ∃ r, ns !! l = some r ∧ (g l).cs = r.cs) →
    ([∗list] l ∈ S, ∃ nv, l ↦ nv ∗ nv.children' ↦* (g l).cs ∗ P l nv) ⊢ nodeTreeW P g n t := by
  intro n
  induction n with
  | zero =>
    intro t S hl hk
    cases hk with
    | mk _ r subs _ _ _ => simp at hl
  | succ n ih =>
    intro t S hl hk hg
    cases hk with
    | mk _ r subs hr hF hnd =>
      obtain ⟨r', hr', hcs⟩ := hg t List.mem_cons_self
      rw [hr] at hr'; cases hr'
      iintro H
      icases BigSepL.bigSepL_cons.1 $$ H with ⟨⟨%nv, Hn, Hcs, Hp⟩, H⟩
      iapply (nodeTreeW_succ _ _ _ _).2
      iexists nv
      iframe
      rw [hcs]
      have hsub : ∀ (cs : List Loc) (ss : List (List Loc)), List.Forall₂ (kidsTree ns) cs ss →
          ss.flatten.length ≤ n → (∀ l ∈ ss.flatten, ∃ r, ns !! l = some r ∧ (g l).cs = r.cs) →
          ([∗list] l ∈ ss.flatten, ∃ nv, l ↦ nv ∗ nv.children' ↦* (g l).cs ∗ P l nv) ⊢
            [∗list] c ∈ cs, nodeTreeW P g n c := by
        intro cs ss hF2
        induction hF2 with
        | nil => intro _ _; iintro -; iapply BigSepL.bigSepL_nil.2; iempintro
        | @cons c s cs' ss' hk2 _ ih2 =>
          intro hlen hg2
          simp only [List.flatten_cons, List.length_append] at hlen
          simp only [List.flatten_cons]
          iintro H
          icases (BigSepL.bigSepL_append).1 $$ H with ⟨H1, H2⟩
          iapply BigSepL.bigSepL_cons.2
          isplitl [H1]
          · iapply (ih c s (by omega) hk2 (fun l hl => hg2 l (by simp [List.mem_flatten] at hl ⊢; exact Or.inl hl)))
            iexact H1
          · iapply (ih2 (by omega) (fun l hl => hg2 l (by simp only [List.flatten_cons, List.mem_append]; exact Or.inr hl)))
            iexact H2
      iapply (hsub r.cs subs hF (by simp only [List.length_cons] at hl; omega) (fun l hl => hg l (List.mem_cons_of_mem _ hl)))
      iexact H

/-- A tree of `g` from `t`, as the list of its nodes. -/
theorem list_of_tree (P : Loc → node → IProp GF) (g : Loc → DerefIn) (ns : GMap Loc NRec) :
    ∀ (n : Nat) (t : Loc) (S : List Loc), kidsTree ns t S →
    (∀ l ∈ S, ∃ r, ns !! l = some r ∧ (g l).cs = r.cs) →
    nodeTreeW P g n t ⊢ [∗list] l ∈ S, ∃ nv, l ↦ nv ∗ nv.children' ↦* (g l).cs ∗ P l nv := by
  intro n
  induction n with
  | zero =>
    intro t S _ _
    iintro H; icases (nodeTreeW_zero _ _ _).1 $$ H with %H; exact H.elim
  | succ n ih =>
    intro t S hk hg
    cases hk with
    | mk _ r subs hr hF hnd =>
      obtain ⟨r', hr', hcs⟩ := hg t List.mem_cons_self
      rw [hr] at hr'; cases hr'
      iintro H
      icases (nodeTreeW_succ _ _ _ _).1 $$ H with ⟨%nv, Hn, Hcs, Hp, Hk⟩
      iapply BigSepL.bigSepL_cons.2
      isplitl [Hn Hcs Hp]
      · iexists nv; iframe
      rw [hcs]
      have hsub : ∀ (cs : List Loc) (ss : List (List Loc)), List.Forall₂ (kidsTree ns) cs ss →
          (∀ l ∈ ss.flatten, ∃ r, ns !! l = some r ∧ (g l).cs = r.cs) →
          ([∗list] c ∈ cs, nodeTreeW P g n c) ⊢
            [∗list] l ∈ ss.flatten, ∃ nv, l ↦ nv ∗ nv.children' ↦* (g l).cs ∗ P l nv := by
        intro cs ss hF2
        induction hF2 with
        | nil => intro _; iintro -; simp only [List.flatten_nil]; iapply BigSepL.bigSepL_nil.2; iempintro
        | @cons c s cs' ss' hk2 _ ih2 =>
          intro hg2
          iintro H
          icases BigSepL.bigSepL_cons.1 $$ H with ⟨H1, H2⟩
          simp only [List.flatten_cons]
          iapply (BigSepL.bigSepL_append).2
          isplitl [H1]
          · iapply (ih c s hk2 (fun l hl => hg2 l (by simp [List.mem_flatten] at hl ⊢; exact Or.inl hl)))
            iexact H1
          · iapply (ih2 (fun l hl => hg2 l (by simp only [List.flatten_cons, List.mem_append]; exact Or.inr hl)))
            iexact H2
      iapply (hsub r.cs subs hF (fun l hl => hg l (List.mem_cons_of_mem _ hl)))
      iexact Hk

/-- The nodes of a parent chain, out of the bucket's nodes (for `node.root`), and back. -/
theorem chain_acc (W : WView) (ns : GMap Loc NRec) :
    ∀ (l : Loc) (p : List Loc) (t : Loc), upPath ns l p t → p.Nodup → ∀ (m : GMap Loc NRec),
    (∀ x ∈ p, m !! x = ns !! x) →
    ([∗map] x ↦ r ∈ m, nodeOwn (GF := GF) W x r) ⊢
      ([∗list] y ∈ chainList ns p, y.1 ↦ y.2) ∗
      (([∗list] y ∈ chainList ns p, y.1 ↦ y.2) -∗ [∗map] x ↦ r ∈ m, nodeOwn (GF := GF) W x r) := by
  intro l p t h
  induction h with
  | self l r hr hp =>
    intro _ m hm
    have hm' := (hm l List.mem_cons_self).trans hr
    iintro H
    icases (BigSepM.bigSepM_lookup_acc (M := GMap Loc) (Φ := fun x r => nodeOwn (GF := GF) W x r)
      (show Std.get? m l = some r from hm')).1 $$ H with ⟨Hl, Hback⟩
    isimp only [nodeOwn] at Hl
    icases Hl with ⟨Hn, Hrest⟩
    simp only [chainList, List.map_cons, List.map_nil, hr, Option.map_some, Option.getD_some]
    isplitl [Hn]
    · iapply BigSepL.bigSepL_cons.2
      iframe
      iapply BigSepL.bigSepL_nil.2; iempintro
    iintro Hl
    icases BigSepL.bigSepL_cons.1 $$ Hl with ⟨Hn, -⟩
    iapply Hback
    unfold nodeOwn; iframe
  | up l r p t hr hp hu ih =>
    intro hnd m hm
    have hm' := (hm l List.mem_cons_self).trans hr
    have hl : l ∉ p := (List.nodup_cons.1 hnd).1
    iintro H
    icases (BigSepM.bigSepM_delete (M := GMap Loc) (Φ := fun x r => nodeOwn (GF := GF) W x r)
      (show Std.get? m l = some r from hm')).1 $$ H with ⟨Hl, H⟩
    isimp only [nodeOwn] at Hl
    icases Hl with ⟨Hn, Hrest⟩
    have hm2 : ∀ x ∈ p, (Std.delete m l) !! x = ns !! x := by
      intro x hx
      have hne : l ≠ x := fun e => hl (e ▸ hx)
      change (GMap.delete l m) !! x = ns !! x
      rw [GMap.lookup_delete_ne _ hne]; exact hm x (List.mem_cons_of_mem _ hx)
    icases ih (List.nodup_cons.1 hnd).2 (Std.delete m l) hm2 $$ H with ⟨Hc, Hcback⟩
    have he : chainList ns (l :: p) = (l, r.nv) :: chainList ns p := by
      simp [chainList, hr]
    rw [he]
    isplitl [Hn Hc]
    · iapply BigSepL.bigSepL_cons.2
      iframe
    iintro Hl
    icases BigSepL.bigSepL_cons.1 $$ Hl with ⟨Hn, Hc⟩
    ihave H := Hcback $$ Hc
    iapply (BigSepM.bigSepM_delete (M := GMap Loc) (Φ := fun x r => nodeOwn (GF := GF) W x r)
      (show Std.get? m l = some r from hm')).2
    iframe
    unfold nodeOwn; iframe

/-- The tree of a bucket's nodes from `top` (its nodes `S`), lent to `dereference` (the view's
fraction `q` shared among them), and back: the nodes dereferenced (the others dropped). -/
theorem bkt_tree_acc (W : WView) (hc : W.data.locCar ≠ 0) (bl : Loc) (ns : GMap Loc NRec)
    (top : Loc) (S : List Loc) (hk : kidsTree ns top S)
    (hok : ∀ l ∈ S, ∃ r, ns !! l = some r ∧ derefOK bl r) (q : Qp) :
    pagesView (GF := GF) W.data W.ps q W.pages ∗ ([∗map] l ↦ r ∈ ns, nodeOwn W l r) ⊢
      nodeTreeW (derefPreW (gOf ns S q) bl) (gOf ns S q) S.length top ∗
      (nodeTreeW (derefPostW (gOf ns S q) bl) (gOf ns S q) S.length top -∗
        ∃ (M : GMap Loc NRec), ⌜(∀ l, (M !! l).isSome ↔ l ∈ S) ∧
          ∀ l r', M !! l = some r' → ∃ r, ns !! l = some r ∧ derefNode r r'⌝ ∗
          pagesView W.data W.ps q W.pages ∗ [∗map] l ↦ r ∈ M, nodeOwn W l r) := by
  have hnd := kidsTree_nodup ns top S hk
  have hdom : ∀ l ∈ S, (ns !! l).isSome := by
    intro l hl; obtain ⟨r, hr, -⟩ := hok l hl; rw [hr]; rfl
  have hgcs : ∀ l ∈ S, ∃ r, ns !! l = some r ∧ (gOf ns S q l).cs = r.cs := by
    intro l hl; obtain ⟨r, hr, -⟩ := hok l hl
    exact ⟨r, hr, by simp [gOf, hr, dIn]⟩
  iintro ⟨Hpv, Hm⟩
  icases pv_list W S q hnd $$ Hpv with ⟨Hpl, Hpback⟩
  ihave Hl := map_list (fun l r => nodeOwn (GF := GF) W l r) S ns hnd hdom $$ Hm
  ihave Hb := (BigSepL.bigSepL_sep_eqv_symm).1 $$ [Hl Hpl]
  · iframe
  ihave Hb := (BigSepL.bigSepL_mono (Ψ := fun _ l => iprop(qPre (GF := GF) (gOf ns S q) bl l ∗
      (qPost (gOf ns S q) bl l -∗ ∃ r', ⌜∃ r, ns !! l = some r ∧ derefNode r r'⌝ ∗ nodeOwn W l r' ∗
        pagesView W.data W.ps (fracOf S q l) W.pages))) ?_) $$ Hb
  · intro k l hl
    iintro ⟨⟨%r, %hr, Hn⟩, Hp⟩
    obtain ⟨r0, hr0, hok0⟩ := hok l (List.mem_of_getElem? hl)
    rw [hr] at hr0; cases hr0
    icases node_deref_acc W hc bl l r (fracOf S q l) (gOf ns S q) (by simp [gOf, hr]) hok0 $$ [Hn Hp]
      with ⟨Hpre, Hback⟩
    · iframe
    iframe Hpre
    iintro Hpost
    ihave H := Hback $$ Hpost
    icases H with ⟨%nv', %ins', %Hd, Hn, Hp⟩
    iexists (derefRec r nv' ins')
    iframe
    ipureintro; exact ⟨r, hr, Hd⟩
  icases (BigSepL.bigSepL_sep_eqv).1 $$ Hb with ⟨Hpre, Hback⟩
  isimp only [qPre] at Hpre
  isimp only [qPost] at Hback
  isplitl [Hpre]
  · iapply (tree_of_list _ _ ns S.length top S (Nat.le_refl _) hk hgcs)
    iexact Hpre
  iintro Hpost
  ihave Hpost := (list_of_tree _ _ ns S.length top S hk hgcs) $$ Hpost
  ihave Hr := (BigSepL.bigSepL_wand) $$ Hpost Hback
  ihave Hr := (BigSepL.bigSepL_mono (Ψ := fun _ l => iprop((∃ r', ⌜∃ r, ns !! l = some r ∧ derefNode r r'⌝ ∗
      nodeOwn (GF := GF) W l r') ∗ pagesView W.data W.ps (fracOf S q l) W.pages)) ?_) $$ Hr
  · intro k l _
    iintro ⟨%r', %Hd, Hn, Hp⟩
    iframe
    ipureintro; exact Hd
  icases (BigSepL.bigSepL_sep_eqv).1 $$ Hr with ⟨Hn, Hp⟩
  ihave Hpv := Hpback $$ Hp
  ihave HM := list_map (fun l r => nodeOwn (GF := GF) W l r)
    (fun l r' => ∃ r, ns !! l = some r ∧ derefNode r r') S hnd $$ Hn
  icases HM with ⟨%M, %HM, HM⟩
  iexists M
  iframe
  ipureintro; exact HM

end own

end bbolt
end EtcdGrove
end Perennial
