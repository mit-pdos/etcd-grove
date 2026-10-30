/-
`node.spill`'s posts (`Proof/go_etcd_io/bbolt/SpillNodeCore.lean`): after the parts loop, the
state the proof is in (`SpExit`: `node.spill.wp_core`'s premises, the children loop's end
`loopP`, the split `rc`, `B3`, `T3`, `xs`, the parts loop's start and end `partsP`, the first
part `rn5`) and what it gives:

* no parent (`spPost_root`): the part is the bucket's root, `finPost`;
* the existing parent (`spPost_sub`): `subPost`;
* a new parent (pgid 0; `n.children` set nil, `B7`, `T7`): its tokens (`spNewParent_toks`) and
  `topSpecB`'s premises (`spNewParent_pre`) for its spill, and its `finPost` that of the node
  (`spNewParent_post`).
-/
module

public import Proof.go_etcd_io.bbolt.SpillNodeStep
public import Spec.go_etcd_io.bbolt.node__split_x

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section own
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]
variable [float_sem : go.FloatConvSemantics]

/-- The state after `node.spill`'s parts loop (see the module doc; the fields are named as the
hypotheses of `node.spill.wp_core`'s proof). -/
structure SpExit (N : Nat) (top : Bool) (I : FLImpl (GF := GF)) (W : WView) (txl : Loc)
    (txid : w64) (T : WTx) (ρ : DBState) (F : GMap Nat (List w8)) (K : Loc → Bool) (bl : Loc)
    (B : BRec) (bnd : Loc → Option (List w8) × Option (List w8)) (kd ht : Loc → Nat) (n : Loc)
    (r : NRec) (sp : Loc → Bool) (sub : Loc → List Loc)
    (W' : WView) (T' : WTx) (ρ' : DBState) (F' : GMap Nat (List w8)) (K' : Loc → Bool)
    (B' : BRec) (rn : NRec) (i : Nat) (sp' : Loc → Bool) (sub' : Loc → List Loc)
    (rc : NRec) (B3 : BRec) (T3 : WTx) (xs : List (Loc × node × List Inode))
    (Ts : WTx) (Bs : BRec) (Ks : Loc → Bool) (par : Loc) (ws0 : List WEntry) (i0 : Nat)
    (W'' : WView) (T'' : WTx) (ρ'' : DBState) (F'' : GMap Nat (List w8)) (K'' : Loc → Bool)
    (B'' : BRec) (ps : List (w64 × List w8)) (rn5 : NRec) : Prop where
  hf : I.FreeSpec
  hg : spillG (hG := hG) W txl txid T ρ F
  hB : T.bs !! bl = some B
  hHt : top = false → nodeHts B ht
  hht0 : r.nv.isLeaf' = true → ht n = 0
  hht1 : r.nv.isLeaf' = false → 1 ≤ ht n
  hn : B.ns !! n = some r
  hK : K n = false
  hL : nodeL W bl B bnd kd n r
  hch : ∀ c ∈ r.cs, kidsTree B.ns c (sub c) ∧
    (sp c = true → spilledN bl B c) ∧
    (sp c = false → (sub c).length < N ∧ subU W bl B bnd kd K c (sub c))
  htopc : top = true → (∀ c ∈ r.cs, sp c = true) ∧ r.ws.length ≤ N
  hkt : kidsTree B.ns n (n :: (r.cs.map sub).flatten)
  hthr : uint.Z (splitThr (W64 (W.ps : Int)) B.bv.FillPercent') ≤ W.ps
  hps : W.ps < 2 ^ 20
  hel : ∀ l r, B.ns !! l = some r → ∀ w ∈ r.ws, w.key.length + w.value.length ≤ 2 ^ 28
  hne : ∀ l r, B.ns !! l = some r → r.nv.parent' ≠ null → 0 < r.ws.length
  hP1 : ∀ l r, B.ns !! l = some r → l ≠ n → r.nv.isLeaf' = false → r.nv.pgid' ≠ W64 0
  hP1n : top = false → r.nv.isLeaf' = false → r.nv.pgid' ≠ W64 0
  hP2 : ∀ c l, B.nm !! c = some l → c = W64 0 ∨ (W.pages !! uint.nat c).isSome
  hP3 : ∀ l r w, B.ns !! l = some r → r.nv.isLeaf' = false → w ∈ r.ws →
    (spillPages W T !! uint.nat w.pgid).isSome
  htok : top = false → treeOK bl B
  hpar0 : r.nv.parent' = null → bnd n = (none, none) ∧
    ∃ p, upPath B.ns B.bv.rootNode' p n ∧ p.Nodup ∧
      ∀ l, (B.ns !! l).isSome → l ∈ p ∨ l ∈ (r.cs.map sub).flatten
  hplf : ∀ pl rp, r.nv.parent' = pl → pl ≠ null → B.ns !! pl = some rp →
    pl ∉ n :: (r.cs.map sub).flatten ∧ K pl = false ∧ nodeL W bl B bnd kd pl rp ∧
    rp.nv.pgid' ≠ W64 0 ∧ rp.nv.isLeaf' = false
  hpar1 : r.nv.parent' ≠ null → (B.ns !! r.nv.parent').isSome
  hnn : n ≠ null
  hlp : loopP (hG := hG) bl bnd kd ht N n txl txid W T B r K (n :: (r.cs.map sub).flatten)
    W' T' ρ' F' K' B' rn i sp' sub'
  htrp : top = false → treeOK bl B'
  hall : ∀ c ∈ rn.cs, spilledN bl B' c
  hdrop : rn.cs.drop i = []
  hrc : rc = NRec.mk ({ rn.nv with children' := slice.nil } : node) rn.ins rn.ws [] rn.key rn.ksrc
  hB3 : B3 = ({ setN B' n rc with ns := cutNs (setN B' n rc).ns (onRootPath B') rn.cs } : BRec)
  hT3 : T3 = setB (setB T' bl (setN B' n rc)) bl B3
  hxsf : splitIdxOK (splitThr (W64 (W'.ps : Int)) B3.bv.FillPercent') xs ∧
    lastFits (W64 (W'.ps : Int)) xs
  hst : partsP (hG := hG) bl txl txid n rc xs par ws0 i0 (bnd n).1 (bnd n).2 W' Ts Bs Ks
      W' Ts ρ' F' Ks Bs [] ∧
    startP bl n rc xs par Bs ws0 i0 ∧ spillFrame T3 Ts (· = bl)
  hPs : spillPages W' Ts = spillPages W' T'
  hpp : partsP (hG := hG) bl txl txid n rc xs par ws0 i0 (bnd n).1 (bnd n).2 W' Ts Bs Ks
    W'' T'' ρ'' F'' K'' B'' ps
  hpx : ps.length = xs.length
  hrn5 : B''.ns !! n = some rn5
  hpar5 : rn5.nv.parent' = par
  hsr : splitRes bl n rc ((B3.ns !! rc.nv.parent').getD rc) xs T3 B3 K' Ts Bs Ks par
  htopn : top = true → r.nv.parent' = null
  htopP : top = true → ∃ p, upPath B'.ns B.bv.rootNode' p n ∧ p.Nodup ∧
    (∀ l, (B'.ns !! l).isSome → l ∈ p ∨ l ∈ rn.cs) ∧
    ∀ l ∈ p, l = n ∨ l ∈ rn.cs ∨ ∃ r', B'.ns !! l = some r' ∧ noViewRec r'
  htopw : top = true → rn.ws.length ≤ N
  hpw : ∀ j x rx, j < ps.length → (xs[j]?).map (fun x => x.1) = some x → B''.ns !! x = some rx →
    rx.ws.map ownFresh = ((chunksOf rc xs).getD j []).map ownFresh ∧ rx.nv.isLeaf' = rc.nv.isLeaf'
  h3nn : ∀ l r3, B3.ns !! l = some r3 → l ≠ null

variable {N : Nat} {top : Bool} {I : FLImpl (GF := GF)} {W : WView} {txl : Loc} {txid : w64}
  {T : WTx} {ρ : DBState} {F : GMap Nat (List w8)} {K : Loc → Bool} {bl : Loc} {B : BRec}
  {bnd : Loc → Option (List w8) × Option (List w8)} {kd ht : Loc → Nat} {n : Loc} {r : NRec}
  {sp : Loc → Bool} {sub : Loc → List Loc}
  {W' : WView} {T' : WTx} {ρ' : DBState} {F' : GMap Nat (List w8)} {K' : Loc → Bool} {B' : BRec}
  {rn : NRec} {i : Nat} {sp' : Loc → Bool} {sub' : Loc → List Loc}
  {rc : NRec} {B3 : BRec} {T3 : WTx} {xs : List (Loc × node × List Inode)}
  {Ts : WTx} {Bs : BRec} {Ks : Loc → Bool} {par : Loc} {ws0 : List WEntry} {i0 : Nat}
  {W'' : WView} {T'' : WTx} {ρ'' : DBState} {F'' : GMap Nat (List w8)} {K'' : Loc → Bool}
  {B'' : BRec} {ps : List (w64 × List w8)} {rn5 : NRec}

set_option linter.unusedSectionVars false
variable [hash_sem : _root_.Perennial.hash.Hash64.TypeAssumptions]

local notation "SPX" => SpExit (hG := hG) N top I W txl txid T ρ F K bl B bnd kd ht n r sp sub W' T'
  ρ' F' K' B' rn i sp' sub' rc B3 T3 xs Ts Bs Ks par ws0 i0 W'' T'' ρ'' F'' K'' B'' ps rn5

/-! ### Pure facts of the exit state -/

theorem spP_fresh_idem (ws : List WEntry) : (ws.map ownFresh).map ownFresh = ws.map ownFresh := by
  simp only [List.map_map]; rfl

/-- What `dnK` keeps. -/
theorem spP_dnK {r r' : NRec} (h : dnK r r') :
    r'.nv = { r.nv with key' := r'.nv.key' } ∧ r'.cs = r.cs ∧ r'.key = r.key ∧
    r'.ws.map ownFresh = r.ws.map ownFresh ∧
    (r.nv.key' = slice.nil → r'.nv.key' = slice.nil) ∧
    (r'.ksrc = r.ksrc ∨ r'.ksrc = Src.own (DFrac.own 1)) ∧
    (r.ins.length = r.ws.length → r'.ins.length = r'.ws.length) := by
  rcases h with rfl | ⟨⟨⟨-, hws, hcs, hkey, hkn, hks, hil⟩, -⟩, hnv'⟩
  · exact ⟨rfl, rfl, rfl, rfl, id, Or.inl rfl, id⟩
  · refine ⟨hnv', hcs, hkey, by rw [hws, spP_fresh_idem], hkn, Or.inr hks, fun _ => hil⟩

theorem spP_stale_fresh (ws : List WEntry) : (ws.map staleW).map ownFresh = ws.map ownFresh := by
  simp only [List.map_map]; rfl

theorem spP_dnK_trans {r r1 r2 : NRec} (h1 : dnK r r1) (h2 : dnK r1 r2) : dnK r r2 :=
  dnK_step r r1 r2 h1 h2

/-- The node `n`'s record after the cut. -/
theorem spP_rc (h : SPX) :
    rc.nv.parent' = r.nv.parent' ∧ rc.nv.isLeaf' = r.nv.isLeaf' ∧ rc.nv.pgid' = r.nv.pgid' ∧
    rc.nv.bucket' = bl ∧ rc.ws = rn.ws ∧ rc.ins = rn.ins ∧ rc.key = r.key ∧ rc.cs = [] := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hnv, hkey, -, -, hL, -⟩ := h.hlp
  have e := h.hrc
  subst e
  refine ⟨?_, ?_, ?_, hL.1, rfl, rfl, hkey, rfl⟩
  · show rn.nv.parent' = r.nv.parent'; rw [hnv]
  · show rn.nv.isLeaf' = r.nv.isLeaf'; rw [hnv]
  · show rn.nv.pgid' = r.nv.pgid'; rw [hnv]

/-- The cut's nodes. -/
theorem spP_B3 (h : SPX) :
    B3.ns !! n = some rc ∧ (∀ x, x ≠ n → x ∉ rn.cs → B3.ns !! x = B'.ns !! x) ∧
    (∀ x ∈ rn.cs, B3.ns !! x = if onRootPath B' x then (B'.ns !! x).map staleRec else none) ∧
    B3.bv = B'.bv ∧ B3.ib = B'.ib ∧ B3.nm = B'.nm ∧ B3.bm = B'.bm := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hnd, hnc, -⟩ := h.hlp
  have e := h.hB3
  subst e
  have hl : ∀ x, cutNs (setN B' n rc).ns (onRootPath B') rn.cs !! x =
      if x ∈ rn.cs then (if onRootPath B' x then ((setN B' n rc).ns !! x).map staleRec else none)
      else (setN B' n rc).ns !! x := cutNs_lookup _ _ _ hnd
  refine ⟨?_, fun x hx hxc => ?_, fun x hx => ?_, rfl, rfl, rfl, rfl⟩
  · show cutNs (setN B' n rc).ns (onRootPath B') rn.cs !! n = some rc
    rw [hl, if_neg hnc]; exact GMap.lookup_insert _ _ _
  · show cutNs (setN B' n rc).ns (onRootPath B') rn.cs !! x = B'.ns !! x
    rw [hl, if_neg hxc]; exact GMap.lookup_insert_ne _ _ (Ne.symm hx)
  · show cutNs (setN B' n rc).ns (onRootPath B') rn.cs !! x = _
    have hxn : x ≠ n := fun e => hnc (e ▸ hx)
    rw [hl, if_pos hx]
    have e2 : (setN B' n rc).ns !! x = B'.ns !! x := GMap.lookup_insert_ne _ _ (Ne.symm hxn)
    rw [e2]

/-- The split's buckets: the same but for the nodes. -/
theorem spP_Bs (h : SPX) :
    Bs.bv = B3.bv ∧ Bs.ib = B3.ib ∧ Bs.nm = B3.nm ∧ Bs.bm = B3.bm ∧
    ∀ x, x ∉ xs.map (fun x => x.1) → x ≠ par → Bs.ns !! x = B3.ns !! x := by
  rcases h.hsr with ⟨-, -, rfl, -⟩ | ⟨pv', pcs', st, -, -, -, hfr, -, rfl, -, -⟩
  · exact ⟨rfl, rfl, rfl, rfl, fun _ _ _ => rfl⟩
  · exact ⟨rfl, rfl, rfl, rfl, fun x hx hp => splitNs_other _ _ _ _ _ _ _ x hx hp⟩

/-- The transaction: only the bucket `bl` changed. -/
theorem spP_frame (h : SPX) : spillFrame T T'' (· = bl) := by
  obtain ⟨-, hB', -, -, hfr, -⟩ := h.hlp
  have h2 := spillFrame_setB T' bl (setN B' n rc) (by rw [hB']; rfl)
  have h3 := spillFrame_setB (setB T' bl (setN B' n rc)) bl B3
    (by show ((<[bl := setN B' n rc]> T'.bs) !! bl).isSome; rw [GMap.lookup_insert]; rfl)
  have e := h.hT3
  rw [← e] at h3
  have h4 := h.hst.2.2
  have h5 := h.hpp.2.2.1
  exact spillFrame_transN _ _ _ _ _
    (spillFrame_transN _ _ _ _ _
      (spillFrame_transN _ _ _ _ _ (spillFrame_transN _ _ _ _ _ hfr h2 (fun _ h => h)) h3
        (fun _ h => h)) h4 (fun _ h => h)) h5 (fun _ h => h)

theorem spP_frame' (h : SPX) : spillFrame T' T'' (· = bl) := by
  obtain ⟨-, hB', -⟩ := h.hlp
  have h2 := spillFrame_setB T' bl (setN B' n rc) (by rw [hB']; rfl)
  have h3 := spillFrame_setB (setB T' bl (setN B' n rc)) bl B3
    (by show ((<[bl := setN B' n rc]> T'.bs) !! bl).isSome; rw [GMap.lookup_insert]; rfl)
  have e := h.hT3
  rw [← e] at h3
  exact spillFrame_transN _ _ _ _ _
    (spillFrame_transN _ _ _ _ _ (spillFrame_transN _ _ _ _ _ h2 h3 (fun _ h => h)) h.hst.2.2
      (fun _ h => h)) h.hpp.2.2.1 (fun _ h => h)

theorem spP_pages (h : SPX) : W''.pages = W.pages ∧ W''.ps = W.ps := by
  obtain ⟨-, -, -, -, -, hpg, hps, -⟩ := h.hlp
  obtain ⟨-, -, -, hpg', hps', -⟩ := h.hpp
  exact ⟨hpg'.trans hpg, hps'.trans hps⟩

theorem spP_bkt (h : SPX) :
    T''.bs !! bl = some B'' ∧ B''.bv = B.bv ∧ B''.ib = B.ib ∧ B''.nm = B.nm ∧ B''.bm = B.bm := by
  obtain ⟨-, -, -, -, -, -, -, -, hbv, hib, hnm, hbm, -⟩ := h.hlp
  obtain ⟨-, hB'', -, -, -, -, hbv', hib', hnm', hbm', -⟩ := h.hpp
  obtain ⟨-, -, -, hbv3, hib3, hnm3, hbm3⟩ := spP_B3 h
  obtain ⟨hbvs, hibs, hnms, hbms, -⟩ := spP_Bs h
  exact ⟨hB'', by rw [hbv', hbvs, hbv3, hbv], by rw [hib', hibs, hib3, hib],
    by rw [hnm', hnms, hnm3, hnm], by rw [hbm', hbms, hbm3, hbm]⟩

theorem spP_spages (h : SPX) : spillPages W T ⊆ spillPages W'' T'' := by
  obtain ⟨-, -, -, -, -, -, -, hsp, -⟩ := h.hlp
  obtain ⟨-, -, -, -, -, hsp', -⟩ := h.hpp
  have e := h.hPs
  rw [e] at hsp'
  exact GMap.map_subseteq_trans hsp hsp'

/-- `n`'s parent at the parts: the old one, or a new one if the node split. -/
theorem spP_par (h : SPX) :
    (2 ≤ xs.length → par ≠ null) ∧ (xs.length = 1 → par = r.nv.parent') ∧
    (r.nv.parent' ≠ null → par = r.nv.parent') ∧ xs ≠ [] := by
  obtain ⟨hne, -, -, -, h1, h2, -⟩ := h.hst.2.1
  have hp := (spP_rc h).1
  refine ⟨fun hl => (h2 hl).1, fun hl => by rw [h1 hl, hp], fun hpn => ?_, hne⟩
  by_cases hl : 2 ≤ xs.length
  · rw [(h2 hl).2 (by rw [hp]; exact hpn), hp]
  · have : xs.length = 1 := by
      have := List.length_pos_iff.2 hne; omega
    rw [h1 this, hp]


/-! ### Facts from the spill's resources -/

/-- The nodes of the bucket `bl` are no other bucket's. -/
theorem spP_disj (I : FLImpl (GF := GF)) (γd : DBNames) (γ : GName) (W : WView) (txl : Loc)
    (txid : w64) (T : WTx) (ρ : DBState) (F : GMap Nat (List w8)) (K : Loc → Bool) (bl : Loc)
    (B : BRec) (hB : T.bs !! bl = some B) :
    spillR I γd γ W txl txid T ρ F K ⊢
      ⌜∀ c C l, c ≠ bl → T.bs !! c = some C → (B.ns !! l).isSome → C.ns !! l = none⌝ ∗
      spillR I γd γ W txl txid T ρ F K := by
  by_cases hd : ∀ c C l, c ≠ bl → T.bs !! c = some C → (B.ns !! l).isSome → C.ns !! l = none
  · iintro H; iframe; ipureintro; exact hd
  · obtain ⟨c, C, l, hc, hC, hl, rC, hrC⟩ : ∃ c C l, c ≠ bl ∧ T.bs !! c = some C ∧
        (B.ns !! l).isSome ∧ ∃ rC, C.ns !! l = some rC := by
      apply Classical.byContradiction
      intro hn
      apply hd
      intro c C l hc hC hl
      cases hx : C.ns !! l with
      | none => rfl
      | some rC => exact absurd ⟨c, C, l, hc, hC, hl, rC, hx⟩ hn
    obtain ⟨rB, hrB⟩ := Option.isSome_iff_exists.1 hl
    iintro HR
    icases (spillR_at I γd γ W txl txid T ρ F K bl B hB).1 $$ HR with
      ⟨-, -, -, -, -, -, Hb, -, Ho, -, -⟩
    unfold othersOwn
    icases (BigSepM.bigSepM_lookup_acc (M := GMap Loc)
      (Φ := fun b C => iprop(bktOwnX (GF := GF) W b C ∗ capsB C K))
      (show Std.get? (Std.delete T.bs bl) c = some C from by
        show (GMap.delete bl T.bs) !! c = some C
        rw [GMap.lookup_delete_ne _ (Ne.symm hc)]; exact hC)).1 $$ Ho with ⟨⟨Hc, -⟩, -⟩
    unfold bktOwnX
    icases Hb with ⟨-, -, -, -, -, Hns⟩
    icases Hc with ⟨-, -, -, -, -, Hns2⟩
    icases (BigSepM.bigSepM_lookup_acc (M := GMap Loc) (Φ := fun l r => nodeOwnX (GF := GF) W l r)
      (show Std.get? B.ns l = some rB from hrB)).1 $$ Hns with ⟨Hn1, -⟩
    icases (BigSepM.bigSepM_lookup_acc (M := GMap Loc) (Φ := fun l r => nodeOwnX (GF := GF) W l r)
      (show Std.get? C.ns l = some rC from hrC)).1 $$ Hns2 with ⟨Hn2, -⟩
    unfold nodeOwnX
    icases Hn1 with ⟨Hn1, -⟩
    icases Hn2 with ⟨Hn2, -⟩
    iexfalso
    iapply node_ptsto_excl
    iframe

/-- The nodes of the bucket `bl` are not null. -/
theorem spP_nnull (I : FLImpl (GF := GF)) (γd : DBNames) (γ : GName) (W : WView) (txl : Loc)
    (txid : w64) (T : WTx) (ρ : DBState) (F : GMap Nat (List w8)) (K : Loc → Bool) (bl : Loc)
    (B : BRec) (hB : T.bs !! bl = some B) :
    spillR I γd γ W txl txid T ρ F K ⊢
      ⌜∀ l r, B.ns !! l = some r → l ≠ null⌝ ∗ spillR I γd γ W txl txid T ρ F K := by
  by_cases hd : ∀ l r, B.ns !! l = some r → l ≠ null
  · iintro H; iframe; ipureintro; exact hd
  · obtain ⟨l, rl, hrl, hnl⟩ : ∃ l rl, B.ns !! l = some rl ∧ l = null := by
      apply Classical.byContradiction
      intro hn
      exact hd (fun l rl hrl e => hn ⟨l, rl, hrl, e⟩)
    iintro HR
    icases spillR_node I γd γ W txl txid T ρ F K bl B l rl hB hrl $$ HR with ⟨Hn, -, -⟩
    icases typedPointsto_not_null_dup l rl.nv (DFrac.own 1) $$ Hn with ⟨-, %hn⟩
    exact absurd hnl hn

/-- The capacities of the other buckets' nodes: as at the call. -/
theorem spExit_keep (γd : DBNames) (γ : GName) (h : SPX) :
    spillR I γd γ W'' txl txid T'' ρ'' F'' K'' ⊢
      ⌜∀ c C l, c ≠ bl → T''.bs !! c = some C → (C.ns !! l).isSome → K'' l = K l⌝ ∗
      spillR I γd γ W'' txl txid T'' ρ'' F'' K'' := by
  obtain ⟨hB'', -⟩ := spP_bkt h
  iintro HR
  icases spP_disj I γd γ W'' txl txid T'' ρ'' F'' K'' bl B'' hB'' $$ HR with ⟨%hd, HR⟩
  iframe HR
  ipureintro
  intro c C l hc hC hl
  have hlB : B''.ns !! l = none := by
    cases hx : B''.ns !! l with
    | none => rfl
    | some _ =>
      have := hd c C l hc hC (by rw [hx]; rfl)
      obtain ⟨rC, hrC⟩ := Option.isSome_iff_exists.1 hl
      rw [this] at hrC; cases hrC
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hwr, -, -, -, -, hpar, -, -, hK, -⟩ := h.hpp
  have hpx := h.hpx
  -- `l` is no part
  have hlx : l ∉ xs.map (fun x => x.1) := by
    intro hm
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hm
    have hjl : j < ps.length := by
      have := (List.getElem?_eq_some_iff.1 hj).1; rw [List.length_map] at this; omega
    obtain ⟨-, rx, p, hrx, -⟩ := hwr j l hjl (by rw [← List.getElem?_map]; exact hj)
    rw [hlB] at hrx; cases hrx
  have hK1 : K'' l = Ks l := hK l (by rw [List.take_of_length_le (by omega)]; exact hlx)
  have hK2 : Ks l = K' l := by
    rcases h.hsr with ⟨-, -, -, rfl⟩ | ⟨pv', pcs', st, -, -, hp0, -, -, -, rfl, -⟩
    · rfl
    · have hlp : l ≠ par := by
        intro e; subst e
        obtain ⟨rp, hrp, -⟩ := hpar hp0
        rw [hlB] at hrp; cases hrp
      unfold splitK; rw [if_neg hlx, if_neg hlp]
  rw [hK1, hK2]
  -- `l` was in the bucket `c` after the loop
  obtain ⟨d1, -, -, -, -, d6⟩ := spP_frame' h
  obtain ⟨C', hC'⟩ := Option.isSome_iff_exists.1 ((d1 c).2 (by rw [hC]; rfl))
  obtain ⟨r', hr'⟩ := Option.isSome_iff_exists.1 hl
  obtain ⟨r0, hr0⟩ := derefStarX_ns C' C (d6 c C' C hc hC' hC).1 l r' hr'
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    hkk, -⟩ := h.hlp
  exact hkk.2 c C' l hc hC' (by rw [hr0]; rfl)

/-- A new parent (pgid 0), the part's `children` set nil: the end of its spill that of the
node's. -/
theorem spNewParent_post (γd : DBNames) (γ : GName) (h : SPX)
    (hpn : rn5.nv.parent' ≠ null) (rq : NRec) (hrq : B''.ns !! rn5.nv.parent' = some rq)
    (hq0 : rq.nv.pgid' = W64 0) (err : GoInterface)
    (hko : ∀ c C l, c ≠ bl → T''.bs !! c = some C → (C.ns !! l).isSome → K'' l = K l) :
    finPost I γd γ W'' txl txid
        (setB T'' bl (setN B'' n { rn5 with nv := { rn5.nv with children' := slice.nil } })) bl
        (setN B'' n { rn5 with nv := { rn5.nv with children' := slice.nil } }) K'' err ⊢
      finPost I γd γ W txl txid T bl B K err := by
  have hfr := spP_frame h
  obtain ⟨hpg, -⟩ := spP_pages h
  obtain ⟨hB'', hbv, hib, hnm, hbm⟩ := spP_bkt h
  have hfr7 := spillFrame_setB T'' bl
    (setN B'' n { rn5 with nv := { rn5.nv with children' := slice.nil } }) (by rw [hB'']; rfl)
  unfold finPost
  iintro (⟨%he, %W3, %T3', %ρ3, %F3, %K3, %B3', %p, %top', %pid, %Q, HR, Hw, %hf⟩ | ⟨%he, Herr⟩)
  · ileft
    isplitr
    · ipureintro; exact he
    iexists W3, T3', ρ3, F3, K3, B3', p, top', pid, Q
    iframe HR Hw
    ipureintro
    obtain ⟨hg3, hfr3, hpg3, hB3', hbv3, hib3, hnm3, hbm3, hup, hnd, hdom, hQ, hQs, hbuf, hK3, hrt⟩ := hf
    refine ⟨hg3, spillFrame_transN _ _ _ _ _ (spillFrame_transN _ _ _ _ _ hfr hfr7 (fun _ h => h))
      hfr3 (fun _ h => h), hpg3.trans hpg, hB3', hbv3.trans hbv, hib3.trans hib, hnm3.trans hnm,
      hbm3.trans hbm, ?_, hnd, hdom, hQ, hQs, hbuf, ?_, hrt⟩
    · rw [← hbv]; exact hup
    · intro c C' l hc hC' hl
      rw [hK3 c C' l hc hC' hl]
      obtain ⟨d1, -, -, -, -, d6⟩ := hfr3
      obtain ⟨C7, hC7⟩ := Option.isSome_iff_exists.1 ((d1 c).2 (by rw [hC']; rfl))
      obtain ⟨r', hr'⟩ := Option.isSome_iff_exists.1 hl
      obtain ⟨r0, hr0⟩ := derefStarX_ns C7 C' (d6 c C7 C' hc hC7 hC').1 l r' hr'
      have hC7' : T''.bs !! c = some C7 := by
        have e : (setB T'' bl (setN B'' n { rn5 with nv := { rn5.nv with children' := slice.nil } })).bs !! c =
            T''.bs !! c := GMap.lookup_insert_ne _ _ (Ne.symm hc)
        rw [← e]; exact hC7
      exact hko c C7 l hc hC7' (by rw [hr0]; rfl)
  · iright
    iframe
    ipureintro; exact he

/-! ### The root's parent chain -/

theorem spP_onRoot_true (B : BRec) (c : Loc) (p : List Loc) (t : Loc)
    (hu : upPath B.ns B.bv.rootNode' p t) (hc : c ∈ p) : onRootPath B c = true := by
  unfold onRootPath; exact @decide_eq_true _ (Classical.propDecidable _) ⟨p, t, hu, hc⟩

theorem spP_onRoot_of (B : BRec) (c : Loc) (h : onRootPath B c = true) :
    ∃ p t, upPath B.ns B.bv.rootNode' p t ∧ c ∈ p := by
  unfold onRootPath at h; exact @of_decide_eq_true _ (Classical.propDecidable _) h

/-- No parent: the chain from the root node to `n` after the children loop. -/
theorem spP_pathB' (h : SPX) (hp0 : r.nv.parent' = null) :
    ∃ p, upPath B'.ns B.bv.rootNode' p n ∧ p.Nodup ∧
      (∀ l, (B'.ns !! l).isSome → l ∈ p ∨ l ∈ rn.cs) ∧
      ∀ l ∈ p, l = n ∨ l ∈ rn.cs ∨ ∃ r', B'.ns !! l = some r' ∧ noViewRec r' := by
  cases htt : top
  · obtain ⟨-, -, hn', -, -, -, -, -, -, -, -, -, hnv, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
      -, hdom, hrem, -⟩ := h.hlp
    obtain ⟨-, -, hroot, -⟩ := h.htok htt
    have hnr : n = B.bv.rootNode' := hroot n r h.hn hp0
    have hrn : rn.nv.parent' = null := by rw [hnv]; exact hp0
    obtain ⟨-, p0, hup0, -, hdom0⟩ := h.hpar0 hp0
    rw [← hnr] at hup0 ⊢
    have hp0e : p0 = [n] := (upPath_det B.ns hup0 (upPath.self n r h.hn hp0)).1
    subst hp0e
    refine ⟨[n], upPath.self n rn hn' hrn, List.nodup_cons.2 ⟨List.not_mem_nil, List.nodup_nil⟩, fun l hl => ?_,
      fun l hl => Or.inl (List.mem_singleton.1 hl)⟩
    rcases hdom l hl with hb | hc
    · rcases hdom0 l hb with hm | hm
      · exact Or.inl hm
      · rcases hrem l (List.mem_cons_of_mem _ hm) hl with e | e | e
        · exact Or.inl (by rw [e]; exact List.mem_singleton_self n)
        · exact Or.inr e
        · rw [h.hdrop] at e; simp at e
    · exact Or.inr hc
  · exact h.htopP htt

/-- No parent: the chain from the root node to `n` after the cut, all the cut's nodes. -/
theorem spP_pathB3 (h : SPX) (hp0 : r.nv.parent' = null) :
    ∃ p, upPath B3.ns B.bv.rootNode' p n ∧ p.Nodup ∧
      (∀ l, (B3.ns !! l).isSome → l ∈ p) ∧ (∀ l ∈ p, (B3.ns !! l).isSome) ∧
      ∀ l ∈ p, l = n ∨ ∃ r', B3.ns !! l = some r' ∧ noViewRec r' := by
  obtain ⟨p, hup, hnd, hdom, hnv⟩ := spP_pathB' h hp0
  obtain ⟨-, -, hn', -, -, -, -, -, hbv, -, -, -, hnvr, -⟩ := h.hlp
  obtain ⟨h3n, h3o, h3c, -⟩ := spP_B3 h
  obtain ⟨hrcp, -⟩ := spP_rc h
  have hup' : upPath B'.ns B'.bv.rootNode' p n := by rw [hbv]; exact hup
  have hag : ∀ x ∈ p, ∀ r1, B'.ns !! x = some r1 →
      ∃ r3, B3.ns !! x = some r3 ∧ r3.nv.parent' = r1.nv.parent' ∧
        (x ≠ n → (x ∈ rn.cs ∧ r3 = staleRec r1) ∨ (x ∉ rn.cs ∧ r3 = r1)) := by
    intro x hx r1 hr1
    by_cases e : x = n
    · subst e; rw [hn'] at hr1; cases hr1
      exact ⟨rc, h3n, by rw [hrcp, hnvr], fun hh => absurd rfl hh⟩
    · by_cases hc : x ∈ rn.cs
      · rw [h3c x hc, spP_onRoot_true B' x p n hup' hx, if_pos rfl, hr1]
        exact ⟨staleRec r1, rfl, rfl, fun _ => Or.inl ⟨hc, rfl⟩⟩
      · rw [h3o x e hc]
        exact ⟨r1, hr1, rfl, fun _ => Or.inr ⟨hc, rfl⟩⟩
  have hup3 : upPath B3.ns B.bv.rootNode' p n :=
    upPath_par B'.ns B3.ns hup (fun x hx r1 hr1 => by
      obtain ⟨r3, hr3, hp, -⟩ := hag x hx r1 hr1; exact ⟨r3, hr3, hp⟩)
  refine ⟨p, hup3, hnd, fun l hl => ?_, fun l hl => upPath_dom _ hup3 l hl, fun l hl => ?_⟩
  · by_cases e : l = n
    · subst e; exact upPath_last_mem _ hup
    · by_cases hc : l ∈ rn.cs
      · rw [h3c l hc] at hl
        by_cases ho : onRootPath B' l = true
        · obtain ⟨p', t', hu', hm⟩ := spP_onRoot_of B' l ho
          rw [hbv] at hu'
          rw [(upPath_det B'.ns hup hu').1]; exact hm
        · rw [if_neg ho] at hl; cases hl
      · rw [h3o l e hc] at hl
        rcases hdom l hl with h1 | h1
        · exact h1
        · exact absurd h1 hc
  · by_cases e : l = n
    · exact Or.inl e
    · right
      obtain ⟨r1, hr1⟩ := Option.isSome_iff_exists.1 (upPath_dom _ hup l hl)
      obtain ⟨r3, hr3, -, hk⟩ := hag l hl r1 hr1
      refine ⟨r3, hr3, ?_⟩
      rcases hk e with ⟨-, rfl⟩ | ⟨hc, rfl⟩
      · exact staleRec_noView r1
      · rcases hnv l hl with e' | e' | ⟨r', hr', hv⟩
        · exact absurd e' e
        · exact absurd e' hc
        · rw [hr1] at hr'; cases hr'; exact hv

/-- The nodes kept through the parts loop (not parts, not the parent). -/
theorem spP_keep3 (h : SPX) (x : Loc) (r3 : NRec) (hx : x ∉ xs.map (fun x => x.1)) (hp : x ≠ par)
    (h3 : B3.ns !! x = some r3) : ∃ rx, B''.ns !! x = some rx ∧ dnK r3 rx := by
  obtain ⟨-, -, -, -, hso⟩ := spP_Bs h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hout, -⟩ := h.hpp
  exact hout x r3 hx hp (by rw [hso x hx hp]; exact h3)

/-- The nodes of `B''`: parts, the parent, or the cut's. -/
theorem spP_dom'' (h : SPX) (x : Loc) (hx : (B''.ns !! x).isSome) :
    x ∈ xs.map (fun x => x.1) ∨ x = par ∨ (B3.ns !! x).isSome := by
  obtain ⟨-, -, -, -, hso⟩ := spP_Bs h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hdom, -⟩ := h.hpp
  by_cases h1 : x ∈ xs.map (fun x => x.1)
  · exact Or.inl h1
  by_cases h2 : x = par
  · exact Or.inr (Or.inl h2)
  exact Or.inr (Or.inr (by rw [← hso x h1 h2]; exact hdom x hx))

/-- The written part `j` (a parent: a spilled part). -/
theorem spP_written (h : SPX) (hpar : par ≠ null) (j : Nat) (x : Loc) (hj : j < ps.length)
    (hx : (xs[j]?).map (fun x => x.1) = some x) :
    spilledN bl B'' x ∧ ∃ rx p, B''.ns !! x = some rx ∧ ps[j]? = some p ∧ rx.nv.pgid' = p.1 ∧
      rx.nv.parent' = par ∧ rx.ws.map ownFresh = ((chunksOf rc xs).getD j []).map ownFresh ∧
      rx.nv.isLeaf' = rc.nv.isLeaf' := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hwr, -⟩ := h.hpp
  obtain ⟨hs, rx, p, hrx, -, -, -, -, -, hp', hpg, hpa, hws, hlf⟩ := hwr j x hj hx
  exact ⟨hs hpar, rx, p, hrx, hp', hpg, hpa, hws, hlf⟩

/-- The written part `j`, whatever the parent. -/
theorem spP_written0 (h : SPX) (j : Nat) (x : Loc) (hj : j < ps.length)
    (hx : (xs[j]?).map (fun x => x.1) = some x) :
    ∃ rx p, B''.ns !! x = some rx ∧ rx.nv.spilled' = true ∧ rx.cs = [] ∧ ps[j]? = some p ∧
      rx.nv.pgid' = p.1 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hwr, -⟩ := h.hpp
  obtain ⟨-, rx, p, hrx, hsp, hcs, -, -, -, hp', hpg, -⟩ := hwr j x hj hx
  exact ⟨rx, p, hrx, hsp, hcs, hp', hpg⟩

/-! ### The parent -/

/-- The old parent (the node had one): its records along the way. -/
theorem spP_oldpar (h : SPX) (hp : r.nv.parent' ≠ null) :
    top = false ∧ par = r.nv.parent' ∧ par ≠ n ∧ par ∉ rn.cs ∧
    ∃ rpB rp1, B.ns !! par = some rpB ∧ B'.ns !! par = some rp1 ∧ dnK rpB rp1 ∧
      B3.ns !! par = some rp1 ∧
      ∃ rp0, Bs.ns !! par = some rp0 ∧ rp0.nv = { rp1.nv with children' := rp0.nv.children' } ∧
        rp0.cs = rp1.cs ++ (xs.drop 1).map (fun x => x.1) ∧ rp0.ws = rp1.ws ∧ rp0.ins = rp1.ins ∧
        rp0.key = rp1.key ∧ rp0.ksrc = rp1.ksrc := by
  have htf : top = false := by
    cases htt : top
    · rfl
    · exact absurd (h.htopn htt) hp
  have hpe : par = r.nv.parent' := (spP_par h).2.2.1 hp
  obtain ⟨rpB, hrpB⟩ := Option.isSome_iff_exists.1 (h.hpar1 hp)
  obtain ⟨hnS, -, -, -, -⟩ := h.hplf _ rpB rfl hp hrpB
  have hpn : r.nv.parent' ≠ n := fun e => hnS (e ▸ List.mem_cons_self)
  obtain ⟨-, hB', hn', -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    hout, -⟩ := h.hlp
  obtain ⟨rp1, hrp1, hd1⟩ := hout _ rpB hnS hrpB
  -- `par` is not a child of `n`: ranks
  have hnc : r.nv.parent' ∉ rn.cs := by
    intro hc
    obtain ⟨⟨rk, Nt, hT⟩, -⟩ := h.htok htf
    obtain ⟨⟨rk', Nt', hT'⟩, -⟩ := h.htrp htf
    obtain ⟨rc', hrc', hpc⟩ := (hT'.2.1 n rn hn').2 _ hc
    rw [hrp1] at hrc'; cases hrc'
    have hpB : rpB.nv.parent' = n := by rw [← hpc, (spP_dnK hd1).1]
    have h1 := (hT.1 n r h.hn).2 hp
    have h2 := (hT.1 _ rpB hrpB).2 (by rw [hpB]; exact h.hnn)
    rw [hpB] at h2
    omega
  obtain ⟨-, h3o, -⟩ := spP_B3 h
  have h3 : B3.ns !! r.nv.parent' = some rp1 := by rw [h3o _ hpn hnc]; exact hrp1
  rw [hpe]
  refine ⟨htf, rfl, hpn, hnc, rpB, rp1, hrpB, hrp1, hd1, h3, ?_⟩
  rcases h.hsr with ⟨hxs, -, hBs, -⟩ | ⟨pv', pcs', st, -, -, -, hfr, -, hBs, -, hcase⟩
  · rw [hBs, hxs]
    exact ⟨rp1, h3, rfl, by simp, rfl, rfl, rfl, rfl⟩
  · have hrcp := (spP_rc h).1
    rcases hcase with ⟨hn0, -⟩ | ⟨-, hpl, hpv, hpcs⟩
    · exact absurd (hrcp.symm.trans hn0) hp
    · have hgd : (B3.ns !! rc.nv.parent').getD rc = rp1 := by rw [hrcp, h3]; rfl
      rw [hgd] at hpv hpcs
      rw [hBs]
      have hpl' : par ∉ xs.map (fun x => x.1) := hfr.2.2.1
      have e : parentRec rc rp1 pv' pcs' = { rp1 with nv := pv', cs := pcs' } := by
        unfold parentRec; rw [if_neg (by rw [hrcp]; exact hp)]
      refine ⟨{ rp1 with nv := pv', cs := pcs' }, ?_, hpv, hpcs, rfl, rfl, rfl, rfl⟩
      show splitNs B3.ns rc ((B3.ns !! rc.nv.parent').getD rc) xs par pv' pcs' !! r.nv.parent' = _
      rw [hgd, ← hpe, ← e]
      exact splitNs_par _ _ _ _ _ _ _ hpl'

/-- A new parent (pgid 0): the node had none, split; the parent's record. -/
theorem spP_np (h : SPX) (hpn : rn5.nv.parent' ≠ null) (rq : NRec)
    (hrq : B''.ns !! rn5.nv.parent' = some rq) (hq0 : rq.nv.pgid' = W64 0) :
    r.nv.parent' = null ∧ 2 ≤ xs.length ∧ par = rn5.nv.parent' ∧ par ≠ null ∧ B3.ns !! par = none ∧
    (∀ x ∈ xs, x.1 ≠ n → B3.ns !! x.1 = none) ∧ par ∉ xs.map (fun x => x.1) ∧
    splitPieces n rc.nv par rc.ins xs ∧
    rq.nv.parent' = null ∧ rq.nv.isLeaf' = false ∧ rq.nv.bucket' = bl ∧ rq.nv.key' = slice.nil ∧
    rq.nv.spilled' = false ∧ rq.cs = xs.map (fun x => x.1) ∧ K'' par = false ∧ wsLive rq.ws ∧
    rq.ins.length = rq.ws.length ∧ wsSorted rq.ws ∧
    ∃ es, pieceEntries ps es ∧ rq.ws.map ownFresh = es.map ownFresh := by
  have hpe : par = rn5.nv.parent' := h.hpar5.symm
  have hp0 : par ≠ null := hpe ▸ hpn
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hpar, -⟩ := h.hpp
  obtain ⟨rp, hrp, hKp, hpws, hwl, hil, hsrt, -, -, rp0, hrp0, hcs0, -, hnv0, hkn0, -⟩ := hpar hp0
  have e : rp = rq := by rw [hpe, hrq] at hrp; exact (Option.some.inj hrp).symm
  subst e
  have hr0 : r.nv.parent' = null := by
    apply Classical.byContradiction
    intro hp
    obtain ⟨-, hpe', -, -, rpB, rp1, hrpB, -, hd1, -, rp0', hrp0', hnv', -⟩ := spP_oldpar h hp
    rw [hrp0] at hrp0'; cases hrp0'
    rw [hpe'] at hrpB
    obtain ⟨-, -, -, hpgB, -⟩ := h.hplf _ rpB rfl hp hrpB
    have e1 : rp.nv.pgid' = rp0.nv.pgid' := by rw [hnv0]
    have e2 : rp0.nv.pgid' = rp1.nv.pgid' := by rw [hnv']
    have e3 : rp1.nv.pgid' = rpB.nv.pgid' := by rw [(spP_dnK hd1).1]
    exact hpgB (by rw [← e3, ← e2, ← e1]; exact hq0)
  obtain ⟨h2p, h1p, -, hne⟩ := spP_par h
  have hlen : 2 ≤ xs.length := by
    have := List.length_pos_iff.2 hne
    by_cases hc : 2 ≤ xs.length
    · exact hc
    · exact absurd ((h1p (by omega)).trans hr0) hp0
  have hrcp : rc.nv.parent' = null := (spP_rc h).1.trans hr0
  obtain ⟨-, -, -, hbk, -⟩ := spP_rc h
  rcases h.hsr with ⟨hxs, -⟩ | ⟨pv', pcs', st, -, hsp, -, hfr, -, hBs, -, hcase⟩
  · rw [hxs] at hlen; simp at hlen
  obtain ⟨-, hpv, hpcs⟩ := hcase.resolve_right (fun hh => hh.1 hrcp)
  have hpx : par ∉ xs.map (fun x => x.1) := hfr.2.2.1
  have hBp : Bs.ns !! par = some ⟨pv', [], [], pcs', [], Src.own (DFrac.own 1)⟩ := by
    rw [hBs]
    show splitNs B3.ns rc _ xs par pv' pcs' !! par = _
    rw [splitNs_par _ _ _ _ _ _ _ hpx]
    unfold parentRec; rw [if_pos hrcp]
  rw [hBp] at hrp0; cases hrp0
  have hpar' : rp.nv.parent' = pv'.parent' := by rw [hnv0]
  have hleaf' : rp.nv.isLeaf' = pv'.isLeaf' := by rw [hnv0]
  have hbk' : rp.nv.bucket' = pv'.bucket' := by rw [hnv0]
  have hsp' : rp.nv.spilled' = pv'.spilled' := by rw [hnv0]
  rw [hpv] at hpar' hleaf' hbk' hsp' hkn0
  obtain ⟨-, -, -, -, -, -, hspar, -⟩ := h.hst.2.1
  obtain ⟨rp0', hrp0', hws0, hcase'⟩ := hspar hp0
  rw [hBp] at hrp0'; cases hrp0'
  have hw0 : ws0 = [] := by
    rcases hcase' with ⟨hn1, -⟩ | ⟨-, h1, -⟩
    · exact absurd hrcp hn1
    · exact h1
  have hpsne : ps ≠ [] := by
    intro e; have := h.hpx; rw [e] at this; simp at this; omega
  have hes : ∃ es, pieceEntries ps es ∧ rp.ws.map ownFresh = es.map ownFresh := by
    rcases hpws with ⟨e, -⟩ | ⟨-, es, hes, hws⟩
    · exact absurd e hpsne
    · rw [hw0] at hws; simp at hws; exact ⟨es, hes, hws⟩
  refine ⟨hr0, hlen, hpe, hp0, hfr.2.1 hrcp, hfr.1, hpx, hsp, hpar', hleaf', ?_, hkn0 rfl, hsp',
    by rw [hcs0, hpcs], hKp, hwl, hil, hsrt, hes⟩
  rw [hbk']; exact hbk

/-! ### Entries for the parts -/

theorem spP_f2_pieces (ps : List (w64 × List w8)) (es : List WEntry) (h : pieceEntries ps es) :
    List.Forall₂ (fun (p : w64 × List w8) (w : WEntry) => w.pgid = p.1 ∧ w.key = p.2) ps es :=
  List.Forall₂.imp (fun hh => ⟨hh.2.1, hh.2.2.1⟩) h

theorem spP_f2_fresh : ∀ (ps : List (w64 × List w8)) (es ws : List WEntry),
    List.Forall₂ (fun (p : w64 × List w8) (w : WEntry) => w.pgid = p.1 ∧ w.key = p.2) ps es →
    ws.map ownFresh = es.map ownFresh →
    List.Forall₂ (fun (p : w64 × List w8) (w : WEntry) => w.pgid = p.1 ∧ w.key = p.2) ps ws
  | [], [], [], _, _ => .nil
  | [], [], _ :: _, _, h => by simp at h
  | p :: ps, e :: es, [], _, h => by simp at h
  | p :: ps, e :: es, w :: ws, .cons hr hrs, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    have e1 : w.pgid = e.pgid := by have := congrArg WEntry.pgid h.1; exact this
    have e2 : w.key = e.key := by have := congrArg WEntry.key h.1; exact this
    exact .cons ⟨e1.trans hr.1, e2.trans hr.2⟩ (spP_f2_fresh ps es ws hrs h.2)

theorem spP_f2_map : ∀ (ps : List (w64 × List w8)) (ws : List WEntry),
    List.Forall₂ (fun (p : w64 × List w8) (w : WEntry) => w.pgid = p.1 ∧ w.key = p.2) ps ws →
    ws.map WEntry.pgid = ps.map (fun p => p.1)
  | [], [], _ => rfl
  | _ :: ps, _ :: ws, .cons hr hrs => by
    simp only [List.map_cons, List.cons.injEq]; exact ⟨hr.1, spP_f2_map ps ws hrs⟩

/-! ### The nodes after the parts -/

theorem spP_mem_fresh {ws ws' : List WEntry} (h : ws.map ownFresh = ws'.map ownFresh) {w : WEntry}
    (hw : w ∈ ws) : ∃ w' ∈ ws', w.key = w'.key ∧ w.value = w'.value ∧ w.pgid = w'.pgid ∧
      w.flags = w'.flags := by
  have hm : ownFresh w ∈ ws'.map ownFresh := by rw [← h]; exact List.mem_map_of_mem hw
  obtain ⟨w', hw', he⟩ := List.mem_map.1 hm
  exact ⟨w', hw', (congrArg WEntry.key he).symm, (congrArg WEntry.value he).symm,
    (congrArg WEntry.pgid he).symm, (congrArg WEntry.flags he).symm⟩

theorem spP_len_fresh {ws ws' : List WEntry} (h : ws.map ownFresh = ws'.map ownFresh) :
    ws.length = ws'.length := by
  have := congrArg List.length h; simpa using this

theorem spP_n_mem (h : SPX) : n ∈ xs.map (fun x => x.1) := by
  obtain ⟨-, -, hhd, -⟩ := h.hst.2.1
  cases hx : xs with
  | nil => rw [hx] at hhd; cases hhd
  | cons x0 rest =>
    rw [hx] at hhd; simp only [List.head?_cons, Option.map_some, Option.some.injEq] at hhd
    rw [List.map_cons, hhd]; exact List.mem_cons_self

/-- A node after the parts: a written part, the parent, or a node of the loop's end. -/
theorem spP_class (h : SPX) (hpar : par ≠ null) (l : Loc) (rx : NRec) (hl : B''.ns !! l = some rx) :
    (∃ j x, j < ps.length ∧ xs[j]? = some x ∧ x.1 = l ∧
      rx.ws.map ownFresh = ((chunksOf rc xs).getD j []).map ownFresh ∧
      rx.nv.isLeaf' = rc.nv.isLeaf' ∧ spilledN bl B'' l ∧
      ∃ p, ps[j]? = some p ∧ rx.nv.pgid' = p.1 ∧ rx.nv.parent' = par) ∨
    (l = par ∧ l ∉ xs.map (fun x => x.1)) ∨
    (l ∉ xs.map (fun x => x.1) ∧ l ≠ par ∧ l ≠ n ∧ ∃ r1, B'.ns !! l = some r1 ∧
      rx.ws.map ownFresh = r1.ws.map ownFresh ∧ rx.nv = { r1.nv with key' := rx.nv.key' } ∧
      rx.cs = r1.cs ∧ (r1.ins.length = r1.ws.length → rx.ins.length = rx.ws.length) ∧
      (l ∈ rn.cs → onRootPath B' l = true) ∧ (B3.ns !! l).isSome) := by
  by_cases hx : l ∈ xs.map (fun x => x.1)
  · left
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hx
    rw [List.getElem?_map] at hj
    obtain ⟨x, hxj, hx1⟩ := Option.map_eq_some_iff.1 hj
    have hjl : j < ps.length := by
      rw [h.hpx]; exact (List.getElem?_eq_some_iff.1 hxj).1
    obtain ⟨hs, rx', p, hrx', hp, hpg, hpa, hws, hlf⟩ :=
      spP_written h hpar j l hjl (by rw [hxj]; simp [hx1])
    rw [hl] at hrx'; cases hrx'
    exact ⟨j, x, hjl, hxj, hx1, hws, hlf, hs, p, hp, hpg, hpa⟩
  right
  by_cases hp : l = par
  · exact Or.inl ⟨hp, hx⟩
  right
  have hln : l ≠ n := fun e => hx (e ▸ spP_n_mem h)
  rcases spP_dom'' h l (by rw [hl]; rfl) with h1 | h1 | h1
  · exact absurd h1 hx
  · exact absurd h1 hp
  obtain ⟨r3, h3⟩ := Option.isSome_iff_exists.1 h1
  obtain ⟨rx', hrx', hd⟩ := spP_keep3 h l r3 hx hp h3
  rw [hl] at hrx'; cases hrx'
  obtain ⟨hnv, hcs, -, hws, -, -, hil⟩ := spP_dnK hd
  obtain ⟨-, h3o, h3c, -⟩ := spP_B3 h
  refine ⟨hx, hp, hln, ?_⟩
  by_cases hc : l ∈ rn.cs
  · rw [h3c l hc] at h3
    by_cases ho : onRootPath B' l = true
    · rw [if_pos ho] at h3
      obtain ⟨r1, hr1, e⟩ := Option.map_eq_some_iff.1 h3
      subst e
      exact ⟨r1, hr1, by rw [hws]; exact spP_stale_fresh r1.ws, hnv, hcs,
        fun hh => hil (by show r1.ins.length = (r1.ws.map staleW).length; rw [List.length_map]; exact hh),
        fun _ => ho, by rw [h1]⟩
    · rw [if_neg ho] at h3; cases h3
  · rw [h3o l hln hc] at h3
    exact ⟨r3, h3, hws, hnv, hcs, hil, fun hh => absurd hh hc, h1⟩

/-- The parts' first keys: entries of the node (its parts non-empty). -/
theorem spP_pmem (h : SPX) (hpos : ∀ x ∈ xs, 0 < x.2.2.length) (j : Nat) (p : w64 × List w8)
    (hp : ps[j]? = some p) :
    ∃ w ∈ rn.ws, p.2 = w.key := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hkey, -⟩ := h.hpp
  have hjl : j < xs.length := by rw [← h.hpx]; exact (List.getElem?_eq_some_iff.1 hp).1
  obtain ⟨x, hx⟩ : ∃ x, xs[j]? = some x := ⟨_, List.getElem?_eq_getElem hjl⟩
  obtain ⟨-, -, -, -, hws, hins, -⟩ := spP_rc h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hL, -⟩ := h.hlp
  obtain ⟨-, -, -, hflat, -⟩ := h.hst.2.1
  have hsum : (xs.map (fun x => x.2.2.length)).sum ≤ rc.ws.length := by
    rw [hws, ← hL.2.2.1, ← hins, ← hflat.1, List.length_flatten, List.map_map]; exact Nat.le_refl _
  obtain ⟨hcl, hcm⟩ := wsChunks_get rc.ws (xs.map (fun x => x.2.2.length)) j x.2.2.length
    (by rw [List.getElem?_map, hx]; rfl) hsum
  have hpos' := hpos x (List.mem_of_getElem? hx)
  rw [hkey j p hp]
  unfold chunksOf
  cases hch : (wsChunks rc.ws (xs.map (fun x => x.2.2.length))).getD j [] with
  | nil => rw [hch] at hcl; simp at hcl; omega
  | cons w ws =>
    rw [hch] at hcm
    refine ⟨w, ?_, rfl⟩
    rw [← hws]; exact hcm w List.mem_cons_self

theorem spP_sub_some {P Q : GMap Nat (List w8)} (hs : P ⊆ Q) (k : Nat) (h : (P !! k).isSome) :
    (Q !! k).isSome := by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 h
  rw [hs k v hv]; rfl

theorem spP_spages' (h : SPX) : spillPages W' T' ⊆ spillPages W'' T'' := by
  obtain ⟨-, -, -, -, -, hsp', -⟩ := h.hpp
  have e := h.hPs
  rw [e] at hsp'
  exact hsp'

/-- A chunk's entries: the node's. -/
theorem spP_chunk_mem (h : SPX) (j : Nat) (x : Loc × node × List Inode) (hx : xs[j]? = some x) :
    ((chunksOf rc xs).getD j []).length = x.2.2.length ∧ ∀ w ∈ (chunksOf rc xs).getD j [], w ∈ rn.ws := by
  obtain ⟨-, -, -, -, hws, hins, -⟩ := spP_rc h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hL, -⟩ := h.hlp
  obtain ⟨-, -, -, hflat, -⟩ := h.hst.2.1
  have hsum : (xs.map (fun x => x.2.2.length)).sum ≤ rc.ws.length := by
    rw [hws, ← hL.2.2.1, ← hins, ← hflat.1, List.length_flatten, List.map_map]; exact Nat.le_refl _
  obtain ⟨hcl, hcm⟩ := wsChunks_get rc.ws (xs.map (fun x => x.2.2.length)) j x.2.2.length
    (by rw [List.getElem?_map, hx]; rfl) hsum
  exact ⟨hcl, fun w hw => by rw [← hws]; exact hcm w hw⟩

/-- The facts `node.spill` keeps of the nodes, after the parts (but the parent). -/
theorem spP_nodes'' (h : SPX) (hpar : par ≠ null) (hpos : ∀ x ∈ xs, 0 < x.2.2.length) (l : Loc) (rx : NRec)
    (hl : B''.ns !! l = some rx) (hlp : l ≠ par) :
    (∀ w ∈ rx.ws, w.key.length + w.value.length ≤ 2 ^ 28) ∧
    (rx.nv.parent' ≠ null → 0 < rx.ws.length) ∧
    (rx.nv.isLeaf' = false → rx.nv.pgid' ≠ W64 0) ∧
    (rx.nv.isLeaf' = false → ∀ w ∈ rx.ws, (spillPages W'' T'' !! uint.nat w.pgid).isSome) := by
  obtain ⟨-, -, hn', -, -, -, -, -, -, -, -, -, hnv, -, -, -, -, hok, hP1, -⟩ := h.hlp
  obtain ⟨hok1, hok2, -, hok4⟩ := hok
  have hsp := spP_spages' h
  rcases spP_class h hpar l rx hl with ⟨j, x, hjl, hxj, hx1, hws, hlf, -, p, hp, hpg, -⟩ | ⟨e, -⟩ |
      ⟨-, -, hln, r1, hr1, hws, hnv1, -, -, -, -⟩
  · obtain ⟨hcl, hcm⟩ := spP_chunk_mem h j x hxj
    have hlfn : rx.nv.isLeaf' = rn.nv.isLeaf' := by
      rw [hlf, (spP_rc h).2.1]; show r.nv.isLeaf' = rn.nv.isLeaf'; rw [hnv]
    refine ⟨fun w hw => ?_, fun _ => ?_, fun _ => ?_, fun hb w hw => ?_⟩
    · obtain ⟨w', hw', hk, hv, -⟩ := spP_mem_fresh hws hw
      rw [hk, hv]; exact hok1 n rn hn' w' (hcm w' hw')
    · rw [spP_len_fresh hws, hcl]; exact hpos x (List.mem_of_getElem? hxj)
    · obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hfresh, -⟩ := h.hpp
      have h2 := (hfresh p (List.mem_of_getElem? hp)).2.2.2.2
      rw [hpg]; intro e; rw [e] at h2; simp at h2
    · obtain ⟨w', hw', -, -, hpw, -⟩ := spP_mem_fresh hws hw
      rw [hpw]
      exact spP_sub_some hsp _ (hok4 n rn w' hn' (by rw [← hlfn]; exact hb) (hcm w' hw'))
  · exact absurd e hlp
  · have hlf : rx.nv.isLeaf' = r1.nv.isLeaf' := by rw [hnv1]
    have hpa : rx.nv.parent' = r1.nv.parent' := by rw [hnv1]
    have hpg : rx.nv.pgid' = r1.nv.pgid' := by rw [hnv1]
    refine ⟨fun w hw => ?_, fun hh => ?_, fun hb => ?_, fun hb w hw => ?_⟩
    · obtain ⟨w', hw', hk, hv, -⟩ := spP_mem_fresh hws hw
      rw [hk, hv]; exact hok1 l r1 hr1 w' hw'
    · rw [spP_len_fresh hws]; exact hok2 l r1 hr1 (by rw [← hpa]; exact hh)
    · rw [hpg]; exact hP1 l r1 hr1 hln (by rw [← hlf]; exact hb)
    · obtain ⟨w', hw', -, -, hpw, -⟩ := spP_mem_fresh hws hw
      rw [hpw]
      exact spP_sub_some hsp _ (hok4 l r1 w' hr1 (by rw [← hlf]; exact hb) hw')

theorem spP_sum2 {α : Type} (f : α → Nat) : ∀ (L : List α), (∀ x ∈ L, 2 ≤ f x) →
    2 * L.length ≤ (L.map f).sum
  | [], _ => by simp
  | a :: L, h => by
    have := spP_sum2 f L (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have ha := h a List.mem_cons_self
    simp only [List.length_cons, List.map_cons, List.sum_cons]; omega

/-! ### Under an old parent (`top = false`, a tree) -/

/-- A child of `n` is not on the root's chain (the root has no parent). -/
theorem spP_noroot (h : SPX) (htf : top = false) (x : Loc) (hx : x ∈ rn.cs) :
    onRootPath B' x = false := by
  cases ho : onRootPath B' x
  · rfl
  obtain ⟨p, t, hu, hm⟩ := spP_onRoot_of B' x ho
  obtain ⟨⟨rk, Nt, hT⟩, ⟨r0, h0, hp0⟩, -⟩ := h.htrp htf
  obtain ⟨-, -, hn', -⟩ := h.hlp
  have e := (upPath_det B'.ns hu (upPath.self _ r0 h0 hp0)).1
  rw [e, List.mem_singleton] at hm
  obtain ⟨rc', hrc', hpc⟩ := (hT.2.1 n rn hn').2 x hx
  rw [hm, h0] at hrc'; cases hrc'
  rw [hp0] at hpc; exact absurd hpc.symm h.hnn

theorem spP_cs_spilled (h : SPX) (c : Loc) (hc : c ∈ rn.cs) : spilledN bl B' c := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hi, -, -, hlt, -⟩ := h.hlp
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hc
  have hjl := (List.getElem?_eq_some_iff.1 hj).1
  have hd := h.hdrop
  have : rn.cs.length ≤ i := by
    have := congrArg List.length hd; simp at this; omega
  exact hlt j c (by omega) hj

/-- The cut, under a tree: the children of `n` gone, the rest as at the loop's end. -/
theorem spP_B3eq (h : SPX) (htf : top = false) (x : Loc) (hxn : x ≠ n) (hx : (B3.ns !! x).isSome) :
    B3.ns !! x = B'.ns !! x ∧ x ∉ rn.cs := by
  obtain ⟨-, h3o, h3c, -⟩ := spP_B3 h
  by_cases hc : x ∈ rn.cs
  · rw [h3c x hc, spP_noroot h htf x hc] at hx; simp at hx
  · exact ⟨h3o x hxn hc, hc⟩

/-- A node of the call outside `n`'s tree: in the cut. -/
theorem spP_outS (h : SPX) (htf : top = false) (x : Loc) (rx : NRec)
    (hxS : x ∉ n :: (r.cs.map sub).flatten) (hx : B.ns !! x = some rx) :
    x ∉ rn.cs ∧ x ≠ n ∧ ∃ r1, B'.ns !! x = some r1 ∧ dnK rx r1 ∧ B3.ns !! x = some r1 := by
  obtain ⟨-, hB', hn', -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    hout, -⟩ := h.hlp
  obtain ⟨r1, hr1, hd⟩ := hout x rx hxS hx
  have hxn : x ≠ n := fun e => hxS (e ▸ List.mem_cons_self)
  have hxc : x ∉ rn.cs := by
    intro hc
    obtain ⟨⟨rk', Nt', hT'⟩, -⟩ := h.htrp htf
    obtain ⟨⟨rk, Nt, hT⟩, -⟩ := h.htok htf
    obtain ⟨rc', hrc', hpc⟩ := (hT'.2.1 n rn hn').2 x hc
    rw [hr1] at hrc'; cases hrc'
    have hpx : rx.nv.parent' = n := by rw [← hpc, (spP_dnK hd).1]
    obtain ⟨rp, hrp, hm⟩ := hT.2.2.1 x rx hx (by rw [hpx]; exact h.hnn)
    rw [hpx, h.hn] at hrp; cases hrp
    obtain ⟨hkt, -⟩ := h.hch x hm
    exact hxS (List.mem_cons_of_mem _ (List.mem_flatten.2 ⟨sub x, List.mem_map.2 ⟨x, hm, rfl⟩,
      kidsTree_head _ _ _ hkt⟩))
  obtain ⟨-, h3o, -⟩ := spP_B3 h
  exact ⟨hxc, hxn, r1, hr1, hd, by rw [h3o x hxn hxc]; exact hr1⟩

/-- The parts but `n`: not in the cut. -/
theorem spP_fresh3 (h : SPX) (x : Loc) (hx : x ∈ xs.map (fun x => x.1)) (hxn : x ≠ n) :
    B3.ns !! x = none := by
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
  rcases h.hsr with ⟨hxs, -⟩ | ⟨-, -, -, -, -, -, hfr, -⟩
  · rw [hxs] at hy; rw [List.mem_singleton] at hy; subst hy; exact absurd rfl hxn
  · exact hfr.1 y hy hxn

/-- The capacities after the split. -/
theorem spP_Ks (h : SPX) (x : Loc) (hx : x ∉ xs.map (fun x => x.1)) (hp : x ≠ par) :
    Ks x = K' x := by
  rcases h.hsr with ⟨-, -, -, rfl⟩ | ⟨-, -, -, -, -, -, -, -, -, rfl, -⟩
  · rfl
  · unfold splitK; rw [if_neg hx, if_neg hp]

theorem spP_bufs (h : SPX) : T.bufs ⊆ Ts.bufs := by
  obtain ⟨-, -, -, -, hfr, -⟩ := h.hlp
  have e := h.hT3
  have h1 := hfr.2.2.2.1
  have h2 := h.hst.2.2.2.2.2.1
  have e3 : T3.bufs = T'.bufs := by rw [e]; rfl
  rw [e3] at h2
  exact GMap.map_subseteq_trans h1 h2

/-- The ids of the parts: `n` first. -/
theorem spP_ids (h : SPX) :
    xs.map (fun x => x.1) = n :: (xs.drop 1).map (fun x => x.1) ∧ (xs.map (fun x => x.1)).Nodup := by
  obtain ⟨hne, hnd, hhd, -⟩ := h.hst.2.1
  cases hx : xs with
  | nil => exact absurd hx hne
  | cons x0 rest =>
    rw [hx] at hhd hnd
    simp only [List.head?_cons, Option.map_some, Option.some.injEq] at hhd
    exact ⟨by simp [hhd], hnd⟩

/-- Under an old parent: the parent's record after the parts. -/
theorem spP_parent'' (h : SPX) (hp : r.nv.parent' ≠ null) :
    ∃ rpB rp1 rq, B.ns !! par = some rpB ∧ B'.ns !! par = some rp1 ∧ dnK rpB rp1 ∧
      B3.ns !! par = some rp1 ∧ B''.ns !! par = some rq ∧ K'' par = false ∧
      rq.nv = { rp1.nv with inodes' := rq.nv.inodes', children' := rq.nv.children', key' := rq.nv.key' } ∧
      rq.cs = rp1.cs ++ (xs.drop 1).map (fun x => x.1) ∧ rq.key = rp1.key ∧
      (rp1.nv.key' = slice.nil → rq.nv.key' = slice.nil) ∧
      (rp1.nv.key' ≠ slice.nil → 0 < rp1.key.length → rq.nv.key' ≠ slice.nil) ∧
      (rq.ksrc = rp1.ksrc ∨ rq.ksrc = Src.own (DFrac.own 1)) ∧
      wsLive rq.ws ∧ rq.ins.length = rq.ws.length ∧ wsSorted rq.ws ∧ rq.nv.bucket' = bl ∧
      par ∉ xs.map (fun x => x.1) ∧
      ∃ i0' w0 es, rp1.ws[i0']? = some w0 ∧ w0.key = r.key ∧ w0.pgid = r.nv.pgid' ∧
        pieceEntries ps es ∧
        rq.ws.map ownFresh = (rp1.ws.take i0' ++ es ++ rp1.ws.drop (i0' + 1)).map ownFresh := by
  obtain ⟨-, hpe, -, -, rpB, rp1, hrpB, hrp1, hd1, h3p, rp0, hrp0, hnv0, hcs0, hws0, -, hkey0, hks0⟩ :=
    spP_oldpar h hp
  have hp0 : par ≠ null := hpe ▸ hp
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hpar, -⟩ := h.hpp
  obtain ⟨rq, hrq, hKq, hpws, hwl, hil, hsrt, hbk, hpx, rp0', hrp0', hcsq, hkeyq, hnvq, hknq, hknnq, hksq⟩ :=
    hpar hp0
  rw [hrp0] at hrp0'; cases hrp0'
  obtain ⟨-, -, -, -, -, -, hspar, -⟩ := h.hst.2.1
  obtain ⟨rp0'', hrp0'', hw0, hcase⟩ := hspar hp0
  rw [hrp0] at hrp0''; cases hrp0''
  obtain ⟨-, -, -, -, -, -, hrck, -⟩ := spP_rc h
  obtain ⟨w0, hw0i, hw0k, hw0p⟩ : ∃ w, ws0[i0]? = some w ∧ w.key = rc.key ∧ w.pgid = rc.nv.pgid' := by
    rcases hcase with ⟨-, hh⟩ | ⟨hn0, -⟩
    · exact hh
    · exact absurd ((spP_rc h).1.symm.trans hn0) hp
  have hpsne : ps ≠ [] := by
    intro e; have := h.hpx; rw [e] at this; have := (spP_par h).2.2.2
    have h1 := List.length_pos_iff.2 this; simp at *; omega
  obtain ⟨es, hes, hwsq⟩ : ∃ es, pieceEntries ps es ∧
      rq.ws.map ownFresh = (ws0.take i0 ++ es ++ ws0.drop (i0 + 1)).map ownFresh := by
    rcases hpws with ⟨e, -⟩ | ⟨-, hh⟩
    · exact absurd e hpsne
    · exact hh
  rw [← hw0, hws0] at hw0i hwsq
  refine ⟨rpB, rp1, rq, hrpB, hrp1, hd1, h3p, hrq, hKq, ?_, by rw [hcsq, hcs0], by rw [hkeyq, hkey0],
    fun hh => hknq (by rw [hnv0]; exact hh), fun hh hl => hknnq (by rw [hnv0]; exact hh) (by rw [hkey0]; exact hl),
    ?_, hwl, hil, hsrt, hbk, hpx, i0, w0, es, hw0i,
    by rw [hw0k, hrck], by rw [hw0p, (spP_rc h).2.2.1], hes, hwsq⟩
  · rw [hnvq]; rw [hnv0]
  · rcases hksq with e | e
    · left; rw [e, hks0]
    · right; exact e

/-- Under an old parent, the bucket's nodes after the parts: a tree. -/
theorem spP_tree'' (h : SPX) (htf : top = false) (hp : r.nv.parent' ≠ null)
    (hpos : ∀ x ∈ xs, 0 < x.2.2.length)
    (hnn'' : ∀ l rx, B''.ns !! l = some rx → l ≠ null) : treeOK bl B'' := by
  obtain ⟨-, hpe, hpn, hpc, -⟩ := spP_oldpar h hp
  obtain ⟨rpB, rp1, rq, -, hrp1, -, h3p, hrq, -, hnvq, hcsq, hkeyq, hknq, -, hksq, hwl, hil, -, hbk, hpx,
    i0', w0, es, -, -, -, hes, hwsq⟩ := spP_parent'' h hp
  obtain ⟨⟨rk, Nt, hT⟩, ⟨r0, h0, hr0p⟩, hroot, hok⟩ := h.htrp htf
  obtain ⟨-, -, hn', -, -, -, -, -, -, -, -, -, hnvn, -, -, -, hL, -⟩ := h.hlp
  obtain ⟨hids, hidnd⟩ := spP_ids h
  have hrnp : rn.nv.parent' = par := by rw [hnvn, hpe]
  have hp0 : par ≠ null := hpe ▸ hp
  have hqp : rq.nv.parent' = rp1.nv.parent' := by rw [hnvq]
  have hqpg : rq.nv.pgid' = rp1.nv.pgid' := by rw [hnvq]
  obtain ⟨-, h3o, -⟩ := spP_B3 h
  have hbv'' : B''.bv = B'.bv := by
    obtain ⟨-, -, -, -, -, -, hbv', -⟩ := h.hpp
    rw [hbv', (spP_Bs h).1, (spP_B3 h).2.2.2.1]
  -- B''s nodes outside the parts and the parent: those of B' kept
  have hnotids : ∀ x r1, B'.ns !! x = some r1 → x ≠ n → x ∉ rn.cs → x ∉ xs.map (fun x => x.1) := by
    intro x r1 hx hxn hxc hm
    have := spP_fresh3 h x hm hxn
    rw [h3o x hxn hxc, hx] at this; cases this
  have hk3 : ∀ x r1, B'.ns !! x = some r1 → x ≠ n → x ∉ rn.cs → x ≠ par →
      ∃ rx, B''.ns !! x = some rx ∧ dnK r1 rx := by
    intro x r1 hx hxn hxc hxp
    exact spP_keep3 h x r1 (hnotids x r1 hx hxn hxc) hxp (by rw [h3o x hxn hxc]; exact hx)
  have hcsE : ∀ c ∈ rn.cs, ∀ rc', B'.ns !! c = some rc' → rc'.cs = [] := by
    intro c hc rc' hrc'
    obtain ⟨rc2, hrc2, -, hcs2, -⟩ := spP_cs_spilled h c hc
    rw [hrc'] at hrc2; cases hrc2; exact hcs2
  have hcsN : ∀ c ∈ rn.cs, ∃ rc', B'.ns !! c = some rc' ∧ rc'.nv.parent' = n :=
    fun c hc => (hT.2.1 n rn hn').2 c hc
  have hrkn : rk n < rk par := by have := (hT.1 n rn hn').2 (by rw [hrnp]; exact hp0); rwa [hrnp] at this
  have hnin : n ∈ rp1.cs := by
    obtain ⟨rp, hrp, hm⟩ := hT.2.2.1 n rn hn' (by rw [hrnp]; exact hp0)
    rw [hrnp, hrp1] at hrp; cases hrp; exact hm
  -- a parent in B' of a node outside `n`'s children: not a child of `n`, not `n` (but `par`'s
  -- own children)
  have hpar_ok : ∀ y ry, B'.ns !! y = some ry → y ≠ n → y ∉ rn.cs → ry.nv.parent' ≠ null →
      ry.nv.parent' ≠ n ∧ ry.nv.parent' ∉ rn.cs := by
    intro y ry hy hyn hyc hyp
    refine ⟨fun e => ?_, fun hc => ?_⟩
    · obtain ⟨rp, hrp, hm⟩ := hT.2.2.1 y ry hy hyp
      rw [e, hn'] at hrp; cases hrp; exact hyc hm
    · obtain ⟨rp, hrp, hm⟩ := hT.2.2.1 y ry hy hyp
      obtain ⟨rc', hrc', -⟩ := hcsN _ hc
      rw [hrc'] at hrp; cases hrp
      rw [hcsE _ hc rp hrc'] at hm; cases hm
  have hpar1 := hpar_ok par rp1 hrp1 hpn hpc
  have hpar_rk : rp1.nv.parent' ≠ null → rk par < rk rp1.nv.parent' := fun hh => (hT.1 par rp1 hrp1).2 hh
  let rk'' : Loc → Nat := fun l => if l ∈ xs.map (fun x => x.1) then rk n else rk l
  have hrkp : rk'' par = rk par := by show (if _ then _ else _) = _; rw [if_neg hpx]
  have hrkx : ∀ y ry, B'.ns !! y = some ry → y ≠ n → y ∉ rn.cs → rk'' y = rk y :=
    fun y ry hy hyn hyc => by show (if _ then _ else _) = _; rw [if_neg (hnotids y ry hy hyn hyc)]
  -- the records of B''
  have hcl := spP_class h hp0
  refine ⟨⟨rk'', Nt, ⟨fun l rx hl => ?_, fun l rx hl => ?_, fun l rx hl hlp => ?_, hnn''⟩⟩,
    ?_, fun l rx hl hlp => ?_, fun l rx hl => ?_⟩
  -- ranks
  · rcases hcl l rx hl with ⟨j, x, -, hxj, hx1, -, -, -, -, -, -, hxp⟩ | ⟨e, -⟩ |
        ⟨hlx, hlp, hln, r1, hr1, -, hnv1, -, -, -, hl3⟩
    · have hli : l ∈ xs.map (fun x => x.1) := by
        rw [← hx1]; exact List.mem_map_of_mem (List.mem_of_getElem? hxj)
      have e1 : rk'' l = rk n := by show (if _ then _ else _) = _; rw [if_pos hli]
      rw [e1, hxp, hrkp]
      exact ⟨(hT.1 n rn hn').1, fun _ => hrkn⟩
    · rw [e, hrq] at hl; cases hl
      rw [e, hrkp, hqp]
      refine ⟨(hT.1 _ rp1 hrp1).1, fun hh => ?_⟩
      obtain ⟨rpp, hrpp, -⟩ := hT.2.2.1 _ rp1 hrp1 hh
      have := hpar1 hh
      rw [hrkx _ rpp hrpp this.1 this.2]; exact hpar_rk hh
    · have hlc : l ∉ rn.cs := (spP_B3eq h htf l hln hl3).2
      have hp1 : rx.nv.parent' = r1.nv.parent' := by rw [hnv1]
      rw [hrkx l r1 hr1 hln hlc, hp1]
      refine ⟨(hT.1 l r1 hr1).1, fun hh => ?_⟩
      obtain ⟨rpp, hrpp, -⟩ := hT.2.2.1 l r1 hr1 hh
      have := hpar_ok l r1 hr1 hln hlc hh
      rw [hrkx _ rpp hrpp this.1 this.2]; exact (hT.1 l r1 hr1).2 hh
  -- children lists
  · rcases hcl l rx hl with ⟨j, x, -, hxj, hx1, -, -, hs, -⟩ | ⟨e, -⟩ |
        ⟨hlx, hlp, hln, r1, hr1, -, hnv1, hcs1, -, -, hl3⟩
    · obtain ⟨rs, hrs, -, hcss, -⟩ := hs
      rw [hl] at hrs; cases hrs
      rw [hcss]; exact ⟨List.nodup_nil, fun c hc => by cases hc⟩
    · rw [e, hrq] at hl; cases hl; rw [e]
      rw [hcsq]
      have hxnd : ((xs.drop 1).map (fun x => x.1)).Nodup := by
        have := hidnd; rw [hids] at this; exact (List.nodup_cons.1 this).2
      have hnx : n ∉ (xs.drop 1).map (fun x => x.1) := by
        have := hidnd; rw [hids] at this; exact (List.nodup_cons.1 this).1
      have hxid : ∀ c ∈ (xs.drop 1).map (fun x => x.1), c ∈ xs.map (fun x => x.1) := by
        intro c hc; rw [hids]; exact List.mem_cons_of_mem _ hc
      refine ⟨List.nodup_append.2 ⟨(hT.2.1 _ rp1 hrp1).1, hxnd, fun a ha b hb eab => ?_⟩,
        fun c hc => ?_⟩
      · subst eab
        obtain ⟨rc', hrc', hpc'⟩ := (hT.2.1 _ rp1 hrp1).2 a ha
        have han : a ≠ n := fun e' => hnx (e' ▸ hb)
        have hac : a ∉ rn.cs := by
          intro hc'; obtain ⟨rc2, hrc2, hp2⟩ := hcsN a hc'
          rw [hrc'] at hrc2; cases hrc2; rw [hpc'] at hp2; exact hpn hp2
        exact hnotids a rc' hrc' han hac (hxid a hb)
      · rcases List.mem_append.1 hc with hc | hc
        · obtain ⟨rc', hrc', hpc'⟩ := (hT.2.1 _ rp1 hrp1).2 c hc
          by_cases hcn : c = n
          · rw [hcn]; exact ⟨rn5, h.hrn5, h.hpar5⟩
          have hcc : c ∉ rn.cs := by
            intro hc'; obtain ⟨rc2, hrc2, hp2⟩ := hcsN c hc'
            rw [hrc'] at hrc2; cases hrc2; rw [hpc'] at hp2; exact hpn hp2
          have hcp : c ≠ par := by
            intro e'; rw [e', hrp1] at hrc'; cases hrc'
            have := hpar_rk (by rw [hpc']; exact hp0); rw [hpc'] at this; omega
          obtain ⟨rx', hrx', hd⟩ := hk3 c rc' hrc' hcn hcc hcp
          exact ⟨rx', hrx', by rw [(spP_dnK hd).1]; exact hpc'⟩
        · obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 (hxid c hc)
          rw [List.getElem?_map] at hj
          obtain ⟨y, hyj, hy1⟩ := Option.map_eq_some_iff.1 hj
          have hjl : j < ps.length := by rw [h.hpx]; exact (List.getElem?_eq_some_iff.1 hyj).1
          obtain ⟨-, rx', p, hrx', -, -, hpa, -⟩ := spP_written h hp0 j c hjl (by rw [hyj]; simp [hy1])
          exact ⟨rx', hrx', hpa⟩
    · rw [hcs1]
      refine ⟨(hT.2.1 l r1 hr1).1, fun c hc => ?_⟩
      obtain ⟨rc', hrc', hpc'⟩ := (hT.2.1 l r1 hr1).2 c hc
      have hlc : l ∉ rn.cs := (spP_B3eq h htf l hln hl3).2
      have hcn : c ≠ n := by
        intro e'; rw [e', hn'] at hrc'; cases hrc'; rw [hrnp] at hpc'; exact hlp hpc'.symm
      have hcc : c ∉ rn.cs := by
        intro hc'; obtain ⟨rc2, hrc2, hp2⟩ := hcsN c hc'
        rw [hrc'] at hrc2; cases hrc2; rw [hpc'] at hp2; exact hln hp2
      by_cases hcp : c = par
      · rw [hcp] at hrc' ⊢; rw [hrp1] at hrc'; cases hrc'
        exact ⟨rq, hrq, by rw [hqp]; exact hpc'⟩
      · obtain ⟨rx', hrx', hd⟩ := hk3 c rc' hrc' hcn hcc hcp
        exact ⟨rx', hrx', by rw [(spP_dnK hd).1]; exact hpc'⟩
  -- each node in its parent's children
  · rcases hcl l rx hl with ⟨j, x, -, hxj, hx1, -, -, -, -, -, -, hxp⟩ | ⟨e, -⟩ |
        ⟨hlx, hlp', hln, r1, hr1, -, hnv1, -, -, -, hl3⟩
    · rw [hxp]
      refine ⟨rq, hrq, ?_⟩
      rw [hcsq]
      by_cases hln : l = n
      · rw [hln]; exact List.mem_append_left _ hnin
      · apply List.mem_append_right
        have hli : l ∈ xs.map (fun x => x.1) := by
          rw [← hx1]; exact List.mem_map_of_mem (List.mem_of_getElem? hxj)
        rw [hids] at hli
        rcases List.mem_cons.1 hli with e' | e'
        · exact absurd e' hln
        · exact e'
    · rw [e, hrq] at hl; cases hl
      rw [hqp] at hlp ⊢
      obtain ⟨rpp, hrpp, hm⟩ := hT.2.2.1 _ rp1 hrp1 hlp
      have := hpar1 hlp
      have hqp' : rp1.nv.parent' ≠ par := by
        intro e'; have := hpar_rk hlp; rw [e'] at this; omega
      obtain ⟨rx', hrx', hd⟩ := hk3 _ rpp hrpp this.1 this.2 hqp'
      exact ⟨rx', hrx', by rw [(spP_dnK hd).2.1, e]; exact hm⟩
    · have hlc : l ∉ rn.cs := (spP_B3eq h htf l hln hl3).2
      have hp1 : rx.nv.parent' = r1.nv.parent' := by rw [hnv1]
      rw [hp1] at hlp ⊢
      obtain ⟨rpp, hrpp, hm⟩ := hT.2.2.1 l r1 hr1 hlp
      by_cases hpp : r1.nv.parent' = par
      · rw [hpp] at hrpp ⊢; rw [hrp1] at hrpp; cases hrpp
        exact ⟨rq, hrq, by rw [hcsq]; exact List.mem_append_left _ hm⟩
      · have := hpar_ok l r1 hr1 hln hlc hlp
        obtain ⟨rx', hrx', hd⟩ := hk3 _ rpp hrpp this.1 this.2 hpp
        exact ⟨rx', hrx', by rw [(spP_dnK hd).2.1]; exact hm⟩
  -- the root node
  · rw [hbv'']
    have hrn : B'.bv.rootNode' ≠ n := by
      intro e; rw [e, hn'] at h0; cases h0; rw [hrnp] at hr0p; exact hp0 hr0p
    have hrc : B'.bv.rootNode' ∉ rn.cs := by
      intro hc; obtain ⟨rc2, hrc2, hp2⟩ := hcsN _ hc
      rw [h0] at hrc2; cases hrc2; rw [hr0p] at hp2; exact h.hnn hp2.symm
    by_cases hrp : B'.bv.rootNode' = par
    · rw [hrp] at h0 ⊢; rw [hrp1] at h0; cases h0
      exact ⟨rq, hrq, by rw [hqp]; exact hr0p⟩
    · obtain ⟨rx', hrx', hd⟩ := hk3 _ r0 h0 hrn hrc hrp
      exact ⟨rx', hrx', by rw [(spP_dnK hd).1]; exact hr0p⟩
  · rcases hcl l rx hl with ⟨j, x, -, hxj, hx1, -, -, -, -, -, -, hxp⟩ | ⟨e, -⟩ |
        ⟨hlx, hlp', hln, r1, hr1, -, hnv1, -, -, -, hl3⟩
    · rw [hxp] at hlp; exact absurd hlp hp0
    · rw [e, hrq] at hl; cases hl
      rw [hqp] at hlp
      rw [e, hbv'']; exact hroot _ rp1 hrp1 hlp
    · have hp1 : rx.nv.parent' = r1.nv.parent' := by rw [hnv1]
      rw [hp1] at hlp
      rw [hbv'']; exact hroot l r1 hr1 hlp
  -- every node readable by `dereference`
  · rcases hcl l rx hl with ⟨j, x, -, hxj, hx1, -, -, hs, -⟩ | ⟨e, -⟩ |
        ⟨hlx, hlp', hln, r1, hr1, -, -, -, -, -, hl3⟩
    · obtain ⟨rs, hrs, -, -, -, -, -, hdok, -⟩ := hs
      rw [hl] at hrs; cases hrs; exact hdok
    · rw [e, hrq] at hl; cases hl
      obtain ⟨-, -, hws1, hkk1⟩ := hok _ rp1 hrp1
      refine ⟨hbk, hil, fun w hw => ⟨(hwl w hw).1, (hwl w hw).2, ?_⟩, ?_⟩
      · obtain ⟨w', hw', hk, -⟩ := spP_mem_fresh hwsq hw
        rw [hk]
        rcases List.mem_append.1 hw' with hw' | hw'
        · rcases List.mem_append.1 hw' with hw' | hw'
          · exact (hws1 w' (List.mem_of_mem_take hw')).2.2
          · obtain ⟨p, hp, -, -, hk2, -⟩ := spF2_mem_r hes w' hw'
            obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hp
            obtain ⟨w'', hw'', hk'⟩ := spP_pmem h hpos j p hj
            rw [hk2, hk']; exact (hL.2.2.2.2.1 w'' hw'').1
        · exact (hws1 w' (List.mem_of_mem_drop hw')).2.2
      · by_cases hk : rq.nv.key' = slice.nil
        · exact Or.inl hk
        · right
          rcases hkk1 with hk1 | ⟨hks1, hpg1⟩
          · exact absurd (hknq hk1) hk
          · refine ⟨?_, by rw [hqpg, hkeyq]; exact hpg1⟩
            rcases hksq with e' | e'
            · rw [e']; exact hks1
            · rw [e']; nofun
    · have h3 := (spP_B3eq h htf l hln hl3).1
      rw [hr1] at h3
      obtain ⟨rx', hrx', hd⟩ := spP_keep3 h l r1 hlx hlp' h3
      rw [hl] at hrx'; cases hrx'
      rcases hd with rfl | hd
      · exact hok l _ hr1
      · exact derefOK_derefNode bl _ _ (hok l r1 hr1) hd.1.1

theorem spP_pe_fresh (ps : List (w64 × List w8)) (es : List WEntry) (h : pieceEntries ps es) :
    pieceEntries ps (es.map ownFresh) := by
  unfold pieceEntries at *
  induction h with
  | nil => exact .nil
  | cons hr _ ih => exact .cons ⟨hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, nofun, nofun⟩ ih

/-- No old parent but a parent after the parts: a new one, pgid 0. -/
theorem spP_newpar_pg (h : SPX) (hr0 : r.nv.parent' = null) (hlen : 2 ≤ xs.length) (rq : NRec)
    (hrq : B''.ns !! par = some rq) : rq.nv.pgid' = W64 0 := by
  have hp0 : par ≠ null := (spP_par h).1 hlen
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hpar, -⟩ := h.hpp
  obtain ⟨rp, hrp, -, -, -, -, -, -, -, rp0, hrp0, -, -, hnv0, -⟩ := hpar hp0
  rw [hrq] at hrp; cases hrp
  have hrcp : rc.nv.parent' = null := (spP_rc h).1.trans hr0
  rcases h.hsr with ⟨hxs, -⟩ | ⟨pv', pcs', st, -, -, -, hfr, -, hBs, -, hcase⟩
  · rw [hxs] at hlen; simp at hlen
  obtain ⟨-, hpv, -⟩ := hcase.resolve_right (fun hh => hh.1 hrcp)
  have hBp : Bs.ns !! par = some ⟨pv', [], [], pcs', [], Src.own (DFrac.own 1)⟩ := by
    rw [hBs]
    show splitNs B3.ns rc _ xs par pv' pcs' !! par = _
    rw [splitNs_par _ _ _ _ _ _ _ hfr.2.2.1]
    unfold parentRec; rw [if_pos hrcp]
  rw [hBp] at hrp0; cases hrp0
  have e : rq.nv.pgid' = pv'.pgid' := by rw [hnv0]
  rw [e, hpv]; rfl

/-- No parent: the part is the bucket's root (its only part), `finPost`. -/
theorem spPost_root (γd : DBNames) (γ : GName)
    (h : SPX)
    (hpn : rn5.nv.parent' = null) :
    spillR I γd γ W'' txl txid T'' ρ'' F'' K'' ∗
      pieceResP (par ≠ null) γ (spillPages W'' T'') (if rc.nv.isLeaf' then leafPageFlag else branchPageFlag)
        (ht n) ps
        (hiAt (chunksOf rc xs) (bnd n).2 (ps.length - 1)) ∗
      chunkToks γ (spillPages W'' T'') B'' rc.nv.isLeaf' (kd n) (ht n - 1) (chunksOf rc xs) (bnd n).2
        ps.length ∗
      (if ps = [] ∧ rc.nv.pgid' ≠ W64 0 then (uint.nat rc.nv.pgid' ↪[γ] () : IProp GF) else emp) ⊢
    ⌜r.nv.parent' = null⌝ ∗ finPost I γd γ W txl txid T bl B K interface.nil := by
  have hpar0 : par = null := h.hpar5 ▸ hpn
  obtain ⟨h2p, h1p, -, hne⟩ := spP_par h
  have hlen : xs.length = 1 := by
    have := List.length_pos_iff.2 hne
    by_cases hc : 2 ≤ xs.length
    · exact absurd hpar0 (h2p hc)
    · omega
  have hr0 : r.nv.parent' = null := by rw [← h1p hlen, hpar0]
  obtain ⟨hxs, hTs, hBs, hKs⟩ : xs = [(n, rc.nv, rc.ins)] ∧ Ts = T3 ∧ Bs = B3 ∧ Ks = K' := by
    rcases h.hsr with h1 | ⟨_, _, _, h2, -⟩
    · exact h1
    · omega
  have hps1 : ps.length = 1 := h.hpx.trans hlen
  obtain ⟨p0, hp0⟩ : ∃ p0, ps = [p0] := List.length_eq_one_iff.1 hps1
  have hids : xs.map (fun x => x.1) = [n] := by rw [hxs]; rfl
  obtain ⟨hB'', hbv, hib, hnm, hbm⟩ := spP_bkt h
  -- the part
  obtain ⟨rx, p1, hrx, hsps, hcss, hp1, hpg1⟩ := spP_written0 h 0 n (by omega) (by rw [hxs]; rfl)
  rw [h.hrn5] at hrx; cases hrx
  rw [hp0] at hp1; simp only [List.getElem?_cons_zero, Option.some.injEq] at hp1; subst hp1
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hfresh, -⟩ := h.hpp
  have hbuf := (hfresh p0 (by rw [hp0]; exact List.mem_singleton_self _)).2.2.1
  -- the chain from the root node
  obtain ⟨p, hup3, hnd, hdom3, hin3, -⟩ := spP_pathB3 h hr0
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hdomp, -⟩ := h.hpp
  have hkp : ∀ x ∈ p, x ≠ n → ∀ r3, B3.ns !! x = some r3 → ∃ rx, B''.ns !! x = some rx ∧ dnK r3 rx :=
    fun x hx hxn r3 h3 => spP_keep3 h x r3 (by rw [hids]; simpa using hxn)
      (by rw [hpar0]; exact h.h3nn x r3 h3) h3
  have hup'' : upPath B''.ns B.bv.rootNode' p n := by
    apply upPath_par B3.ns B''.ns hup3
    intro x hx r3 h3
    by_cases e : x = n
    · subst e
      rw [(spP_B3 h).1] at h3; cases h3
      exact ⟨rn5, h.hrn5, by rw [hpn, (spP_rc h).1, hr0]⟩
    · obtain ⟨rx, hrx, hd⟩ := hkp x hx e r3 h3
      exact ⟨rx, hrx, by rw [(spP_dnK hd).1]⟩
  have hdom'' : ∀ l, (B''.ns !! l).isSome ↔ l ∈ p := by
    intro l
    constructor
    · intro hl
      have := hdomp l hl
      rw [hBs] at this
      exact hdom3 l this
    · intro hl
      by_cases e : l = n
      · subst e; rw [h.hrn5]; rfl
      · obtain ⟨r3, h3⟩ := Option.isSome_iff_exists.1 (hin3 l hl)
        obtain ⟨rx, hrx, -⟩ := hkp l hl e r3 h3
        rw [hrx]; rfl
  iintro ⟨HR, Hpcs, -, -⟩
  icases spExit_keep γd γ h $$ HR with ⟨%hko, HR⟩
  rw [hp0]
  unfold pieceResP
  icases (BigSepL.bigSepL_cons (PROP := IProp GF)).1 $$ Hpcs with ⟨⟨%Q, %pg, %hQ, Hw⟩, -⟩
  isplitr
  · ipureintro; exact hr0
  unfold finPost
  ileft
  isplitr
  · ipureintro; rfl
  iexists W'', T'', ρ'', F'', K'', B'', p, n, p0.1, Q
  iframe HR
  isplitl [Hw]
  · unfold wtreeQ
    icases Hw with ⟨Ht, %hF⟩
    iframe Ht
    ipureintro
    exact wtreeF_widen _ _ _ _ _ _ hF (fun l hl => by cases hl) (fun hh hl => by cases hl)
  ipureintro
  obtain ⟨hQs, hQp, -⟩ := hQ
  exact ⟨h.hpp.1, spP_frame h, (spP_pages h).1, hB'', hbv, hib, hnm, hbm, hup'', hnd, hdom'',
    by rw [hQp]; rfl, hQs, hbuf, hko, rn5, h.hrn5, hpg1, hsps, hpn, hcss⟩

/-- The existing parent (a page): `subPost`. -/
theorem spPost_sub' (γd : DBNames) (γ : GName)
    (h : SPX)
    (hpn : rn5.nv.parent' ≠ null) (rq : NRec) (hrq : B''.ns !! rn5.nv.parent' = some rq)
    (hq0 : rq.nv.pgid' ≠ W64 0) :
    spillR I γd γ W'' txl txid T'' ρ'' F'' K'' ∗
      pieceRes γ (spillPages W'' T'') (if rc.nv.isLeaf' then leafPageFlag else branchPageFlag) (ht n) ps
        (hiAt (chunksOf rc xs) (bnd n).2 (ps.length - 1)) ∗
      chunkToks γ (spillPages W'' T'') B'' rc.nv.isLeaf' (kd n) (ht n - 1) (chunksOf rc xs) (bnd n).2
        ps.length ∗
      (if ps = [] ∧ rc.nv.pgid' ≠ W64 0 then (uint.nat rc.nv.pgid' ↪[γ] () : IProp GF) else emp) ⊢
    ⌜r.nv.parent' ≠ null⌝ ∗ ∃ rp, ⌜B.ns !! r.nv.parent' = some rp⌝ ∗
      node.spill.subPost I γd γ W txl txid T bl B bnd (n :: (r.cs.map sub).flatten) n r
        r.nv.parent' rp K ht interface.nil := by
  have hpar' : par ≠ null := h.hpar5 ▸ hpn
  have hrqp : B''.ns !! par = some rq := by rw [← h.hpar5]; exact hrq
  -- the node had a parent
  have hp : r.nv.parent' ≠ null := by
    intro hr0
    obtain ⟨-, h1p, -, hne⟩ := spP_par h
    have hlen : 2 ≤ xs.length := by
      have := List.length_pos_iff.2 hne
      by_cases hc : 2 ≤ xs.length
      · exact hc
      · exact absurd ((h1p (by omega)).trans hr0) hpar'
    exact hq0 (spP_newpar_pg h hr0 hlen rq hrqp)
  obtain ⟨htf, hpe, hpn', hpc, -⟩ := spP_oldpar h hp
  obtain ⟨rpB, rp1, rq', hrpB, hrp1, hd1, h3p, hrq', hKq, hnvq, hcsq, hkeyq, hknq, hknnq, hksq, hwl, hil,
    hsrt, -, hpx, i0', w0, es, hw0, hw0k, -, hes, hwsq⟩ := spP_parent'' h hp
  rw [hrqp] at hrq'; cases hrq'
  obtain ⟨hB'', hbv, hib, hnm, hbm⟩ := spP_bkt h
  obtain ⟨hpg, hpss⟩ := spP_pages h
  obtain ⟨hids, hidnd⟩ := spP_ids h
  have hxnd : ((xs.drop 1).map (fun x => x.1)).Nodup := by
    have := hidnd; rw [hids] at this; exact (List.nodup_cons.1 this).2
  have hnx : n ∉ (xs.drop 1).map (fun x => x.1) := by
    have := hidnd; rw [hids] at this; exact (List.nodup_cons.1 this).1
  obtain ⟨-, hB', hn', -, -, hpgs, -, -, hbv', hib', hnm', hbm', hnvn, -, -, -, hL, hok, -, -, -, -,
    -, -, -, -, -, -, hdom', hrem, hkk, -⟩ := h.hlp
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hkey, hfresh, hpnd, -, -, -, hKs, -⟩ := h.hpp
  have hrnp : rn.nv.parent' ≠ null := by rw [hnvn]; exact hp
  have hpos : ∀ x ∈ xs, 0 < x.2.2.length := by
    intro x hx
    rcases h.hsr with ⟨hxs, -⟩ | ⟨-, -, -, h2, hsp, -⟩
    · rw [hxs, List.mem_singleton] at hx
      rw [hx]
      show 0 < rc.ins.length
      obtain ⟨-, -, -, -, -, hins, -⟩ := spP_rc h
      rw [hins, hL.2.2.1]; exact hok.2.1 n rn hn' hrnp
    · have := hsp.2.2 h2 x hx; omega
  have hlen1 : 1 ≤ xs.length := List.length_pos_iff.2 (spP_par h).2.2.2
  have hpsl : ps.length = xs.length := h.hpx
  have hps0 : ps ≠ [] := by intro e; rw [e] at hpsl; simp at hpsl; omega
  have hxs' : ∀ x, x ∈ xs.map (fun x => x.1) → x ≠ n → x ∈ (xs.drop 1).map (fun x => x.1) := by
    intro x hx hxn; rw [hids] at hx
    rcases List.mem_cons.1 hx with e | e
    · exact absurd e hxn
    · exact e
  have hnm0 : Bs.nm = B.nm := by rw [(spP_Bs h).2.2.1, (spP_B3 h).2.2.2.2.2.1, hnm']
  -- the written part `j`
  have hwj : ∀ j x, j < ps.length → (xs[j]?).map (fun x => x.1) = some x →
      spilledN bl B'' x ∧ ∃ rx p, B''.ns !! x = some rx ∧ ps[j]? = some p ∧ rx.nv.pgid' = p.1 :=
    fun j x hj hx => by
      obtain ⟨hs, rx, p, hrx, hp', hpg', -⟩ := spP_written h hpar' j x hj hx
      exact ⟨hs, rx, p, hrx, hp', hpg'⟩
  have hx0 : (xs[0]?).map (fun x => x.1) = some n := by
    rw [← List.getElem?_map, hids]; rfl
  have hxj : ∀ j x, ((xs.drop 1).map (fun x => x.1))[j]? = some x →
      (xs[j + 1]?).map (fun x => x.1) = some x ∧ j + 1 < ps.length := by
    intro j x hj
    rw [List.getElem?_map, List.getElem?_drop] at hj
    refine ⟨by rw [Nat.add_comm]; exact hj, ?_⟩
    obtain ⟨y, hy, -⟩ := Option.map_eq_some_iff.1 hj
    have := (List.getElem?_eq_some_iff.1 hy).1; omega
  -- the parts' entries in the parent
  have hf2 := spP_f2_pieces ps es hes
  have hw0l : i0' < rp1.ws.length := (List.getElem?_eq_some_iff.1 hw0).1
  have hdk1 := spP_dnK hd1
  iintro ⟨HR, Hpcs, -, -⟩
  icases spExit_keep γd γ h $$ HR with ⟨%hko, HR⟩
  icases spP_nnull I γd γ W'' txl txid T'' ρ'' F'' K'' bl B'' hB'' $$ HR with ⟨%hnn, HR⟩
  have htree := spP_tree'' h htf hp hpos hnn
  isplitr
  · ipureintro; exact hp
  iexists rpB
  isplitr
  · ipureintro; rw [← hpe]; exact hrpB
  unfold node.spill.subPost
  ileft
  isplitr
  · ipureintro; rfl
  iexists W'', T'', ρ'', F'', K'', B'', ps, (xs.drop 1).map (fun x => x.1), rq
  iframe HR
  isplitl [Hpcs]
  · have hhi : hiAt (chunksOf rc xs) (bnd n).2 (ps.length - 1) = (bnd n).2 := by
      unfold hiAt
      have hcl : (chunksOf rc xs).length = ps.length := by
        unfold chunksOf; rw [wsChunks_length, List.length_map, hpsl]
      rw [show ps.length - 1 + 1 = ps.length by omega, List.getElem?_eq_none (by omega)]
    have hE : pieceRes (GF := GF) γ (spillPages W'' T'')
        (if rc.nv.isLeaf' then leafPageFlag else branchPageFlag) (ht n) ps
        (hiAt (chunksOf rc xs) (bnd n).2 (ps.length - 1)) ⊢
        pieceRes γ (spillPages W'' T'') (if r.nv.isLeaf' then leafPageFlag else branchPageFlag)
          (ht n) ps (bnd n).2 := by
      rw [hhi, (spP_rc h).2.1]
    iapply hE
    iexact Hpcs
  ipureintro
  unfold node.spill.subPostP
  refine ⟨h.hpp.1, spP_frame h, hpg, hpss, hB'', hbv, hib, hnm, hbm, by rw [← hpe]; exact hrqp,
    by rw [← hpe]; exact hKq, ?_, hkeyq.trans hdk1.2.2.1, fun h0 => hknq (hdk1.2.2.2.2.1 h0), ?_, ?_,
    hwl, hil, by rw [hcsq, hdk1.2.1], hps0, by simp only [List.length_map, List.length_drop]; omega,
    hpnd, spP_spages h, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hxnd, hnx, ?_, ?_, ?_, ?_, ?_, ?_, ⟨?_, hko⟩, htree, fun hh hl => ?_⟩
  -- the parent's struct
  · rw [hnvq, hdk1.1]
  -- its key's source
  · rcases hksq with e | e
    · rw [e]; rcases hdk1.2.2.2.2.2.1 with e' | e'
      · exact Or.inl e'
      · exact Or.inr e'
    · exact Or.inr e
  -- its entries: the node's replaced by the parts'
  · refine ⟨i0', ownFresh w0, es.map ownFresh, ?_, hw0k, spP_pe_fresh ps es hes, ?_⟩
    · rw [← hdk1.2.2.2.1, List.getElem?_map, hw0]; rfl
    · rw [hwsq, ← hdk1.2.2.2.1, List.map_append, List.map_append, List.map_take, List.map_drop]
  -- the parts' pages
  · intro p hp'
    obtain ⟨h1, h2, h3, h4, h5⟩ := hfresh p hp'
    refine ⟨?_, by rw [← hpgs]; exact h2, h3, by rw [← hnm0]; exact h4, h5⟩
    cases hb : T.bufs !! p.1 with
    | none => rfl
    | some v => rw [spP_bufs h _ _ hb] at h1; cases h1
  · intro j p x hp' hx
    obtain ⟨hx1, hjl⟩ := hxj j x hx
    obtain ⟨-, rx, p', hrx, hp'', hpg'⟩ := hwj (j + 1) x hjl hx1
    rw [hp'] at hp''; cases hp''
    exact ⟨rx, hrx, hpg'⟩
  · intro p hp'
    obtain ⟨-, rx, p', hrx, hp'', hpg'⟩ := hwj 0 n (by omega) hx0
    rw [hp'] at hp''; cases hp''
    exact ⟨rx, hrx, hpg'⟩
  -- the parts' keys
  · intro p hp'
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hp'
    obtain ⟨w, hw, hk⟩ := spP_pmem h hpos j p hj
    rw [hk]; exact ⟨(hL.2.2.2.2.1 w hw).2, (hL.2.2.2.2.1 w hw).1⟩
  · intro j k a b hjk ha hb
    have hel : es.length = ps.length := hf2.length_eq.symm
    have hkl : k < ps.length := (List.getElem?_eq_some_iff.1 hb).1
    obtain ⟨ea, hea, hra⟩ := forall2_get' _ ps es hf2 j a ha
    obtain ⟨eb, heb, hrb⟩ := forall2_get' _ ps es hf2 k b hb
    have htl : (rp1.ws.take i0').length = i0' := by rw [List.length_take]; omega
    have hwk : ∀ m e, es[m]? = some e → m < es.length → wKey rq.ws (i0' + m) = e.key := by
      intro m e he hm
      have hm' := wKey_mid_es (rp1.ws.take i0') es (rp1.ws.drop (i0' + 1)) m hm
      rw [htl] at hm'
      rw [← wKey_fresh, hwsq, wKey_fresh, hm']
      unfold wKey; rw [he]; rfl
    have hlq : rq.ws.length = rp1.ws.length - 1 + es.length := by
      have := congrArg List.length hwsq
      simp only [List.length_map, List.length_append, List.length_take, List.length_drop] at this
      omega
    have := hsrt (i0' + j) (i0' + k) (by omega) (by omega)
    rw [hwk j ea hea (by omega), hwk k eb heb (by omega), hra.2, hrb.2] at this
    exact this
  · intro x hx
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hx
    obtain ⟨hx1, hjl⟩ := hxj j x hj
    exact (hwj (j + 1) x hjl hx1).1
  · exact (hwj 0 n (by omega) hx0).1
  -- the parts: no node of the call outside `n`'s tree
  · intro x hx l hlS hl e
    subst e
    obtain ⟨rl, hrl⟩ := Option.isSome_iff_exists.1 hl
    obtain ⟨-, hln, r1, -, -, h3⟩ := spP_outS h htf l rl hlS hrl
    rw [spP_fresh3 h l (by rw [hids]; exact List.mem_cons_of_mem _ hx) hln] at h3; cases h3
  -- the nodes outside `n`'s tree: kept
  · intro x rx hxS hxp hx
    obtain ⟨-, hxn, r1, -, hd, h3⟩ := spP_outS h htf x rx hxS hx
    have hxi : x ∉ xs.map (fun x => x.1) := fun hm => by
      rw [spP_fresh3 h x hm hxn] at h3; cases h3
    obtain ⟨rx', hrx', hd'⟩ := spP_keep3 h x r1 hxi (by rw [hpe]; exact hxp) h3
    exact ⟨rx', hrx', dnK_step rx r1 rx' hd hd'⟩
  · intro x hx
    rcases spP_dom'' h x hx with h1 | h1 | h1
    · by_cases hxn : x = n
      · left; rw [hxn, h.hn]; rfl
      · exact Or.inr (hxs' x h1 hxn)
    · left; rw [h1, hpe]; exact h.hpar1 hp
    · by_cases hxn : x = n
      · left; rw [hxn, h.hn]; rfl
      · obtain ⟨e3, hxc⟩ := spP_B3eq h htf x hxn h1
        rw [e3] at h1
        rcases hdom' x h1 with h2 | h2
        · exact Or.inl h2
        · exact absurd h2 hxc
  · intro x hxS hxn hxx
    cases hx : B''.ns !! x with
    | none => rfl
    | some rx =>
      exfalso
      rcases spP_dom'' h x (by rw [hx]; rfl) with h1 | h1 | h1
      · exact hxx (hxs' x h1 hxn)
      · rw [h1, hpe] at hxS
        obtain ⟨rpB', hrpB'⟩ := Option.isSome_iff_exists.1 (h.hpar1 hp)
        exact (h.hplf _ rpB' rfl hp hrpB').1 hxS
      · obtain ⟨e3, hxc⟩ := spP_B3eq h htf x hxn h1
        rw [e3] at h1
        rcases hrem x hxS h1 with e | e | e
        · exact hxn e
        · exact hxc e
        · rw [h.hdrop] at e; simp at e
  · intro p hp'
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hp'
    obtain ⟨w, hw, hk⟩ := spP_pmem h hpos j p hj
    have := hok.1 n rn hn' w hw
    rw [hk]; omega
  · intro x rx hx hrx
    have hxi : x ∈ xs.map (fun x => x.1) := by
      rcases hx with e | e
      · rw [e, hids]; exact List.mem_cons_self
      · rw [hids]; exact List.mem_cons_of_mem _ e
    have hxp : x ≠ par := fun e => hpx (e ▸ hxi)
    obtain ⟨a1, -, -, a4⟩ := spP_nodes'' h hpar' hpos x rx hrx hxp
    exact ⟨a1, a4⟩
  -- capacities
  · intro x hxS hb
    by_cases hxp : x = r.nv.parent'
    · rw [hxp]
      obtain ⟨rpB', hrpB'⟩ := Option.isSome_iff_exists.1 (h.hpar1 hp)
      rw [(h.hplf _ rpB' rfl hp hrpB').2.1, ← hpe]; exact hKq
    obtain ⟨rx, hrx⟩ := Option.isSome_iff_exists.1 hb
    obtain ⟨-, hxn, r1, -, -, h3⟩ := spP_outS h htf x rx hxS hrx
    have hxi : x ∉ xs.map (fun x => x.1) := fun hm => by
      rw [spP_fresh3 h x hm hxn] at h3; cases h3
    rw [hKs x (by rw [List.take_of_length_le (by omega)]; exact hxi),
      spP_Ks h x hxi (by rw [hpe]; exact hxp)]
    exact hkk.1 x hxS hb
  -- the parent's key kept
  · rcases hd1 with rfl | ⟨⟨hd, hx⟩, -⟩
    · exact hknnq hh hl
    · exact hknnq (hx hh hl) (by rw [hd.2.2.2.1]; exact hl)

/-- A new parent (pgid 0), the part's `children` set nil: the new parent's tokens. -/
theorem spNewParent_toks' (γ : GName)
    (h : SPX)
    (hpn : rn5.nv.parent' ≠ null) (rq : NRec) (hrq : B''.ns !! rn5.nv.parent' = some rq)
    (hq0 : rq.nv.pgid' = W64 0) :
    pieceRes (GF := GF) γ (spillPages W'' T'') (if rc.nv.isLeaf' then leafPageFlag else branchPageFlag)
        (ht n) ps (hiAt (chunksOf rc xs) (bnd n).2 (ps.length - 1)) ∗
      chunkToks γ (spillPages W'' T'') B'' rc.nv.isLeaf' (kd n) (ht n - 1) (chunksOf rc xs) (bnd n).2
        ps.length ∗
      (if ps = [] ∧ rc.nv.pgid' ≠ W64 0 then (uint.nat rc.nv.pgid' ↪[γ] () : IProp GF) else emp) ⊢
    rtoks γ (spillPages W'' (setB T'' bl (setN B'' n { rn5 with nv := { rn5.nv with children' := slice.nil } })))
      (setN B'' n { rn5 with nv := { rn5.nv with children' := slice.nil } }) (none, none)
      (if rc.nv.isLeaf' then leafPageFlag else branchPageFlag) (ht n) rq := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hleaf, -, -, -, -, -, -, -, -, es, hes, hws⟩ :=
    spP_np h hpn rq hrq hq0
  have hf2 := spP_f2_fresh ps es rq.ws (spP_f2_pieces ps es hes) hws
  have hlw : rq.ws.length = ps.length := hf2.length_eq.symm
  obtain ⟨-, -, -, -, -, -, -, -, hnm, -, -, -, -, -, hfresh, -⟩ := h.hpp
  have hnm7 : ∀ p ∈ ps, (setN B'' n { rn5 with nv := { rn5.nv with children' := slice.nil } }).nm !! p.1 = none :=
    fun p hp => by show B''.nm !! p.1 = none; rw [hnm]; exact (hfresh p hp).2.2.2.1
  have hP7 : spillPages W'' (setB T'' bl (setN B'' n { rn5 with nv := { rn5.nv with children' := slice.nil } })) =
      spillPages W'' T'' := rfl
  rw [hP7]
  iintro ⟨Hp, -, -⟩
  unfold rtoks
  rw [if_pos hq0, hleaf]
  isplitl []
  · iempintro
  unfold pieceRes
  iapply (bigSepL_forall2 (fun (p : w64 × List w8) (w : WEntry) => w.pgid = p.1 ∧ w.key = p.2) _
    (fun k w => entRes (GF := GF) γ (spillPages W'' T'')
      (setN B'' n { rn5 with nv := { rn5.nv with children' := slice.nil } }) (none, none).2 false
      (if rc.nv.isLeaf' then leafPageFlag else branchPageFlag) (ht n) rq.ws k w) ps rq.ws hf2 ?_) $$ Hp
  intro k p w hpk hwk hr
  iintro ⟨%Q, %pg, %hQ, Hw⟩
  unfold entRes
  simp only [Bool.false_eq_true, ite_false]
  rw [hr.1, if_pos (hnm7 p (List.mem_of_getElem? hpk)), hr.2]
  iexists Q, pg, (pieceHi ps (hiAt (chunksOf rc xs) (bnd n).2 (ps.length - 1)) k)
  iframe Hw
  ipureintro
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hQ
  refine ⟨h1, h2, h3, h4, h5, ?_, h6⟩
  intro hh hhe
  unfold childHi at hhe
  by_cases hk : k + 1 < rq.ws.length
  · rw [if_pos hk] at hhe
    cases hhe
    obtain ⟨p', hp'⟩ : ∃ p', ps[k + 1]? = some p' := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨w', hw', hr'⟩ := forall2_get' _ ps rq.ws hf2 (k + 1) p' hp'
    refine ⟨p'.2, ?_, ?_⟩
    · unfold pieceHi; rw [hp']
    · have e : wKey rq.ws (k + 1) = p'.2 := by unfold wKey; rw [hw']; simp [hr'.2]
      rw [e]; exact goStringLt_irrefl_w _
  · rw [if_neg hk] at hhe; cases hhe

/-- The existing parent (a page): `subPost`. -/
theorem spPost_sub (γd : DBNames) (γ : GName)
    (h : SPX)
    (hpn : rn5.nv.parent' ≠ null) (rq : NRec) (hrq : B''.ns !! rn5.nv.parent' = some rq)
    (hq0 : rq.nv.pgid' ≠ W64 0) :
    spillR I γd γ W'' txl txid T'' ρ'' F'' K'' ∗
      pieceResP (par ≠ null) γ (spillPages W'' T'') (if rc.nv.isLeaf' then leafPageFlag else branchPageFlag)
        (ht n) ps (hiAt (chunksOf rc xs) (bnd n).2 (ps.length - 1)) ∗
      chunkToks γ (spillPages W'' T'') B'' rc.nv.isLeaf' (kd n) (ht n - 1) (chunksOf rc xs) (bnd n).2
        ps.length ∗
      (if ps = [] ∧ rc.nv.pgid' ≠ W64 0 then (uint.nat rc.nv.pgid' ↪[γ] () : IProp GF) else emp) ⊢
    ⌜r.nv.parent' ≠ null⌝ ∗ ∃ rp, ⌜B.ns !! r.nv.parent' = some rp⌝ ∗
      node.spill.subPost I γd γ W txl txid T bl B bnd (n :: (r.cs.map sub).flatten) n r
        r.nv.parent' rp K ht interface.nil := by
  have hpar' : par ≠ null := h.hpar5 ▸ hpn
  iintro ⟨HR, Hpcs, Hct, Hpg⟩
  ihave Hpcs := (pieceResP_pos _ hpar' _ _ _ _ _ _).1 $$ Hpcs
  iapply spPost_sub' γd γ h hpn rq hrq hq0
  iframe

/-- A new parent (pgid 0), the part's `children` set nil: the new parent's tokens. -/
theorem spNewParent_toks (γ : GName)
    (h : SPX)
    (hpn : rn5.nv.parent' ≠ null) (rq : NRec) (hrq : B''.ns !! rn5.nv.parent' = some rq)
    (hq0 : rq.nv.pgid' = W64 0) :
    pieceResP (GF := GF) (par ≠ null) γ (spillPages W'' T'')
        (if rc.nv.isLeaf' then leafPageFlag else branchPageFlag)
        (ht n) ps (hiAt (chunksOf rc xs) (bnd n).2 (ps.length - 1)) ∗
      chunkToks γ (spillPages W'' T'') B'' rc.nv.isLeaf' (kd n) (ht n - 1) (chunksOf rc xs) (bnd n).2
        ps.length ∗
      (if ps = [] ∧ rc.nv.pgid' ≠ W64 0 then (uint.nat rc.nv.pgid' ↪[γ] () : IProp GF) else emp) ⊢
    rtoks γ (spillPages W'' (setB T'' bl (setN B'' n { rn5 with nv := { rn5.nv with children' := slice.nil } })))
      (setN B'' n { rn5 with nv := { rn5.nv with children' := slice.nil } }) (none, none)
      (if rc.nv.isLeaf' then leafPageFlag else branchPageFlag) (ht n) rq := by
  have hpar' : par ≠ null := h.hpar5 ▸ hpn
  iintro ⟨Hpcs, Hct, Hpg⟩
  ihave Hpcs := (pieceResP_pos _ hpar' _ _ _ _ _ _).1 $$ Hpcs
  iapply spNewParent_toks' γ h hpn rq hrq hq0
  iframe

/-- A new parent (pgid 0), the part's `children` set nil: `topSpecB`'s premises for its spill
(`B7`, `T7`), the root's chain `p` up to it. -/
theorem spNewParent_pre
    (h : SPX)
    (hpn : rn5.nv.parent' ≠ null) (rq : NRec) (hrq : B''.ns !! rn5.nv.parent' = some rq)
    (hq0 : rq.nv.pgid' = W64 0) :
    let B7 := setN B'' n { rn5 with nv := { rn5.nv with children' := slice.nil } }
    let T7 := setB T'' bl B7
    r.nv.parent' = null ∧ (top = true → rq.ws.length + 1 < N) ∧
    spillG (hG := hG) W'' txl txid T7 ρ'' F'' ∧ B7.ns !! rn5.nv.parent' = some rq ∧
    rq.nv.parent' = null ∧ rq.nv.isLeaf' = false ∧ K'' rn5.nv.parent' = false ∧
    nodeL W'' bl B7 (fun _ => (none, none)) (fun _ => if rc.nv.isLeaf' then leafPageFlag else branchPageFlag)
      rn5.nv.parent' rq ∧
    (∀ c ∈ rq.cs, spilledN bl B7 c) ∧
    (∃ p, upPath B7.ns B7.bv.rootNode' p rn5.nv.parent' ∧ p.Nodup ∧
      (∀ l, (B7.ns !! l).isSome → l ∈ p ∨ l ∈ rq.cs) ∧
      ∀ l ∈ p, l = rn5.nv.parent' ∨ l ∈ rq.cs ∨ ∃ r', B7.ns !! l = some r' ∧ noViewRec r') ∧
    uint.Z (splitThr (W64 (W''.ps : Int)) B7.bv.FillPercent') ≤ W''.ps ∧ W''.ps < 2 ^ 20 ∧
    (∀ l r, B7.ns !! l = some r → ∀ w ∈ r.ws, w.key.length + w.value.length ≤ 2 ^ 28) ∧
    (∀ l r, B7.ns !! l = some r → r.nv.parent' ≠ null → 0 < r.ws.length) ∧
    (∀ l r, B7.ns !! l = some r → l ≠ rn5.nv.parent' → r.nv.isLeaf' = false → r.nv.pgid' ≠ W64 0) ∧
    (∀ c l, B7.nm !! c = some l → c = W64 0 ∨ (W''.pages !! uint.nat c).isSome) ∧
    (∀ l r w, B7.ns !! l = some r → r.nv.isLeaf' = false → w ∈ r.ws →
      (spillPages W'' T7 !! uint.nat w.pgid).isSome) := by
  intro B7 T7
  obtain ⟨hr0, hlen, hpe, hp0, h3p, h3x, hpx, hsp, hqp, hql, hqb, hqk, hqs, hqcs, hKp, hwl, hil, hsrt,
    es, hes, hws⟩ := spP_np h hpn rq hrq hq0
  subst hpe
  have hf2 := spP_f2_fresh ps es rq.ws (spP_f2_pieces ps es hes) hws
  have hlw : rq.ws.length = ps.length := hf2.length_eq.symm
  have hpos2 : ∀ x ∈ xs, 2 ≤ x.2.2.length := hsp.2.2 hlen
  have hpos : ∀ x ∈ xs, 0 < x.2.2.length := fun x hx => by have := hpos2 x hx; omega
  obtain ⟨hB'', hbv, hib, hnm, hbm⟩ := spP_bkt h
  obtain ⟨hpg, hpss⟩ := spP_pages h
  have hnmn : n ∈ xs.map (fun x => x.1) := spP_n_mem h
  have hqn : rn5.nv.parent' ≠ n := fun e => hpx (e ▸ hnmn)
  have h7 : ∀ l, l ≠ n → B7.ns !! l = B''.ns !! l := fun l hl =>
    GMap.lookup_insert_ne _ _ (Ne.symm hl)
  have h7n : B7.ns !! n = some { rn5 with nv := { rn5.nv with children' := slice.nil } } :=
    GMap.lookup_insert _ _ _
  have h7q : B7.ns !! rn5.nv.parent' = some rq := by rw [h7 _ hqn]; exact hrq
  have h7r : ∀ l r7, B7.ns !! l = some r7 → ∃ rx, B''.ns !! l = some rx ∧ r7.ws = rx.ws ∧
      r7.nv.parent' = rx.nv.parent' ∧ r7.nv.isLeaf' = rx.nv.isLeaf' ∧ r7.nv.pgid' = rx.nv.pgid' := by
    intro l r7 hl
    by_cases e : l = n
    · rw [e, h7n] at hl; cases hl
      exact ⟨rn5, by rw [e]; exact h.hrn5, rfl, rfl, rfl, rfl⟩
    · rw [h7 l e] at hl; exact ⟨r7, hl, rfl, rfl, rfl, rfl⟩
  obtain ⟨-, -, hn', -, -, -, -, -, -, -, -, -, -, -, -, -, hL, hok, -⟩ := h.hlp
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hfresh, hpnd, -⟩ := h.hpp
  obtain ⟨-, hxnd, -⟩ := h.hst.2.1
  -- the parts, spilled
  have hspc : ∀ c ∈ rq.cs, spilledN bl B7 c := by
    intro c hc
    rw [hqcs] at hc
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hc
    rw [List.getElem?_map] at hj
    obtain ⟨x, hxj, hx1⟩ := Option.map_eq_some_iff.1 hj
    have hjl : j < ps.length := by rw [h.hpx]; exact (List.getElem?_eq_some_iff.1 hxj).1
    obtain ⟨hs, -⟩ := spP_written h hp0 j c hjl (by rw [hxj]; simp [hx1])
    obtain ⟨r0, hr0, hs1, hs2, hs3, hs4, hs5, hs6⟩ := hs
    by_cases e : c = n
    · rw [e] at hr0 ⊢; rw [h.hrn5] at hr0; cases hr0
      exact ⟨_, h7n, hs1, hs2, hs3, hs4, hs5, hs6⟩
    · exact ⟨r0, by rw [h7 c e]; exact hr0, hs1, hs2, hs3, hs4, hs5, hs6⟩
  -- the parent's entries
  have hqw : ∀ w ∈ rq.ws, ∃ p ∈ ps, w.pgid = p.1 ∧ w.key = p.2 := fun w hw => spF2_mem_r hf2 w hw
  have hqkey : ∀ w ∈ rq.ws, ∃ w' ∈ rn.ws, w.key = w'.key := by
    intro w hw
    obtain ⟨p, hp, -, hk⟩ := hqw w hw
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hp
    obtain ⟨w', hw', hk'⟩ := spP_pmem h hpos j p hj
    exact ⟨w', hw', hk.trans hk'⟩
  -- the chain from the root node
  obtain ⟨p3, hup3, hnd3, hdom3, hin3, hnv3⟩ := spP_pathB3 h hr0
  have hp3q : rn5.nv.parent' ∉ p3 := fun hm => by have := hin3 _ hm; rw [h3p] at this; cases this
  have hkp : ∀ x ∈ p3, x ≠ n → ∀ r3, B3.ns !! x = some r3 →
      ∃ rx, B''.ns !! x = some rx ∧ dnK r3 rx := by
    intro x hx hxn r3 h3
    refine spP_keep3 h x r3 ?_ ?_ h3
    · intro hm
      obtain ⟨y, hy, hyx⟩ := List.mem_map.1 hm
      rw [← hyx] at h3 hxn
      rw [h3x y hy hxn] at h3; cases h3
    · intro e; rw [e, h3p] at h3; cases h3
  have hup'' : upPath B''.ns B.bv.rootNode' (p3 ++ [rn5.nv.parent']) rn5.nv.parent' :=
    upPath_ext B3.ns B''.ns _ hup3 hnd3
      (fun x hx hxn r3 h3 => by
        obtain ⟨rx, hrx, hd⟩ := hkp x hx hxn r3 h3
        exact ⟨rx, hrx, by rw [(spP_dnK hd).1]⟩)
      ⟨rn5, h.hrn5, rfl⟩ hpn ⟨rq, hrq, hqp⟩
  have hup7 : upPath B7.ns B7.bv.rootNode' (p3 ++ [rn5.nv.parent']) rn5.nv.parent' := by
    show upPath B7.ns B''.bv.rootNode' _ _
    rw [hbv]
    exact upPath_par B''.ns B7.ns hup'' (fun x _ rx hrx => by
      by_cases e : x = n
      · rw [e] at hrx ⊢; rw [h.hrn5] at hrx; cases hrx; exact ⟨_, h7n, rfl⟩
      · exact ⟨rx, by rw [h7 x e]; exact hrx, rfl⟩)
  have hfr0 : ∀ p ∈ ps, B7.nm !! p.1 = none := fun p hp => by
    show B''.nm !! p.1 = none
    rw [h.hpp.2.2.2.2.2.2.2.2.1]; exact (hfresh p hp).2.2.2.1
  refine ⟨hr0, fun htt => ?_, ?_, h7q, hqp, hql, hKp, ?_, hspc,
    ⟨p3 ++ [rn5.nv.parent'], hup7, ?_, ?_, ?_⟩, ?_, by rw [hpss]; exact h.hps, ?_, ?_, ?_, ?_, ?_⟩
  -- the bound on the up-recursion
  · have hw := h.htopw htt
    obtain ⟨-, -, -, -, -, hins, -⟩ := spP_rc h
    have hs := spP_sum2 (fun x : Loc × node × List Inode => x.2.2.length) xs hpos2
    have hfl : (xs.map (fun x : Loc × node × List Inode => x.2.2.length)).sum = rn.ws.length := by
      rw [← hL.2.2.1, ← hins, ← hsp.1, List.length_flatten, List.map_map]; rfl
    rw [hlw, h.hpx]; omega
  · exact spSpillG_setN W'' txl txid T'' ρ'' F'' bl B'' n rn5 _ h.hpp.1 hB'' h.hrn5 rfl rfl id id
  · refine ⟨hqb, hqs, hil, hsrt, fun w hw => ?_, hwl, Or.inl hqk, fun hh => absurd hq0 hh,
      fun hh => (by rw [hql] at hh; cases hh), fun _ => ⟨?_, (by rw [hlw, h.hpx]; exact hlen),
      (by rw [hqcs]; exact hxnd), fun i w c hw hc => ?_, fun c hc => Or.inr (hspc c hc)⟩⟩
    · obtain ⟨w', hw', hk⟩ := hqkey w hw
      refine ⟨by rw [hk]; exact (hL.2.2.2.2.1 w' hw').1, ?_⟩
      unfold keyIn keyGe keyLt
      exact ⟨fun l hl => by simp at hl, fun hh hl => by simp at hl⟩
    · rw [spP_f2_map ps rq.ws hf2]; exact hpnd
    · obtain ⟨p, hp, hr⟩ := forall2_get_r _ ps rq.ws hf2 i w hw
      rw [hr.1, hfr0 p (List.mem_of_getElem? hp)] at hc; cases hc
  · exact List.nodup_append.2 ⟨hnd3, List.nodup_cons.2 ⟨List.not_mem_nil, List.nodup_nil⟩,
      fun a ha b hb e => hp3q (by rw [List.mem_singleton] at hb; rw [← hb, ← e]; exact ha)⟩
  · intro l hl
    by_cases e : l = n
    · right; rw [hqcs, e]; exact hnmn
    rw [h7 l e] at hl
    rcases spP_dom'' h l hl with h1 | h1 | h1
    · right; rw [hqcs]; exact h1
    · left; rw [h1]; exact List.mem_append_right _ (List.mem_singleton_self _)
    · left; exact List.mem_append_left _ (hdom3 l h1)
  · intro l hl
    rcases List.mem_append.1 hl with hl | hl
    · by_cases e : l = n
      · right; left; rw [hqcs, e]; exact hnmn
      rcases hnv3 l hl with e' | ⟨r3, h3, hv⟩
      · exact absurd e' e
      · obtain ⟨rx, hrx, hd⟩ := hkp l hl e r3 h3
        right; right
        refine ⟨rx, by rw [h7 l e]; exact hrx, ?_⟩
        rcases hd with rfl | hd
        · exact hv
        · exact derefNode_noView _ _ hd.1.1
    · left; exact List.mem_singleton.1 hl
  · show uint.Z (splitThr (W64 (W''.ps : Int)) B''.bv.FillPercent') ≤ W''.ps
    rw [hpss, hbv]; exact h.hthr
  · intro l r7 hl w hw
    obtain ⟨rx, hrx, hws7, -⟩ := h7r l r7 hl
    rw [hws7] at hw
    by_cases e : l = rn5.nv.parent'
    · rw [e, hrq] at hrx; cases hrx
      obtain ⟨w1, hw1, hk1, hv1, -⟩ := spP_mem_fresh hws hw
      obtain ⟨p, hp, -, -, hk2, hv2, -⟩ := spF2_mem_r hes w1 hw1
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hp
      obtain ⟨w', hw', hk'⟩ := spP_pmem h hpos j p hj
      have := hok.1 n rn hn' w' hw'
      rw [hk1, hv1, hk2, hv2, hk']; simp only [List.length_nil]; omega
    · exact (spP_nodes'' h hp0 hpos l rx hrx e).1 w hw
  · intro l r7 hl hpa
    obtain ⟨rx, hrx, hws7, hpa7, -⟩ := h7r l r7 hl
    rw [hws7]
    by_cases e : l = rn5.nv.parent'
    · rw [e, hrq] at hrx; cases hrx; rw [hpa7, hqp] at hpa; exact absurd rfl hpa
    · exact (spP_nodes'' h hp0 hpos l rx hrx e).2.1 (by rw [← hpa7]; exact hpa)
  · intro l r7 hl hlq hb
    obtain ⟨rx, hrx, -, -, hlf7, hpg7⟩ := h7r l r7 hl
    rw [hpg7]; exact (spP_nodes'' h hp0 hpos l rx hrx hlq).2.2.1 (by rw [← hlf7]; exact hb)
  · intro c l hc
    obtain ⟨-, -, hok3, -⟩ := hok
    obtain ⟨-, -, -, -, -, -, -, -, hbv', hib', hnm', -⟩ := h.hlp
    have e1 : B7.nm = B'.nm := by show B''.nm = B'.nm; rw [hnm, hnm']
    rw [e1] at hc
    rw [show W''.pages = W'.pages from hpg.trans h.hlp.2.2.2.2.2.1.symm]
    exact hok3 c l hc
  · intro l r7 w hl hb hw
    obtain ⟨rx, hrx, hws7, -, hlf7, -⟩ := h7r l r7 hl
    rw [hws7] at hw
    show (spillPages W'' T'' !! uint.nat w.pgid).isSome
    by_cases e : l = rn5.nv.parent'
    · rw [e, hrq] at hrx; cases hrx
      obtain ⟨p, hp, hpw, -⟩ := hqw w hw
      rw [hpw]; exact spillPages_buf W'' T'' p.1 (hfresh p hp).2.2.1
    · exact (spP_nodes'' h hp0 hpos l rx hrx e).2.2.2 (by rw [← hlf7]; exact hb) w hw


end own

end bbolt
end EtcdGrove
end Perennial
