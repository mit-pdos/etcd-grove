/-
`node.spill`'s recursion (`Proof/go_etcd_io/bbolt/node__spill.lean`): the states of a node it is
called on, and what each call gives.

**Modes.** `n.spill()` is called (1) by a parent's children loop on an unspilled child
(`subPre`/`subPost`: its parts' entries put into the parent, `putPieces`, their written trees
returned, `pieceRes`), (2) on a part already spilled (`donePre`: it returns at once), (3) by
`Bucket.spill` on the bucket's root (`node.spill.spec`), (4) by a split root (or a split new
parent) on its new parent (`topPre`: pgid 0, its children all spilled parts, their written
trees attached to its entries). (3) and (4) end with the bucket's final top node written
(`finPost`).

**A node in its children loop** (`nodeL`): `nodeU` but for its children: each child of its
children list is still materialized and unspilled (an entry's `nm` child, `nodeU`'s facts), or
a part already spilled (its entry's child page written, the tree in `rtoks`).
-/
module

public import Proof.go_etcd_io.bbolt.SpillNode
public import Spec.go_etcd_io.bbolt.node__spill

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pure
variable [ext : FfiSyntax]

/-- The capacities kept: of the bucket's old nodes outside `S`, of the other buckets' nodes. -/
def kKeep (T' : WTx) (bl : Loc) (B : BRec) (S : List Loc) (K K' : Loc → Bool) : Prop :=
  (∀ x, x ∉ S → (B.ns !! x).isSome → K' x = K x) ∧
  (∀ c C l, c ≠ bl → T'.bs !! c = some C → (C.ns !! l).isSome → K' l = K l)

/-- A spilled part of the bucket `bl`: written, no children, readable by `dereference`. -/
def spilledN (bl : Loc) (B : BRec) (c : Loc) : Prop :=
  ∃ rc, B.ns !! c = some rc ∧ rc.nv.spilled' = true ∧ rc.cs = [] ∧ rc.nv.bucket' = bl ∧
    0 < rc.ins.length ∧ rc.ins.length = rc.ws.length ∧ derefOK bl rc ∧ B.nm !! rc.nv.pgid' = none

/-- A node in its children loop (see the module doc). -/
def nodeL (W : WView) (bl : Loc) (B : BRec) (bnd : Loc → Option (List w8) × Option (List w8))
    (kd : Loc → Nat) (l : Loc) (r : NRec) : Prop :=
  r.nv.bucket' = bl ∧ r.nv.spilled' = false ∧ r.ins.length = r.ws.length ∧ wsSorted r.ws ∧
  (∀ w ∈ r.ws, 0 < w.key.length ∧ keyIn (bnd l).1 (bnd l).2 w.key) ∧ wsLive r.ws ∧
  (r.nv.key' = slice.nil ∨ (0 < r.key.length ∧ r.ksrc ≠ Src.stale)) ∧
  (r.nv.pgid' ≠ W64 0 → ∃ pg, W.pages !! uint.nat r.nv.pgid' = some pg ∧
    ∃ h, treeWF W.pages h (uint.nat r.nv.pgid')) ∧
  (r.nv.isLeaf' = true → r.cs = []) ∧
  (r.nv.isLeaf' = false → (r.ws.map WEntry.pgid).Nodup ∧ 2 ≤ r.ws.length ∧ r.cs.Nodup ∧
    (∀ (i : Nat) (w : WEntry) (c : Loc), r.ws[i]? = some w → B.nm !! w.pgid = some c →
      ∃ rc, B.ns !! c = some rc ∧
      rc.nv.parent' = l ∧ rc.nv.pgid' = w.pgid ∧ rc.key = w.key ∧ rc.nv.key' ≠ slice.nil ∧
      c ∈ r.cs ∧ kd l = (if rc.nv.isLeaf' then leafPageFlag else branchPageFlag) ∧
      bndIn (bnd c) (entryBnd (bnd l) r.ws i)) ∧
    (∀ c ∈ r.cs, (∃ (i : Nat) (w : WEntry), r.ws[i]? = some w ∧ B.nm !! w.pgid = some c) ∨
      spilledN bl B c))

theorem nodeL_of_nodeU (W : WView) (bl : Loc) (B : BRec)
    (bnd : Loc → Option (List w8) × Option (List w8)) (kd : Loc → Nat) (l : Loc) (r : NRec)
    (h : nodeU W bl B bnd kd l r) : nodeL W bl B bnd kd l r := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, fun hb => ?_⟩
  obtain ⟨a, b, c, d, e⟩ := h10 hb
  exact ⟨a, b, c, d, fun x hx => Or.inl (e x hx)⟩

end pure

section own
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]
variable [float_sem : go.FloatConvSemantics]

/-- The end of a root's (or a new parent's) spill, the bucket's root node `rn`: `node.spill.spec`'s
postcondition. -/
def finPost (I : FLImpl (GF := GF)) (γd : DBNames) (γ : GName) (W : WView) (txl : Loc)
    (txid : w64) (T : WTx) (bl : Loc) (B : BRec) (K : Loc → Bool) (err : GoInterface) : IProp GF :=
  iprop((⌜err = interface.nil⌝ ∗ ∃ (W' : WView) (T' : WTx) (ρ' : DBState)
        (F' : GMap Nat (List w8)) (K' : Loc → Bool) (B' : BRec) (p : List Loc) (top : Loc)
        (pid : w64) (Q : GMap Nat (List w8)),
      spillR I γd γ W' txl txid T' ρ' F' K' ∗ wtreeQ γ Q (uint.nat pid) none none ∗
      ⌜spillG (hG := hG) W' txl txid T' ρ' F' ∧ spillFrame T T' (· = bl) ∧ W'.pages = W.pages ∧
        T'.bs !! bl = some B' ∧ B'.bv = B.bv ∧ B'.ib = B.ib ∧ B'.nm = B.nm ∧ B'.bm = B.bm ∧
        upPath B'.ns B.bv.rootNode' p top ∧ p.Nodup ∧ (∀ l, (B'.ns !! l).isSome ↔ l ∈ p) ∧
        (Q !! uint.nat pid).isSome ∧ Q ⊆ spillPages W' T' ∧ (T'.bufs !! pid).isSome ∧
          (∀ c C' l, c ≠ bl → T'.bs !! c = some C' → (C'.ns !! l).isSome → K' l = K l) ∧
        ∃ rt, B'.ns !! top = some rt ∧ rt.nv.pgid' = pid ∧ rt.nv.spilled' = true ∧
          rt.nv.parent' = null ∧ rt.cs = []⌝) ∨
    (⌜err ≠ interface.nil⌝ ∗ spillErr I γd txl txid))

/-- `n.spill()` on a spilled part: it returns nil, nothing changed. -/
def node.spill.doneSpec : Prop :=
  ∀ (I : FLImpl (GF := GF)) (γd : DBNames) (γ : GName) (W : WView) (txl : Loc) (txid : w64)
    (T : WTx) (ρ : DBState) (F : GMap Nat (List w8)) (K : Loc → Bool) (bl : Loc) (B : BRec)
    (n : Loc),
  spillG (hG := hG) W txl txid T ρ F → T.bs !! bl = some B → spilledN bl B n →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ spillR I γd γ W txl txid T ρ F K }}
    (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"spill")) (Val #()))
  {{ RET #interface.nil; spillR I γd γ W txl txid T ρ F K }}

/-- The facts of `subPost`. -/
def node.spill.subPostP (W : WView) (txl : Loc) (txid : w64) (T : WTx) (bl : Loc) (B : BRec)
    (bnd : Loc → Option (List w8) × Option (List w8)) (S : List Loc) (n : Loc) (r : NRec)
    (pl : Loc) (rp : NRec) (K : Loc → Bool) (W' : WView) (T' : WTx) (ρ' : DBState)
    (F' : GMap Nat (List w8)) (K' : Loc → Bool) (B' : BRec) (ps : List (w64 × List w8))
    (xs : List Loc) (rp' : NRec) : Prop :=
  spillG (hG := hG) W' txl txid T' ρ' F' ∧ spillFrame T T' (· = bl) ∧ W'.pages = W.pages ∧ W'.ps = W.ps ∧
          T'.bs !! bl = some B' ∧ B'.bv = B.bv ∧ B'.ib = B.ib ∧ B'.nm = B.nm ∧ B'.bm = B.bm ∧
          B'.ns !! pl = some rp' ∧ K' pl = false ∧
          rp'.nv = ({ rp.nv with inodes' := rp'.nv.inodes', children' := rp'.nv.children', key' := rp'.nv.key' } : node) ∧ rp'.key = rp.key ∧
          (rp.nv.key' = slice.nil → rp'.nv.key' = slice.nil) ∧
          (rp'.ksrc = rp.ksrc ∨ rp'.ksrc = Src.own (DFrac.own 1)) ∧
          putPieces (rp.ws.map ownFresh) r.key ps (rp'.ws.map ownFresh) ∧ wsLive rp'.ws ∧
          rp'.ins.length = rp'.ws.length ∧ rp'.cs = rp.cs ++ xs ∧ ps ≠ [] ∧
          ps.length = xs.length + 1 ∧ (ps.map (fun p => p.1)).Nodup ∧ spillPages W T ⊆ spillPages W' T' ∧
          (∀ p ∈ ps, T.bufs !! p.1 = none ∧ W.pages !! uint.nat p.1 = none ∧
            (T'.bufs !! p.1).isSome ∧ B.nm !! p.1 = none ∧ 2 ≤ uint.nat p.1) ∧
          (∀ (j : Nat) (p : w64 × List w8) (x : Loc), ps[j + 1]? = some p → xs[j]? = some x →
            ∃ rx, B'.ns !! x = some rx ∧ rx.nv.pgid' = p.1) ∧
          (∀ p, ps[0]? = some p → ∃ rn, B'.ns !! n = some rn ∧ rn.nv.pgid' = p.1) ∧
          (∀ p ∈ ps, keyIn (bnd n).1 (bnd n).2 p.2 ∧ 0 < p.2.length) ∧
          (∀ (j k : Nat) (a b : w64 × List w8), j < k → ps[j]? = some a → ps[k]? = some b →
            go.GoStringLt a.2 b.2) ∧
          (∀ x ∈ xs, spilledN bl B' x) ∧ spilledN bl B' n ∧ xs.Nodup ∧ n ∉ xs ∧
          (∀ x ∈ xs, ∀ l, l ∉ S → (B.ns !! l).isSome → l ≠ x) ∧
          (∀ x rx, x ∉ S → x ≠ pl → B.ns !! x = some rx →
            ∃ rx', B'.ns !! x = some rx' ∧ (rx' = rx ∨ derefNodeK rx rx')) ∧
          (∀ x, (B'.ns !! x).isSome → (B.ns !! x).isSome ∨ x ∈ xs) ∧
          (∀ x, x ∈ S → x ≠ n → x ∉ xs → B'.ns !! x = none) ∧
          (∀ p ∈ ps, p.2.length ≤ 2 ^ 28) ∧
          (∀ x rx, (x = n ∨ x ∈ xs) → B'.ns !! x = some rx →
            (∀ w ∈ rx.ws, w.key.length + w.value.length ≤ 2 ^ 28) ∧
            (rx.nv.isLeaf' = false → ∀ w ∈ rx.ws, (spillPages W' T' !! uint.nat w.pgid).isSome)) ∧
          kKeep T' bl B S K K' ∧ treeOK bl B' ∧
          (rp.nv.key' ≠ slice.nil → 0 < rp.key.length → rp'.nv.key' ≠ slice.nil)

/-- What `n.spill()` gives on an unspilled child (`subSpecB`). -/
def node.spill.subPost (I : FLImpl (GF := GF)) (γd : DBNames) (γ : GName) (W : WView) (txl : Loc)
    (txid : w64) (T : WTx) (bl : Loc) (B : BRec)
    (bnd : Loc → Option (List w8) × Option (List w8)) (S : List Loc) (n : Loc) (r : NRec)
    (pl : Loc) (rp : NRec) (K : Loc → Bool) (ht : Loc → Nat) (err : GoInterface) : IProp GF :=
  iprop((⌜err = interface.nil⌝ ∗ ∃ (W' : WView) (T' : WTx) (ρ' : DBState) (F' : GMap Nat (List w8))
          (K' : Loc → Bool) (B' : BRec) (ps : List (w64 × List w8)) (xs : List Loc) (rp' : NRec),
        spillR I γd γ W' txl txid T' ρ' F' K' ∗
        pieceRes γ (spillPages W' T') (if r.nv.isLeaf' then leafPageFlag else branchPageFlag) (ht n) ps
          (bnd n).2 ∗
        ⌜node.spill.subPostP (hG := hG) W txl txid T bl B bnd S n r pl rp K W' T' ρ' F' K' B' ps xs rp'⌝) ∨
      (⌜err ≠ interface.nil⌝ ∗ spillErr I γd txl txid))

/-- `n.spill()` on an unspilled child `n` (record `r`, its tree `S`) of the unspilled node `pl`
(record `rp`, in its children loop), the bucket's other nodes outside `S`: the parts of `n`
(page ids and first keys `ps`) replace its entry in `pl` (`putPieces`; `pl`'s children list
extended by the new parts, spilled), their written trees returned (`pieceRes`, the last below
`n`'s bound), `S` gone from the bucket's nodes but for the parts; the other nodes as they were
(possibly dereferenced). -/
def node.spill.subSpecB (N : Nat) : Prop :=
  ∀ (I : FLImpl (GF := GF)) (γd : DBNames) (γ : GName) (W : WView) (txl : Loc) (txid : w64)
    (T : WTx) (ρ : DBState) (F : GMap Nat (List w8)) (K : Loc → Bool) (bl : Loc) (B : BRec)
    (bnd : Loc → Option (List w8) × Option (List w8)) (kd : Loc → Nat) (S : List Loc)
    (n : Loc) (r : NRec) (pl : Loc) (rp : NRec) (ht : Loc → Nat),
  I.FreeSpec → spillG (hG := hG) W txl txid T ρ F → T.bs !! bl = some B →
  nodeHts B ht → S.length < N → subU W bl B bnd kd K n S → B.ns !! n = some r → r.nv.parent' = pl → pl ≠ null →
  B.ns !! pl = some rp → n ∈ rp.cs → pl ∉ S → K pl = false → nodeL W bl B bnd kd pl rp →
  rp.nv.pgid' ≠ W64 0 → rp.nv.isLeaf' = false →
  uint.Z (splitThr (W64 (W.ps : Int)) B.bv.FillPercent') ≤ W.ps → W.ps < 2 ^ 20 →
  (∀ l r, B.ns !! l = some r → ∀ w ∈ r.ws, w.key.length + w.value.length ≤ 2 ^ 28) →
  (∀ l r, B.ns !! l = some r → r.nv.parent' ≠ null → 0 < r.ws.length) →
  (∀ l r, B.ns !! l = some r → r.nv.isLeaf' = false → r.nv.pgid' ≠ W64 0) →
  (∀ c l, B.nm !! c = some l → c = W64 0 ∨ (W.pages !! uint.nat c).isSome) →
  (∀ l r w, B.ns !! l = some r → r.nv.isLeaf' = false → w ∈ r.ws →
    (spillPages W T !! uint.nat w.pgid).isSome) →
  treeOK bl B →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ spillR I γd γ W txl txid T ρ F K ∗
      [∗list] l ∈ S, ∃ r, ⌜B.ns !! l = some r⌝ ∗ rtoks γ (spillPages W T) B (bnd l) (kd l) (ht l - 1) r }}
    (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"spill")) (Val #()))
  {{ (err : GoInterface), RET #err; node.spill.subPost I γd γ W txl txid T bl B bnd S n r pl rp K ht err }}

/-- `n.spill()` on a new parent `n` (record `r`: pgid 0, parent nil, unspilled, its children
`r.cs` all spilled parts, its entries theirs with their written trees, `rtoks`), the top of the
bucket's node tree, the root node's parent chain `p` up to it: the final top written. -/
def node.spill.topSpecB (M : Nat) : Prop :=
  ∀ (I : FLImpl (GF := GF)) (γd : DBNames) (γ : GName) (W : WView) (txl : Loc) (txid : w64)
    (T : WTx) (ρ : DBState) (F : GMap Nat (List w8)) (K : Loc → Bool) (bl : Loc) (B : BRec)
    (kd ht0 : Nat) (n : Loc) (r : NRec) (p : List Loc),
  I.FreeSpec → spillG (hG := hG) W txl txid T ρ F → T.bs !! bl = some B →
  r.ws.length < M → B.ns !! n = some r → r.nv.pgid' = W64 0 → r.nv.parent' = null →
  r.nv.isLeaf' = false → K n = false →
  nodeL W bl B (fun _ => (none, none)) (fun _ => kd) n r → (∀ c ∈ r.cs, spilledN bl B c) →
  upPath B.ns B.bv.rootNode' p n → p.Nodup →
  (∀ l ∈ p, l = n ∨ l ∈ r.cs ∨ ∃ r', B.ns !! l = some r' ∧ noViewRec r') →
  (∀ l, (B.ns !! l).isSome → l ∈ p ∨ l ∈ r.cs) →
  uint.Z (splitThr (W64 (W.ps : Int)) B.bv.FillPercent') ≤ W.ps → W.ps < 2 ^ 20 →
  (∀ l r, B.ns !! l = some r → ∀ w ∈ r.ws, w.key.length + w.value.length ≤ 2 ^ 28) →
  (∀ l r, B.ns !! l = some r → r.nv.parent' ≠ null → 0 < r.ws.length) →
  (∀ l r, B.ns !! l = some r → l ≠ n → r.nv.isLeaf' = false → r.nv.pgid' ≠ W64 0) →
  (∀ c l, B.nm !! c = some l → c = W64 0 ∨ (W.pages !! uint.nat c).isSome) →
  (∀ l r w, B.ns !! l = some r → r.nv.isLeaf' = false → w ∈ r.ws →
    (spillPages W T !! uint.nat w.pgid).isSome) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ spillR I γd γ W txl txid T ρ F K ∗
      rtoks γ (spillPages W T) B (none, none) kd ht0 r }}
    (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"spill")) (Val #()))
  {{ (err : GoInterface), RET #err; finPost I γd γ W txl txid T bl B K err }}

/-- `subSpecB` for every bound. -/
def node.spill.subSpec : Prop := ∀ N, node.spill.subSpecB (GF := GF) (hG := hG) N

/-- `topSpecB` for every bound. -/
def node.spill.topSpec : Prop := ∀ M, node.spill.topSpecB (GF := GF) (hG := hG) M

end own

end bbolt
end EtcdGrove
end Perennial
