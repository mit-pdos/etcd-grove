/-
`node.spill` (`Commit`'s spill of a bucket's nodes): the state of a bucket's nodes during it.

**An unspilled node** `l` of the bucket `bl` (`nodeU`): not spilled, its entries sorted, with
non-empty keys inside its bounds (`bnd l`: the exact ones, `SpillExact.lean`), its page (if any)
of the view; a branch has at least two entries, distinct children, all of one kind (`kd l`, a
page flag); a materialized child `c` (`B.nm`) is in its children list, its parent is `l`, its
key the entry's (`put` replaces exactly that entry), its bounds inside the entry's
(`entryBnd`, over the current entries: re-keying a spilled sibling only widens them).

**What a node holds** (`rtoks`): its page's token (to the stash when it is freed), and, for each
entry: of a leaf, a nested bucket's written value (`wbktQ`); of a branch whose child is not
materialized (a page position, or a child already written), the child's written tree
(`wtreeQ`, from the entry's key, below the next key; its root page of the node's kind
`kd l`).

**A written part** (`pieceRes`): the parts `n.split` made of a node, each its page's written
tree, from its first key below the next part's (the last below the node's bound); the parent's
entries for them (`pieceEntries`) replace the node's (`putPieces`).
-/
module

public import Proof.go_etcd_io.bbolt.SpillState
public import Proof.go_etcd_io.bbolt.SpillExact

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pure
variable [ext : FfiSyntax]

/-- An unspilled node (see the module doc). -/
def nodeU (W : WView) (bl : Loc) (B : BRec) (bnd : Loc → Option (List w8) × Option (List w8))
    (kd : Loc → Nat) (l : Loc) (r : NRec) : Prop :=
  r.nv.bucket' = bl ∧ r.nv.spilled' = false ∧ r.ins.length = r.ws.length ∧ wsSorted r.ws ∧
  (∀ w ∈ r.ws, 0 < w.key.length ∧ keyIn (bnd l).1 (bnd l).2 w.key) ∧ wsLive r.ws ∧
  (r.nv.key' = slice.nil ∨ (0 < r.key.length ∧ r.ksrc ≠ Src.stale)) ∧
  (r.nv.pgid' ≠ W64 0 → ∃ pg, W.pages !! uint.nat r.nv.pgid' = some pg ∧
    ∃ h, treeWF W.pages h (uint.nat r.nv.pgid')) ∧
  (r.nv.isLeaf' = true → r.cs = []) ∧
  (r.nv.isLeaf' = false → (r.ws.map WEntry.pgid).Nodup ∧ 2 ≤ r.ws.length ∧ r.cs.Nodup ∧
    (∀ (i : Nat) (w : WEntry) (c : Loc), r.ws[i]? = some w → B.nm !! w.pgid = some c → ∃ rc, B.ns !! c = some rc ∧
      rc.nv.parent' = l ∧ rc.nv.pgid' = w.pgid ∧ rc.key = w.key ∧ rc.nv.key' ≠ slice.nil ∧
      c ∈ r.cs ∧ kd l = (if rc.nv.isLeaf' then leafPageFlag else branchPageFlag) ∧
      bndIn (bnd c) (entryBnd (bnd l) r.ws i)) ∧
    (∀ c ∈ r.cs, ∃ (i : Nat) (w : WEntry), r.ws[i]? = some w ∧ B.nm !! w.pgid = some c))

/-- The tree of nodes from `l` (`kidsTree`, the nodes `S`), all unspilled, with a capacity. -/
def subU (W : WView) (bl : Loc) (B : BRec) (bnd : Loc → Option (List w8) × Option (List w8))
    (kd : Loc → Nat) (K : Loc → Bool) (l : Loc) (S : List Loc) : Prop :=
  kidsTree B.ns l S ∧ ∀ x ∈ S, K x = false ∧ ∃ r, B.ns !! x = some r ∧ nodeU W bl B bnd kd x r

/-- The unspilled nodes' heights `ht` (a leaf 0, a branch one more than its materialized children; its
other children's trees are of its height minus one: `rtoks`), so that every written tree has
its leaves at one depth (`qHt`; `rebalance`'s `rblHt`). -/
def nodeHts (B : BRec) (ht : Loc → Nat) : Prop :=
  ∀ l r, B.ns !! l = some r → r.nv.spilled' = false → (r.nv.isLeaf' = true → ht l = 0) ∧
    (r.nv.isLeaf' = false → 1 ≤ ht l ∧ ∀ w ∈ r.ws, ∀ c, B.nm !! w.pgid = some c → ht c + 1 = ht l)

/-- The parent's entries for the written parts (page id, first key). -/
def pieceEntries (ps : List (w64 × List w8)) (es : List WEntry) : Prop :=
  List.Forall₂ (fun p w => w.flags = W32 0 ∧ w.pgid = p.1 ∧ w.key = p.2 ∧ w.value = [] ∧
    w.ks ≠ Src.stale ∧ w.vs ≠ Src.stale) ps es

/-- The entries `ws'`: those of `ws`, the one with key `key` replaced by the parts'. -/
def putPieces (ws : List WEntry) (key : List w8) (ps : List (w64 × List w8)) (ws' : List WEntry) :
    Prop :=
  ∃ i w es, ws[i]? = some w ∧ w.key = key ∧ pieceEntries ps es ∧
    ws' = ws.take i ++ es ++ ws.drop (i + 1)

/-- The upper bound of part `j` of the parts `ps` (first keys), the last's `hi`. -/
def pieceHi (ps : List (w64 × List w8)) (hi : Option (List w8)) (j : Nat) : Option (List w8) :=
  match ps[j + 1]? with
  | some p => some p.2
  | none => hi

/-- `T'` is `T` after the spill of some nodes of the buckets `X`: the same buckets, the other
buckets possibly dereferenced, each node keeping its struct but its key; the dirty pages kept. -/
def spillFrame (T T' : WTx) (X : Loc → Prop) : Prop :=
  (∀ c, (T.bs !! c).isSome ↔ (T'.bs !! c).isSome) ∧ T'.mv.txid' = T.mv.txid' ∧
  uint.nat T.mv.pgid' ≤ uint.nat T'.mv.pgid' ∧ T.bufs ⊆ T'.bufs ∧
  T'.t = { T.t with stats' := T'.t.stats' } ∧
  ∀ c C C', ¬ X c → T.bs !! c = some C → T'.bs !! c = some C' →
    derefStarX C C' ∧ ∀ l r r', C.ns !! l = some r → C'.ns !! l = some r' →
      r'.nv = { r.nv with key' := r'.nv.key' }

end pure

section own
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- A written nested bucket's value (`wbktQ`), its tree's pages among `P`. -/
def wbktQP (γ : GName) (P : GMap Nat (List w8)) (v : List w8) : IProp GF :=
  iprop(⌜16 ≤ v.length⌝ ∗
    if inBucketRoot v = 0 then ⌜inlineGood (inlinePage v)⌝
    else ∃ Q, ⌜Q ⊆ P⌝ ∗ wtreeQ γ Q (inBucketRoot v) none none)

/-- What a node holds for its entry `i` (`w`) (see the module doc), the written trees' pages
among `P` (the view's and the dirty ones, `spillPages`). -/
def entRes (γ : GName) (P : GMap Nat (List w8)) (B : BRec) (hi : Option (List w8)) (leaf : Bool)
    (kind ch : Nat) (ws : List WEntry) (i : Nat) (w : WEntry) : IProp GF :=
  if leaf then (if w.flags &&& W32 1 = W32 0 then emp else wbktQP γ P w.value)
  else if B.nm !! w.pgid = none then
    iprop(∃ (Q : GMap Nat (List w8)) (cpg : List w8) (H : Option (List w8)),
      ⌜Q ⊆ P ∧ Q !! uint.nat w.pgid = some cpg ∧ 0 < pageCount cpg ∧ pageFlags cpg = kind ∧
        pageKey cpg 0 = w.key ∧ hiLe H (childHi hi (wKey ws) ws.length i) ∧
        qHt Q (uint.nat w.pgid) ch⌝ ∗
      wtreeQ γ Q (uint.nat w.pgid) (some w.key) H)
  else emp

/-- What a node holds (see the module doc), its bounds `b`, its children's kind `kind` and
height `ch`. -/
def rtoks (γ : GName) (P : GMap Nat (List w8)) (B : BRec) (b : Option (List w8) × Option (List w8))
    (kind ch : Nat) (r : NRec) : IProp GF :=
  iprop((if r.nv.pgid' = W64 0 then emp else (uint.nat r.nv.pgid' ↪[γ] () : IProp GF)) ∗
    [∗list] i ↦ w ∈ r.ws, entRes γ P B b.2 r.nv.isLeaf' kind ch r.ws i w)

/-- The written parts (see the module doc): page ids and first keys `ps`, of the kind `kind`,
the last below `hi`, their pages among `P`, all of height `h`. -/
def pieceRes (γ : GName) (P : GMap Nat (List w8)) (kind h : Nat) (ps : List (w64 × List w8))
    (hi : Option (List w8)) : IProp GF :=
  [∗list] j ↦ p ∈ ps, iprop(∃ (Q : GMap Nat (List w8)) (pg : List w8),
    ⌜Q ⊆ P ∧ Q !! uint.nat p.1 = some pg ∧ 0 < pageCount pg ∧ pageFlags pg = kind ∧
      pageKey pg 0 = p.2 ∧ qHt Q (uint.nat p.1) h⌝ ∗
    wtreeQ γ Q (uint.nat p.1) (some p.2) (pieceHi ps hi j))

/-- `pieceRes`, a part's page non-empty (and its first key the part's) only if `pos`: the parts
of a node with a parent (`pos`) or of the bucket's root (which may be an empty leaf). -/
def pieceResP (pos : Prop) (γ : GName) (P : GMap Nat (List w8)) (kind h : Nat)
    (ps : List (w64 × List w8)) (hi : Option (List w8)) : IProp GF :=
  [∗list] j ↦ p ∈ ps, iprop(∃ (Q : GMap Nat (List w8)) (pg : List w8),
    ⌜Q ⊆ P ∧ Q !! uint.nat p.1 = some pg ∧ (pos → 0 < pageCount pg) ∧ pageFlags pg = kind ∧
      (pos → pageKey pg 0 = p.2) ∧ qHt Q (uint.nat p.1) h⌝ ∗
    wtreeQ γ Q (uint.nat p.1) (some p.2) (pieceHi ps hi j))

theorem pieceResP_pos (pos : Prop) (hp : pos) (γ : GName) (P : GMap Nat (List w8)) (kind h : Nat)
    (ps : List (w64 × List w8)) (hi : Option (List w8)) :
    pieceResP (GF := GF) pos γ P kind h ps hi ⊣⊢ pieceRes γ P kind h ps hi := by
  unfold pieceResP pieceRes
  constructor
  · refine BigSepL.bigSepL_mono (fun {j q} _ => ?_)
    iintro ⟨%Q, %pg, %hq, H⟩
    iexists Q, pg
    iframe
    ipureintro
    exact ⟨hq.1, hq.2.1, hq.2.2.1 hp, hq.2.2.2.1, hq.2.2.2.2.1 hp, hq.2.2.2.2.2⟩
  · refine BigSepL.bigSepL_mono (fun {j q} _ => ?_)
    iintro ⟨%Q, %pg, %hq, H⟩
    iexists Q, pg
    iframe
    ipureintro
    exact ⟨hq.1, hq.2.1, fun _ => hq.2.2.1, hq.2.2.2.1, fun _ => hq.2.2.2.2.1, hq.2.2.2.2.2⟩

end own

end bbolt
end EtcdGrove
end Perennial
