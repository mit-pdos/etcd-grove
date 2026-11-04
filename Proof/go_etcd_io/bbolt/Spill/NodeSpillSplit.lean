/-
`node.spill` after its children's loop (U9r, `notes/bbolt-proof-plan.md`): **the split's heap
step** (`splitStep_wp`): `n.split(uintptr(tx.db.pageSize))` on `wtxW`, from the state `X1` after
`n.children = nil` (`Spill/NodeSpillPiecesKill.wtxW_nilCh`) to a state `X2` related by
`Spill/NodeSpillSplitDefs.splitRel` (`n`'s record and its parent's reshaped, the fresh pieces and
the top case's new parent added), the returned slice the pieces' locations.
-/
module

public import Proof.go_etcd_io.bbolt.Spill.NodeSpillSplitDefs
public import Proof.go_etcd_io.bbolt.Spill.NodeSpillPiecesCode
public import Proof.go_etcd_io.bbolt.Spill.DerefHeap

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section code
variable [GooseExts] [GoGlobalContext]

/-- **`n.split(uintptr(tx.db.pageSize))`** as `spillTail` has it (the cells `np`, `txp`). -/
abbrev splitCall (np txp : Loc) : Expr :=
  (Let "$a0" (App (Val (GoInstruction (Convert go.int go.uintptr))) (App (Val (GoInstruction (GoLoad go.int))) (App (Val (GoInstruction (StructFieldRef DB.ty go!"pageSize"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType DB.ty)))) (App (Val (GoInstruction (StructFieldRef Tx.ty go!"db"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType Tx.ty)))) (Val #txp)))))))
      (App (App (Val (GoInstruction (MethodResolve (go.GoType.PointerType node.ty) go!"split"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType node.ty)))) (Val #np))) (Var "$a0")))

end code

section cut
variable [GooseExts]

/-- **The entries cut at the pieces' inode counts** (`ps` the pieces' inodes). -/
def cutWs {α : Type} : List (List α) → List WEntry → List (List WEntry)
  | [], _ => []
  | a :: ps, ws => ws.take a.length :: cutWs ps (ws.drop a.length)

omit [GooseExts] in
theorem cutWs_length {α : Type} (ps : List (List α)) (ws : List WEntry) :
    (cutWs ps ws).length = ps.length := by
  induction ps generalizing ws with
  | nil => rfl
  | cons a ps ih => simp [cutWs, ih]

omit [GooseExts] in
theorem cutWs_flatten {α : Type} (ps : List (List α)) (ws : List WEntry)
    (h : ps.flatten.length = ws.length) : (cutWs ps ws).flatten = ws := by
  induction ps generalizing ws with
  | nil => simp at h; simp [cutWs, List.length_eq_zero_iff.1 h.symm]
  | cons a ps ih =>
    simp only [cutWs, List.flatten_cons]
    simp only [List.flatten_cons, List.length_append] at h
    rw [ih (ws.drop a.length) (by simp only [List.length_drop]; omega), List.take_append_drop]

omit [GooseExts] in
theorem cutWs_get {α : Type} (ps : List (List α)) (ws : List WEntry)
    (h : ps.flatten.length = ws.length) (i : Nat) (a : List α) (w : List WEntry)
    (ha : ps[i]? = some a) (hw : (cutWs ps ws)[i]? = some w) : w.length = a.length := by
  induction ps generalizing ws i with
  | nil => simp at ha
  | cons b ps ih =>
    simp only [List.flatten_cons, List.length_append] at h
    cases i with
    | zero =>
      simp only [cutWs, List.getElem?_cons_zero, Option.some.injEq] at ha hw
      subst ha hw; simp; omega
    | succ i =>
      simp only [cutWs, List.getElem?_cons_succ] at ha hw
      exact ih (ws.drop b.length) (by simp only [List.length_drop]; omega) i ha hw

end cut

section cutIProp
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]

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

end cutIProp

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- **The split's heap step** (see the module doc). `n` (record `rN` in `X1`, live, of bucket `bl`,
owning its inodes' capacity, its entries one per inode); its parent, if any, a live node of `bl`.
After: `splitRel`, and every piece fits a page (`pieceFits 4096`), with at least two inodes when
split. -/
theorem splitStep_wp (hSplit : node.split.spec (GF := GF) (hG := hG))
    (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X1 : WX) (bl n : Loc) (rN : NRec) (np txp : Loc)
    (hn : X1.node bl n = some rN) (hlv : n ∈ X1.live) (hbl : rN.nv.bucket' = bl)
    (hcap : rN.capOwn = true) (hsp : rN.nv.spilled' = false) (hil : rN.ins.length = rN.ws.length)
    (hsz : insSize rN.ins < 2 ^ 63)
    (hpar : rN.nv.parent' ≠ null → ∃ rp, X1.node bl rN.nv.parent' = some rp ∧
      rN.nv.parent' ∈ X1.live)
    (Φ : val → IProp GF) :
    wtxW K tx r m X1 ∗ np ↦ n ∗ txp ↦ tx ∗
      (∀ (s : GoSlice) (xs : List (Loc × node × List Inode)) (wss : List (List WEntry))
          (pl : Loc) (rp' : NRec) (X2 : WX),
        ⌜splitRel X1 X2 bl n rN xs wss pl rp' ∧
          ∀ x ∈ xs, pieceFits 4096 x.2.2 ∧ (2 ≤ xs.length → 2 ≤ x.2.2.length)⌝ -∗
        wtxW K tx r m X2 -∗ s ↦* xs.map (·.1) -∗ np ↦ n -∗ txp ↦ tx -∗ Φ #s) ⊢
    WP (splitCall np txp) {{ Φ }} := by
  -- Not yet (U9r hand-off). Plan:
  -- 1. `uintptr(tx.db.pageSize)`: `wtxW_size_acc` (`Spill/NodeSpillPiecesOne`) for `tx.db` and
  --    `pageSize ↦□ 4096`, closed at once; the conversion leaves `W64 4096`.
  -- 2. open `wtxW` with `wtxW_split` + `unfold wtxCore` (as `node__rebalance`): `fills` is
  --    there, not in `wtxHeap`; `Hfp` (bl's `FillPercent`: `rootFill` if `bl = X1.rl`, else its
  --    `fills` entry; `heapOK`'s last clause decides) exactly as `node__rebalance`'s.
  -- 3. `wtxHeap_reshape` with `L = n :: (parent if ≠ null)` (distinct: `heapOK`'s no-own-parent
  --    clause), `Lb = [bl]`; `objOwn_bkt_tx_acc` for the bucket's `tx` field; `n`'s object
  --    unfolded (`objOwn_live_node`): struct, inodes, `Hcap` (`hcap`), `Hws`, children, key;
  --    `parentOwn` from the parent's unfolded object (struct, children, their capacity), or `emp`.
  -- 4. `hSplit K tx r m 1 n rN.nv rN.ins f dqf dqb pv pcs (W64 4096)`, `statsTok r m 1` from
  --    the core.
  -- 5. Post, unsplit: everything back (`X2 = X1`, `wss = [rN.ws]`, `pl = rN.nv.parent'`).
  --    Split: the pieces' records `splitRec rN x w (i = 0) false` with `wss = cutWs (xs.map
  --    (·.2.2)) rN.ws` (`bigSepL2_cut` splits `Hws`; `cutWs_get` the lengths); `n`'s and an old
  --    parent's records back through the reshape (to an `X1'` with `bl`'s `ns` updated at `L`),
  --    then the fresh pieces and a new parent (`newParRec`, `capOwn := true`, nil inodes:
  --    `ownSlice_nil`, `ownSliceCap_nil`) inserted one by one (`wtxHeap_fresh` gives freshness,
  --    `wtxHeap_node_insert`): a fold lemma over the list to write. `splitRel.frame`/`same`:
  --    only `bl`'s `ns` grows/changes at the pieces and `pl`, `objs` only grow.
  sorry

end proof

end Spill

end bbolt
end EtcdGrove
end Perennial
