/-
`n.split(pageSize)` in `node.spill`: the node's resources lent to `node.split`, and the bucket
after it (`splitNs`): the node (part 0) and its new parts (`partRecs`: its entries split as its
inodes are, `wsChunks`), and the parent (the old one, its children appended, or a new one, its
children the parts); the parts' capacities (only the last keeps one, `splitK`).
-/
module

public import Proof.go_etcd_io.bbolt.SpillNodeCut
public import Spec.go_etcd_io.bbolt.node__split_x

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pure
variable [ext : FfiSyntax]

/-- The entries `ws` in chunks of the lengths `ks`. -/
def wsChunks (ws : List WEntry) : List Nat → List (List WEntry)
  | [] => []
  | k :: ks => ws.take k :: wsChunks (ws.drop k) ks

/-- The parts' records: part 0 the node `r` with its share, the others new (no children, no
key). -/
def partRec (r : NRec) (j : Nat) (x : Loc × node × List Inode) (ws : List WEntry) : NRec :=
  if j = 0 then { r with nv := x.2.1, ins := x.2.2, ws := ws }
  else ⟨x.2.1, x.2.2, ws, [], [], Src.own (DFrac.own 1)⟩

def partRecs (r : NRec) (xs : List (Loc × node × List Inode)) : List NRec :=
  ((xs.zip (wsChunks r.ws (xs.map (fun x => x.2.2.length)))).zipIdx).map
    (fun p => partRec r p.2 p.1.1 p.1.2)

/-- The nodes `ns` with the nodes `ls` (records `rs`). -/
def insertAll (ns : GMap Loc NRec) : List Loc → List NRec → GMap Loc NRec
  | l :: ls, r :: rs => <[l := r]> (insertAll ns ls rs)
  | _, _ => ns

/-- The parent's record after the split: the old one (`rp`), or a new one. -/
def parentRec (r rp : NRec) (pv' : node) (pcs' : List Loc) : NRec :=
  if r.nv.parent' = null then ⟨pv', [], [], pcs', [], Src.own (DFrac.own 1)⟩
  else { rp with nv := pv', cs := pcs' }

/-- The bucket's nodes after the split of `n` (record `r`) into the parts `xs`, under `pl`. -/
def splitNs (ns : GMap Loc NRec) (r rp : NRec) (xs : List (Loc × node × List Inode)) (pl : Loc)
    (pv' : node) (pcs' : List Loc) : GMap Loc NRec :=
  insertAll (<[pl := parentRec r rp pv' pcs']> ns) (xs.map (fun x => x.1)) (partRecs r xs)

/-- The capacities after the split: the parts but the last have none; the parent has one. -/
def splitK (K : Loc → Bool) (xs : List (Loc × node × List Inode)) (pl : Loc) : Loc → Bool :=
  fun l => if l ∈ xs.map (fun x => x.1) then decide (xs.getLast?.map (fun x => x.1) ≠ some l)
    else if l = pl then false else K l

/-- The transaction after the split. -/
def splitT (T : WTx) (bl : Loc) (B : BRec) (r rp : NRec) (xs : List (Loc × node × List Inode))
    (pl : Loc) (pv' : node) (pcs' : List Loc) (st : TxStats) : WTx :=
  { T with t := { T.t with stats' := st }, bs := <[bl := { B with ns := splitNs B.ns r rp xs pl pv' pcs' }]> T.bs }

theorem insertAll_notin (ns : GMap Loc NRec) :
    ∀ (ls : List Loc) (rs : List NRec) (k : Loc), k ∉ ls → insertAll ns ls rs !! k = ns !! k
  | [], _, _, _ => by simp [insertAll]
  | _ :: _, [], _, _ => by simp [insertAll]
  | l :: ls, r :: rs, k, hk => by
    simp only [insertAll]
    have hne : l ≠ k := fun e => hk (by rw [e]; exact List.mem_cons_self)
    rw [GMap.lookup_insert_ne _ _ hne]
    exact insertAll_notin ns ls rs k (fun h => hk (List.mem_cons_of_mem _ h))

theorem insertAll_in (ns ns' : GMap Loc NRec) :
    ∀ (ls : List Loc) (rs : List NRec) (k : Loc), ls.length = rs.length → k ∈ ls →
      insertAll ns ls rs !! k = insertAll ns' ls rs !! k
  | [], _, _, _, hk => by simp at hk
  | _ :: _, [], _, h, _ => by simp at h
  | l :: ls, r :: rs, k, hl, hk => by
    simp only [insertAll]
    by_cases e : l = k
    · subst e; rw [GMap.lookup_insert, GMap.lookup_insert]
    · rw [GMap.lookup_insert_ne _ _ e, GMap.lookup_insert_ne _ _ e]
      exact insertAll_in ns ns' ls rs k (by simpa using hl) (by
        rcases List.mem_cons.1 hk with h | h
        · exact absurd h.symm e
        · exact h)

theorem insertAll_in_some (ns : GMap Loc NRec) :
    ∀ (ls : List Loc) (rs : List NRec) (k : Loc), ls.length = rs.length → k ∈ ls →
      (insertAll ns ls rs !! k).isSome
  | [], _, _, _, hk => by simp at hk
  | _ :: _, [], _, h, _ => by simp at h
  | l :: ls, r :: rs, k, hl, hk => by
    simp only [insertAll]
    by_cases e : l = k
    · subst e; rw [GMap.lookup_insert]; rfl
    · rw [GMap.lookup_insert_ne _ _ e]
      exact insertAll_in_some ns ls rs k (by simpa using hl) (by
        rcases List.mem_cons.1 hk with h | h
        · exact absurd h.symm e
        · exact h)

theorem wsChunks_length (ws : List WEntry) : ∀ ks : List Nat, (wsChunks ws ks).length = ks.length
  | [] => rfl
  | k :: ks => by simp [wsChunks, wsChunks_length (ws.drop k) ks]

theorem partRecs_length (r : NRec) (xs : List (Loc × node × List Inode)) :
    (partRecs r xs).length = xs.length := by
  unfold partRecs; simp [List.length_zip, wsChunks_length]

theorem partRec_rest (r : NRec) :
    ∀ (l : List ((Loc × node × List Inode) × List WEntry)) (k : Nat),
      (l.zipIdx (k + 1)).map (fun p => partRec r p.2 p.1.1 p.1.2) =
        l.map (fun q => (⟨q.1.2.1, q.1.2.2, q.2, [], [], Src.own (DFrac.own 1)⟩ : NRec))
  | [], _ => rfl
  | q :: l, k => by
    simp only [List.zipIdx_cons, List.map_cons]
    rw [show k + 1 + 1 = (k + 1) + 1 from rfl, partRec_rest r l (k + 1)]
    simp [partRec]

theorem partRecs_cons (r : NRec) (x0 : Loc × node × List Inode) (rest : List (Loc × node × List Inode)) :
    partRecs r (x0 :: rest) =
      partRec r 0 x0 (r.ws.take x0.2.2.length) ::
        (rest.zip (wsChunks (r.ws.drop x0.2.2.length) (rest.map (fun x => x.2.2.length)))).map
          (fun q => (⟨q.1.2.1, q.1.2.2, q.2, [], [], Src.own (DFrac.own 1)⟩ : NRec)) := by
  unfold partRecs
  simp only [List.map_cons, wsChunks, List.zip_cons_cons, List.zipIdx_cons, List.map_cons]
  congr 1
  exact partRec_rest r _ 0

theorem wsChunks_take_drop_len (ws : List WEntry) :
    ∀ (ys : List (Loc × node × List Inode)), (ys.map (fun x => x.2.2.length)).sum = ws.length →
      ∀ q ∈ ys.zip (wsChunks ws (ys.map (fun x => x.2.2.length))), q.2.length = q.1.2.2.length
  | [], _, q, hq => by simp at hq
  | y :: ys, hs, q, hq => by
    simp only [List.map_cons, List.sum_cons, wsChunks, List.zip_cons_cons, List.mem_cons] at hs hq
    rcases hq with rfl | hq
    · simp; omega
    · exact wsChunks_take_drop_len (ws.drop y.2.2.length) ys (by rw [List.length_drop]; omega) q hq


theorem zip_map_snd' {α β γ : Type} (f : β → γ) :
    ∀ (l1 : List α) (l2 : List β), (l1.zip l2).map (fun p => (p.1, f p.2)) = l1.zip (l2.map f)
  | [], _ => rfl
  | _ :: _, [] => rfl
  | a :: l1, b :: l2 => by simp only [List.zip_cons_cons, List.map_cons, zip_map_snd' f l1 l2]

theorem zip_map_map' {α β γ : Type} (f : α → β) (g : α → γ) :
    ∀ (xs : List α), (xs.map f).zip (xs.map g) = xs.map (fun x => (f x, g x))
  | [] => rfl
  | x :: xs => by simp only [List.map_cons, List.zip_cons_cons, zip_map_map' f g xs]

theorem partRecs_nv (r : NRec) (x0 : Loc × node × List Inode) (rest : List (Loc × node × List Inode)) :
    (partRecs r (x0 :: rest)).map NRec.nv = (x0 :: rest).map (fun x => x.2.1) := by
  rw [partRecs_cons, List.map_cons, List.map_cons, List.map_map]
  congr 1
  have e : (NRec.nv ∘ fun q : (Loc × node × List Inode) × List WEntry =>
        (⟨q.1.2.1, q.1.2.2, q.2, [], [], Src.own (DFrac.own 1)⟩ : NRec)) =
        (fun x : Loc × node × List Inode => x.2.1) ∘ Prod.fst := rfl
  rw [e, ← List.map_map, List.map_fst_zip (by rw [wsChunks_length, List.length_map]; exact Nat.le_refl _)]

theorem splitK_ids (K : Loc → Bool) (xs : List (Loc × node × List Inode)) (pl : Loc) (xl : Loc × node × List Inode)
    (hlast : xs.getLast? = some xl) (l : Loc) (hl : l ∈ xs.map (fun x => x.1)) :
    splitK K xs pl l = decide (some xl.1 ≠ some l) := by
  unfold splitK; rw [if_pos hl, hlast]; rfl

theorem splitK_out (K : Loc → Bool) (xs : List (Loc × node × List Inode)) (pl l : Loc)
    (hl : l ∉ xs.map (fun x => x.1)) (hpl : l ≠ pl) : splitK K xs pl l = K l := by
  unfold splitK; rw [if_neg hl, if_neg hpl]

theorem splitK_pl (K : Loc → Bool) (xs : List (Loc × node × List Inode)) (pl : Loc)
    (hl : pl ∉ xs.map (fun x => x.1)) : splitK K xs pl pl = false := by
  unfold splitK; rw [if_neg hl, if_pos rfl]

/-- What `spillR_split` tells of the split's nodes: fresh, but the node. -/
def splitFresh (B : BRec) (n : Loc) (xs : List (Loc × node × List Inode)) (pl par0 : Loc) : Prop :=
  (∀ x ∈ xs, x.1 ≠ n → B.ns !! x.1 = none) ∧ (par0 = null → B.ns !! pl = none) ∧
  pl ∉ xs.map (fun x => x.1) ∧ (xs.map (fun x => x.1)).Nodup

end pure

section res
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

theorem insertAll_sep (Φ : Loc → NRec → IProp GF) (ns0 : GMap Loc NRec) :
    ∀ (ls : List Loc) (rs : List NRec), ls.length = rs.length → ls.Nodup →
      (∀ l ∈ ls, ns0 !! l = none) →
      ([∗map] l ↦ r ∈ ns0, Φ l r) ∗ ([∗list] p ∈ ls.zip rs, Φ p.1 p.2) ⊢
        [∗map] l ↦ r ∈ insertAll ns0 ls rs, Φ l r
  | [], [], _, _, _ => by
    simp only [insertAll, List.zip_nil_left]
    iintro ⟨H, -⟩; iexact H
  | [], _ :: _, h, _, _ => by simp at h
  | _ :: _, [], h, _, _ => by simp at h
  | l :: ls, r :: rs, hlen, hnd, hfr => by
    simp only [insertAll, List.zip_cons_cons]
    have hl : insertAll ns0 ls rs !! l = none := by
      rw [insertAll_notin ns0 ls rs l (List.nodup_cons.1 hnd).1]
      exact hfr l List.mem_cons_self
    iintro ⟨H, Hl⟩
    icases BigSepL.bigSepL_cons.1 $$ Hl with ⟨Hx, Hl⟩
    iapply (BigSepM.bigSepM_insert (M := GMap Loc) (Φ := Φ) (show Std.get? (insertAll ns0 ls rs) l = none from hl)).2
    iframe Hx
    iapply insertAll_sep Φ ns0 ls rs (by simpa using hlen) (List.nodup_cons.1 hnd).2
      (fun l' h => hfr l' (List.mem_cons_of_mem _ h))
    iframe

/-- A node held is not among the nodes `ns`. -/
theorem nodes_excl (W : WView) (ns : GMap Loc NRec) (x : Loc) (v : node) :
    ([∗map] l ↦ r ∈ ns, nodeOwnX (GF := GF) W l r) ∗ x ↦ v ⊢
      ⌜ns !! x = none⌝ ∗ ([∗map] l ↦ r ∈ ns, nodeOwnX W l r) ∗ x ↦ v := by
  cases h : ns !! x with
  | none => iintro ⟨H1, H2⟩; iframe; ipureintro; rfl
  | some r =>
    iintro ⟨H1, H2⟩
    icases (BigSepM.bigSepM_lookup_acc (M := GMap Loc) (Φ := fun l r => nodeOwnX (GF := GF) W l r)
      (show Std.get? ns x = some r from h)).1 $$ H1 with ⟨Hn, -⟩
    unfold nodeOwnX
    icases Hn with ⟨Hn, -⟩
    iexfalso
    iapply node_ptsto_excl
    iframe

/-- Nodes held are distinct. -/
theorem parts_nodup (R : Loc × node × List Inode → IProp GF) :
    ∀ (xs : List (Loc × node × List Inode)),
      ([∗list] x ∈ xs, x.1 ↦ x.2.1 ∗ R x) ⊢
        ⌜(xs.map (fun x => x.1)).Nodup⌝ ∗ [∗list] x ∈ xs, x.1 ↦ x.2.1 ∗ R x
  | [] => by iintro H; iframe; ipureintro; simp
  | x :: xs => by
    iintro H
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨⟨Hx, Rx⟩, H⟩
    icases parts_nodup R xs $$ H with ⟨%hnd, H⟩
    have : ∀ y ∈ xs, True := fun _ _ => trivial
    by_cases hin : x.1 ∈ xs.map (fun x => x.1)
    · obtain ⟨y, hy, hyx⟩ := List.mem_map.1 hin
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hy
      icases (BigSepL.bigSepL_lookup_acc (Φ := fun _ x => iprop(x.1 ↦ x.2.1 ∗ R x))
        (List.getElem?_eq_getElem hj)).1 $$ H with ⟨⟨Hy, -⟩, -⟩
      rw [hyx]
      iexfalso
      iapply node_ptsto_excl
      iframe
    · iframe
      ipureintro
      simp only [List.map_cons, List.nodup_cons]
      exact ⟨hin, hnd⟩

end res


section res2
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- The entries' resources in the parts' chunks. -/
theorem wOwn_chunks (W : WView) (ws : List WEntry) :
    ∀ (ys : List (Loc × node × List Inode)), (ys.map (fun x => x.2.2.length)).sum = ws.length →
      ([∗list] it;w ∈ (ys.map (fun x => x.2.2)).flatten;ws, wOwn (GF := GF) W it w) ⊢
        [∗list] q ∈ ys.zip (wsChunks ws (ys.map (fun x => x.2.2.length))),
          [∗list] it;w ∈ q.1.2.2;q.2, wOwn W it w
  | [], hs => by
    have : ws = [] := List.eq_nil_of_length_eq_zero (by simpa using hs.symm)
    subst this
    simp only [List.map_nil, List.flatten_nil, List.zip_nil_left]
    iintro -; iapply BigSepL.bigSepL_nil.2; iempintro
  | y :: ys, hs => by
    simp only [List.map_cons, List.sum_cons, List.flatten_cons, wsChunks, List.zip_cons_cons] at hs ⊢
    have hk : y.2.2.length ≤ ws.length := by omega
    have e : ws = ws.take y.2.2.length ++ ws.drop y.2.2.length := (List.take_append_drop _ _).symm
    refine (BiEntails.of_eq (congrArg (fun l => [∗list] it;w ∈ y.2.2 ++ (ys.map (fun x => x.2.2)).flatten;l,
      wOwn (GF := GF) W it w) e)).1.trans ?_
    refine (BigSepL2.bigSepL2_append (Φ := fun _ it w => wOwn (GF := GF) W it w)
      (Or.inl (by rw [List.length_take, Nat.min_eq_left hk]))).1.trans ?_
    refine BIBase.Entails.trans ?_ BigSepL.bigSepL_cons.2
    exact sep_mono .rfl (wOwn_chunks W (ws.drop y.2.2.length) ys (by rw [List.length_drop]; omega))

/-- The new parts (no children, no key) as nodes. -/
theorem rest_own (W : WView) :
    ∀ (l : List ((Loc × node × List Inode) × List WEntry)),
      (∀ q ∈ l, q.1.2.1.children' = slice.nil ∧ q.1.2.1.key' = slice.nil) →
      ([∗list] q ∈ l, q.1.1 ↦ q.1.2.1 ∗ q.1.2.1.inodes' ↦* q.1.2.2) ∗
      ([∗list] q ∈ l, [∗list] it;w ∈ q.1.2.2;q.2, wOwn (GF := GF) W it w) ⊢
        [∗list] p ∈ (l.map (fun q => q.1.1)).zip
            (l.map (fun q => (⟨q.1.2.1, q.1.2.2, q.2, [], [], Src.own (DFrac.own 1)⟩ : NRec))),
          nodeOwnX W p.1 p.2
  | [], _ => by
    simp only [List.map_nil, List.zip_nil_left]
    iintro -; iapply BigSepL.bigSepL_nil.2; iempintro
  | q :: l, hq => by
    simp only [List.map_cons, List.zip_cons_cons]
    iintro ⟨H1, H2⟩
    icases BigSepL.bigSepL_cons.1 $$ H1 with ⟨⟨Hq, Hi⟩, H1⟩
    icases BigSepL.bigSepL_cons.1 $$ H2 with ⟨Hw, H2⟩
    iapply BigSepL.bigSepL_cons.2
    obtain ⟨hc, hk⟩ := hq q List.mem_cons_self
    isplitl [Hq Hi Hw]
    · unfold nodeOwnX
      simp only
      rw [hc, hk]
      iframe
      isplitl []
      · iapply ownSlice_nil
      isplitl []
      · iapply ownSliceCap_nil
      simp only [ite_true]
      ipureintro; trivial
    iapply rest_own W l (fun q' h => hq q' (List.mem_cons_of_mem _ h))
    iframe

/-- Nodes held vs. a list of parts held: distinct. -/
theorem nodes_excl_parts (W : WView) (ns : GMap Loc NRec) (R : Loc × node × List Inode → IProp GF) :
    ∀ (xs : List (Loc × node × List Inode)),
      ([∗map] l ↦ r ∈ ns, nodeOwnX (GF := GF) W l r) ∗ ([∗list] x ∈ xs, x.1 ↦ x.2.1 ∗ R x) ⊢
        ⌜∀ x ∈ xs, ns !! x.1 = none⌝ ∗
        ([∗map] l ↦ r ∈ ns, nodeOwnX W l r) ∗ ([∗list] x ∈ xs, x.1 ↦ x.2.1 ∗ R x)
  | [] => by iintro ⟨H1, H2⟩; iframe; ipureintro; simp
  | x :: xs => by
    iintro ⟨H1, H2⟩
    icases BigSepL.bigSepL_cons.1 $$ H2 with ⟨⟨Hx, Rx⟩, H2⟩
    icases nodes_excl W ns x.1 x.2.1 $$ [H1 Hx] with ⟨%h1, H1, Hx⟩
    · iframe
    icases nodes_excl_parts W ns R xs $$ [H1 H2] with ⟨%h2, H1, H2⟩
    · iframe
    iframe H1
    isplitr
    · ipureintro
      intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · exact h1
      · exact h2 y hy
    iapply BigSepL.bigSepL_cons.2
    iframe

/-- A node held is not among a list of parts held. -/
theorem node_excl_parts (R : Loc × node × List Inode → IProp GF) (y : Loc) (v : node) :
    ∀ (xs : List (Loc × node × List Inode)),
      (y ↦ v ∗ [∗list] x ∈ xs, x.1 ↦ x.2.1 ∗ R x) ⊢
        ⌜y ∉ xs.map (fun x => x.1)⌝ ∗ y ↦ v ∗ ([∗list] x ∈ xs, x.1 ↦ x.2.1 ∗ R x)
  | [] => by iintro ⟨H1, H2⟩; iframe; ipureintro; simp
  | x :: xs => by
    iintro ⟨H1, H2⟩
    icases BigSepL.bigSepL_cons.1 $$ H2 with ⟨⟨Hx, Rx⟩, H2⟩
    by_cases e : y = x.1
    · rw [e]
      iexfalso
      iapply node_ptsto_excl
      iframe
    · icases node_excl_parts R y v xs $$ [H1 H2] with ⟨%h, H1, H2⟩
      · iframe
      iframe H1
      isplitr
      · ipureintro
        simp only [List.map_cons, List.mem_cons, not_or]
        exact ⟨e, h⟩
      iapply BigSepL.bigSepL_cons.2
      iframe

end res2

section own
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `spillR_bkt`, with the transaction's statistics field. -/
theorem spillR_bkt_st (I : FLImpl (GF := GF)) (γd : DBNames) (γ : GName) (W : WView) (txl : Loc)
    (txid : w64) (T : WTx) (ρ : DBState) (F : GMap Nat (List w8)) (K : Loc → Bool) (bl : Loc)
    (B : BRec) (hB : T.bs !! bl = some B) :
    spillR I γd γ W txl txid T ρ F K ⊢
      bktOwnX W bl B ∗ capsKN K B.ns ∗ structFieldRef Tx go!"stats" txl ↦ T.t.stats' ∗
      (∀ (B' : BRec) (K' : Loc → Bool) (st : TxStats),
        ⌜∀ l, K' l ≠ K l → (B.ns !! l).isSome ∨ (B'.ns !! l).isSome⌝ -∗
        bktOwnX W bl B' -∗ capsKN K' B'.ns -∗ structFieldRef Tx go!"stats" txl ↦ st -∗
        spillR I γd γ W txl txid { setB T bl B' with t := { T.t with stats' := st } } ρ F K') := by
  unfold spillR ownWriteTxGX capsOwn
  iintro ⟨Hdb, ⟨Hrest, Hm, Hpm, Hbufs, Hbs⟩, Hv, Hcaps, Hgh, HF⟩
  isimp only [TxW_rest_root] at Hrest
  icases Hrest with ⟨Hw, Hma, Hdbf, Hmet, Hpgs, Hst, Hch, Hwf, %Htn⟩
  icases (BigSepM.bigSepM_delete (M := GMap Loc) (Φ := fun bl B => bktOwnX (GF := GF) W bl B)
    (show Std.get? T.bs bl = some B from hB)).1 $$ Hbs with ⟨Hb, Hbs⟩
  icases (BigSepM.bigSepM_delete (M := GMap Loc)
    (Φ := fun _bl B => iprop([∗map] l ↦ r ∈ B.ns, if K l then iprop(emp) else capOwn (GF := GF) r))
    (show Std.get? T.bs bl = some B from hB)).1 $$ Hcaps with ⟨Hc, Hcaps⟩
  icases bkts_excl_b W (Std.delete T.bs bl) bl B $$ [Hbs Hb] with ⟨%hx1, Hbs, Hb⟩
  · iframe
  iframe Hb Hst
  unfold capsKN
  iframe Hc
  iintro %B' %K' %st %hK Hb' Hc' Hst
  icases bkts_excl_b W (Std.delete T.bs bl) bl B' $$ [Hbs Hb'] with ⟨%hx2, Hbs, Hb'⟩
  · iframe
  dsimp only [setB]
  have e : spillPages W { T with bs := <[bl := B']> T.bs, t := { T.t with stats' := st } } =
      spillPages W T := rfl
  rw [e]
  iframe Hdb Hm Hpm Hbufs Hv Hgh HF
  isplitl [Hw Hma Hdbf Hmet Hpgs Hst Hch Hwf Hb' Hbs]
  · unfold TxW_rest_root
    iframe Hw Hma Hdbf Hmet Hpgs Hst Hch Hwf
    isplitr
    · ipureintro; exact Htn
    iapply (BigSepM.bigSepM_insert_delete (M := GMap Loc) (Φ := fun bl B => bktOwnX (GF := GF) W bl B)).2
    iframe
  iapply (BigSepM.bigSepM_insert_delete (M := GMap Loc) (m := T.bs) (i := bl) (x := B')
    (Φ := fun _bl B => [∗map] l ↦ r ∈ B.ns, if K' l then iprop(emp) else capOwn (GF := GF) r)).2
  iframe Hc'
  iapply (BigSepM.bigSepM_mono (M := GMap Loc) ?_) $$ Hcaps
  intro b2 B2 hB2
  apply BigSepM.bigSepM_mono
  intro l r hr
  have e : K' l = K l := by
    apply Classical.byContradiction
    intro hne
    rcases hK l hne with h | h
    · have := hx1 b2 B2 l hB2 h; have hr' : B2.ns !! l = some r := hr
      rw [this] at hr'; cases hr'
    · have := hx2 b2 B2 l hB2 h; have hr' : B2.ns !! l = some r := hr
      rw [this] at hr'; cases hr'
  rw [e]


theorem bigSepL_zip_fst {A C : Type} (P : A → IProp GF) :
    ∀ (ys : List A) (cs : List C), ys.length = cs.length →
      ([∗list] y ∈ ys, P y) ⊢ [∗list] q ∈ ys.zip cs, P q.1
  | [], _, _ => by iintro -; simp only [List.zip_nil_left]; iapply BigSepL.bigSepL_nil.2; iempintro
  | _ :: _, [], h => by simp at h
  | y :: ys, c :: cs, h => by
    simp only [List.zip_cons_cons]
    iintro H
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨Hy, H⟩
    iapply BigSepL.bigSepL_cons.2
    iframe Hy
    iapply bigSepL_zip_fst P ys cs (by simpa using h)
    iexact H

/-- The parts' capacities: only the last one's. -/
theorem caps_parts (K' : Loc → Bool) (a : Loc) (va : node) :
    ∀ (L : List (Loc × NRec)), (L.map Prod.fst).Nodup →
      (L.map (fun p => (p.1, p.2.nv))).getLast? = some (a, va) →
      (∀ p ∈ L, K' p.1 = decide (some a ≠ some p.1)) →
      ownSliceCap Inode va.inodes' (DFrac.own 1) ⊢
        [∗list] p ∈ L, (if K' p.1 then iprop(emp) else capOwn (GF := GF) p.2)
  | [], _, h, _ => by simp at h
  | [p], _, h, hk => by
    simp only [List.map_cons, List.map_nil, List.getLast?_singleton, Option.some.injEq,
      Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have : K' p.1 = false := by rw [hk p List.mem_cons_self, h1]; simp
    refine BIBase.Entails.trans ?_ BigSepL.bigSepL_singleton.2
    rw [this]
    simp only [Bool.false_eq_true, ite_false, capOwn]
    rw [h2]
  | p :: q :: t, hnd, h, hk => by
    have h' : ((q :: t).map (fun p => (p.1, p.2.nv))).getLast? = some (a, va) := by
      rw [List.map_cons, List.map_cons, List.getLast?_cons_cons] at h
      rw [List.map_cons]; exact h
    have ha : a ∈ (q :: t).map Prod.fst := by
      obtain ⟨y, hy, hya⟩ := List.mem_map.1 (List.mem_of_getLast? h')
      exact List.mem_map.2 ⟨y, hy, by simp only [Prod.mk.injEq] at hya; exact hya.1⟩
    have hpa : p.1 ≠ a := by
      intro e; rw [List.map_cons] at hnd; exact (List.nodup_cons.1 hnd).1 (e ▸ ha)
    have hkp : K' p.1 = true := by
      rw [hk p List.mem_cons_self]; simp only [ne_eq, Option.some.injEq, decide_eq_true_eq]
      exact fun e => hpa e.symm
    have IH := caps_parts K' a va (q :: t) (by rw [List.map_cons] at hnd; exact (List.nodup_cons.1 hnd).2) h'
      (fun p' hp' => hk p' (List.mem_cons_of_mem _ hp'))
    refine BIBase.Entails.trans ?_ BigSepL.bigSepL_cons.2
    rw [hkp]
    simp only [ite_true]
    iintro H
    isplitl []
    · iempintro
    iapply IH; iexact H

/-- The bucket's nodes and capacities after the split, assembled. -/
theorem split_assemble (W : WView) (K : Loc → Bool) (n pl : Loc) (r prec : NRec)
    (xs : List (Loc × node × List Inode)) (xl : Loc × node × List Inode) (D2 ns0 : GMap Loc NRec)
    (hsp : splitPieces n r.nv pl r.ins xs) (hlast : xs.getLast? = some xl)
    (hnd : (xs.map (fun x => x.1)).Nodup) (hfr : ∀ x ∈ xs, D2 !! x.1 = none)
    (hpl : pl ∉ xs.map (fun x => x.1)) (hD2pl : D2 !! pl = none)
    (hD2 : ∀ k, k ∉ xs.map (fun x => x.1) → k ≠ pl → ns0 !! k = D2 !! k) :
    ([∗map] l ↦ r ∈ D2, nodeOwnX (GF := GF) W l r) ∗
      ([∗map] l ↦ r ∈ D2, if K l then iprop(emp) else capOwn (GF := GF) r) ∗
      nodeOwnX W pl prec ∗ capOwn prec ∗
      ([∗list] x ∈ xs, x.1 ↦ x.2.1 ∗ x.2.1.inodes' ↦* x.2.2) ∗
      ([∗list] it;w ∈ r.ins;r.ws, wOwn W it w) ∗ r.nv.children' ↦* r.cs ∗
      ownSliceCap Loc r.nv.children' (DFrac.own 1) ∗
      (if r.nv.key' = slice.nil then iprop(True) else srcOwn W r.nv.key' r.ksrc r.key) ∗
      ownSliceCap Inode xl.2.1.inodes' (DFrac.own 1) ⊢
    ([∗map] l ↦ r' ∈ insertAll (<[pl := prec]> ns0) (xs.map (fun x => x.1)) (partRecs r xs),
        nodeOwnX W l r') ∗
      capsKN (splitK K xs pl) (insertAll (<[pl := prec]> ns0) (xs.map (fun x => x.1)) (partRecs r xs)) := by
  have hlen : (xs.map (fun x => x.1)).length = (partRecs r xs).length := by
    rw [List.length_map, partRecs_length]
  have hmeq : insertAll (<[pl := prec]> ns0) (xs.map (fun x => x.1)) (partRecs r xs) =
      insertAll (<[pl := prec]> D2) (xs.map (fun x => x.1)) (partRecs r xs) := by
    apply GMap.ext; intro k
    show insertAll (<[pl := prec]> ns0) _ _ !! k = insertAll (<[pl := prec]> D2) _ _ !! k
    by_cases hk : k ∈ xs.map (fun x => x.1)
    · exact insertAll_in _ _ _ _ k hlen hk
    · rw [insertAll_notin _ _ _ k hk, insertAll_notin _ _ _ k hk]
      by_cases e : pl = k
      · subst e; rw [GMap.lookup_insert, GMap.lookup_insert]
      · rw [GMap.lookup_insert_ne _ _ e, GMap.lookup_insert_ne _ _ e]
        exact hD2 k hk (Ne.symm e)
  rw [hmeq]
  obtain ⟨hflat, ⟨x0, rest, hxs, hx0n, hx0v, hrest⟩, -⟩ := hsp
  subst hxs
  have hfresh : ∀ l ∈ (x0 :: rest).map (fun x => x.1), (<[pl := prec]> D2) !! l = none := by
    intro l hl
    have hne : pl ≠ l := fun e => hpl (e ▸ hl)
    rw [GMap.lookup_insert_ne _ _ hne]
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hl
    exact hfr x hx
  have hD2pl' : Std.get? D2 pl = none := hD2pl
  have hc0 : x0.2.1.children' = r.nv.children' := by rw [hx0v]
  have hk0 : x0.2.1.key' = r.nv.key' := by rw [hx0v]
  have hchl : (wsChunks (r.ws.drop x0.2.2.length) (rest.map (fun x => x.2.2.length))).length =
      rest.length := by rw [wsChunks_length, List.length_map]
  iintro ⟨Hns, Hc, Hp, Hpc, Hparts, Hents, Hch, Hchc, Hkey, Hxl⟩
  ihave %hel := BigSepL2.bigSepL2_length $$ Hents
  have hsum : ((x0 :: rest).map (fun x => x.2.2.length)).sum = r.ws.length := by
    rw [← hel, ← hflat, List.length_flatten, List.map_map]; rfl
  isplitl [Hns Hp Hparts Hents Hch Hchc Hkey]
  · iapply insertAll_sep (fun l r => nodeOwnX (GF := GF) W l r) (<[pl := prec]> D2) _ _ hlen hnd hfresh
    isplitl [Hns Hp]
    · iapply (BigSepM.bigSepM_insert (M := GMap Loc) (Φ := fun l r => nodeOwnX (GF := GF) W l r) hD2pl').2
      iframe
    rw [← hflat]
    ihave Hch2 := wOwn_chunks W r.ws (x0 :: rest) hsum $$ Hents
    simp only [List.map_cons, wsChunks, List.zip_cons_cons]
    icases BigSepL.bigSepL_cons.1 $$ Hch2 with ⟨He0, Hes⟩
    icases BigSepL.bigSepL_cons.1 $$ Hparts with ⟨⟨Hn0, Hi0⟩, Hparts⟩
    rw [partRecs_cons, List.zip_cons_cons]
    iapply BigSepL.bigSepL_cons.2
    isplitl [Hn0 Hi0 He0 Hch Hchc Hkey]
    · unfold nodeOwnX partRec
      simp only [ite_true]
      rw [hc0, hk0]
      iframe
    ihave Hpz := bigSepL_zip_fst (fun x : Loc × node × List Inode => iprop(x.1 ↦ x.2.1 ∗ x.2.1.inodes' ↦* x.2.2))
      rest _ hchl.symm $$ Hparts
    have hfst : (rest.zip (wsChunks (r.ws.drop x0.2.2.length) (rest.map (fun x => x.2.2.length)))).map
        (fun q => q.1.1) = rest.map (fun x => x.1) := by
      rw [show (fun q : (Loc × node × List Inode) × List WEntry => q.1.1) = (fun x : Loc × node × List Inode => x.1) ∘ Prod.fst from rfl,
        ← List.map_map, List.map_fst_zip (by rw [hchl]; exact Nat.le_refl _)]
    rw [← hfst]
    have hnil : ∀ q ∈ rest.zip (wsChunks (r.ws.drop x0.2.2.length) (rest.map (fun x => x.2.2.length))),
        q.1.2.1.children' = slice.nil ∧ q.1.2.1.key' = slice.nil := by
      intro q hq
      have hq1 : q.1 ∈ rest := (List.of_mem_zip hq).1
      obtain ⟨-, hv⟩ := hrest q.1 hq1
      rw [hv]; exact ⟨rfl, rfl⟩
    iapply rest_own W _ hnil
    iframe
  · unfold capsKN
    iapply insertAll_sep (fun l r => if splitK K (x0 :: rest) pl l then iprop(emp) else capOwn (GF := GF) r)
      (<[pl := prec]> D2) _ _ hlen hnd hfresh
    isplitl [Hc Hpc]
    · iapply (BigSepM.bigSepM_insert (M := GMap Loc)
        (Φ := fun l r => if splitK K (x0 :: rest) pl l then iprop(emp) else capOwn (GF := GF) r) hD2pl').2
      isplitl [Hpc]
      · rw [splitK_pl K _ pl hpl]; simp only [Bool.false_eq_true, ite_false]; iexact Hpc
      iapply (BigSepM.bigSepM_mono (M := GMap Loc) ?_) $$ Hc
      intro l v hv
      have hv' : D2 !! l = some v := hv
      have hl1 : l ∉ (x0 :: rest).map (fun x => x.1) := by
        intro hl
        obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hl
        rw [hfr x hx] at hv'; cases hv'
      have hl2 : l ≠ pl := by intro e; subst e; rw [hD2pl] at hv'; cases hv'
      rw [splitK_out K _ pl l hl1 hl2]
    have hA : (((x0 :: rest).map (fun x => x.1)).zip (partRecs r (x0 :: rest))).map Prod.fst |>.Nodup := by
      rw [List.map_fst_zip (by rw [hlen]; exact Nat.le_refl _)]; exact hnd
    have hB : ((((x0 :: rest).map (fun x => x.1)).zip (partRecs r (x0 :: rest))).map
        (fun p => (p.1, p.2.nv))).getLast? = some (xl.1, xl.2.1) := by
      rw [zip_map_snd' NRec.nv, partRecs_nv, zip_map_map', List.getLast?_map, hlast]; rfl
    have hC : ∀ p ∈ ((x0 :: rest).map (fun x => x.1)).zip (partRecs r (x0 :: rest)),
        splitK K (x0 :: rest) pl p.1 = decide (some xl.1 ≠ some p.1) := by
      intro p hp
      exact splitK_ids K _ pl xl hlast p.1 (List.of_mem_zip hp).1
    iapply caps_parts (splitK K (x0 :: rest) pl) xl.1 xl.2.1 _ hA hB hC
    iexact Hxl


theorem pageOwn_ns (W : WView) (B : BRec) (m : GMap Loc NRec) :
    pageOwn (GF := GF) W ({ B with ns := m } : BRec) = pageOwn W B := rfl
/-- What `node.split` takes of the spill state, and back: unchanged, or after the split. -/
theorem spillR_split (I : FLImpl (GF := GF)) (γd : DBNames) (γ : GName) (W : WView) (txl : Loc)
    (txid : w64) (T : WTx) (ρ : DBState) (F : GMap Nat (List w8)) (K : Loc → Bool) (bl : Loc)
    (B : BRec) (n : Loc) (r rp : NRec) (hB : T.bs !! bl = some B) (hn : B.ns !! n = some r)
    (hK : K n = false) (hbk : r.nv.bucket' = bl) (htx : B.bv.tx' = txl)
    (hpl : r.nv.parent' ≠ null → B.ns !! r.nv.parent' = some rp ∧ r.nv.parent' ≠ n)
    (hcs : r.cs = []) (hKp : r.nv.parent' ≠ null → K r.nv.parent' = false) :
    spillR I γd γ W txl txid T ρ F K ⊢
      (n ↦ r.nv ∗ r.nv.inodes' ↦* r.ins ∗ ownSliceCap Inode r.nv.inodes' (DFrac.own 1) ∗
        r.nv.bucket' ↦ B.bv ∗ structFieldRef Tx go!"stats" B.bv.tx' ↦ T.t.stats' ∗
        parentOwn r.nv.parent' rp.nv rp.cs) ∗
      ((n ↦ r.nv ∗ r.nv.inodes' ↦* r.ins ∗ ownSliceCap Inode r.nv.inodes' (DFrac.own 1) ∗
          r.nv.bucket' ↦ B.bv ∗ structFieldRef Tx go!"stats" B.bv.tx' ↦ T.t.stats' ∗
          parentOwn r.nv.parent' rp.nv rp.cs -∗ spillR I γd γ W txl txid T ρ F K) ∧
       (∀ (xs : List (Loc × node × List Inode)) (pl : Loc) (pv' : node) (pcs' : List Loc)
          (xl : Loc × node × List Inode) (st : TxStats),
          ⌜2 ≤ xs.length ∧ splitPieces n r.nv pl r.ins xs ∧ xs.getLast? = some xl ∧ pl ≠ null ∧
            ((r.nv.parent' = null ∧ pv' = newParent r.nv pv'.children' ∧
                pcs' = xs.map (fun x => x.1)) ∨
             (r.nv.parent' ≠ null ∧ pl = r.nv.parent' ∧ pv' = { rp.nv with children' := pv'.children' } ∧
              pcs' = rp.cs ++ (xs.drop 1).map (fun x => x.1)))⌝ -∗
          r.nv.bucket' ↦ B.bv -∗
          ([∗list] x ∈ xs, x.1 ↦ x.2.1 ∗ x.2.1.inodes' ↦* x.2.2) -∗
          ownSliceCap Inode xl.2.1.inodes' (DFrac.own 1) -∗
          pl ↦ pv' -∗ pv'.children' ↦* pcs' -∗ ownSliceCap Loc pv'.children' (DFrac.own 1) -∗
          structFieldRef Tx go!"stats" B.bv.tx' ↦ st -∗
          ⌜splitFresh B n xs pl r.nv.parent'⌝ ∗
          spillR I γd γ W txl txid (splitT T bl B r rp xs pl pv' pcs' st) ρ F (splitK K xs pl))) := by
  rw [hbk, htx]
  have hn' : Std.get? B.ns n = some r := hn
  have eT : ({ setB T bl B with t := { T.t with stats' := T.t.stats' } } : WTx) = T := by
    unfold setB; rw [GMap.insert_id _ _ _ hB]
  have hdiff : ∀ (xs : List (Loc × node × List Inode)) (pl : Loc) (prec : NRec) (l : Loc),
      splitK K xs pl l ≠ K l → (B.ns !! l).isSome ∨
        ((insertAll (<[pl := prec]> B.ns) (xs.map (fun x => x.1)) (partRecs r xs)) !! l).isSome := by
    intro xs pl prec l hl
    right
    by_cases h1 : l ∈ xs.map (fun x => x.1)
    · exact insertAll_in_some _ _ _ l (by rw [List.length_map, partRecs_length]) h1
    · rw [insertAll_notin _ _ _ l h1]
      by_cases h2 : l = pl
      · subst h2; rw [GMap.lookup_insert]; rfl
      · exact absurd (splitK_out K xs pl l h1 h2) hl
  have hnin : ∀ (xs : List (Loc × node × List Inode)) (pl : Loc), splitPieces n r.nv pl r.ins xs →
      n ∈ xs.map (fun x => x.1) := by
    intro xs pl hsp
    obtain ⟨-, ⟨x0, rest, rfl, hx0, -⟩, -⟩ := hsp
    rw [← hx0]; exact List.mem_cons_self
  iintro HR
  icases spillR_bkt_st I γd γ W txl txid T ρ F K bl B hB $$ HR with ⟨Hb, Hc, Hst, Hback⟩
  isimp only [bktOwnX] at Hb
  icases Hb with ⟨Hbv, Hib, Hnm, Hbm, Hpg, Hns⟩
  icases (BigSepM.bigSepM_delete (M := GMap Loc) (Φ := fun l r => nodeOwnX (GF := GF) W l r) hn').1 $$ Hns
    with ⟨Hn, Hns⟩
  isimp only [capsKN] at Hc
  icases (BigSepM.bigSepM_delete (M := GMap Loc)
    (Φ := fun l r => if K l then iprop(emp) else capOwn (GF := GF) r) hn').1 $$ Hc with ⟨Hcn, Hc⟩
  isimp only [hK, Bool.false_eq_true, ite_false, capOwn] at Hcn
  isimp only [nodeOwnX] at Hn
  icases Hn with ⟨Hn, Hins, Hents, Hch, Hchc, Hkey⟩
  by_cases hp : r.nv.parent' = null
  · have hpo : parentOwn (GF := GF) r.nv.parent' rp.nv rp.cs = iprop(emp) := by
      unfold parentOwn; rw [if_pos hp]
    rw [hpo]
    isplitl [Hn Hins Hcn Hbv Hst]
    · iframe
    isplit
    · iintro ⟨Hn, Hins, Hcn, Hbv, Hst, -⟩
      ihave Hb' : bktOwnX W bl B $$ [Hbv Hib Hnm Hbm Hpg Hns Hn Hins Hents Hch Hchc Hkey]
      · unfold bktOwnX
        iframe Hbv Hib Hnm Hbm Hpg
        iapply (BigSepM.bigSepM_delete (M := GMap Loc) (Φ := fun l r => nodeOwnX (GF := GF) W l r) hn').2
        iframe Hns
        unfold nodeOwnX
        iframe
      ihave Hc' : capsKN K B.ns $$ [Hc Hcn]
      · unfold capsKN
        iapply (BigSepM.bigSepM_delete (M := GMap Loc)
          (Φ := fun l r => if K l then iprop(emp) else capOwn (GF := GF) r) hn').2
        iframe Hc
        isimp only [hK, Bool.false_eq_true, ite_false, capOwn]
        iexact Hcn
      ihave HR := Hback $$ %B %K %T.t.stats' %(fun l h => absurd rfl h) Hb' Hc' Hst
      isimp only [eT] at HR
      iexact HR
    · iintro %xs %pl %pv' %pcs' %xl %st %hsf Hbk Hparts Hxlc Hpl Hpch Hpcc Hst
      obtain ⟨-, hsp, hlast, -, hcase⟩ := hsf
      obtain ⟨-, hpv, -⟩ := hcase.resolve_right (fun h => h.1 hp)
      icases nodes_excl W (Std.delete B.ns n) pl pv' $$ [Hns Hpl] with ⟨%hpl1, Hns, Hpl⟩
      · iframe
      icases nodes_excl_parts W (Std.delete B.ns n) (fun x => iprop(x.2.1.inodes' ↦* x.2.2)) xs $$ [Hns Hparts]
        with ⟨%hfr, Hns, Hparts⟩
      · iframe
      icases node_excl_parts (fun x => iprop(x.2.1.inodes' ↦* x.2.2)) pl pv' xs $$ [Hpl Hparts]
        with ⟨%hpl2, Hpl, Hparts⟩
      · iframe
      icases parts_nodup (fun x => iprop(x.2.1.inodes' ↦* x.2.2)) xs $$ Hparts with ⟨%hnd, Hparts⟩
      have hin : pv'.inodes' = slice.nil := by rw [hpv]; rfl
      have hky : pv'.key' = slice.nil := by rw [hpv]; rfl
      ihave Hprec : nodeOwnX W pl ⟨pv', [], [], pcs', [], Src.own (DFrac.own 1)⟩ $$ [Hpl Hpch Hpcc]
      · unfold nodeOwnX
        simp only
        rw [hin, hky]
        iframe
        isplitl []
        · iapply ownSlice_nil
        isplitl []
        · iapply BigSepL2.bigSepL2_nil.2; iempintro
        simp only [ite_true]
        ipureintro; trivial
      ihave Hpc : capOwn (GF := GF) (⟨pv', [], [], pcs', [], Src.own (DFrac.own 1)⟩ : NRec) $$ []
      · unfold capOwn; simp only; rw [hin]; iapply ownSliceCap_nil
      have hD2 : ∀ k, k ∉ xs.map (fun x => x.1) → k ≠ pl →
          B.ns !! k = (Std.delete B.ns n : GMap Loc NRec) !! k := by
        intro k hk _
        have : n ≠ k := fun e => hk (e ▸ hnin xs pl hsp)
        exact (GMap.lookup_delete_ne _ this).symm
      icases split_assemble W K n pl r ⟨pv', [], [], pcs', [], Src.own (DFrac.own 1)⟩ xs xl
        (Std.delete B.ns n) B.ns hsp hlast hnd hfr hpl2 hpl1 hD2
        $$ [Hns Hc Hprec Hpc Hparts Hents Hch Hchc Hkey Hxlc] with ⟨Hns', Hc'⟩
      · iframe
      have e : splitT T bl B r rp xs pl pv' pcs' st =
          ({ (setB T bl ({ B with ns := (insertAll (<[pl := (⟨pv', [], [], pcs', [], Src.own (DFrac.own 1)⟩ : NRec)]> B.ns) (xs.map (fun x => x.1)) (partRecs r xs)) } : BRec)) with
              t := { T.t with stats' := st } } : WTx) := by
        unfold splitT splitNs parentRec setB; rw [if_pos hp]
      rw [e]
      isplitr
      · ipureintro
        have hn_ids := hnin xs pl hsp
        refine ⟨fun x hx hxn => ?_, fun _ => ?_, hpl2, hnd⟩
        · have := hfr x hx
          rwa [show (Std.delete B.ns n : GMap Loc NRec) !! x.1 = B.ns !! x.1 from
            GMap.lookup_delete_ne _ (Ne.symm hxn)] at this
        · have hpn : n ≠ pl := fun e => hpl2 (e ▸ hn_ids)
          have := hpl1
          rwa [show (Std.delete B.ns n : GMap Loc NRec) !! pl = B.ns !! pl from
            GMap.lookup_delete_ne _ hpn] at this
      iapply Hback $$ %({ B with ns := (insertAll (<[pl := (⟨pv', [], [], pcs', [], Src.own (DFrac.own 1)⟩ : NRec)]> B.ns) (xs.map (fun x => x.1)) (partRecs r xs)) } : BRec)
        %(splitK K xs pl) %st %(hdiff xs pl (⟨pv', [], [], pcs', [], Src.own (DFrac.own 1)⟩ : NRec)) [Hbk Hib Hnm Hbm Hpg Hns'] Hc' Hst
      unfold bktOwnX
      iframe Hbk Hib Hnm Hbm Hns'
      iapply (BiEntails.of_eq (pageOwn_ns (GF := GF) W B _)).2
      iexact Hpg
  · obtain ⟨hrp, hpn⟩ := hpl hp
    have hrp' : Std.get? (Std.delete B.ns n) r.nv.parent' = some rp := by
      show (GMap.delete n B.ns : GMap Loc NRec) !! r.nv.parent' = some rp
      rw [GMap.lookup_delete_ne _ (Ne.symm hpn)]; exact hrp
    icases (BigSepM.bigSepM_delete (M := GMap Loc) (Φ := fun l r => nodeOwnX (GF := GF) W l r) hrp').1 $$ Hns
      with ⟨Hp, Hns⟩
    icases (BigSepM.bigSepM_delete (M := GMap Loc)
      (Φ := fun l r => if K l then iprop(emp) else capOwn (GF := GF) r) hrp').1 $$ Hc with ⟨Hcp, Hc⟩
    isimp only [hKp hp, Bool.false_eq_true, ite_false, capOwn] at Hcp
    isimp only [nodeOwnX] at Hp
    icases Hp with ⟨Hpn, Hpins, Hpents, Hpch, Hpchc, Hpkey⟩
    have hpo : parentOwn (GF := GF) r.nv.parent' rp.nv rp.cs =
        iprop(r.nv.parent' ↦ rp.nv ∗ rp.nv.children' ↦* rp.cs ∗ ownSliceCap Loc rp.nv.children' (DFrac.own 1)) := by
      unfold parentOwn; rw [if_neg hp]
    rw [hpo]
    isplitl [Hn Hins Hcn Hbv Hst Hpn Hpch Hpchc]
    · iframe
    isplit
    · iintro ⟨Hn, Hins, Hcn, Hbv, Hst, Hpn, Hpch, Hpchc⟩
      ihave Hb' : bktOwnX W bl B $$ [Hbv Hib Hnm Hbm Hpg Hns Hn Hins Hents Hch Hchc Hkey Hpn Hpins Hpents Hpch Hpchc Hpkey]
      · unfold bktOwnX
        iframe Hbv Hib Hnm Hbm Hpg
        iapply (BigSepM.bigSepM_delete (M := GMap Loc) (Φ := fun l r => nodeOwnX (GF := GF) W l r) hn').2
        isplitl [Hn Hins Hents Hch Hchc Hkey]
        · unfold nodeOwnX; iframe
        iapply (BigSepM.bigSepM_delete (M := GMap Loc) (Φ := fun l r => nodeOwnX (GF := GF) W l r) hrp').2
        iframe Hns
        unfold nodeOwnX
        iframe
      ihave Hc' : capsKN K B.ns $$ [Hc Hcn Hcp]
      · unfold capsKN
        iapply (BigSepM.bigSepM_delete (M := GMap Loc)
          (Φ := fun l r => if K l then iprop(emp) else capOwn (GF := GF) r) hn').2
        isplitl [Hcn]
        · isimp only [hK, Bool.false_eq_true, ite_false, capOwn]; iexact Hcn
        iapply (BigSepM.bigSepM_delete (M := GMap Loc)
          (Φ := fun l r => if K l then iprop(emp) else capOwn (GF := GF) r) hrp').2
        iframe Hc
        isimp only [hKp hp, Bool.false_eq_true, ite_false, capOwn]
        iexact Hcp
      ihave HR := Hback $$ %B %K %T.t.stats' %(fun l h => absurd rfl h) Hb' Hc' Hst
      isimp only [eT] at HR
      iexact HR
    · iintro %xs %pl %pv' %pcs' %xl %st %hsf Hbk Hparts Hxlc Hpl Hpch Hpcc Hst
      obtain ⟨-, hsp, hlast, -, hcase⟩ := hsf
      obtain ⟨-, hpleq, hpv, -⟩ := hcase.resolve_left (fun h => hp h.1)
      icases nodes_excl_parts W (Std.delete (Std.delete B.ns n) r.nv.parent')
        (fun x => iprop(x.2.1.inodes' ↦* x.2.2)) xs $$ [Hns Hparts] with ⟨%hfr, Hns, Hparts⟩
      · iframe
      icases node_excl_parts (fun x => iprop(x.2.1.inodes' ↦* x.2.2)) pl pv' xs $$ [Hpl Hparts]
        with ⟨%hpl2, Hpl, Hparts⟩
      · iframe
      icases parts_nodup (fun x => iprop(x.2.1.inodes' ↦* x.2.2)) xs $$ Hparts with ⟨%hnd, Hparts⟩
      have hpl1 : (Std.delete (Std.delete B.ns n) r.nv.parent' : GMap Loc NRec) !! pl = none := by
        rw [hpleq]; exact GMap.lookup_delete _ _
      have hin : pv'.inodes' = rp.nv.inodes' := by rw [hpv]
      have hky : pv'.key' = rp.nv.key' := by rw [hpv]
      ihave Hprec : nodeOwnX W pl { rp with nv := pv', cs := pcs' } $$ [Hpl Hpch Hpcc Hpins Hpents Hpkey]
      · unfold nodeOwnX
        simp only
        rw [hin, hky]
        iframe
      ihave Hpc : capOwn (GF := GF) ({ rp with nv := pv', cs := pcs' } : NRec) $$ [Hcp]
      · unfold capOwn; simp only; rw [hin]; iexact Hcp
      have hD2 : ∀ k, k ∉ xs.map (fun x => x.1) → k ≠ pl →
          B.ns !! k = (Std.delete (Std.delete B.ns n) r.nv.parent' : GMap Loc NRec) !! k := by
        intro k hk hkp
        have h1 : n ≠ k := fun e => hk (e ▸ hnin xs pl hsp)
        have h2 : r.nv.parent' ≠ k := fun e => hkp (by rw [hpleq, e])
        show B.ns !! k = (GMap.delete r.nv.parent' (GMap.delete n B.ns) : GMap Loc NRec) !! k
        rw [GMap.lookup_delete_ne _ h2, GMap.lookup_delete_ne _ h1]
      icases split_assemble W K n pl r { rp with nv := pv', cs := pcs' } xs xl
        (Std.delete (Std.delete B.ns n) r.nv.parent') B.ns hsp hlast hnd hfr hpl2 hpl1 hD2
        $$ [Hns Hc Hprec Hpc Hparts Hents Hch Hchc Hkey Hxlc] with ⟨Hns', Hc'⟩
      · iframe
      have e : splitT T bl B r rp xs pl pv' pcs' st =
          ({ (setB T bl ({ B with ns := (insertAll (<[pl := ({ rp with nv := pv', cs := pcs' } : NRec)]> B.ns) (xs.map (fun x => x.1)) (partRecs r xs)) } : BRec)) with
              t := { T.t with stats' := st } } : WTx) := by
        unfold splitT splitNs parentRec setB; rw [if_neg hp]
      rw [e]
      isplitr
      · ipureintro
        refine ⟨fun x hx hxn => ?_, fun h => absurd h hp, hpl2, hnd⟩
        have hxp : r.nv.parent' ≠ x.1 := fun e => hpl2 (by rw [hpleq, e]; exact List.mem_map.2 ⟨x, hx, rfl⟩)
        have := hfr x hx
        rwa [show (Std.delete (Std.delete B.ns n) r.nv.parent' : GMap Loc NRec) !! x.1 = B.ns !! x.1 from by
          show (GMap.delete r.nv.parent' (GMap.delete n B.ns)) !! x.1 = _
          rw [GMap.lookup_delete_ne _ hxp, GMap.lookup_delete_ne _ (Ne.symm hxn)]] at this
      iapply Hback $$ %({ B with ns := (insertAll (<[pl := ({ rp with nv := pv', cs := pcs' } : NRec)]> B.ns) (xs.map (fun x => x.1)) (partRecs r xs)) } : BRec)
        %(splitK K xs pl) %st %(hdiff xs pl ({ rp with nv := pv', cs := pcs' } : NRec)) [Hbk Hib Hnm Hbm Hpg Hns'] Hc' Hst
      unfold bktOwnX
      iframe Hbk Hib Hnm Hbm Hns'
      iapply (BiEntails.of_eq (pageOwn_ns (GF := GF) W B _)).2
      iexact Hpg



end own

end bbolt
end EtcdGrove
end Perennial
