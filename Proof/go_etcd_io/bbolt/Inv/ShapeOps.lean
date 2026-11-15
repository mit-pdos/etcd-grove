/-
**Keeping the writer's page tokens** (batch 37 item 14; `notes/bbolt-proof-plan.md`, "txShape
preservation"). `txShape γ X extra` (`Inv/Shape`, in the writer's exclusive part `txExcl` and in
`wtxEnd`) holds one token per position of the records `X`; every operation that changes the
records (a materialization, an entry put or delete, a bucket's open, create or drop) must carry
it to the new records `X'`.

The design: the tokens are a **list of page ids** (`txTokL X`: per bucket `bktTokL`, per node
`nodeTokL`, per leaf entry `entTokL`, per branch entry `brTokL`, mirroring `bktToks`/`nodeToks`
with lists for `∗`), and `bktToks γ v B ⊣⊢ [∗list] id ∈ bktTokL v B, id ↪[γ] ()`
(`bktToks_list`). The tokens are exclusive, so the list of `X` has no duplicate
(`toks_nodup`). Then one general lemma, **`txShape_sub`**, keeps `txShape` from `X` to any `X'`
on the same pages whose token list is a sub-multiset of `X`'s when `X`'s has no duplicate (the
tokens of freed pages are dropped). Each operation proves only a fact about lists: the
structural ones are here (`txTokL_setBkt_sub`, `txTokL_setNode_sub`, the leaf-entry lemmas
`entsTokL_wsPutAt_sub`/`entsTokL_wsDelAt_sub`); the ones that need the view's shape in
`Inv/ShapeOpsMat` (materialization), `Inv/ShapeOpsOpen` (a bucket's open) and
`Inv/ShapeOpsBkt` (create, drop).
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Shape
public import Proof.go_etcd_io.bbolt.Model.WOps
public import Batteries.Data.List.Perm

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt


open Iris Iris.BI Iris.Std go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section tokl
variable [GooseExts]

open Classical

/-- The ids of the pages `P` (its keys, in `toList`'s order). -/
def pgIds (P : Pages) : List Nat := (FiniteMap.toList P).map Prod.fst

/-- The tokens of a leaf entry of bucket `B`: a stored nested bucket (not opened) owns its tree. -/
def entTokL (v : View) (B : BRec) (w : WEntry) : List Nat :=
  if isBktFlag w.flags ∧ inBucketRoot w.value ≠ 0 ∧ ¬ opened B w.key then
    pgIds (treePages v.pages (inBucketRoot w.value)) else []

/-- The tokens of a branch entry of bucket `B`: a child not materialized owns its subtree. -/
def brTokL (v : View) (B : BRec) (w : WEntry) : List Nat :=
  if B.nm !! w.pgid = none then pgIds (xPages v.pages (opened B) w.pgid.toNat) else []

/-- The tokens of a node's own page. -/
def ownTokL (v : View) (r : NRec) : List Nat :=
  if r.nv.pgid' = W64 0 then [] else
    pgIds (GMap.filter (fun id _ => decide (id = r.nv.pgid'.toNat)) v.pages)

/-- The tokens of a node's entries. -/
def entsTokL (v : View) (B : BRec) (leaf : Bool) (ws : List WEntry) : List Nat :=
  ws.flatMap (fun w => if leaf = true then entTokL v B w else brTokL v B w)

/-- **A node's tokens** (`nodeToks`'s): its own page's, and its entries'. -/
def nodeTokL (v : View) (B : BRec) (r : NRec) : List Nat :=
  ownTokL v r ++ entsTokL v B r.nv.isLeaf' r.ws

/-- **A bucket's tokens** (`bktToks`'s). -/
def bktTokL (v : View) (B : BRec) : List Nat :=
  if B.bv.rootNode' = null then
    (if B.ib.root' = W64 0 then [] else pgIds (xPages v.pages (opened B) B.ib.root'.toNat))
  else (FiniteMap.toList B.ns).flatMap (fun p => nodeTokL v B p.2)

/-- The tokens of the buckets `bs`. -/
def bktsTokL (v : View) (bs : GMap Loc BRec) : List Nat :=
  (FiniteMap.toList bs).flatMap (fun p => bktTokL v p.2)

/-- **The records' tokens** (`txShape`'s big separating conjunction's). -/
def txTokL (X : WX) : List Nat := bktsTokL X.v X.t.bs

end tokl

/-! ## Lists -/

section lists

theorem subperm_append' {α : Type _} {l1 l2 l3 l4 : List α} (h1 : l1.Subperm l2)
    (h2 : l3.Subperm l4) : (l1 ++ l3).Subperm (l2 ++ l4) :=
  ((List.subperm_append_right l3).2 h1).trans ((List.subperm_append_left l2).2 h2)

/-- Pointwise sub-multisets give a sub-multiset of the concatenation. -/
theorem flatMap_subperm {α β : Type _} (l : List α) (f g : α → List β)
    (h : ∀ x ∈ l, (f x).Subperm (g x)) : (l.flatMap f).Subperm (l.flatMap g) := by
  induction l with
  | nil => exact List.Subperm.refl _
  | cons a l ih =>
    simp only [List.flatMap_cons]
    exact subperm_append' (h a (List.mem_cons_self ..))
      (ih fun x hx => h x (List.mem_cons_of_mem _ hx))

/-- Dropping one more element drops its contribution. -/
theorem flatMap_drop_succ_subperm {α β : Type _} (l : List α) (i : Nat) (f : α → List β) :
    ((l.drop (i + 1)).flatMap f).Subperm ((l.drop i).flatMap f) := by
  have e : l.drop i = (l.drop i).take 1 ++ l.drop (i + 1) := by
    conv => lhs; rw [← List.take_append_drop 1 (l.drop i)]
    rw [List.drop_drop]
  conv => rhs; rw [e, List.flatMap_append]
  exact (List.sublist_append_right _ _).subperm

variable {K : Type _} [DecidableEq K] {V : Type _}

/-- A map's list with `k`'s binding first. -/
theorem toList_lookup_perm (m : GMap K V) (k : K) (v : V) (h : m !! k = some v) :
    (FiniteMap.toList m).Perm ((k, v) :: FiniteMap.toList (GMap.delete k m)) :=
  LawfulFiniteMap.toList_delete (M := GMap K) h

/-- A map with `k` bound to `v`: its list is `(k, v)` and the rest's. -/
theorem toList_insert_perm_gm (m : GMap K V) (k : K) (v : V) :
    (FiniteMap.toList (m.insert k v)).Perm ((k, v) :: FiniteMap.toList (GMap.delete k m)) := by
  have e : m.insert k v = (GMap.delete k m).insert k v := (GMap.insert_delete m k v).symm
  rw [e]
  exact LawfulFiniteMap.toList_insert (M := GMap K) (GMap.lookup_delete _ _)

theorem flatMap_perm {α β : Type _} {l l' : List α} (f : α → List β) (h : l.Perm l') :
    (l.flatMap f).Perm (l'.flatMap f) := h.flatMap_right f

/-- **Replacing a binding**: the list of `m.insert k v'` under `f` is a sub-multiset of `m`'s
under `g` when `k`'s new contribution is below its old one and every other binding's is. -/
theorem flatMap_insert_subperm {β : Type _} (m : GMap K V) (k : K) (v v' : V)
    (f g : K × V → List β) (hk : m !! k = some v) (hkv : (f (k, v')).Subperm (g (k, v)))
    (ho : ∀ k' w, k' ≠ k → m !! k' = some w → (f (k', w)).Subperm (g (k', w))) :
    ((FiniteMap.toList (m.insert k v')).flatMap f).Subperm ((FiniteMap.toList m).flatMap g) := by
  refine ((flatMap_perm f (toList_insert_perm_gm m k v')).subperm).trans ?_
  refine List.Subperm.trans ?_ ((flatMap_perm g (toList_lookup_perm m k v hk)).symm.subperm)
  simp only [List.flatMap_cons]
  refine subperm_append' hkv (flatMap_subperm _ _ _ fun ⟨k', w⟩ hx => ?_)
  have hx' : (GMap.delete k m) !! k' = some w := (GMap.mem_toList _ _ _).1 hx
  have hne : k' ≠ k := by
    intro e; subst e; rw [GMap.lookup_delete] at hx'; cases hx'
  rw [GMap.lookup_delete_ne _ (Ne.symm hne)] at hx'
  exact ho k' w hne hx'

/-- **Adding a binding at a fresh key and replacing another**: `k` new (`f (k, a)`), `j`
replaced; together below `j`'s old contribution, every other binding's below its old one. -/
theorem flatMap_insert2_subperm {β : Type _} (m : GMap K V) (k j : K) (a v v' : V)
    (f g : K × V → List β) (hkj : k ≠ j) (hk : m !! k = none) (hj : m !! j = some v)
    (hkv : (f (k, a) ++ f (j, v')).Subperm (g (j, v)))
    (ho : ∀ k' w, k' ≠ j → m !! k' = some w → (f (k', w)).Subperm (g (k', w))) :
    ((FiniteMap.toList ((m.insert j v').insert k a)).flatMap f).Subperm
      ((FiniteMap.toList m).flatMap g) := by
  have hk' : (m.insert j v') !! k = none := by
    rw [GMap.lookup_insert_ne _ _ (Ne.symm hkj)]; exact hk
  refine ((flatMap_perm f (LawfulFiniteMap.toList_insert (M := GMap K) hk')).subperm).trans ?_
  refine ((flatMap_perm f ((toList_insert_perm_gm m j v').cons _)).subperm).trans ?_
  refine List.Subperm.trans ?_ ((flatMap_perm g (toList_lookup_perm m j v hj)).symm.subperm)
  simp only [List.flatMap_cons, ← List.append_assoc]
  refine subperm_append' hkv (flatMap_subperm _ _ _ fun ⟨k', w⟩ hx => ?_)
  have hx' : (GMap.delete j m) !! k' = some w := (GMap.mem_toList _ _ _).1 hx
  have hne : k' ≠ j := by
    intro e; subst e; rw [GMap.lookup_delete] at hx'; cases hx'
  rw [GMap.lookup_delete_ne _ (Ne.symm hne)] at hx'
  exact ho k' w hne hx'

/-- Removing a binding drops its contribution. -/
theorem flatMap_delete_subperm {β : Type _} (m : GMap K V) (k : K) (f : K × V → List β) :
    ((FiniteMap.toList (GMap.delete k m)).flatMap f).Subperm ((FiniteMap.toList m).flatMap f) := by
  cases hk : m !! k with
  | none =>
    have : GMap.delete k m = m := by
      ext k'; by_cases e : k' = k
      · subst e; rw [GMap.lookup_delete, hk]
      · rw [GMap.lookup_delete_ne _ (Ne.symm e)]
    rw [this]
  | some v =>
    refine List.Subperm.trans ?_ ((flatMap_perm f (toList_lookup_perm m k v hk)).symm.subperm)
    simp only [List.flatMap_cons]
    exact (List.sublist_append_right _ _).subperm

end lists

section pure
variable [GooseExts]

open Classical

theorem pgIds_nodup (P : Pages) : (pgIds P).Nodup := GMap.toList_keys_nodup P

theorem mem_pgIds (P : Pages) (id : Nat) : id ∈ pgIds P ↔ (P !! id).isSome := by
  unfold pgIds
  constructor
  · intro h
    obtain ⟨⟨k, pg⟩, hk, rfl⟩ := List.mem_map.1 h
    rw [(GMap.mem_toList _ _ _).1 hk]; rfl
  · intro h
    obtain ⟨pg, hpg⟩ := Option.isSome_iff_exists.1 h
    exact List.mem_map.2 ⟨(id, pg), (GMap.mem_toList _ _ _).2 hpg, rfl⟩

/-- The pages of a filter below those of a weaker filter. -/
theorem pgIds_filter_subperm (P : Pages) (p q : Nat → List w8 → Bool)
    (h : ∀ id pg, P !! id = some pg → p id pg = true → q id pg = true) :
    (pgIds (GMap.filter p P)).Subperm (pgIds (GMap.filter q P)) := by
  refine List.subperm_of_subset (pgIds_nodup _) fun id hid => ?_
  rw [mem_pgIds] at hid ⊢
  rw [GMap.lookup_filter] at hid ⊢
  cases e : P !! id with
  | none => rw [e] at hid; cases hid
  | some pg =>
    rw [e] at hid
    have hp : p id pg = true := by simpa [Option.filter] using hid
    simp [Option.filter, h id pg e hp]

/-- A list without duplicates whose elements are page ids of `P` is below `pgIds P`. -/
theorem subperm_pgIds (P : Pages) (l : List Nat) (hl : l.Nodup)
    (h : ∀ id ∈ l, (P !! id).isSome) : l.Subperm (pgIds P) :=
  List.subperm_of_subset hl fun id hid => (mem_pgIds P id).2 (h id hid)

end pure

/-! ## The tokens as a list -/

section res
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]

open Classical

/-- One token. -/
abbrev tok (γ : GName) (id : Nat) : IProp GF := iprop(id ↪[γ] ())

theorem bigSepL_congr' {A : Type _} {Φ Ψ : A → IProp GF} {l : List A}
    (h : ∀ x, Φ x ⊣⊢ Ψ x) : ([∗list] x ∈ l, Φ x) ⊣⊢ [∗list] x ∈ l, Ψ x :=
  ⟨BigSepL.bigSepL_mono_of_forall fun {_ x} => (h x).1,
   BigSepL.bigSepL_mono_of_forall fun {_ x} => (h x).2⟩

theorem pgToks_list (γ : GName) (P : Pages) :
    pgToks (GF := GF) γ P ⊣⊢ [∗list] id ∈ pgIds P, tok γ id := by
  unfold pgToks pgIds
  rw [BigSepL.bigSepL_map]
  exact BigSepM.bigSepM_toList

theorem nil_toks (γ : GName) : (emp : IProp GF) ⊣⊢ [∗list] id ∈ ([] : List Nat), tok γ id :=
  BigSepL.bigSepL_nil.symm

theorem nodeToks_list (γ : GName) (v : View) (B : BRec) (r : NRec) :
    nodeToks (GF := GF) γ v B r ⊣⊢ [∗list] id ∈ nodeTokL v B r, tok γ id := by
  unfold nodeToks nodeTokL ownTokL entsTokL
  refine (sep_congr ?_ ?_).trans BigSepL.bigSepL_append.symm
  · split
    · exact nil_toks γ
    · exact pgToks_list γ _
  · rw [BigSepL.bigSepL_flatMap]
    refine bigSepL_congr' fun w => ?_
    unfold entTokL brTokL
    split
    · split
      · exact pgToks_list γ _
      · exact nil_toks γ
    · split
      · exact pgToks_list γ _
      · exact nil_toks γ

theorem bktToks_list (γ : GName) (v : View) (B : BRec) :
    bktToks (GF := GF) γ v B ⊣⊢ [∗list] id ∈ bktTokL v B, tok γ id := by
  unfold bktToks bktTokL
  split
  · split
    · exact nil_toks γ
    · exact pgToks_list γ _
  · rw [BigSepL.bigSepL_flatMap]
    exact BigSepM.bigSepM_toList.trans (bigSepL_congr' fun p => nodeToks_list γ v B p.2)

theorem bktsToks_list (γ : GName) (v : View) (bs : GMap Loc BRec) :
    ([∗map] _bl ↦ B ∈ bs, bktToks (GF := GF) γ v B) ⊣⊢
      [∗list] id ∈ bktsTokL v bs, tok γ id := by
  unfold bktsTokL
  rw [BigSepL.bigSepL_flatMap]
  exact BigSepM.bigSepM_toList.trans (bigSepL_congr' fun p => bktToks_list γ v p.2)

open Iris.ProofMode in
/-- Two copies of one token are contradictory. -/
theorem toks_dup (γ : GName) (a : Nat) (Q : IProp GF) :
    ([∗list] id ∈ [a, a], tok γ id) ⊢ Q := by
  iintro ⟨H1, H2, -⟩
  ihave %hne := ghostMapElem_ne γ a a (DFrac.own 1) () () $$ H1 H2
  exact absurd rfl hne

open Iris.ProofMode in
/-- **The tokens are exclusive**: a list of them has no duplicate. -/
theorem toks_nodup (γ : GName) (l : List Nat) :
    ([∗list] id ∈ l, tok (GF := GF) γ id) ⊢ ⌜l.Nodup⌝ ∗ [∗list] id ∈ l, tok γ id := by
  induction l with
  | nil => iintro H; isplitr; · ipureintro; exact List.nodup_nil
           iexact H
  | cons a l ih =>
    by_cases ha : a ∈ l
    · iintro ⟨Ha, Hl⟩
      icases BigSepL.bigSepL_mem_acc ha $$ Hl with ⟨Ha', -⟩
      ihave %hne := ghostMapElem_ne γ a a (DFrac.own 1) () () $$ Ha Ha'
      exact absurd rfl hne
    · iintro ⟨Ha, Hl⟩
      icases ih $$ Hl with ⟨%hl, Hl⟩
      isplitr
      · ipureintro; exact List.nodup_cons.2 ⟨ha, hl⟩
      · iframe

open Iris.ProofMode in
/-- **The general lemma: `txShape` is kept by any change of the records on the same pages whose
tokens are a sub-multiset of the old ones** (the rest are dropped), knowing that the old ones
have no duplicate (`toks_nodup`). -/
theorem txShape_sub (γ : GName) (X X' : WX) (extra : GMap Nat Unit)
    (hp : X'.v.pages = X.v.pages) (hs : (txTokL X).Nodup → (txTokL X').Subperm (txTokL X)) :
    txShape (GF := GF) γ X extra ⊢ txShape γ X' extra := by
  unfold txShape
  iintro ⟨%M, Ha, %HM, Hb, He⟩
  iexists M
  iframe Ha He
  isplitr
  · ipureintro; intro id; rw [hp]; exact HM id
  ihave Hb := (bktsToks_list γ X.v X.t.bs).1 $$ Hb
  icases toks_nodup γ _ $$ Hb with ⟨%hnd, Hb⟩
  obtain ⟨l, hl, hsub⟩ := hs hnd
  obtain ⟨rest, hrest⟩ := hsub.exists_perm_append
  unfold txTokL at hl hrest
  iapply (bktsToks_list γ X'.v X'.t.bs).2
  iapply (BigSepL.bigSepL_perm hl).1
  iapply BigSepL.bigSepL_submseteq hrest.symm
  iexact Hb

/-- `txShape`'s tokens have no duplicate (for an operation's list reasoning). -/
theorem txShape_nodup (γ : GName) (X : WX) (extra : GMap Nat Unit) :
    txShape (GF := GF) γ X extra ⊢ ⌜(txTokL X).Nodup⌝ := by
  unfold txShape
  iintro ⟨%M, -, -, Hb, -⟩
  ihave Hb := (bktsToks_list γ X.v X.t.bs).1 $$ Hb
  icases toks_nodup γ _ $$ Hb with ⟨%hnd, -⟩
  ipureintro; exact hnd

end res

/-! ## Structural corollaries -/

section struct
variable [GooseExts]

open Classical

/-- **A bucket record replaced** (`WX.setBkt`): the new bucket's tokens below the old one's. -/
theorem txTokL_setBkt_sub (X : WX) (bl : Loc) (B B' : BRec) (hB : X.t.bs !! bl = some B)
    (h : (bktTokL X.v B').Subperm (bktTokL X.v B)) :
    (txTokL (X.setBkt bl B')).Subperm (txTokL X) :=
  flatMap_insert_subperm X.t.bs bl B B' _ _ hB h fun _ _ _ _ => List.Subperm.refl _

/-- The node tokens of a bucket with the same node cache, bucket cache and root node. -/
theorem nodeTokL_congr (v : View) (B B' : BRec) (r : NRec) (hnm : B'.nm = B.nm)
    (hbm : B'.bm = B.bm) : nodeTokL v B' r = nodeTokL v B r := by
  unfold nodeTokL entsTokL entTokL brTokL opened; rw [hnm, hbm]

/-- **A node record replaced** (`WX.setNode`): its new tokens below its old ones. -/
theorem txTokL_setNode_sub (X : WX) (bl l : Loc) (B : BRec) (r r' : NRec)
    (hB : X.t.bs !! bl = some B) (hr : B.ns !! l = some r)
    (h : (nodeTokL X.v B r').Subperm (nodeTokL X.v B r)) :
    (txTokL (X.setNode bl l r')).Subperm (txTokL X) := by
  unfold WX.setNode; rw [hB]
  refine txTokL_setBkt_sub X bl B _ hB ?_
  unfold bktTokL
  by_cases hn : B.bv.rootNode' = null
  · simp only [hn, ↓reduceIte]; exact List.Subperm.refl _
  · simp only [hn, ↓reduceIte]
    have hc : ∀ r0, nodeTokL X.v { B with ns := B.ns.insert l r' } r0 = nodeTokL X.v B r0 :=
      fun r0 => nodeTokL_congr _ _ _ _ rfl rfl
    refine flatMap_insert_subperm B.ns l r r' _ (fun p => nodeTokL X.v B p.2) hr ?_
      fun k w _ _ => ?_
    · dsimp only; rw [hc]; exact h
    · dsimp only; rw [hc]

/-- A node with the same page id and kind: its tokens are its entries'. -/
theorem nodeTokL_sub_of_ents (v : View) (B : BRec) (r r' : NRec)
    (hpg : r'.nv.pgid' = r.nv.pgid') (hlf : r'.nv.isLeaf' = r.nv.isLeaf')
    (h : (entsTokL v B r.nv.isLeaf' r'.ws).Subperm (entsTokL v B r.nv.isLeaf' r.ws)) :
    (nodeTokL v B r').Subperm (nodeTokL v B r) := by
  unfold nodeTokL ownTokL; rw [hpg, hlf]
  exact (List.subperm_append_left _).2 h

/-- `withEnts` keeps a node's page id and kind. -/
theorem nodeTokL_withEnts_sub (v : View) (B : BRec) (r : NRec) (s : GoSlice) (ins : List Inode)
    (ws' : List WEntry) (h : (entsTokL v B r.nv.isLeaf' ws').Subperm (entsTokL v B r.nv.isLeaf' r.ws)) :
    (nodeTokL v B (r.withEnts s ins ws')).Subperm (nodeTokL v B r) :=
  nodeTokL_sub_of_ents v B r _ rfl rfl h

/-- The same for `withEntsU` (`node.del`). -/
theorem nodeTokL_withEntsU_sub (v : View) (B : BRec) (r : NRec) (s : GoSlice) (ins : List Inode)
    (ws' : List WEntry) (u : Bool)
    (h : (entsTokL v B r.nv.isLeaf' ws').Subperm (entsTokL v B r.nv.isLeaf' r.ws)) :
    (nodeTokL v B (r.withEntsU s ins ws' u)).Subperm (nodeTokL v B r) :=
  nodeTokL_sub_of_ents v B r _ rfl rfl h

/-- An entry that owns no tokens: a plain entry, an inline bucket, an opened bucket. -/
def entNoTok (v : View) (B : BRec) (leaf : Bool) (e : WEntry) : Prop :=
  (if leaf = true then entTokL v B e else brTokL v B e) = []

/-- **A put of an entry that owns no tokens** (`node.put`'s `wsPutAt`: a replacement drops the
old entry's tokens, an insertion adds none). -/
theorem entsTokL_wsPutAt_sub (v : View) (B : BRec) (leaf : Bool) (ws : List WEntry)
    (k : List w8) (e : WEntry) (he : entNoTok v B leaf e) :
    (entsTokL v B leaf (wsPutAt ws k e)).Subperm (entsTokL v B leaf ws) := by
  unfold entNoTok at he
  unfold wsPutAt entsTokL
  by_cases hf : wsFound ws k
  · rw [if_pos hf, List.flatMap_append, List.flatMap_append, List.flatMap_singleton, he, List.append_nil]
    conv => rhs; rw [← List.take_append_drop (wsIdx ws k) ws, List.flatMap_append]
    exact (List.subperm_append_left _).2 (flatMap_drop_succ_subperm ws _ _)
  · rw [if_neg hf, List.flatMap_append, List.flatMap_append, List.flatMap_singleton, he,
      List.append_nil]
    conv => rhs; rw [← List.take_append_drop (wsIdx ws k) ws, List.flatMap_append]

/-- **A delete** (`node.del`'s `wsDelAt`): drops the entry's tokens. -/
theorem entsTokL_wsDelAt_sub (v : View) (B : BRec) (leaf : Bool) (ws : List WEntry)
    (k : List w8) : (entsTokL v B leaf (wsDelAt ws k)).Subperm (entsTokL v B leaf ws) := by
  unfold wsDelAt entsTokL
  by_cases hf : wsFound ws k
  · rw [if_pos hf]
    conv => rhs; rw [← List.take_append_drop (wsIdx ws k) ws, List.flatMap_append]
    rw [List.flatMap_append]
    exact (List.subperm_append_left _).2 (flatMap_drop_succ_subperm ws _ _)
  · rw [if_neg hf]

end struct

end bbolt
end EtcdGrove
end Perennial
