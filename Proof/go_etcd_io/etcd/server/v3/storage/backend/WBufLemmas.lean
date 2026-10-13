/-
Lemmas on a writable buckets map (`ownBks`), for the write buffer's proofs
(`txWriteBuffer__*.lean`). Lean-first (no Rocq counterpart); see `InvBuffer.lean`.

`ownBks m B` is split into the map's points-to `m ↦$ M` (`M` the buffers' pointers by id) and
`bksOwn M B`, the buffers: a buffer is taken out of it and put back (`bksOwn_acc`), added
(`bksOwn_insert`) or removed (`bksOwn_delete`) with the map's insertion and deletion.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBuffer

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace backend

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.backend

/-! ## Pure facts -/

/-- A key at index `i` of a list without duplicates is not among the first `i`. -/
theorem not_mem_take_of_getElem?' {α} {l : List α} {i : Nat} {a : α} (hnd : l.Nodup)
    (h : l[i]? = some a) : a ∉ l.take i := by
  intro hmem
  have hl := List.take_append_drop i l
  have hd : a ∈ l.drop i := by
    rw [List.mem_iff_getElem?]; exact ⟨0, by rw [List.getElem?_drop]; simpa using h⟩
  rw [← hl, List.nodup_append] at hnd
  exact hnd.2.2 _ hmem _ hd rfl

theorem take_succ_of_getElem? {α} {l : List α} {i : Nat} {a : α} (h : l[i]? = some a) :
    l.take (i + 1) = l.take i ++ [a] := by
  rw [List.take_add_one, h]; rfl

/-- A reset bucket is empty. -/
theorem bksReset_lookup_some {B : GMap w64 (List Ent)} {id : w64} {es : List Ent}
    (h : bksReset B !! id = some es) : es = [] := by
  unfold bksReset at h
  rw [GMap.lookup_fmap] at h
  cases h' : (GMap.filter (fun _ es => !es.isEmpty) B) !! id with
  | none => rw [h'] at h; cases h
  | some _ => rw [h'] at h; cases h; rfl

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- The buffers of a writable buckets map whose pointers are `M`, holding `B`. -/
def bksOwn (M : GMap w64 Loc) (B : GMap w64 (List Ent)) : IProp GF :=
  iprop(∃ P : BksPhys, ⌜M = P.fmap Prod.fst⌝ ∗
    ([∗map] _id ↦ x;es ∈ P;B, bbAt x.1 (DFrac.own 1) x.2 es) ∗
    ⌜∀ id x es, P.lookup id = some x → B.lookup id = some es → bbOk x.2 es⌝)

theorem ownBks_open (m : GoMap) (B : GMap w64 (List Ent)) :
    ownBks (GF := GF) m B ⊢ ∃ M, m ↦$ M ∗ bksOwn M B := by
  iintro H
  unfold ownBks bksAt
  icases H with ⟨%P, ⟨Hm, Hs⟩, %Hok⟩
  iexists P.fmap Prod.fst
  iframe Hm
  unfold bksOwn
  iexists P
  iframe Hs
  ipureintro
  exact ⟨rfl, Hok⟩

theorem ownBks_close (m : GoMap) (M : GMap w64 Loc) (B : GMap w64 (List Ent)) :
    (m ↦$ M : IProp GF) ∗ bksOwn M B ⊢ ownBks m B := by
  iintro ⟨Hm, H⟩
  unfold bksOwn
  icases H with ⟨%P, %HM, Hs, %Hok⟩
  subst HM
  unfold ownBks bksAt
  iexists P
  iframe Hm Hs
  ipureintro
  exact Hok

/-- The pointers and the buffers have the same ids. -/
theorem bksOwn_dom (M : GMap w64 Loc) (B : GMap w64 (List Ent)) :
    bksOwn (GF := GF) M B ⊢ ⌜∀ id, (M !! id).isSome = (B !! id).isSome⌝ := by
  iintro H
  unfold bksOwn
  icases H with ⟨%P, %HM, Hs, -⟩
  ihave %Hiff := BigSepM2.bigSepM2_lookup_iff $$ Hs
  ipureintro
  intro id
  subst HM
  rw [GMap.lookup_fmap, Option.isSome_map]
  exact Bool.eq_iff_iff.2 (Hiff id)

theorem bksOwn_none {M : GMap w64 Loc} {B : GMap w64 (List Ent)} {id : w64}
    (Hdom : ∀ id, (M !! id).isSome = (B !! id).isSome) (h : M !! id = none) : B !! id = none := by
  have := Hdom id
  rw [h] at this
  cases hB : B !! id with
  | none => rfl
  | some _ => rw [hB] at this; cases this

theorem bksOwn_some {M : GMap w64 Loc} {B : GMap w64 (List Ent)} {id : w64} {bb : Loc}
    (Hdom : ∀ id, (M !! id).isSome = (B !! id).isSome) (h : M !! id = some bb) :
    ∃ es, B !! id = some es := by
  have := Hdom id
  rw [h] at this
  cases hB : B !! id with
  | none => rw [hB] at this; cases this
  | some es => exact ⟨es, rfl⟩

/-- Take a buffer out, and put it back with other entries. -/
theorem bksOwn_acc {M : GMap w64 Loc} {B : GMap w64 (List Ent)} {id : w64} {bb : Loc}
    {es : List Ent} (h1 : M !! id = some bb) (h2 : B !! id = some es) :
    bksOwn (GF := GF) M B ⊢
      ownBB bb es ∗ (∀ es', ownBB bb es' -∗ bksOwn M (<[id := es']> B)) := by
  iintro H
  unfold bksOwn
  icases H with ⟨%P, %HM, Hs, %Hok⟩
  subst HM
  obtain ⟨x, hx, hxb⟩ : ∃ x, P !! id = some x ∧ x.1 = bb := by
    rw [GMap.lookup_fmap] at h1
    cases hP : P !! id with
    | none => rw [hP] at h1; cases h1
    | some x => rw [hP] at h1; cases h1; exact ⟨x, rfl, rfl⟩
  icases BigSepM2.bigSepM2_insert_acc (Φ := fun _ (x : Loc × BBPhys) es =>
      bbAt (GF := GF) x.1 (DFrac.own 1) x.2 es) (m1 := P) (m2 := B) hx h2 $$ Hs with ⟨Hb, Hback⟩
  isplitl [Hb]
  · unfold ownBB
    iexists x.2
    rw [← hxb]
    iframe Hb
    ipureintro
    exact Hok id x es hx h2
  iintro %es' Hb
  unfold ownBB
  icases Hb with ⟨%p', Hb, %Hok'⟩
  ihave Hs := Hback $$ %(bb, p') %es' Hb
  iexists <[id := (bb, p')]> P
  iframe Hs
  ipureintro
  constructor
  · rw [GMap.fmap_insert, GMap.insert_id _ _ _ (by rw [GMap.lookup_fmap, hx, Option.map_some, hxb])]
  · intro id' x' es'' hx' hes
    by_cases he : id = id'
    · subst he
      rw [GMap.lookup_insert] at hx' hes
      cases hx'; cases hes
      exact Hok'
    · rw [GMap.lookup_insert_ne _ _ he] at hx' hes
      exact Hok id' x' es'' hx' hes

/-- Add a buffer under a new id. -/
theorem bksOwn_insert {M : GMap w64 Loc} {B : GMap w64 (List Ent)} {id : w64} {bb : Loc}
    {es : List Ent} (h : M !! id = none) :
    bksOwn (GF := GF) M B ∗ ownBB bb es ⊢ bksOwn (<[id := bb]> M) (<[id := es]> B) := by
  iintro ⟨H, Hb⟩
  ihave %Hdom := bksOwn_dom M B $$ H
  have hB := bksOwn_none Hdom h
  unfold bksOwn
  icases H with ⟨%P, %HM, Hs, %Hok⟩
  subst HM
  have hP : P !! id = none := by
    rw [GMap.lookup_fmap] at h
    cases hP : P !! id with
    | none => rfl
    | some _ => rw [hP] at h; cases h
  unfold ownBB
  icases Hb with ⟨%p, Hb, %Hokb⟩
  iexists <[id := (bb, p)]> P
  isplitr
  · ipureintro; rw [GMap.fmap_insert]
  isplitl
  · iapply (BigSepM2.bigSepM2_insert (Φ := fun _ (x : Loc × BBPhys) es =>
      bbAt (GF := GF) x.1 (DFrac.own 1) x.2 es) (m1 := P) (m2 := B) hP hB).2
    iframe Hb Hs
  ipureintro
  intro id' x' es' hx' hes
  by_cases he : id = id'
  · subst he
    rw [GMap.lookup_insert] at hx' hes
    cases hx'; cases hes
    exact Hokb
  · rw [GMap.lookup_insert_ne _ _ he] at hx' hes
    exact Hok id' x' es' hx' hes

/-- Remove a buffer. -/
theorem bksOwn_delete {M : GMap w64 Loc} {B : GMap w64 (List Ent)} {id : w64} {bb : Loc}
    {es : List Ent} (h1 : M !! id = some bb) (h2 : B !! id = some es) :
    bksOwn (GF := GF) M B ⊢ ownBB bb es ∗ bksOwn (GMap.delete id M) (GMap.delete id B) := by
  iintro H
  unfold bksOwn
  icases H with ⟨%P, %HM, Hs, %Hok⟩
  subst HM
  obtain ⟨x, hx, hxb⟩ : ∃ x, P !! id = some x ∧ x.1 = bb := by
    rw [GMap.lookup_fmap] at h1
    cases hP : P !! id with
    | none => rw [hP] at h1; cases h1
    | some x => rw [hP] at h1; cases h1; exact ⟨x, rfl, rfl⟩
  icases (BigSepM2.bigSepM2_delete (Φ := fun _ (x : Loc × BBPhys) es =>
      bbAt (GF := GF) x.1 (DFrac.own 1) x.2 es) (m1 := P) (m2 := B) hx h2).1 $$ Hs with ⟨Hb, Hs⟩
  isplitl [Hb]
  · unfold ownBB
    iexists x.2
    rw [← hxb]
    iframe Hb
    ipureintro
    exact Hok id x es hx h2
  iexists GMap.delete id P
  iframe Hs
  ipureintro
  constructor
  · rw [GMap.fmap_delete]
  · intro id' x' es' hx' hes
    by_cases he : id = id'
    · subst he
      rw [GMap.lookup_delete] at hx'
      cases hx'
    · rw [GMap.lookup_delete_ne _ he] at hx' hes
      exact Hok id' x' es' hx' hes

end defs

end backend
end EtcdGrove
end Perennial
