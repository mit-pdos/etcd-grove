/-
**Per-type prototype: `raftpb.Entry` at its wire content** (stage A prototype; the Scope's E for
`Entry`, with the coordinator's correction of 2026-11-07: proto2 presence per optional field).

- `EntryC`: `Term`, `Index`, `Type` each `nil` or a pointer to a value (zero included), `Data` `nil`
  or not (an empty non-nil `Data` has size 2, a nil one 0), and the unknown fields.
- `entRoC l c`: a frozen `*Entry` holding exactly `c`: each scalar cell `nil` or `p ↦□ v`
  (`optCell`), `Data` `nil` or a non-nil slice (Go's `== nil` is `= slice.nil`) holding its bytes
  read-only (`bytesC`), the hidden fields' invariant at `c.uf`, which gives `uf`'s validity
  (`pbMsg` records `ufWire` at the type's schema, `pbSchemaOf`: `pbMsg_uf_entry`).
- `entryEncC` (opaque) and its one trusted fact `entryEncC_ok`, backed by Go round-trip tests of
  `proto.Size` against `entrySize` and of `Unmarshal(Marshal)`.
- `pbEntryM` (the data, no axiom), `pbEntryC` (with the encoder), its registration `pbEntryC_reg`,
  and `pbEntryC_sat : pbEntryM.Sat` (`pbEntryC.data` is `pbEntryM`; whose axioms do not include `entryEncC_ok`).

**Why `ro` is not today's `entRO`.** `entRO` (`InvPb.lean`) reads a `nil` cell and a zero one
alike, and an empty non-nil `Data` as a nil one: `ro_iff` at `ro := entRO` is unprovable. (Its
unknown fields' validity it now has: `pbMsg` carries `ufWire`, CP2.) Here `ro` is
`∃ c, entRoC l c ∗ ⌜…⌝`, and `entRoC_entRO` shows it gives today's `entRO`, so its clients keep
working.
-/
module

public import Proof.google_golang_org.protobuf.proto.InvProto
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.PbMessage

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

/-- **An `Entry`'s wire content** (see the file header). -/
structure EntryC [GooseExts] where
  term : Option w64
  index : Option w64
  type : Option raftpb.EntryType
  data : Option (List w8)
  uf : List w8

/-- What the getters read of a wire content. -/
def EntryC.model [GooseExts] (c : EntryC) : EntryM :=
  ⟨c.term.getD (zero_val w64), c.index.getD (zero_val w64), c.type.getD (zero_val raftpb.EntryType),
    c.data.getD []⟩

/-- An optional varint field's size: its tag and its value. -/
def optVarintSize (o : Option Nat) : Nat := match o with | none => 0 | some n => 1 + varintSize n

/-- **protobuf's size of an `Entry`** (an enum is an `int32`, sign-extended to 64 bits). -/
def entrySize [GooseExts] (c : EntryC) : Nat :=
  optVarintSize (c.type.map fun t => (uint.Z (W64 (sint.Z t))).toNat) +
  optVarintSize (c.term.map fun v => (uint.Z v).toNat) +
  optVarintSize (c.index.map fun v => (uint.Z v).toNat) +
  (match c.data with | none => 0 | some bs => 1 + varintSize bs.length + bs.length) +
  c.uf.length

/-- **The encoding of an `Entry`'s wire content** (opaque: protobuf-go's `Marshal`). -/
opaque entryEncC [GooseExts] (c : EntryC) : List w8

/-- **The trust boundary: `Entry`'s encoding** (the type's one trusted fact). Tested in Go: the
round trip `Unmarshal(Marshal(e))` gives the getters' view, and `proto.Size(e)` is `entrySize`,
for every presence combination and for unknown fields routed as `ufWire` says. -/
axiom entryEncC_ok [GooseExts] (c : EntryC) : ufWire entrySchema c.uf → entrySize c < 2 ^ 63 →
    EntWireOk c.model (entryEncC c) ∧ (entryEncC c).length = entrySize c

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- A proto2 optional scalar's cell, frozen: `nil`, or set (possibly to zero). -/
def optCell {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] (p : Loc) : Option V → IProp GF
  | none => iprop(⌜p = null⌝)
  | some v => iprop(p ↦□ v)

/-- A `bytes` field, frozen: `nil`, or a non-nil slice holding the bytes. -/
def bytesC (ds : GoSlice) : Option (List w8) → IProp GF
  | none => iprop(⌜ds = slice.nil⌝)
  | some bs => iprop(⌜ds ≠ slice.nil⌝ ∗ ds ↦*□ bs)

instance optCell_persistent {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] (p : Loc)
    (o : Option V) : Persistent (optCell (GF := GF) p o) := by
  cases o <;> unfold optCell <;> infer_instance

instance bytesC_persistent (ds : GoSlice) (o : Option (List w8)) :
    Persistent (bytesC (GF := GF) ds o) := by
  cases o <;> unfold bytesC <;> infer_instance

/-- An entry's unknown fields are valid at `Entry`'s schema (`pbMsg`'s, `[v6a]` 3). -/
theorem pbMsg_uf_entry (l : Loc) (uf : List w8) :
    pbMsg (GF := GF) raftpb.Entry l uf ⊢ ⌜ufWire entrySchema uf⌝ := by
  have h := pbMsg_ufWire (GF := GF) raftpb.Entry l uf
  rwa [show PbGoType.goTy raftpb.Entry = raftpb.Entry.ty from rfl, pbSchemaOf_entry] at h

/-- **A frozen `*Entry` holding exactly `c`** (see the file header). -/
def entRoC (l : Loc) (c : EntryC) : IProp GF :=
  iprop(∃ (pt pi pty : Loc) (ds : GoSlice),
    ⌜l ≠ null⌝ ∗
    l.[raftpb.Entry, go!"Term"] ↦□ pt ∗ optCell pt c.term ∗
    l.[raftpb.Entry, go!"Index"] ↦□ pi ∗ optCell pi c.index ∗
    l.[raftpb.Entry, go!"Type"] ↦□ pty ∗ optCell pty c.type ∗
    l.[raftpb.Entry, go!"Data"] ↦□ ds ∗ bytesC ds c.data ∗
    pbMsg raftpb.Entry l c.uf)

set_option synthInstance.maxSize 512 in
set_option synthInstance.maxHeartbeats 200000 in
instance entRoC_persistent (l : Loc) (c : EntryC) : Persistent (entRoC (GF := GF) l c) := by
  unfold entRoC; infer_instance

theorem optCell_cellRO {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] (p : Loc) (o : Option V) :
    optCell (GF := GF) p o ⊢ cellRO p (o.getD (zero_val V)) := by
  cases o with
  | none => unfold optCell cellRO; iintro %h; ileft; ipureintro; exact ⟨h, rfl⟩
  | some v => simp only [optCell, cellRO, Option.getD_some]; iintro #h; iright; iexact h

theorem bytesC_ro (ds : GoSlice) (o : Option (List w8)) :
    bytesC (GF := GF) ds o ⊢ ds ↦*□ o.getD [] := by
  cases o with
  | none =>
    unfold bytesC; iintro %h; subst h
    simp only [Option.getD_none]
    ihave H := ownSlice_nil (V := w8) (GF := GF) DFrac.discard
    iexact H
  | some bs => simp only [bytesC, Option.getD_some]; iintro ⟨-, #H⟩; iexact H

/-- **The wire content gives today's `entRO`** (its clients keep working). -/
theorem entRoC_entRO (l : Loc) (c : EntryC) : entRoC (GF := GF) l c ⊢ entRO l c.model := by
  unfold entRoC
  iintro ⟨%pt, %pi, %pty, %ds, %Hnn, #HT, #cT, #HI, #cI, #HY, #cY, #HD, #cD, #Hpb⟩
  simp only [entRO]
  iunfold entPts
  iexists pt, pi, pty, ds, c.uf
  isplitr
  · ipureintro; exact Hnn
  ihave #cT' := optCell_cellRO pt c.term $$ cT
  ihave #cI' := optCell_cellRO pi c.index $$ cI
  ihave #cY' := optCell_cellRO pty c.type $$ cY
  ihave #cD' := bytesC_ro ds c.data $$ cD
  iframe HT HI HY HD Hpb
  simp only [EntryC.model]
  iframe cT' cI' cY' cD'

/-- **The store of an entry**: each scalar `nil` if zero, `Data` `nil` if empty. -/
def entryTree (e : EntryM) : VTree :=
  .strct raftpb.Entry.ty
    [(go!"Term", go.GoType.PointerType go.uint64), (go!"Index", go.GoType.PointerType go.uint64),
     (go!"Type", go.GoType.PointerType raftpb.EntryType.ty), (go!"Data", go.GoType.SliceType go.byte)]
    [cellTree go.uint64 e.Term', cellTree go.uint64 e.Index', cellTree raftpb.EntryType.ty e.Type',
     bytesTree go.byte e.Data']

/-- **`raftpb.Entry` at its wire content: the data** (no axiom: what `Sat` is stated over). -/
def pbEntryM : PbModelC GF where
  ty := raftpb.Entry.ty
  M := EntryM
  ro l e := iprop(∃ c, entRoC l c ∗ ⌜c.model = e⌝)
  ro_persistent _ _ := inferInstance
  marshals _ := True
  wire := EntWireOk
  eqv e e' := e = e'
  blank l := iprop(l ↦ (zero_val raftpb.Entry))
  dec l e := iprop(∃ c, entRoC l c ∗ ⌜c.model = e⌝)
  C := EntryC
  roC := entRoC
  roC_persistent _ _ := inferInstance
  modelOf := EntryC.model
  levels c := [(entrySchema, c.uf)]
  size := entrySize
  tree := entryTree
  ro_iff _ _ := .rfl
  roC_ufValid l c := by
    unfold entRoC
    iintro ⟨%pt, %pi, %pty, %ds, -, -, -, -, -, -, -, -, -, Hpb⟩
    ihave %Hu := pbMsg_uf_entry l c.uf $$ Hpb
    ipureintro
    intro p hp
    rw [List.mem_singleton] at hp
    subst hp
    exact Hu

/-- **`raftpb.Entry` at its wire content** (the registered instance): the data and the encoder,
whose `enc_ok` is the type's one trusted fact `entryEncC_ok`. -/
def pbEntryC : PbTypeC GF where
  data := pbEntryM
  encd := { enc := entryEncC
            enc_ok := fun c _ hu hs => entryEncC_ok c (hu _ (List.mem_singleton.2 rfl)) hs }

end defs

/-- **The registration** of `pbEntryC` (exact shape). -/
axiom pbEntryC_reg [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
    {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [go.Semantics] :
    pbModelOf GF raftpb.Entry.ty = some (pbEntryC (GF := GF))

/-! ## `Sat` -/

section sat
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : go_etcd_io.raft.v3.raftpb.Assumptions]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- A stored cell, frozen, at some presence. -/
theorem optCell_freeze {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] (p : Loc) (x : V) :
    (⌜p = null ∧ x = zero_val V⌝ ∨ p ↦ x : IProp GF) ⊢
      |==> ∃ o : Option V, optCell p o ∗ ⌜o.getD (zero_val V) = x⌝ := by
  iintro (%H | H)
  · imodintro; iexists none
    unfold optCell
    isplitl
    · ipureintro; exact H.1
    · ipureintro; exact H.2.symm
  · imod (typedPointsto_dfractional (GF := GF) p x).dfractional_persist _ $$ H with #H
    imodintro; iexists (some x)
    unfold optCell
    isplitl
    · iexact H
    · ipureintro; rfl

/-- A stored `bytes` field, frozen, at some nil-ness. -/
theorem bytesC_freeze (ds : GoSlice) (xs : List w8) (h : xs = [] → ds = slice.nil) :
    (ds ↦* xs : IProp GF) ⊢ |==> ∃ o : Option (List w8), bytesC ds o ∗ ⌜o.getD [] = xs⌝ := by
  iintro H
  by_cases hx : xs = []
  · subst hx
    imodintro; iexists none
    unfold bytesC
    isplitl
    · ipureintro; exact h rfl
    · ipureintro; rfl
  · ihave %Hlen := ownSlice_len _ _ _ $$ H
    imod ownSlice_persist _ _ _ $$ H with #H
    imodintro; iexists (some xs)
    unfold bytesC
    isplitl
    · isplitl
      · ipureintro
        intro hn; subst hn
        apply hx; apply List.eq_nil_of_length_eq_zero
        rw [Hlen.1]; rfl
      · iexact H
    · ipureintro; rfl

/-- **An entry's struct literal**: its value, which, stored anywhere, freezes to an entry at some
wire content with the model `e`. -/
theorem treeWp_entryTree (e : EntryM) (Φ : val → IProp GF) :
    (∀ x : raftpb.Entry, (∀ p : Loc, p ↦ x ={⊤}=∗ ∃ c, entRoC p c ∗ ⌜c.model = e⌝) -∗ Φ #x) ⊢
      treeWp (entryTree e) Φ := by
  iintro H
  simp only [entryTree, treeWp, treeWpL]
  iapply treeWp_cell
  iintro %pt Hpt
  isplitr
  · ipureintro; exact isPanic_intoVal pt
  iapply treeWp_cell
  iintro %pi Hpi
  isplitr
  · ipureintro; exact isPanic_intoVal pi
  iapply treeWp_cell
  iintro %pty Hpty
  isplitr
  · ipureintro; exact isPanic_intoVal pty
  iapply treeWp_bytes
  iintro %ds %Hds Hs -
  isplitr
  · ipureintro; exact isPanic_intoVal ds
  simp [litBody, strctKes, kesσ, envσ]
  repeat (isplitr; · ipureintro; trivial)
  wp_auto
  iapply H
  iintro %l Hl
  ihave %Hnn := typedPointsto_not_null $$ Hl
  icases typedPointsto_split _ _ _ $$ Hl with Hl
  simp only [TypedPointsto.typedPointstoDef]
  icases Hl with ⟨HS, HT, HI, HY, HD, HU, HSC, -⟩
  imod (typedPointsto_dfractional (GF := GF) _ pt).dfractional_persist _ $$ HT with #HT
  imod (typedPointsto_dfractional (GF := GF) _ pi).dfractional_persist _ $$ HI with #HI
  imod (typedPointsto_dfractional (GF := GF) _ pty).dfractional_persist _ $$ HY with #HY
  imod (typedPointsto_dfractional (GF := GF) _ ds).dfractional_persist _ $$ HD with #HD
  ihave Hnil := ownSlice_nil (V := w8) (GF := GF) (DFrac.own 1)
  ihave Hpb : |={⊤}=> pbMsg raftpb.Entry l [] $$ [HS HSC HU Hnil]
  · iapply (pbMsg_alloc _ _ _ _ _ _ _ (ufWire_nil _))
    iframe
    iexact Hnil
  imod Hpb with #Hpb
  imod optCell_freeze pt e.Term' $$ Hpt with ⟨%o1, #c1, %h1⟩
  imod optCell_freeze pi e.Index' $$ Hpi with ⟨%o2, #c2, %h2⟩
  imod optCell_freeze pty e.Type' $$ Hpty with ⟨%o3, #c3, %h3⟩
  imod bytesC_freeze ds e.Data' Hds.2 $$ Hs with ⟨%o4, #c4, %h4⟩
  imodintro
  iexists ⟨o1, o2, o3, o4, []⟩
  unfold entRoC
  isplitl
  · iexists pt, pi, pty, ds
    isplitr
    · ipureintro; exact Hnn
    iframe HT c1 HI c2 HY c3 HD c4 Hpb
    try (ipureintro; exact ufWire_nil _)
  · ipureintro
    cases e
    simp only [EntryC.model] at h1 h2 h3 h4 ⊢
    rw [← h1, ← h2, ← h3, ← h4]

/-- **`pbEntryC`'s decoded model is satisfiable** by the generic store. -/
theorem pbEntryC_sat : (pbEntryM (GF := GF)).Sat := by
  refine ⟨⟨raftpb.Entry, inferInstance, inferInstance,
    (inferInstance : IntoValTyped raftpb.Entry raftpb.Entry.ty), fun l => .rfl⟩, ?_⟩
  intro e l
  simp only [pbEntryM]
  iintro Hl
  iapply wp_fupd
  iapply (storeInto_wp_typed (V := raftpb.Entry) (ty := raftpb.Entry.ty) l (zero_val raftpb.Entry))
  iapply (treeWp_entryTree (GF := GF) e)
  iintro %x Hx
  iexists x
  isplitr
  · ipureintro; rfl
  iframe Hl
  iintro Hl
  iapply Hx $$ Hl

/-- **An entry's store, at a fresh pointer**: a log entry (`entRO`) at the model `e`. -/
theorem treeWp_entryPtr (e : EntryM) (Φ : val → IProp GF) :
    (∀ p : Loc, entRO p e -∗ Φ #p) ⊢ treeWp (.ptr raftpb.Entry.ty (entryTree e)) Φ := by
  iintro H
  iapply (treeWp_ptr_fupd (V := raftpb.Entry))
  iapply treeWp_entryTree
  iintro %x Hx
  iexists x
  isplitr
  · ipureintro; rfl
  iintro %p Hp
  imod Hx $$ Hp with ⟨%c, #Hc, %Hm⟩
  imodintro
  iapply H
  subst Hm
  iapply entRoC_entRO $$ Hc

end sat

end EtcdGrove
end Perennial
