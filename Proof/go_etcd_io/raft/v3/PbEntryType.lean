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

(out_size C3, 2026-11-12, decided by etcd-grove-81: moved here, with the same names and texts, from the
server's `rafthttp/PerTypeEntry.lean` and, for `entDecode`/`EntWireOk`/`pbEntry`, from
`rafthttp/PbMessage.lean`, so that raft's `limitSize` and `appendEntry` reach `pbEntryC_reg` for
`proto.SizePb`/`proto.ClonePb`.)
-/
module

public import Proof.google_golang_org.protobuf.proto.InvProto
public import Proof.go_etcd_io.raft.v3.PbContent

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section wire
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-! ### Entries (the msgappv2 codec's short frame marshals them one by one) -/

/-- **Decoding a `raftpb.Entry`'s bytes** (opaque): the entry, or `none`. -/
opaque entDecode (bs : List w8) : Option EntryM

/-- **`bs` is an encoding of the entry `e`**: `bs` decodes to it (every entry marshals, of any
`EntryType` value: the file header). -/
def EntWireOk (e : EntryM) (bs : List w8) : Prop :=
  entDecode bs = some e

/-- **A `*raftpb.Entry` at the bytes** (a trusted wire model, read against `raft.proto`'s `Entry`:
`Term`, `Index`, `Type`, `Data`, all in `EntryM`): read-only for good and decoded alike, a log
entry (`entRO`); blank, a zero struct. -/
def pbEntry : PbType GF where
  ty := raftpb.Entry.ty
  M := EntryM
  ro l e := entRO l e
  ro_persistent l e := entRO_persistent l e
  marshals _ := True
  wire := EntWireOk
  eqv e e' := e = e'
  blank l := iprop(l ↦ (zero_val raftpb.Entry))
  dec l e := entRO l e

@[simp] theorem pbEntry_ty : (pbEntry (GF := GF)).ty = raftpb.Entry.ty := rfl
@[simp] theorem pbEntry_M : (pbEntry (GF := GF)).M = EntryM := rfl
@[simp] theorem pbEntry_ro (l : Loc) (e : EntryM) : (pbEntry (GF := GF)).ro l e = entRO l e := rfl
@[simp] theorem pbEntry_marshals (e : EntryM) :
    (pbEntry (GF := GF)).marshals e = True := rfl
@[simp] theorem pbEntry_wire : (pbEntry (GF := GF)).wire = EntWireOk := rfl
@[simp] theorem pbEntry_blank (l : Loc) :
    (pbEntry (GF := GF)).blank l = iprop(l ↦ (zero_val raftpb.Entry)) := rfl
@[simp] theorem pbEntry_dec (l : Loc) (e : EntryM) : (pbEntry (GF := GF)).dec l e = entRO l e := rfl

/-- One encoding is of one entry. -/
theorem EntWireOk.inj {e e' : EntryM} {bs : List w8} (h : EntWireOk e bs) (h' : EntWireOk e' bs) :
    e = e' :=
  Option.some.inj (h.symm.trans h')

end wire

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
  decOk _ := True
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
  decC := entRoC
  decC_dec l c _ := by
    iintro #H
    iexists c
    iframe H
    ipureintro; rfl

/-- **`raftpb.Entry` at its wire content** (the registered instance): the data and the encoder,
whose `enc_ok` is the type's one trusted fact `entryEncC_ok`. -/
def pbEntryC : PbTypeC GF where
  data := pbEntryM
  encd := { enc := entryEncC
            enc_ok := fun c _ hu hs => entryEncC_ok c (hu _ (List.mem_singleton.2 rfl)) hs }

/-! The registered instance's fields (moved from rafthttp's `PerTypeMessage.lean`, out_size C3). -/
@[simp] theorem pbEncC_pbEntryC (c : EntryC) : pbEncC (pbEntryC (GF := GF)) c = entryEncC c := rfl
@[simp] theorem pbEntryC_ty : (pbEntryC (GF := GF)).data.ty = raftpb.Entry.ty := rfl
@[simp] theorem pbEntryC_roC : (pbEntryC (GF := GF)).data.roC = entRoC := rfl
@[simp] theorem pbEntryC_C : (pbEntryC (GF := GF)).data.C = EntryC := rfl
@[simp] theorem pbEntryC_modelOf : (pbEntryC (GF := GF)).data.modelOf = EntryC.model := rfl
@[simp] theorem pbEntryC_size : (pbEntryC (GF := GF)).data.size = entrySize := rfl
@[simp] theorem pbEntryC_marshals (e : EntryM) : (pbEntryC (GF := GF)).data.marshals e = True := rfl
@[simp] theorem pbEntryC_wire : (pbEntryC (GF := GF)).data.wire = EntWireOk := rfl
@[simp] theorem pbEntryC_decOk (c : EntryC) : (pbEntryC (GF := GF)).data.decOk c = True := rfl
@[simp] theorem pbEntryC_ufValid (c : EntryC) :
    (pbEntryC (GF := GF)).data.ufValid c = ∀ q ∈ [(entrySchema, c.uf)], ufWire q.1 q.2 := rfl
@[simp] theorem pbEntryC_blank (l : Loc) :
    (pbEntryC (GF := GF)).data.blank l = iprop(l ↦ (zero_val raftpb.Entry)) := rfl
@[simp] theorem pbEntryC_dec (l : Loc) (e : EntryM) :
    (pbEntryC (GF := GF)).data.dec l e = iprop(∃ c, entRoC l c ∗ ⌜c.model = e⌝) := rfl
@[simp] theorem pbEntryC_decC (l : Loc) (c : EntryC) :
    (pbEntryC (GF := GF)).data.decC l c = entRoC l c := rfl

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
