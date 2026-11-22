-- The copy for the part `KvNet/` of `RaftNoAx/Proof/go_etcd_io/raft/v3/PbEntryTypeCore.lean` (etc/copy-part.py; rerun it, do not edit).
/-
The part's own (prove-raftex, 2026-11-20; until then a copy of the main tree's
`Proof/go_etcd_io/raft/v3/PbEntryTypeCore.lean`): the main file's declarations but its protobuf trust
boundary, which no module of the part uses since stage 2 (`notes/raft-noax-part.md`: the part's
raft calls `raftpb.CloneEntry`/`EntrySize`, Entry's own functions, not `proto.ClonePb`/`SizePb` at a
registered instance). Dropped: the opaque encoder `entryEncC` with its axiom `entryEncC_ok`, the
instance `pbEntryC` with its `simp` lemmas, and its registration axiom `pbEntryC_reg`; so the part
declares no axiom. Kept: `entDecode`, `EntWireOk`, `entryTree`, `pbEntryM`, `entPtsCC_freeze`,
`optCell_freeze`, `bytesC_freeze`, `treeWp_entryTree`, `pbEntryC_sat` (`pbEntryM.Sat`).
-/
module

public import KvNet.Proof.go_etcd_io.raft.v3.PbContentOwnCore
public import KvNet.Proof.google_golang_org.protobuf.proto.PbSchema
public import KvNet.Proof.google_golang_org.protobuf.proto.InvProto

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section extract
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **Decoding a `raftpb.Entry`'s bytes** (opaque): the entry, or `none`. -/
opaque entDecode (bs : List w8) : Option EntryM

/-- **`bs` is an encoding of the entry `e`**: `bs` decodes to it (every entry marshals, of any
`EntryType` value: the file header). -/
def EntWireOk (e : EntryM) (bs : List w8) : Prop :=
  entDecode bs = some e

end extract

section extract
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
  dec l e := iprop(∃ c, entPtsCC l (DFrac.own 1) c ∗ ⌜c.model = e⌝)
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
  decC l c := entPtsCC l (DFrac.own 1) c
  decC_dec l c _ := by
    iintro H
    iexists c
    iframe H
    ipureintro; rfl

/-- (out_size C3) **An entry at a content, frozen**: its fields' points-to made persistent. -/
theorem entPtsCC_freeze (l : Loc) (dq : DFrac) (c : EntryC) :
    entPtsCC (GF := GF) l dq c ⊢ |==> entRoC l c := by
  unfold entPtsCC entRoC
  iintro ⟨%pt, %pi, %pty, %ds, %Hnn, HT, #cT, HI, #cI, HY, #cY, HD, #Hd, #Hpb⟩
  imod (typedPointsto_dfractional (GF := GF) _ pt).dfractional_persist _ $$ HT with #HT
  imod (typedPointsto_dfractional (GF := GF) _ pi).dfractional_persist _ $$ HI with #HI
  imod (typedPointsto_dfractional (GF := GF) _ pty).dfractional_persist _ $$ HY with #HY
  imod (typedPointsto_dfractional (GF := GF) _ ds).dfractional_persist _ $$ HD with #HD
  imodintro
  iexists pt, pi, pty, ds
  isplitr
  · ipureintro; exact Hnn
  iframe HT cT HI cI HY cY HD Hd Hpb

end extract

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

/-- **An entry's struct literal**: its value, which, stored anywhere, is an owned entry at some wire
content with the model `e` (`entPtsCC_freeze` freezes it). -/
theorem treeWp_entryTree (e : EntryM) (Φ : val → IProp GF) :
    (∀ x : raftpb.Entry, (∀ p : Loc, p ↦ x ={⊤}=∗ ∃ c, entPtsCC p (DFrac.own 1) c ∗ ⌜c.model = e⌝) -∗
      Φ #x) ⊢
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
  unfold entPtsCC
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

/-- **`pbEntryM` is satisfiable** by the generic store. -/
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

end sat

end EtcdGrove
end Perennial
