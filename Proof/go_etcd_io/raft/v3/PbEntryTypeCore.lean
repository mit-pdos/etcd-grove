/-
The declarations `entDecode`, `EntWireOk`, `entryEncC`, `entryEncC_ok`, `entryTree`, `pbEntryM`,
`pbEntryC`, `pbEncC_pbEntryC`, `pbEntryC_ty`, `pbEntryC_roC`, `pbEntryC_C`, `pbEntryC_modelOf`,
`pbEntryC_size`, `pbEntryC_marshals`, `pbEntryC_wire`, `pbEntryC_decOk`, `pbEntryC_ufValid`,
`pbEntryC_blank`, `pbEntryC_dec`, `pbEntryC_decC`, `entPtsCC_freeze`, `pbEntryC_reg` of
`Proof/go_etcd_io/raft/v3/PbEntryType.lean`, split from it so that the WAL
(`Proof/go_etcd_io/etcd/server/v3/storage/wal/`) imports them without the rest (until 2026-11-15 an
extract of `etc/gen-part-copies.py` for the part `LinuxFs/`; notes/wal-lean-integration.md). The
source imports this module.
-/
module

public import Proof.go_etcd_io.raft.v3.PbContentOwnCore
public import Proof.google_golang_org.protobuf.proto.PbSchema
public import Proof.google_golang_org.protobuf.proto.InvProto

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

/-- **The encoding of an `Entry`'s wire content** (opaque: protobuf-go's `Marshal`). -/
opaque entryEncC [GooseExts] (c : EntryC) : List w8

/-- **The trust boundary: `Entry`'s encoding** (the type's one trusted fact). Tested in Go: the
round trip `Unmarshal(Marshal(e))` gives the getters' view, and `proto.Size(e)` is `entrySize`,
for every presence combination and for unknown fields routed as `ufWire` says. -/
axiom entryEncC_ok [GooseExts] (c : EntryC) : ufWire entrySchema c.uf → entrySize c < 2 ^ 63 →
    EntWireOk c.model (entryEncC c) ∧ (entryEncC c).length = entrySize c

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

/-- **`raftpb.Entry` at its wire content** (the registered instance): the data and the encoder,
whose `enc_ok` is the type's one trusted fact `entryEncC_ok`. -/
def pbEntryC : PbTypeC GF where
  data := pbEntryM
  encd := { enc := entryEncC
            enc_ok := fun c _ hu hs => entryEncC_ok c (hu _ (List.mem_singleton.2 rfl)) hs }

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
    (pbEntryC (GF := GF)).data.dec l e = iprop(∃ c, entPtsCC l (DFrac.own 1) c ∗ ⌜c.model = e⌝) :=
  rfl

@[simp] theorem pbEntryC_decC (l : Loc) (c : EntryC) :
    (pbEntryC (GF := GF)).data.decC l c = entPtsCC l (DFrac.own 1) c := rfl

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

/-- **The registration** of `pbEntryC` (exact shape). -/
axiom pbEntryC_reg [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
    {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [go.Semantics] :
    pbModelOf GF raftpb.Entry.ty = some (pbEntryC (GF := GF))

end EtcdGrove
end Perennial
