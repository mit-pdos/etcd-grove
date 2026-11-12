/-
**Per-type prototype: `raftpb.Message` at its wire content** (stage A, CP1; the Scope's E for
`Message`, revisions 4-6, on the pattern of `PerTypeEntry.lean`).

- `MsgC`: every proto2 optional scalar's presence (`Option`, `none` the `nil` cell, `some 0` a set
  zero), `Context` `nil` or not (`Option (List w8)`), the `Entries` as `EntryC` contents, the
  `Snapshot` `nil` or present with its own content (`SnapC`: `Data` `nil` or not, `Metadata` `nil`
  or present, `SnapMetaC`: `ConfState` `nil` or present, `CSC`: the four id lists, `AutoLeave`'s
  presence), the `Responses` (each response's pointer and content), and the unknown fields of every
  level.
- **`Responses` is a nested inductive** (`MsgC.mk` takes a `List (Loc × MsgC)`), not a
  depth-bounded form: a depth bound would make a decoded message whose responses have responses
  have no content (D1 false), and Lean's structural recursion goes through the nesting (the
  definitions below are `rfl`-unfoldable, the proofs by mutual structural recursion). The pointers
  are part of the content because the model (`MsgSt.resps : List Loc`) is the pointers; D2 is only
  claimed with no responses (`MsgMarshals`).
- `msgRoC l c`: a frozen `*Message` holding exactly `c` (`optCell`, `bytesC`, each nested object
  frozen at its content, each level's `pbMsg` at its `uf`, which records `uf`'s validity at the level's schema), and the bridge
  `msgRoC_msgOwn` to today's `msgOwn l □` (what `pbMessage.ro` is), **under the premise that the
  snapshot's `ConfState` has no unknown fields** (`MsgC.csUfNil`): today's `csPts` fixes the
  `ConfState`'s `pbMsg` index to `[]` (`InvPb.lean`, `csPts`), so the bridge is false without it.
- `msgEncC` (opaque) and its one trusted fact `msgEncC_ok`; `msgSize`, protobuf's size formula.
- `pbMessageM` (the data, no axiom), `pbMessageC` (with the encoder), the registration
  `pbMessageC_reg`, and `pbMessageC_sat : pbMessageM.Sat`, whose `dec` is today's
  (`msgPtsC l 1 1 true`, what `netRecv` hands `Process`).

**Schemas** (`raftpb/raft.proto` at the fork's `565c2bd`, raft v3.7, proto2; every field number
is below 16, so every tag is one byte):
- `Message` (`raft.proto:62-99`): `type` 1, `to` 2, `from` 3, `term` 4, `logTerm` 5, `index` 6,
  `commit` 8, `vote` 13, `reject` 10, `rejectHint` 11 (varints); `entries` 7, `snapshot` 9,
  `context` 12, `responses` 14 (length-delimited).
- `Snapshot` (`raft.proto:25-28`): `data` 1, `metadata` 2 (length-delimited).
- `SnapshotMetadata` (`raft.proto:19-23`): `conf_state` 1 (length-delimited), `index` 2, `term` 3
  (varints).
- `ConfState` (`raft.proto:127-142`): `voters` 1, `learners` 2, `voters_outgoing` 3,
  `learners_next` 4 (repeated `uint64`, proto2 so unpacked; the decoder takes both the unpacked
  varint and the packed `LEN`), `auto_leave` 5 (varint).
- `Entry`: `entrySchema`.
The schemas are defined, with `pbSchemaOf`, in `proto/PbSchema.lean` (CP2).
-/
module

public import Proof.go_etcd_io.raft.v3.PbEntryType
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.PbMessage
public import Proof.go_etcd_io.raft.v3.PbContentOwn

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3


/-- **The encoding of a `Message`'s wire content** (opaque: protobuf-go's `Marshal`). -/
opaque msgEncC [GooseExts] (c : MsgC) : List w8

/-- **The trust boundary: `Message`'s encoding** (the type's one trusted fact, the shape of
`entryEncC_ok`): `Unmarshal(Marshal(m))` gives the wire view, and `proto.Size(m)` is `msgSize`, for
every presence combination and unknown fields routed as `ufWire` says, at every level. Backed by Go
round-trip tests (`TestC9P2MessageEncoder`, 200,000 contents, passing; the harness's home is
`examples/pbschema`). Only claimed of messages that marshal (no responses). -/
axiom msgEncC_ok [GooseExts] (c : MsgC) : MsgMarshals c.model → (∀ p ∈ c.levels, ufWire p.1 p.2) →
    msgSize c < 2 ^ 63 → MsgWireOk c.model (msgEncC c) ∧ (msgEncC c).length = msgSize c


/-! ## The frozen message at its wire content -/

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-! ### The store -/

/-- **The store of a conf state** (always allocated; its lists `nil` if empty, `AutoLeave` `nil`
if `false`). -/
def csTree (c : ConfStateM) : VTree :=
  .ptr raftpb.ConfState.ty (.strct raftpb.ConfState.ty
    [(go!"Voters", go.GoType.SliceType go.uint64), (go!"Learners", go.GoType.SliceType go.uint64),
     (go!"VotersOutgoing", go.GoType.SliceType go.uint64),
     (go!"LearnersNext", go.GoType.SliceType go.uint64),
     (go!"AutoLeave", go.GoType.PointerType go.bool)]
    [bytesTree go.uint64 c.Voters', bytesTree go.uint64 c.Learners',
     bytesTree go.uint64 c.VotersOutgoing', bytesTree go.uint64 c.LearnersNext',
     cellTree go.bool c.AutoLeave'])

/-- **The store of a snapshot's metadata** (always allocated, its conf state too). -/
def metaTree (md : SnapshotMetadataM) : VTree :=
  .ptr raftpb.SnapshotMetadata.ty (.strct raftpb.SnapshotMetadata.ty
    [(go!"ConfState", go.GoType.PointerType raftpb.ConfState.ty),
     (go!"Index", go.GoType.PointerType go.uint64), (go!"Term", go.GoType.PointerType go.uint64)]
    [csTree md.ConfState', cellTree go.uint64 md.Index', cellTree go.uint64 md.Term'])

/-- **The store of a snapshot** (its `Data` `nil` if empty, its metadata allocated). -/
def snapTree (s : SnapshotM) : VTree :=
  .ptr raftpb.Snapshot.ty (.strct raftpb.Snapshot.ty
    [(go!"Data", go.GoType.SliceType go.byte),
     (go!"Metadata", go.GoType.PointerType raftpb.SnapshotMetadata.ty)]
    [bytesTree go.byte s.Data', metaTree s.Metadata'])

/-- A message's snapshot: `nil`, or a fresh one. -/
def snapOptTree : Option SnapshotM → VTree
  | none => .leaf #(null : Loc)
  | some s => snapTree s

/-- **The store of a message**: each scalar `nil` if zero, the entries (`nil` if none) each a
fresh entry, the snapshot, the context `nil` if empty, the responses' pointers. -/
def msgTree (st : MsgSt) : VTree :=
  .strct raftpb.Message.ty
    [(go!"Type", go.GoType.PointerType raftpb.MessageType.ty),
     (go!"To", go.GoType.PointerType go.uint64), (go!"From", go.GoType.PointerType go.uint64),
     (go!"Term", go.GoType.PointerType go.uint64), (go!"LogTerm", go.GoType.PointerType go.uint64),
     (go!"Index", go.GoType.PointerType go.uint64),
     (go!"Entries", go.GoType.SliceType (go.GoType.PointerType raftpb.Entry.ty)),
     (go!"Commit", go.GoType.PointerType go.uint64), (go!"Vote", go.GoType.PointerType go.uint64),
     (go!"Snapshot", go.GoType.PointerType raftpb.Snapshot.ty),
     (go!"Reject", go.GoType.PointerType go.bool),
     (go!"RejectHint", go.GoType.PointerType go.uint64),
     (go!"Context", go.GoType.SliceType go.byte),
     (go!"Responses", go.GoType.SliceType (go.GoType.PointerType raftpb.Message.ty))]
    [cellTree raftpb.MessageType.ty st.msg.Type', cellTree go.uint64 st.msg.To',
     cellTree go.uint64 st.msg.From', cellTree go.uint64 st.msg.Term',
     cellTree go.uint64 st.msg.LogTerm', cellTree go.uint64 st.msg.Index',
     sliceTree (go.GoType.PointerType raftpb.Entry.ty)
       (st.ents.map fun e => .ptr raftpb.Entry.ty (entryTree e)),
     cellTree go.uint64 st.msg.Commit', cellTree go.uint64 st.msg.Vote', snapOptTree st.snap,
     cellTree go.bool st.msg.Reject', cellTree go.uint64 st.msg.RejectHint',
     bytesTree go.byte st.ctx, bytesTree (go.GoType.PointerType raftpb.Message.ty) st.resps]

/-- **`raftpb.Message` at its wire content: the data** (no axiom: what `Sat` is stated over). `ro`
is a frozen message at some wire content; `dec` today's (`pbMessage`'s): an owned message with its
`Entries` capacity, which fixes the snapshot `ConfState`'s unknown fields to none, so it describes
only a content without (`decOk`, `MsgC.csUfNil`); `decC` the owned message holding exactly a
content (`msgPtsCC`, `PbContentOwn.lean`), which is `dec` under `csUfNil` (`msgPtsCC_msgPtsC`);
`wire` is a decoding (`MsgDecOk`), not an encoding (Go decodes `responses`). -/
def pbMessageM : PbModelC GF where
  ty := raftpb.Message.ty
  M := MsgSt
  ro l st := iprop(∃ c, msgRoC l c ∗ ⌜c.model = st⌝)
  ro_persistent _ _ := inferInstance
  marshals := MsgMarshals
  wire := MsgDecOk
  eqv st st' := wireOf st = wireOf st' ∧ (st.resps = [] → st'.resps = [])
  blank l := iprop(l ↦ (zero_val raftpb.Message))
  dec l st := msgPtsC l (DFrac.own 1) (DFrac.own 1) true st
  C := MsgC
  roC := msgRoC
  roC_persistent _ _ := inferInstance
  modelOf := MsgC.model
  levels := MsgC.levels
  size := msgSize
  tree := msgTree
  decOk := MsgC.csUfNil
  ro_iff _ _ := .rfl
  roC_ufValid := msgRoC_uf
  decC l c := msgPtsCC l (DFrac.own 1) (DFrac.own 1) true c
  decC_dec l c h := msgPtsCC_msgPtsC l (DFrac.own 1) (DFrac.own 1) true c h

/-- **`raftpb.Message` at its wire content** (the registered instance): the data and the encoder,
whose `enc_ok` is the type's one trusted fact `msgEncC_ok`. -/
def pbMessageC : PbTypeC GF where
  data := pbMessageM
  encd := { enc := msgEncC
            enc_ok := fun c hm hu hs => ⟨(msgEncC_ok c hm hu hs).1.2, (msgEncC_ok c hm hu hs).2⟩ }

end defs

/-- **The registration** of `pbMessageC` (exact shape). -/
axiom pbMessageC_reg [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
    {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [go.Semantics] :
    pbModelOf GF raftpb.Message.ty = some (pbMessageC (GF := GF))


/-! ## `Sat` -/

section sat
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : go_etcd_io.raft.v3.raftpb.Assumptions]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- A stored cell, frozen. -/
theorem cellRO_freeze {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] (p : Loc) (x : V) :
    (⌜p = null ∧ x = zero_val V⌝ ∨ p ↦ x : IProp GF) ⊢ |==> cellRO p x := by
  iintro H
  imod optCell_freeze p x $$ H with ⟨%o, #c, %h⟩
  ihave #c' := optCell_cellRO p o $$ c
  subst h
  imodintro
  iexact c'

theorem treeWp_cs (c : ConfStateM) (Φ : val → IProp GF) :
    (∀ p : Loc, csPts p (DFrac.own 1) c false -∗ Φ #p) ⊢ treeWp (csTree c) Φ := by
  iintro H
  unfold csTree
  iapply (treeWp_ptr_fupd (V := raftpb.ConfState))
  simp only [treeWp, treeWpL]
  iapply treeWp_bytes
  iintro %sv %Hsv' Hsv -
  isplitr
  · ipureintro; exact isPanic_intoVal sv
  iapply treeWp_bytes
  iintro %sl %Hsl' Hsl -
  isplitr
  · ipureintro; exact isPanic_intoVal sl
  iapply treeWp_bytes
  iintro %so %Hso' Hso -
  isplitr
  · ipureintro; exact isPanic_intoVal so
  iapply treeWp_bytes
  iintro %sn %Hsn' Hsn -
  isplitr
  · ipureintro; exact isPanic_intoVal sn
  iapply treeWp_cell
  iintro %pa Hpa
  isplitr
  · ipureintro; exact isPanic_intoVal pa
  simp [litBody, strctKes, kesσ, envσ]
  repeat (isplitr; · ipureintro; trivial)
  wp_auto
  iexists _
  isplitr
  · ipureintro; rfl
  iintro %p Hp
  ihave %Hnn := typedPointsto_not_null $$ Hp
  icases typedPointsto_split _ _ _ $$ Hp with Hp
  simp only [TypedPointsto.typedPointstoDef]
  icases Hp with ⟨HS, HV, HL, HO, HN, HA, HU, HSC, -⟩
  ihave Hnil := ownSlice_nil (V := w8) (GF := GF) (DFrac.own 1)
  ihave Hpb : |={⊤}=> pbMsg raftpb.ConfState p [] $$ [HS HSC HU Hnil]
  · iapply (pbMsg_alloc _ _ _ _ _ _ _ (ufWire_nil _))
    iframe
    iexact Hnil
  imod Hpb with #Hpb
  imod cellRO_freeze pa c.AutoLeave' $$ Hpa with #cA
  imodintro
  iapply H
  unfold csPts
  iexists sv, sl, so, sn, pa
  iframe HV Hsv HL Hsl HO Hso HN Hsn HA cA Hpb
  ipureintro; exact ⟨Hnn, fun h => nomatch h⟩

theorem treeWp_meta (md : SnapshotMetadataM) (Φ : val → IProp GF) :
    (∀ p : Loc, smPts p (DFrac.own 1) md -∗ Φ #p) ⊢ treeWp (metaTree md) Φ := by
  iintro H
  unfold metaTree
  iapply (treeWp_ptr_fupd (V := raftpb.SnapshotMetadata))
  simp only [treeWp, treeWpL]
  iapply treeWp_cs
  iintro %pc Hc
  isplitr
  · ipureintro; exact isPanic_intoVal pc
  iapply treeWp_cell
  iintro %pi Hpi
  isplitr
  · ipureintro; exact isPanic_intoVal pi
  iapply treeWp_cell
  iintro %pt Hpt
  isplitr
  · ipureintro; exact isPanic_intoVal pt
  simp [litBody, strctKes, kesσ, envσ]
  repeat (isplitr; · ipureintro; trivial)
  wp_auto
  iexists _
  isplitr
  · ipureintro; rfl
  iintro %p Hp
  ihave %Hnn := typedPointsto_not_null $$ Hp
  icases typedPointsto_split _ _ _ $$ Hp with Hp
  simp only [TypedPointsto.typedPointstoDef]
  icases Hp with ⟨HS, HC, HI, HT, HU, HSC, -⟩
  ihave Hnil := ownSlice_nil (V := w8) (GF := GF) (DFrac.own 1)
  ihave Hpb : |={⊤}=> pbMsg raftpb.SnapshotMetadata p [] $$ [HS HSC HU Hnil]
  · iapply (pbMsg_alloc _ _ _ _ _ _ _ (ufWire_nil _))
    iframe
    iexact Hnil
  imod Hpb with #Hpb
  imod cellRO_freeze pi md.Index' $$ Hpi with #cI
  imod cellRO_freeze pt md.Term' $$ Hpt with #cT
  imodintro
  iapply H
  unfold smPts
  iexists pc, pi, pt, []
  iframe HC HI cI HT cT Hpb
  isplitr
  · ipureintro; exact Hnn
  unfold csOptA
  iright; ileft
  iexact Hc

theorem treeWp_snap (sn : SnapshotM) (Φ : val → IProp GF) :
    (∀ p : Loc, ownSnapM p (DFrac.own 1) sn -∗ Φ #p) ⊢ treeWp (snapTree sn) Φ := by
  iintro H
  unfold snapTree
  iapply (treeWp_ptr_fupd (V := raftpb.Snapshot))
  simp only [treeWp, treeWpL]
  iapply treeWp_bytes
  iintro %ds %Hds' Hds -
  isplitr
  · ipureintro; exact isPanic_intoVal ds
  iapply treeWp_meta
  iintro %pm Hm
  isplitr
  · ipureintro; exact isPanic_intoVal pm
  simp [litBody, strctKes, kesσ, envσ]
  repeat (isplitr; · ipureintro; trivial)
  wp_auto
  iexists _
  isplitr
  · ipureintro; rfl
  iintro %p Hp
  ihave %Hnn := typedPointsto_not_null $$ Hp
  icases typedPointsto_split _ _ _ $$ Hp with Hp
  simp only [TypedPointsto.typedPointstoDef]
  icases Hp with ⟨HS, HD, HM, HU, HSC, -⟩
  ihave Hnil := ownSlice_nil (V := w8) (GF := GF) (DFrac.own 1)
  ihave Hpb : |={⊤}=> pbMsg raftpb.Snapshot p [] $$ [HS HSC HU Hnil]
  · iapply (pbMsg_alloc _ _ _ _ _ _ _ (ufWire_nil _))
    iframe
    iexact Hnil
  imod Hpb with #Hpb
  imodintro
  iapply H
  unfold ownSnapM
  iexists ds, pm, []
  iframe HD Hds HM Hpb
  isplitr
  · ipureintro; exact Hnn
  unfold smOpt
  iright
  iexact Hm

theorem treeWp_snapOpt (o : Option SnapshotM) (Φ : val → IProp GF) :
    (∀ p : Loc, snapOpt p (DFrac.own 1) o -∗ Φ #p) ⊢ treeWp (snapOptTree o) Φ := by
  cases o with
  | none =>
    simp only [snapOptTree, treeWp]
    iintro H
    iapply H
    unfold snapOpt
    ipureintro; rfl
  | some sn =>
    simp only [snapOptTree]
    iintro H
    iapply treeWp_snap
    iintro %p Hp
    iapply H
    unfold snapOpt
    iexact Hp

/-- **`pbMessageC`'s decoded model is satisfiable** by the generic store. -/
theorem pbMessageC_sat : (pbMessageM (GF := GF)).Sat := by
  refine ⟨⟨raftpb.Message, inferInstance, inferInstance,
    (inferInstance : IntoValTyped raftpb.Message raftpb.Message.ty), fun l => .rfl⟩, ?_⟩
  intro st l
  simp only [pbMessageM]
  iintro Hl
  iapply wp_fupd
  iapply (storeInto_wp_typed (V := raftpb.Message) (ty := raftpb.Message.ty) l
    (zero_val raftpb.Message))
  simp only [msgTree, treeWp, treeWpL]
  iapply treeWp_cell
  iintro %pty Hpty
  isplitr
  · ipureintro; exact isPanic_intoVal pty
  iapply treeWp_cell
  iintro %pto Hpto
  isplitr
  · ipureintro; exact isPanic_intoVal pto
  iapply treeWp_cell
  iintro %pfr Hpfr
  isplitr
  · ipureintro; exact isPanic_intoVal pfr
  iapply treeWp_cell
  iintro %pte Hpte
  isplitr
  · ipureintro; exact isPanic_intoVal pte
  iapply treeWp_cell
  iintro %plt Hplt
  isplitr
  · ipureintro; exact isPanic_intoVal plt
  iapply treeWp_cell
  iintro %pix Hpix
  isplitr
  · ipureintro; exact isPanic_intoVal pix
  iapply (treeWp_sliceMap (V := Loc) (fun e => VTree.ptr raftpb.Entry.ty (entryTree e))
    (fun e p => entRO (GF := GF) p e) (fun a Φ => treeWp_entryPtr a Φ))
  iintro %els %es %Hes' Hents Hes Hcap
  isplitr
  · ipureintro; exact isPanic_intoVal es
  iapply treeWp_cell
  iintro %pco Hpco
  isplitr
  · ipureintro; exact isPanic_intoVal pco
  iapply treeWp_cell
  iintro %pvo Hpvo
  isplitr
  · ipureintro; exact isPanic_intoVal pvo
  iapply treeWp_snapOpt
  iintro %ps Hsn
  isplitr
  · ipureintro; exact isPanic_intoVal ps
  iapply treeWp_cell
  iintro %prj Hprj
  isplitr
  · ipureintro; exact isPanic_intoVal prj
  iapply treeWp_cell
  iintro %prh Hprh
  isplitr
  · ipureintro; exact isPanic_intoVal prh
  iapply treeWp_bytes
  iintro %cs %Hcs' Hcs -
  isplitr
  · ipureintro; exact isPanic_intoVal cs
  iapply treeWp_bytes
  iintro %rs %Hrs' Hrs -
  isplitr
  · ipureintro; exact isPanic_intoVal rs
  simp [litBody, strctKes, kesσ, envσ]
  repeat (isplitr; · ipureintro; trivial)
  wp_auto
  iexists _
  isplitr
  · ipureintro; rfl
  iframe Hl
  iintro Hl
  ihave %Hnn := typedPointsto_not_null $$ Hl
  icases typedPointsto_split _ _ _ $$ Hl with Hl
  simp only [TypedPointsto.typedPointstoDef]
  icases Hl with ⟨HS, HTy, HTo, HFr, HTe, HLt, HIx, HEs, HCo, HVo, HSn, HRj, HRh, HCx, HRs, HU,
    HSC, -⟩
  ihave Hnil := ownSlice_nil (V := w8) (GF := GF) (DFrac.own 1)
  ihave Hpb : |={⊤}=> pbMsg raftpb.Message l [] $$ [HS HSC HU Hnil]
  · iapply (pbMsg_alloc _ _ _ _ _ _ _ (ufWire_nil _))
    iframe
    iexact Hnil
  imod Hpb with #Hpb
  imod cellRO_freeze pty st.msg.Type' $$ Hpty with #cTy
  imod cellRO_freeze pto st.msg.To' $$ Hpto with #cTo
  imod cellRO_freeze pfr st.msg.From' $$ Hpfr with #cFr
  imod cellRO_freeze pte st.msg.Term' $$ Hpte with #cTe
  imod cellRO_freeze plt st.msg.LogTerm' $$ Hplt with #cLt
  imod cellRO_freeze pix st.msg.Index' $$ Hpix with #cIx
  imod cellRO_freeze pco st.msg.Commit' $$ Hpco with #cCo
  imod cellRO_freeze pvo st.msg.Vote' $$ Hpvo with #cVo
  imod cellRO_freeze prj st.msg.Reject' $$ Hprj with #cRj
  imod cellRO_freeze prh st.msg.RejectHint' $$ Hprh with #cRh
  imod ownSlice_persist _ _ _ $$ Hcs with #Hcs
  ihave Hents := (BigSepL2.bigSepL2_flip (Φ := fun _ p e => entRO (GF := GF) p e)).1 $$ Hents
  imodintro
  unfold msgPtsC
  iexists pty, pto, pfr, pte, plt, pix, pco, pvo, prj, prh, es, els, ps, cs, rs, []
  simp only [ite_true]
  iframe HTy cTy HTo cTo HFr cFr HTe cTe HLt cLt HIx cIx HCo cCo HVo cVo HRj cRj HRh cRh
  iframe HEs Hes Hents Hcap HSn Hsn HCx Hcs HRs Hrs Hpb
  ipureintro; exact Hnn

end sat


/-! ## From today's `msgOwn` to the wire content (stage A CP3) -/

section fromOwn
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

@[simp] theorem pbEncC_pbMessageC (c : MsgC) : pbEncC (pbMessageC (GF := GF)) c = msgEncC c := rfl

/-! The registered instances' fields (to state the `*Pb` specs at them in this file's terms). -/
@[simp] theorem pbMessageC_ty : (pbMessageC (GF := GF)).data.ty = raftpb.Message.ty := rfl
@[simp] theorem pbMessageC_roC : (pbMessageC (GF := GF)).data.roC = msgRoC := rfl
@[simp] theorem pbMessageC_C : (pbMessageC (GF := GF)).data.C = MsgC := rfl
@[simp] theorem pbMessageC_modelOf : (pbMessageC (GF := GF)).data.modelOf = MsgC.model := rfl
@[simp] theorem pbMessageC_size : (pbMessageC (GF := GF)).data.size = msgSize := rfl
@[simp] theorem pbMessageC_marshals : (pbMessageC (GF := GF)).data.marshals = MsgMarshals := rfl
@[simp] theorem pbMessageC_wire : (pbMessageC (GF := GF)).data.wire = MsgDecOk := rfl
@[simp] theorem pbMessageC_decOk : (pbMessageC (GF := GF)).data.decOk = MsgC.csUfNil := rfl
@[simp] theorem pbMessageC_levels : (pbMessageC (GF := GF)).data.levels = MsgC.levels := rfl
@[simp] theorem pbMessageC_ufValid (c : MsgC) :
    (pbMessageC (GF := GF)).data.ufValid c = ∀ q ∈ c.levels, ufWire q.1 q.2 := rfl
@[simp] theorem pbMessageC_blank (l : Loc) :
    (pbMessageC (GF := GF)).data.blank l = iprop(l ↦ (zero_val raftpb.Message)) := rfl
@[simp] theorem pbMessageC_dec (l : Loc) (st : MsgSt) :
    (pbMessageC (GF := GF)).data.dec l st = msgPtsC l (DFrac.own 1) (DFrac.own 1) true st := rfl
@[simp] theorem pbMessageC_decC (l : Loc) (c : MsgC) :
    (pbMessageC (GF := GF)).data.decC l c = msgPtsCC l (DFrac.own 1) (DFrac.own 1) true c := rfl
@[simp] theorem pbMessageC_eqv (st st' : MsgSt) :
    (pbMessageC (GF := GF)).data.eqv st st' =
      (wireOf st = wireOf st' ∧ (st.resps = [] → st'.resps = [])) := rfl

/-- **A frozen message's encoding** (`msgEncC_ok` with `msgRoC_uf`). -/
theorem msgRoC_enc (l : Loc) (c : MsgC) :
    msgRoC (GF := GF) l c ⊢ ⌜MsgMarshals c.model → msgSize c < 2 ^ 63 →
      MsgWireOk c.model (msgEncC c) ∧ (msgEncC c).length = msgSize c ∧
      ∀ q ∈ c.levels, ufWire q.1 q.2⌝ := by
  iintro #H
  ihave %Hu := msgRoC_uf l c $$ H
  ipureintro
  intro hm hs
  have := msgEncC_ok c hm Hu hs
  exact ⟨this.1, this.2, Hu⟩

end fromOwn

theorem nat_le_sum_of_mem {l : List Nat} {a : Nat} (h : a ∈ l) : a ≤ l.sum := by
  induction l with
  | nil => simp at h
  | cons x xs ih =>
    simp only [List.sum_cons]
    rcases List.mem_cons.1 h with rfl | h
    · omega
    · have := ih h; omega

/-- **A message's encoding is the encoding of a wire content of the message whose unknown fields
are valid at every level** (stage A of the per-type models: the frames and request bodies carry the
sender's content, so that the receiver's `proto.Unmarshal` succeeds and gives it back, D2), whose
snapshot `ConfState` has no unknown fields (`MsgC.csUfNil`, what the receiver's `dec` needs: the
sender's content is raft's, whose `csPts` fixes them to none). -/
def MsgEnc [GooseExts] (st : MsgSt) (mbs : List w8) : Prop :=
  ∃ c : MsgC, c.model = st ∧ (∀ q ∈ c.levels, ufWire q.1 q.2) ∧ c.csUfNil ∧ mbs = msgEncC c

/-- **Each entry's size is at most its message's.** -/
theorem entrySize_le_msgSize [GooseExts] (c : MsgC) (e : EntryC) (he : e ∈ c.f.entries) :
    entrySize e ≤ msgSize c := by
  cases c with
  | mk f rs =>
  simp only [MsgC.f] at he
  have h1 : lenSize (entrySize e) ≤ (f.entries.map fun e => lenSize (entrySize e)).sum :=
    nat_le_sum_of_mem (List.mem_map.2 ⟨e, he, rfl⟩)
  simp only [msgSize, MsgFC.size, lenSize] at *
  omega

end EtcdGrove
end Perennial
