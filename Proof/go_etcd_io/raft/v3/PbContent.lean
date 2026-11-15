/-
**The wire content of raft's messages and entries** (raft-entsize §2, 2026-11-09: moved verbatim
from stage A's `PerTypeEntry.lean` and `PerTypeMessage.lean`, rafthttp, so that raft's API can speak
of content-pinned objects; the per-type instances, their encoders' trust boundaries `entryEncC_ok`
and `msgEncC_ok`, the registrations and `MsgEnc` stay there).

- `EntryC`, `MsgC` (with `CSC`, `SnapMetaC`, `SnapC`, `MsgFC`): the wire contents (every proto2
  optional scalar's presence, `nil` or non-nil bytes, the unknown fields of every level), their
  models (`EntryC.model`, `MsgC.model`), levels and protobuf sizes (`entrySize`, `msgSize`).
- `entRoC`, `msgRoC`: a frozen object holding exactly a content; the bridges to and from today's
  `entRO`/`msgOwn` (`entRoC_entRO`, `msgRoC_msgOwn`, `msgOwn_msgRoC`, ...), and the validity of the
  unknown fields of every level (`msgRoC_uf`).
See `PerTypeEntry.lean` and `PerTypeMessage.lean` (rafthttp) for the design notes.
-/
module

public import Proof.go_etcd_io.raft.v3.InvPbMsg

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


section entDefs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
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

end entDefs

/-! ## The wire content -/

/-- **A `ConfState`'s wire content.** The repeated fields need no presence: an empty list encodes
to nothing, `nil` or not. -/
structure CSC where
  voters : List w64
  learners : List w64
  votersOutgoing : List w64
  learnersNext : List w64
  autoLeave : Option Bool
  uf : List w8

/-- **A `SnapshotMetadata`'s wire content.** -/
structure SnapMetaC [GooseExts] where
  confState : Option CSC
  index : Option w64
  term : Option w64
  uf : List w8

/-- **A `Snapshot`'s wire content.** -/
structure SnapC [GooseExts] where
  data : Option (List w8)
  metadata : Option SnapMetaC
  uf : List w8

/-- **A `Message`'s own fields' wire content** (all but `Responses`). -/
structure MsgFC [GooseExts] where
  type : Option raftpb.MessageType
  to : Option w64
  frm : Option w64
  term : Option w64
  logTerm : Option w64
  index : Option w64
  entries : List EntryC
  commit : Option w64
  vote : Option w64
  snapshot : Option SnapC
  reject : Option Bool
  rejectHint : Option w64
  context : Option (List w8)
  uf : List w8

/-- **A `Message`'s wire content**: its own fields and its responses (each response's pointer and
content; see the file header). -/
inductive MsgC [GooseExts] where
  | mk (f : MsgFC) (resps : List (Loc × MsgC))

/-- The message's own fields. -/
def MsgC.f [GooseExts] : MsgC → MsgFC
  | .mk f _ => f

/-- The message's responses. -/
def MsgC.resps [GooseExts] : MsgC → List (Loc × MsgC)
  | .mk _ rs => rs

section model
variable [GooseExts]

/-- The zero conf state (what a `nil` one reads as). -/
def csZero : ConfStateM := ConfStateM.mk [] [] [] [] false

/-- The zero metadata (what a `nil` one reads as, `smOpt`'s). -/
def metaZero : SnapshotMetadataM := SnapshotMetadataM.mk csZero (W64 0) (W64 0)

def CSC.model (c : CSC) : ConfStateM :=
  ⟨c.voters, c.learners, c.votersOutgoing, c.learnersNext, c.autoLeave.getD (zero_val Bool)⟩

def SnapMetaC.model (m : SnapMetaC) : SnapshotMetadataM :=
  ⟨(m.confState.map CSC.model).getD csZero, m.index.getD (zero_val w64),
    m.term.getD (zero_val w64)⟩

def SnapC.model (s : SnapC) : SnapshotM :=
  ⟨s.data.getD [], (s.metadata.map SnapMetaC.model).getD metaZero⟩

/-- What the getters read of a message's own fields. -/
def MsgFC.msgM (f : MsgFC) : MessageM :=
  ⟨f.type.getD (zero_val raftpb.MessageType), f.to.getD (zero_val w64), f.frm.getD (zero_val w64),
    f.term.getD (zero_val w64), f.logTerm.getD (zero_val w64), f.index.getD (zero_val w64),
    f.commit.getD (zero_val w64), f.vote.getD (zero_val w64), f.reject.getD (zero_val Bool),
    f.rejectHint.getD (zero_val w64)⟩

/-- **The model of a message's wire content** (`pbMessage`'s `MsgSt`). -/
def MsgC.model (c : MsgC) : MsgSt :=
  ⟨c.f.msgM, c.f.entries.map EntryC.model, c.f.snapshot.map SnapC.model, c.f.context.getD [],
    c.resps.map Prod.fst⟩

/-- The snapshot's conf state, if any, has no unknown fields (the bridge's premise). -/
def MsgC.csUfNil (c : MsgC) : Prop :=
  ∀ s ∈ c.f.snapshot, ∀ m ∈ s.metadata, ∀ cs ∈ m.confState, cs.uf = []

end model

/-! ## The levels and the size -/

section levels
variable [GooseExts]

def csLevels : Option CSC → List (FieldSchema × List w8)
  | none => []
  | some c => [(csSchema, c.uf)]

def metaLevels : Option SnapMetaC → List (FieldSchema × List w8)
  | none => []
  | some m => (metaSchema, m.uf) :: csLevels m.confState

def snapLevels : Option SnapC → List (FieldSchema × List w8)
  | none => []
  | some s => (snapSchema, s.uf) :: metaLevels s.metadata

/-- A message's own levels: its own, its entries', its snapshot's. -/
def MsgFC.levels (f : MsgFC) : List (FieldSchema × List w8) :=
  (msgSchema, f.uf) :: (f.entries.map fun e => (entrySchema, e.uf)) ++ snapLevels f.snapshot

mutual
/-- **Every level of a message**, its responses' included. -/
def MsgC.levels : MsgC → List (FieldSchema × List w8)
  | .mk f rs => f.levels ++ respsLevels rs
def respsLevels : List (Loc × MsgC) → List (FieldSchema × List w8)
  | [] => []
  | (_, c) :: rs => c.levels ++ respsLevels rs
end

/-- A length-delimited field's size: its tag (one byte), its length, its bytes. -/
def lenSize (n : Nat) : Nat := 1 + varintSize n + n

def optBytesSize : Option (List w8) → Nat
  | none => 0
  | some bs => lenSize bs.length

def optBoolSize : Option Bool → Nat
  | none => 0
  | some _ => 2

def optW64Size (o : Option w64) : Nat := optVarintSize (o.map fun v => (uint.Z v).toNat)

/-- An unpacked repeated `uint64`: a tag and a varint per element. -/
def repW64Size (xs : List w64) : Nat := (xs.map fun v => 1 + varintSize (uint.Z v).toNat).sum

def csSize (c : CSC) : Nat :=
  repW64Size c.voters + repW64Size c.learners + repW64Size c.votersOutgoing +
  repW64Size c.learnersNext + optBoolSize c.autoLeave + c.uf.length

def metaSize (m : SnapMetaC) : Nat :=
  (match m.confState with | none => 0 | some c => lenSize (csSize c)) +
  optW64Size m.index + optW64Size m.term + m.uf.length

def snapSize (s : SnapC) : Nat :=
  optBytesSize s.data + (match s.metadata with | none => 0 | some m => lenSize (metaSize m)) +
  s.uf.length

/-- A message's own fields' size (an enum is an `int32`, sign-extended to 64 bits). -/
def MsgFC.size (f : MsgFC) : Nat :=
  optVarintSize (f.type.map fun t => (uint.Z (W64 (sint.Z t))).toNat) +
  optW64Size f.to + optW64Size f.frm + optW64Size f.term + optW64Size f.logTerm +
  optW64Size f.index + (f.entries.map fun e => lenSize (entrySize e)).sum +
  optW64Size f.commit + optW64Size f.vote +
  (match f.snapshot with | none => 0 | some s => lenSize (snapSize s)) +
  optBoolSize f.reject + optW64Size f.rejectHint + optBytesSize f.context + f.uf.length

mutual
/-- **protobuf's size of a message**, its responses' included. -/
def msgSize : MsgC → Nat
  | .mk f rs => f.size + respsSize rs
def respsSize : List (Loc × MsgC) → Nat
  | [] => 0
  | (_, c) :: rs => lenSize (msgSize c) + respsSize rs
end

end levels

/-! ## The frozen message at its wire content -/

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **A frozen `*ConfState` holding exactly `c`.** -/
def csRoC (p : Loc) (c : CSC) : IProp GF :=
  iprop(∃ (sv sl so sn : GoSlice) (pa : Loc),
    ⌜p ≠ null⌝ ∗
    p.[raftpb.ConfState, go!"Voters"] ↦□ sv ∗ sv ↦*□ c.voters ∗
    p.[raftpb.ConfState, go!"Learners"] ↦□ sl ∗ sl ↦*□ c.learners ∗
    p.[raftpb.ConfState, go!"VotersOutgoing"] ↦□ so ∗ so ↦*□ c.votersOutgoing ∗
    p.[raftpb.ConfState, go!"LearnersNext"] ↦□ sn ∗ sn ↦*□ c.learnersNext ∗
    p.[raftpb.ConfState, go!"AutoLeave"] ↦□ pa ∗ optCell pa c.autoLeave ∗
    pbMsg raftpb.ConfState p c.uf)

def csOptC (p : Loc) : Option CSC → IProp GF
  | none => iprop(⌜p = null⌝)
  | some c => csRoC p c

/-- **A frozen `*SnapshotMetadata` holding exactly `m`.** -/
def metaRoC (p : Loc) (m : SnapMetaC) : IProp GF :=
  iprop(∃ (pc pi pt : Loc),
    ⌜p ≠ null⌝ ∗
    p.[raftpb.SnapshotMetadata, go!"ConfState"] ↦□ pc ∗ csOptC pc m.confState ∗
    p.[raftpb.SnapshotMetadata, go!"Index"] ↦□ pi ∗ optCell pi m.index ∗
    p.[raftpb.SnapshotMetadata, go!"Term"] ↦□ pt ∗ optCell pt m.term ∗
    pbMsg raftpb.SnapshotMetadata p m.uf)

def metaOptC (p : Loc) : Option SnapMetaC → IProp GF
  | none => iprop(⌜p = null⌝)
  | some m => metaRoC p m

/-- **A frozen `*Snapshot` holding exactly `s`.** -/
def snapRoC (p : Loc) (s : SnapC) : IProp GF :=
  iprop(∃ (ds : GoSlice) (pm : Loc),
    ⌜p ≠ null⌝ ∗
    p.[raftpb.Snapshot, go!"Data"] ↦□ ds ∗ bytesC ds s.data ∗
    p.[raftpb.Snapshot, go!"Metadata"] ↦□ pm ∗ metaOptC pm s.metadata ∗
    pbMsg raftpb.Snapshot p s.uf)

def snapOptC (p : Loc) : Option SnapC → IProp GF
  | none => iprop(⌜p = null⌝)
  | some s => snapRoC p s

/-- **A frozen `*Message`'s own fields at `f`**, its `Responses` slice holding `rps`. -/
def msgFRoC (l : Loc) (f : MsgFC) (rps : List Loc) : IProp GF :=
  iprop(∃ (pty pto pfr pte plt pix pco pvo prj prh : Loc) (es : GoSlice) (els : List Loc)
      (ps : Loc) (cs rs : GoSlice),
    ⌜l ≠ null⌝ ∗
    l.[raftpb.Message, go!"Type"] ↦□ pty ∗ optCell pty f.type ∗
    l.[raftpb.Message, go!"To"] ↦□ pto ∗ optCell pto f.to ∗
    l.[raftpb.Message, go!"From"] ↦□ pfr ∗ optCell pfr f.frm ∗
    l.[raftpb.Message, go!"Term"] ↦□ pte ∗ optCell pte f.term ∗
    l.[raftpb.Message, go!"LogTerm"] ↦□ plt ∗ optCell plt f.logTerm ∗
    l.[raftpb.Message, go!"Index"] ↦□ pix ∗ optCell pix f.index ∗
    l.[raftpb.Message, go!"Commit"] ↦□ pco ∗ optCell pco f.commit ∗
    l.[raftpb.Message, go!"Vote"] ↦□ pvo ∗ optCell pvo f.vote ∗
    l.[raftpb.Message, go!"Reject"] ↦□ prj ∗ optCell prj f.reject ∗
    l.[raftpb.Message, go!"RejectHint"] ↦□ prh ∗ optCell prh f.rejectHint ∗
    l.[raftpb.Message, go!"Entries"] ↦□ es ∗ es ↦*□ els ∗
      ([∗list] p;e ∈ els;f.entries, entRoC p e) ∗
    l.[raftpb.Message, go!"Snapshot"] ↦□ ps ∗ snapOptC ps f.snapshot ∗
    l.[raftpb.Message, go!"Context"] ↦□ cs ∗ bytesC cs f.context ∗
    l.[raftpb.Message, go!"Responses"] ↦□ rs ∗ rs ↦*□ rps ∗
    pbMsg raftpb.Message l f.uf)

mutual
/-- **A frozen `*Message` holding exactly `c`**, its responses frozen at their contents. -/
def msgRoC : Loc → MsgC → IProp GF
  | l, .mk f rs => iprop(msgFRoC l f (rs.map Prod.fst) ∗ respsRoC rs)
/-- The responses, each frozen at its content. -/
def respsRoC : List (Loc × MsgC) → IProp GF
  | [] => iprop(emp)
  | (p, c) :: rs => iprop(msgRoC p c ∗ respsRoC rs)
end

set_option synthInstance.maxSize 1024 in
set_option synthInstance.maxHeartbeats 400000 in
instance csRoC_persistent (p : Loc) (c : CSC) : Persistent (csRoC (GF := GF) p c) := by
  unfold csRoC; infer_instance

instance csOptC_persistent (p : Loc) (o : Option CSC) : Persistent (csOptC (GF := GF) p o) := by
  cases o <;> simp only [csOptC] <;> infer_instance

set_option synthInstance.maxSize 1024 in
set_option synthInstance.maxHeartbeats 400000 in
instance metaRoC_persistent (p : Loc) (m : SnapMetaC) : Persistent (metaRoC (GF := GF) p m) := by
  unfold metaRoC; infer_instance

instance metaOptC_persistent (p : Loc) (o : Option SnapMetaC) :
    Persistent (metaOptC (GF := GF) p o) := by
  cases o <;> simp only [metaOptC] <;> infer_instance

set_option synthInstance.maxSize 1024 in
set_option synthInstance.maxHeartbeats 400000 in
instance snapRoC_persistent (p : Loc) (s : SnapC) : Persistent (snapRoC (GF := GF) p s) := by
  unfold snapRoC; infer_instance

instance snapOptC_persistent (p : Loc) (o : Option SnapC) : Persistent (snapOptC (GF := GF) p o) := by
  cases o <;> simp only [snapOptC] <;> infer_instance

instance msgFRoC_persistent (l : Loc) (f : MsgFC) (rps : List Loc) :
    Persistent (msgFRoC (GF := GF) l f rps) := by
  unfold msgFRoC
  repeat (first
    | refine @exists_persistent _ _ _ _ (fun _ => ?_)
    | refine @sep_persistent _ _ _ _ ?_ ?_
    | infer_instance)

mutual
theorem msgRoC_persistent : ∀ (l : Loc) (c : MsgC), Persistent (msgRoC (GF := GF) l c)
  | l, .mk f rs => by
    have := respsRoC_persistent rs
    simp only [msgRoC]; infer_instance
theorem respsRoC_persistent : ∀ rs : List (Loc × MsgC), Persistent (respsRoC (GF := GF) rs)
  | [] => by simp only [respsRoC]; infer_instance
  | (p, c) :: rs => by
    have := msgRoC_persistent p c
    have := respsRoC_persistent rs
    simp only [respsRoC]; infer_instance
end

attribute [instance] msgRoC_persistent respsRoC_persistent

/-! ### The bridge to today's `msgOwn` -/

theorem optCell_cellRO' {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] (p : Loc)
    (o : Option V) : optCell (GF := GF) p o ⊢ cellRO p (o.getD (zero_val V)) :=
  optCell_cellRO p o

theorem csRoC_csPts (p : Loc) (c : CSC) (h : c.uf = []) :
    csRoC (GF := GF) p c ⊢ csPts p DFrac.discard c.model false := by
  unfold csRoC
  iintro ⟨%sv, %sl, %so, %sn, %pa, %Hnn, #HV, #Hv, #HL, #Hl, #HO, #Ho, #HN, #Hn, #HA, #cA, #Hpb⟩
  rw [h]
  ihave #cA' := optCell_cellRO pa c.autoLeave $$ cA
  unfold csPts
  iexists sv, sl, so, sn, pa
  simp only [CSC.model]
  iframe HV Hv HL Hl HO Ho HN Hn HA cA' Hpb
  ipureintro; exact ⟨Hnn, fun h => nomatch h⟩

theorem csOptC_csOptA (p : Loc) (o : Option CSC) (h : ∀ cs ∈ o, cs.uf = []) :
    csOptC (GF := GF) p o ⊢ csOptA p DFrac.discard ((o.map CSC.model).getD csZero) := by
  cases o with
  | none =>
    simp only [csOptC, csOptA, Option.map_none, Option.getD_none]
    iintro %Hp
    ileft; ipureintro; exact ⟨Hp, rfl⟩
  | some cs =>
    simp only [csOptC, csOptA, Option.map_some, Option.getD_some]
    iintro #H
    iright; ileft
    iapply csRoC_csPts p cs (h cs rfl) $$ H

theorem metaRoC_smPts (p : Loc) (m : SnapMetaC) (h : ∀ cs ∈ m.confState, cs.uf = []) :
    metaRoC (GF := GF) p m ⊢ smPts p DFrac.discard m.model := by
  unfold metaRoC
  iintro ⟨%pc, %pi, %pt, %Hnn, #HC, #Hc, #HI, #cI, #HT, #cT, #Hpb⟩
  ihave #cI' := optCell_cellRO pi m.index $$ cI
  ihave #cT' := optCell_cellRO pt m.term $$ cT
  ihave #Hc' := csOptC_csOptA pc m.confState h $$ Hc
  unfold smPts
  iexists pc, pi, pt, m.uf
  simp only [SnapMetaC.model]
  iframe HC Hc' HI cI' HT cT' Hpb
  ipureintro; exact Hnn

theorem metaOptC_smOpt (p : Loc) (o : Option SnapMetaC)
    (h : ∀ m ∈ o, ∀ cs ∈ m.confState, cs.uf = []) :
    metaOptC (GF := GF) p o ⊢ smOpt p DFrac.discard ((o.map SnapMetaC.model).getD metaZero) := by
  cases o with
  | none =>
    simp only [metaOptC, smOpt, Option.map_none, Option.getD_none]
    iintro %Hp
    ileft; ipureintro; exact ⟨Hp, rfl⟩
  | some m =>
    simp only [metaOptC, smOpt, Option.map_some, Option.getD_some]
    iintro #H
    iright
    iapply metaRoC_smPts p m (h m rfl) $$ H

theorem snapOptC_snapOpt (p : Loc) (o : Option SnapC)
    (h : ∀ s ∈ o, ∀ m ∈ s.metadata, ∀ cs ∈ m.confState, cs.uf = []) :
    snapOptC (GF := GF) p o ⊢ snapOpt p DFrac.discard (o.map SnapC.model) := by
  cases o with
  | none =>
    simp only [snapOptC, snapOpt, Option.map_none]
    iintro %Hp; ipureintro; exact Hp
  | some s =>
    simp only [snapOptC, snapOpt, Option.map_some]
    unfold snapRoC
    iintro ⟨%ds, %pm, %Hnn, #HD, #Hd, #HM, #Hm, #Hpb⟩
    ihave #Hd' := bytesC_ro ds s.data $$ Hd
    ihave #Hm' := metaOptC_smOpt pm s.metadata (h s rfl) $$ Hm
    unfold ownSnapM
    iexists ds, pm, s.uf
    simp only [SnapC.model]
    iframe HD Hd' HM Hm' Hpb
    ipureintro; exact Hnn

/-- **The wire content gives today's `msgOwn`** (`pbMessage.ro`), when the snapshot's conf state
has no unknown fields (today's `csPts` fixes them to none: the file header). -/
theorem msgRoC_msgOwn (l : Loc) (c : MsgC) (h : c.csUfNil) :
    msgRoC (GF := GF) l c ⊢ msgOwn l DFrac.discard c.model := by
  cases c with
  | mk f rs =>
  simp only [msgRoC]
  iintro ⟨H, -⟩
  unfold msgFRoC
  icases H with ⟨%pty, %pto, %pfr, %pte, %plt, %pix, %pco, %pvo, %prj, %prh, %es, %els, %ps, %cs, %rsl,
    %Hnn, #HTy, #cTy, #HTo, #cTo, #HFr, #cFr, #HTe, #cTe, #HLt, #cLt, #HIx, #cIx, #HCo, #cCo,
    #HVo, #cVo, #HRj, #cRj, #HRh, #cRh, #HEs, #Hes, #Hents, #HSn, #Hsn, #HCx, #Hcx, #HRs, #Hrs,
    #Hpb⟩
  ihave #cTy' := optCell_cellRO pty f.type $$ cTy
  ihave #cTo' := optCell_cellRO pto f.to $$ cTo
  ihave #cFr' := optCell_cellRO pfr f.frm $$ cFr
  ihave #cTe' := optCell_cellRO pte f.term $$ cTe
  ihave #cLt' := optCell_cellRO plt f.logTerm $$ cLt
  ihave #cIx' := optCell_cellRO pix f.index $$ cIx
  ihave #cCo' := optCell_cellRO pco f.commit $$ cCo
  ihave #cVo' := optCell_cellRO pvo f.vote $$ cVo
  ihave #cRj' := optCell_cellRO prj f.reject $$ cRj
  ihave #cRh' := optCell_cellRO prh f.rejectHint $$ cRh
  ihave #Hcx' := bytesC_ro cs f.context $$ Hcx
  ihave #Hsn' := snapOptC_snapOpt ps f.snapshot h $$ Hsn
  ihave #Hents' := ((BigSepL2.bigSepL2_mono (Φ := fun _ p e => entRoC (GF := GF) p e)
    (Ψ := fun _ p e => entRO p (EntryC.model e)) (l1 := els) (l2 := f.entries)
    (fun _ _ => entRoC_entRO _ _)).trans
    (BigSepL2.bigSepL2_map_right (Φ := fun _ p e => entRO (GF := GF) p e) EntryC.model).2) $$ Hents
  unfold msgOwn msgPts msgPtsC
  iexists pty, pto, pfr, pte, plt, pix, pco, pvo, prj, prh, es, els, ps, cs, rsl, f.uf
  simp only [MsgC.model, MsgC.f, MsgC.resps, MsgFC.msgM]
  iframe HTy cTy' HTo cTo' HFr cFr' HTe cTe' HLt cLt' HIx cIx' HCo cCo' HVo cVo' HRj cRj' HRh cRh'
  iframe HEs Hes Hents' HSn Hsn' HCx Hcx' HRs Hrs Hpb
  simp only [Bool.false_eq_true, ite_false]
  isplitr
  · ipureintro; exact Hnn
  iempintro


/-! ### The unknown fields of every level are valid -/

theorem pbMsg_uf_cs (p : Loc) (uf : List w8) :
    pbMsg (GF := GF) raftpb.ConfState p uf ⊢ ⌜ufWire csSchema uf⌝ := by
  have h := pbMsg_ufWire (GF := GF) raftpb.ConfState p uf
  rwa [show PbGoType.goTy raftpb.ConfState = raftpb.ConfState.ty from rfl, pbSchemaOf_confState] at h

theorem pbMsg_uf_meta (p : Loc) (uf : List w8) :
    pbMsg (GF := GF) raftpb.SnapshotMetadata p uf ⊢ ⌜ufWire metaSchema uf⌝ := by
  have h := pbMsg_ufWire (GF := GF) raftpb.SnapshotMetadata p uf
  rwa [show PbGoType.goTy raftpb.SnapshotMetadata = raftpb.SnapshotMetadata.ty from rfl,
    pbSchemaOf_snapshotMetadata] at h

theorem pbMsg_uf_snap (p : Loc) (uf : List w8) :
    pbMsg (GF := GF) raftpb.Snapshot p uf ⊢ ⌜ufWire snapSchema uf⌝ := by
  have h := pbMsg_ufWire (GF := GF) raftpb.Snapshot p uf
  rwa [show PbGoType.goTy raftpb.Snapshot = raftpb.Snapshot.ty from rfl, pbSchemaOf_snapshot] at h

theorem pbMsg_uf_msg (l : Loc) (uf : List w8) :
    pbMsg (GF := GF) raftpb.Message l uf ⊢ ⌜ufWire msgSchema uf⌝ := by
  have h := pbMsg_ufWire (GF := GF) raftpb.Message l uf
  rwa [show PbGoType.goTy raftpb.Message = raftpb.Message.ty from rfl, pbSchemaOf_message] at h

theorem entRoC_uf (p : Loc) (e : EntryC) : entRoC (GF := GF) p e ⊢ ⌜ufWire entrySchema e.uf⌝ := by
  unfold entRoC
  iintro ⟨%pt, %pi, %pty, %ds, -, -, -, -, -, -, -, -, -, Hpb⟩
  iapply pbMsg_uf_entry $$ Hpb

theorem entsRoC_uf : ∀ (els : List Loc) (es : List EntryC),
    ([∗list] p;e ∈ els;es, entRoC (GF := GF) p e) ⊢ ⌜∀ e ∈ es, ufWire entrySchema e.uf⌝
  | [], [] => by iintro -; ipureintro; simp
  | [], _ :: _ => false_elim
  | _ :: _, [] => false_elim
  | p :: ps, e :: es => by
    iintro ⟨#H, #Hr⟩
    ihave %h1 := entRoC_uf p e $$ H
    ihave %h2 := entsRoC_uf ps es $$ Hr
    ipureintro
    intro e' he'
    rcases List.mem_cons.1 he' with rfl | h
    · exact h1
    · exact h2 e' h

theorem csOptC_uf (p : Loc) (o : Option CSC) :
    csOptC (GF := GF) p o ⊢ ⌜∀ q ∈ csLevels o, ufWire q.1 q.2⌝ := by
  cases o with
  | none => simp only [csOptC, csLevels]; iintro -; ipureintro; simp
  | some c =>
    simp only [csOptC, csLevels]
    unfold csRoC
    iintro ⟨%sv, %sl, %so, %sn, %pa, -, -, -, -, -, -, -, -, -, -, -, Hpb⟩
    ihave %Hu := pbMsg_uf_cs p c.uf $$ Hpb
    ipureintro; intro q hq; rw [List.mem_singleton] at hq; subst hq; exact Hu

theorem metaOptC_uf (p : Loc) (o : Option SnapMetaC) :
    metaOptC (GF := GF) p o ⊢ ⌜∀ q ∈ metaLevels o, ufWire q.1 q.2⌝ := by
  cases o with
  | none => simp only [metaOptC, metaLevels]; iintro -; ipureintro; simp
  | some m =>
    simp only [metaOptC, metaLevels]
    unfold metaRoC
    iintro ⟨%pc, %pi, %pt, -, -, #Hc, -, -, -, -, #Hpb⟩
    ihave %Hu := pbMsg_uf_meta p m.uf $$ Hpb
    ihave %h := csOptC_uf pc m.confState $$ Hc
    ipureintro; intro q hq
    rcases List.mem_cons.1 hq with rfl | hq
    · exact Hu
    · exact h q hq

theorem snapOptC_uf (p : Loc) (o : Option SnapC) :
    snapOptC (GF := GF) p o ⊢ ⌜∀ q ∈ snapLevels o, ufWire q.1 q.2⌝ := by
  cases o with
  | none => simp only [snapOptC, snapLevels]; iintro -; ipureintro; simp
  | some s =>
    simp only [snapOptC, snapLevels]
    unfold snapRoC
    iintro ⟨%ds, %pm, -, -, -, -, #Hm, #Hpb⟩
    ihave %Hu := pbMsg_uf_snap p s.uf $$ Hpb
    ihave %h := metaOptC_uf pm s.metadata $$ Hm
    ipureintro; intro q hq
    rcases List.mem_cons.1 hq with rfl | hq
    · exact Hu
    · exact h q hq

theorem msgFRoC_uf (l : Loc) (f : MsgFC) (rps : List Loc) :
    msgFRoC (GF := GF) l f rps ⊢ ⌜∀ q ∈ f.levels, ufWire q.1 q.2⌝ := by
  unfold msgFRoC
  iintro ⟨%pty, %pto, %pfr, %pte, %plt, %pix, %pco, %pvo, %prj, %prh, %es, %els, %ps, %cs, %rsl,
    -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hents, -, #Hsn, -, -, -,
    -, #Hpb⟩
  ihave %Hu := pbMsg_uf_msg l f.uf $$ Hpb
  ihave %he := entsRoC_uf els f.entries $$ Hents
  ihave %hs := snapOptC_uf ps f.snapshot $$ Hsn
  ipureintro; intro q hq
  simp only [MsgFC.levels, List.cons_append, List.mem_cons, List.mem_append, List.mem_map] at hq
  rcases hq with rfl | ⟨e, he', rfl⟩ | hq
  · exact Hu
  · exact he e he'
  · exact hs q hq

mutual
theorem msgRoC_uf : ∀ (l : Loc) (c : MsgC), msgRoC (GF := GF) l c ⊢ ⌜∀ q ∈ c.levels, ufWire q.1 q.2⌝
  | l, .mk f rs => by
    have h1 := msgFRoC_uf (GF := GF) l f (rs.map Prod.fst)
    have h2 := respsRoC_uf rs
    simp only [msgRoC, MsgC.levels]
    iintro ⟨#H1, #H2⟩
    ihave %a := h1 $$ H1
    ihave %b := h2 $$ H2
    ipureintro; intro q hq
    rcases List.mem_append.1 hq with hq | hq
    · exact a q hq
    · exact b q hq
theorem respsRoC_uf : ∀ rs : List (Loc × MsgC),
    respsRoC (GF := GF) rs ⊢ ⌜∀ q ∈ respsLevels rs, ufWire q.1 q.2⌝
  | [] => by simp only [respsRoC, respsLevels]; iintro -; ipureintro; simp
  | (p, c) :: rs => by
    have h1 := msgRoC_uf p c
    have h2 := respsRoC_uf rs
    simp only [respsRoC, respsLevels]
    iintro ⟨#H1, #H2⟩
    ihave %a := h1 $$ H1
    ihave %b := h2 $$ H2
    ipureintro; intro q hq
    rcases List.mem_append.1 hq with hq | hq
    · exact a q hq
    · exact b q hq
end


end defs

section fromOwn
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- A cell read as `v` is a cell at some presence reading as `v`. -/
theorem cellRO_optCell {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] (p : Loc) (v : V) :
    cellRO (GF := GF) p v ⊢ ∃ o : Option V, optCell p o ∗ ⌜o.getD (zero_val V) = v⌝ := by
  unfold cellRO
  iintro (%H | #H)
  · iexists none
    simp only [optCell, Option.getD_none]
    ipureintro; exact ⟨H.1, H.2.symm⟩
  · iexists (some v)
    simp only [optCell, Option.getD_some]
    iframe H

/-- Bytes held read-only are a `bytes` field at some presence. -/
theorem ownSlice_bytesC (ds : GoSlice) (xs : List w8) :
    (ds ↦*□ xs : IProp GF) ⊢ ∃ o : Option (List w8), bytesC ds o ∗ ⌜o.getD [] = xs⌝ := by
  iintro #H
  by_cases hn : ds = slice.nil
  · subst hn
    ihave %Hl := ownSlice_len _ _ _ $$ H
    have hx : xs = [] := List.eq_nil_of_length_eq_zero (by rw [Hl.1]; rfl)
    subst hx
    iexists none
    simp only [bytesC, Option.getD_none]
    ipureintro; simp
  · iexists (some xs)
    simp only [bytesC, Option.getD_some]
    iframe H
    ipureintro; simpa using hn

/-- **A log entry is a frozen entry at some wire content.** -/
theorem entRO_entRoC (l : Loc) (e : EntryM) :
    entRO (GF := GF) l e ⊢ ∃ c : EntryC, entRoC l c ∗ ⌜c.model = e⌝ := by
  simp only [entRO]
  iunfold entPts
  iintro ⟨%pt, %pi, %pty, %ds, %uf, %Hnn, #HT, #cT, #HI, #cI, #HY, #cY, #HD, #Hd, #Hpb⟩
  ihave ⟨%oT, #oT', %hT⟩ := cellRO_optCell pt e.Term' $$ cT
  ihave ⟨%oI, #oI', %hI⟩ := cellRO_optCell pi e.Index' $$ cI
  ihave ⟨%oY, #oY', %hY⟩ := cellRO_optCell pty e.Type' $$ cY
  ihave ⟨%oD, #oD', %hD⟩ := ownSlice_bytesC ds e.Data' $$ Hd
  iexists ⟨oT, oI, oY, oD, uf⟩
  unfold entRoC
  isplitl
  · iexists pt, pi, pty, ds
    iframe HT HI HY HD Hpb oT' oI' oY' oD'
    ipureintro; exact Hnn
  ipureintro
  obtain ⟨a, b, c, d⟩ := e
  simp only [EntryC.model] at *
  rw [hT, hI, hY, hD]

theorem entsRO_entsRoC : ∀ (els : List Loc) (es : List EntryM),
    ([∗list] p;e ∈ els;es, entRO (GF := GF) p e) ⊢
      ∃ ecs : List EntryC, ([∗list] p;c ∈ els;ecs, entRoC p c) ∗ ⌜ecs.map EntryC.model = es⌝
  | [], [] => by
    iintro -; iexists []
    isplitl
    · iapply BigSepL2.bigSepL2_nil.2; iempintro
    · ipureintro; rfl
  | [], _ :: _ => false_elim
  | _ :: _, [] => false_elim
  | p :: ps, e :: es => by
    iintro ⟨#H, #Hr⟩
    ihave ⟨%c, #Hc, %hc⟩ := entRO_entRoC p e $$ H
    ihave ⟨%cs, #Hcs, %hcs⟩ := entsRO_entsRoC ps es $$ Hr
    iexists (c :: cs)
    simp only [BigSepL2.bigSepL2_cons, List.map_cons]
    iframe Hc Hcs
    ipureintro; rw [hc, hcs]

end fromOwn

section fromOwnC
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

theorem csPts_csRoC (p : Loc) (c : ConfStateM) (al : Bool) :
    csPts (GF := GF) p DFrac.discard c al ⊢ ∃ cc : CSC, csRoC p cc ∗ ⌜cc.model = c ∧ cc.uf = []⌝ := by
  iunfold csPts
  iintro ⟨%sv, %sl, %so, %sn, %pa, %Hnn, #HV, #Hv, #HL, #Hl, #HO, #Ho, #HN, #Hn, #HA, #cA, -, #Hpb⟩
  ihave ⟨%oA, #oA', %hA⟩ := cellRO_optCell pa c.AutoLeave' $$ cA
  iexists ⟨c.Voters', c.Learners', c.VotersOutgoing', c.LearnersNext', oA, []⟩
  unfold csRoC
  isplitl
  · iexists sv, sl, so, sn, pa
    iframe HV Hv HL Hl HO Ho HN Hn HA oA' Hpb
    ipureintro; exact Hnn
  ipureintro
  refine ⟨?_, rfl⟩
  obtain ⟨a, b, d, e, f⟩ := c
  simp only [CSC.model] at *
  rw [hA]

theorem csOptA_csOptC (p : Loc) (c : ConfStateM) :
    csOptA (GF := GF) p DFrac.discard c ⊢
      ∃ o : Option CSC, csOptC p o ∗
        ⌜(o.map CSC.model).getD csZero = c ∧ ∀ cc ∈ o, cc.uf = []⌝ := by
  unfold csOptA
  iintro (%H | #H | #H)
  · iexists none
    simp only [csOptC, Option.map_none, Option.getD_none]
    ipureintro; exact ⟨H.1, H.2.symm, by simp⟩
  · ihave ⟨%cc, #Hc, %hc⟩ := csPts_csRoC p c false $$ H
    iexists (some cc)
    simp only [csOptC, Option.map_some, Option.getD_some]
    iframe Hc; ipureintro; exact ⟨hc.1, by simp [hc.2]⟩
  · ihave ⟨%cc, #Hc, %hc⟩ := csPts_csRoC p c true $$ H
    iexists (some cc)
    simp only [csOptC, Option.map_some, Option.getD_some]
    iframe Hc; ipureintro; exact ⟨hc.1, by simp [hc.2]⟩

theorem smPts_metaRoC (p : Loc) (md : SnapshotMetadataM) :
    smPts (GF := GF) p DFrac.discard md ⊢
      ∃ m : SnapMetaC, metaRoC p m ∗ ⌜m.model = md ∧ ∀ cs ∈ m.confState, cs.uf = []⌝ := by
  iunfold smPts
  iintro ⟨%pc, %pi, %pt, %uf, %Hnn, #HC, #Hc, #HI, #cI, #HT, #cT, #Hpb⟩
  ihave ⟨%oC, #oC', %hC⟩ := csOptA_csOptC pc md.ConfState' $$ Hc
  ihave ⟨%oI, #oI', %hI⟩ := cellRO_optCell pi md.Index' $$ cI
  ihave ⟨%oT, #oT', %hT⟩ := cellRO_optCell pt md.Term' $$ cT
  iexists ⟨oC, oI, oT, uf⟩
  unfold metaRoC
  isplitl
  · iexists pc, pi, pt
    iframe HC oC' HI oI' HT oT' Hpb
    ipureintro; exact Hnn
  ipureintro
  refine ⟨?_, hC.2⟩
  obtain ⟨a, b, d⟩ := md
  simp only [SnapMetaC.model] at *
  rw [hC.1, hI, hT]

theorem smOpt_metaOptC (p : Loc) (md : SnapshotMetadataM) :
    smOpt (GF := GF) p DFrac.discard md ⊢
      ∃ o : Option SnapMetaC, metaOptC p o ∗
        ⌜(o.map SnapMetaC.model).getD metaZero = md ∧ ∀ m ∈ o, ∀ cs ∈ m.confState, cs.uf = []⌝ := by
  unfold smOpt
  iintro (%H | #H)
  · iexists none
    simp only [metaOptC, Option.map_none, Option.getD_none]
    ipureintro; exact ⟨H.1, H.2.symm, by simp⟩
  · ihave ⟨%m, #Hm, %hm⟩ := smPts_metaRoC p md $$ H
    iexists (some m)
    simp only [metaOptC, Option.map_some, Option.getD_some]
    iframe Hm; ipureintro; exact ⟨hm.1, by simpa using hm.2⟩

theorem snapOpt_snapOptC (p : Loc) (o : Option SnapshotM) :
    snapOpt (GF := GF) p DFrac.discard o ⊢
      ∃ oc : Option SnapC, snapOptC p oc ∗
        ⌜oc.map SnapC.model = o ∧ ∀ s ∈ oc, ∀ m ∈ s.metadata, ∀ cs ∈ m.confState, cs.uf = []⌝ := by
  cases o with
  | none =>
    simp only [snapOpt]
    iintro %H
    iexists none
    simp only [snapOptC, Option.map_none]
    ipureintro; simpa using H
  | some s =>
    simp only [snapOpt]
    iunfold ownSnapM
    iintro ⟨%ds, %pm, %uf, %Hnn, #HD, #Hd, #HM, #Hm, #Hpb⟩
    ihave ⟨%oD, #oD', %hD⟩ := ownSlice_bytesC ds s.Data' $$ Hd
    ihave ⟨%oM, #oM', %hM⟩ := smOpt_metaOptC pm s.Metadata' $$ Hm
    iexists (some ⟨oD, oM, uf⟩)
    simp only [snapOptC, Option.map_some]
    unfold snapRoC
    isplitl
    · iexists ds, pm
      iframe HD oD' HM oM' Hpb
      ipureintro; exact Hnn
    ipureintro
    refine ⟨?_, by simpa using hM.2⟩
    obtain ⟨a, b⟩ := s
    simp only [SnapC.model] at *
    rw [hD, hM.1]

/-- **A frozen message without responses is frozen at some wire content** (the converse of
`msgRoC_msgOwn`; what `proto.Clone` of a message only held as `msgOwn` takes, e.g.
`linkHeartbeatMessage`). -/
theorem msgOwn_msgRoC (l : Loc) (st : MsgSt) (hr : st.resps = []) :
    msgOwn (GF := GF) l DFrac.discard st ⊢ ∃ c : MsgC, msgRoC l c ∗ ⌜c.model = st ∧ c.csUfNil⌝ := by
  iintro H
  iunfold msgOwn at H
  iunfold msgPts at H
  iunfold msgPtsC at H
  icases H with ⟨%pty, %pto, %pfr, %pte, %plt, %pix, %pco, %pvo, %prj, %prh, %es, %els, %ps, %cs,
    %rsl, %uf, %Hnn, #HTy, #cTy, #HTo, #cTo, #HFr, #cFr, #HTe, #cTe, #HLt, #cLt, #HIx, #cIx,
    #HCo, #cCo, #HVo, #cVo, #HRj, #cRj, #HRh, #cRh, #HEs, #Hes, #Hents, -, #HSn, #Hsn, #HCx,
    #Hcx, #HRs, #Hrs, #Hpb⟩
  ihave ⟨%oTy, #oTy', %hTy⟩ := cellRO_optCell pty st.msg.Type' $$ cTy
  ihave ⟨%oTo, #oTo', %hTo⟩ := cellRO_optCell pto st.msg.To' $$ cTo
  ihave ⟨%oFr, #oFr', %hFr⟩ := cellRO_optCell pfr st.msg.From' $$ cFr
  ihave ⟨%oTe, #oTe', %hTe⟩ := cellRO_optCell pte st.msg.Term' $$ cTe
  ihave ⟨%oLt, #oLt', %hLt⟩ := cellRO_optCell plt st.msg.LogTerm' $$ cLt
  ihave ⟨%oIx, #oIx', %hIx⟩ := cellRO_optCell pix st.msg.Index' $$ cIx
  ihave ⟨%oCo, #oCo', %hCo⟩ := cellRO_optCell pco st.msg.Commit' $$ cCo
  ihave ⟨%oVo, #oVo', %hVo⟩ := cellRO_optCell pvo st.msg.Vote' $$ cVo
  ihave ⟨%oRj, #oRj', %hRj⟩ := cellRO_optCell prj st.msg.Reject' $$ cRj
  ihave ⟨%oRh, #oRh', %hRh⟩ := cellRO_optCell prh st.msg.RejectHint' $$ cRh
  ihave ⟨%oCx, #oCx', %hCx⟩ := ownSlice_bytesC cs st.ctx $$ Hcx
  ihave ⟨%oSn, #oSn', %hSn⟩ := snapOpt_snapOptC ps st.snap $$ Hsn
  ihave ⟨%ecs, #Hecs, %hecs⟩ := entsRO_entsRoC els st.ents $$ Hents
  iexists (MsgC.mk ⟨oTy, oTo, oFr, oTe, oLt, oIx, ecs, oCo, oVo, oSn, oRj, oRh, oCx, uf⟩ [])
  simp only [msgRoC, respsRoC, List.map_nil]
  isplitl
  · isplitl
    · unfold msgFRoC
      iexists pty, pto, pfr, pte, plt, pix, pco, pvo, prj, prh, es, els, ps, cs, rsl
      rw [show ([] : List Loc) = st.resps from hr.symm]
      iframe HTy oTy' HTo oTo' HFr oFr' HTe oTe' HLt oLt' HIx oIx' HCo oCo' HVo oVo' HRj oRj'
      iframe HRh oRh' HEs Hes Hecs HSn oSn' HCx oCx' HRs Hrs Hpb
      ipureintro; exact Hnn
    iempintro
  ipureintro
  refine ⟨?_, hSn.2⟩
  obtain ⟨m, ents, snap, ctx, resps⟩ := st
  obtain ⟨a, b, c, d, e, f, g, i, j, k⟩ := m
  simp only [MsgC.model, MsgC.f, MsgC.resps, MsgFC.msgM, List.map_nil] at *
  rw [hTy, hTo, hFr, hTe, hLt, hIx, hCo, hVo, hRj, hRh, hecs, hSn.1, hCx, hr]

/-- A message's entries' contents, from its wire content: the field, its slice, and each entry
frozen at its content. -/
theorem msgRoC_ents (l : Loc) (c : MsgC) :
    msgRoC (GF := GF) l c ⊢
      ∃ (es : GoSlice) (els : List Loc),
        l.[raftpb.Message, go!"Entries"] ↦□ es ∗ es ↦*□ els ∗
        [∗list] p;e ∈ els;c.f.entries, entRoC p e := by
  cases c with
  | mk f rs =>
  simp only [msgRoC, MsgC.f]
  iintro ⟨H, -⟩
  unfold msgFRoC
  icases H with ⟨%pty, %pto, %pfr, %pte, %plt, %pix, %pco, %pvo, %prj, %prh, %es, %els, %ps, %cs,
    %rsl, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #HEs, #Hes, #Hents, -⟩
  iexists es, els
  iframe HEs Hes Hents

/-- The entries' frozen contents give their log entries (`entRO`) at the models. -/
theorem entsRoC_entsRO (els : List Loc) (ecs : List EntryC) :
    ([∗list] p;e ∈ els;ecs, entRoC (GF := GF) p e) ⊢
      [∗list] p;e ∈ els;ecs.map EntryC.model, entRO p e :=
  (BigSepL2.bigSepL2_mono (Φ := fun _ p e => entRoC (GF := GF) p e)
    (Ψ := fun _ p e => entRO p (EntryC.model e)) (l1 := els) (l2 := ecs)
    (fun _ _ => entRoC_entRO _ _)).trans
    (BigSepL2.bigSepL2_map_right (Φ := fun _ p e => entRO (GF := GF) p e) EntryC.model).2

end fromOwnC

end EtcdGrove
end Perennial
