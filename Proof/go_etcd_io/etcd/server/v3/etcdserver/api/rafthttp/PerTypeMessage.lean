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
  frozen at its content, each level's `pbMsg` at its `uf` and `uf`'s validity), and the bridge
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
- `Entry`: `entrySchema` (`PerTypeEntry.lean`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.PerTypeEntry

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

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

/-! ## The schemas (trusted: `proto/PerType.lean`'s header; sources in the file header) -/

/-- `raft.proto:62-99`. -/
def msgSchema : FieldSchema :=
  [(1, [0]), (2, [0]), (3, [0]), (4, [0]), (5, [0]), (6, [0]), (7, [2]), (8, [0]), (9, [2]),
   (10, [0]), (11, [0]), (12, [2]), (13, [0]), (14, [2])]

/-- `raft.proto:25-28`. -/
def snapSchema : FieldSchema := [(1, [2]), (2, [2])]

/-- `raft.proto:19-23`. -/
def metaSchema : FieldSchema := [(1, [2]), (2, [0]), (3, [0])]

/-- `raft.proto:127-142`: the repeated `uint64`s unpacked (`0`) or packed (`2`). -/
def csSchema : FieldSchema := [(1, [0, 2]), (2, [0, 2]), (3, [0, 2]), (4, [0, 2]), (5, [0])]

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

/-- **The encoding of a `Message`'s wire content** (opaque: protobuf-go's `Marshal`). -/
opaque msgEncC [GooseExts] (c : MsgC) : List w8

/-- **The trust boundary: `Message`'s encoding** (the type's one trusted fact, the shape of
`entryEncC_ok`). To be backed by Go round-trip tests: `Unmarshal(Marshal(m))` gives the wire view,
and `proto.Size(m)` is `msgSize`, for every presence combination and unknown fields routed as
`ufWire` says, at every level. Only claimed of messages that marshal (no responses). -/
axiom msgEncC_ok [GooseExts] (c : MsgC) : MsgMarshals c.model → (∀ p ∈ c.levels, ufWire p.1 p.2) →
    msgSize c < 2 ^ 63 → MsgWireOk c.model (msgEncC c) ∧ (msgEncC c).length = msgSize c

/-! ## The frozen message at its wire content -/

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
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
    pbMsg raftpb.ConfState p c.uf ∗ ⌜ufWire csSchema c.uf⌝)

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
    pbMsg raftpb.SnapshotMetadata p m.uf ∗ ⌜ufWire metaSchema m.uf⌝)

def metaOptC (p : Loc) : Option SnapMetaC → IProp GF
  | none => iprop(⌜p = null⌝)
  | some m => metaRoC p m

/-- **A frozen `*Snapshot` holding exactly `s`.** -/
def snapRoC (p : Loc) (s : SnapC) : IProp GF :=
  iprop(∃ (ds : GoSlice) (pm : Loc),
    ⌜p ≠ null⌝ ∗
    p.[raftpb.Snapshot, go!"Data"] ↦□ ds ∗ bytesC ds s.data ∗
    p.[raftpb.Snapshot, go!"Metadata"] ↦□ pm ∗ metaOptC pm s.metadata ∗
    pbMsg raftpb.Snapshot p s.uf ∗ ⌜ufWire snapSchema s.uf⌝)

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
    pbMsg raftpb.Message l f.uf ∗ ⌜ufWire msgSchema f.uf⌝)

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
  iintro ⟨%sv, %sl, %so, %sn, %pa, %Hnn, #HV, #Hv, #HL, #Hl, #HO, #Ho, #HN, #Hn, #HA, #cA, #Hpb, -⟩
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
  iintro ⟨%pc, %pi, %pt, %Hnn, #HC, #Hc, #HI, #cI, #HT, #cT, #Hpb, -⟩
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
    iintro ⟨%ds, %pm, %Hnn, #HD, #Hd, #HM, #Hm, #Hpb, -⟩
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
    #Hpb, -⟩
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

theorem entRoC_uf (p : Loc) (e : EntryC) : entRoC (GF := GF) p e ⊢ ⌜ufWire entrySchema e.uf⌝ := by
  unfold entRoC
  iintro ⟨%pt, %pi, %pty, %ds, -, -, -, -, -, -, -, -, -, -, %Hu⟩
  ipureintro; exact Hu

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
    iintro ⟨%sv, %sl, %so, %sn, %pa, -, -, -, -, -, -, -, -, -, -, -, -, %Hu⟩
    ipureintro; intro q hq; rw [List.mem_singleton] at hq; subst hq; exact Hu

theorem metaOptC_uf (p : Loc) (o : Option SnapMetaC) :
    metaOptC (GF := GF) p o ⊢ ⌜∀ q ∈ metaLevels o, ufWire q.1 q.2⌝ := by
  cases o with
  | none => simp only [metaOptC, metaLevels]; iintro -; ipureintro; simp
  | some m =>
    simp only [metaOptC, metaLevels]
    unfold metaRoC
    iintro ⟨%pc, %pi, %pt, -, -, #Hc, -, -, -, -, -, %Hu⟩
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
    iintro ⟨%ds, %pm, -, -, -, -, #Hm, -, %Hu⟩
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
    -, -, %Hu⟩
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
`Entries` capacity. -/
def pbMessageM : PbModelC GF where
  ty := raftpb.Message.ty
  M := MsgSt
  ro l st := iprop(∃ c, msgRoC l c ∗ ⌜c.model = st⌝)
  ro_persistent _ _ := inferInstance
  marshals := MsgMarshals
  wire := MsgWireOk
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
  ro_iff _ _ := .rfl
  roC_ufValid := msgRoC_uf

/-- **`raftpb.Message` at its wire content** (the registered instance): the data and the encoder,
whose `enc_ok` is the type's one trusted fact `msgEncC_ok`. -/
def pbMessageC : PbTypeC GF where
  data := pbMessageM
  encd := { enc := msgEncC
            enc_ok := fun c hm hu hs => msgEncC_ok c hm hu hs }

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
  · iapply pbMsg_alloc
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
  · iapply pbMsg_alloc
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
  · iapply pbMsg_alloc
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
  · iapply pbMsg_alloc
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

end EtcdGrove
end Perennial
