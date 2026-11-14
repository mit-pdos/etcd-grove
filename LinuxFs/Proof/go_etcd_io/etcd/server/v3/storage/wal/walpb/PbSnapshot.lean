/-
**`walpb.Snapshot` as a registered protobuf message type at its wire content**, and the WAL's
snapshot pointer predicates over it (W6 of `notes/wal-fsext-plan.md`, `SaveSnapshot`'s content
model; the pattern of `PbRecord.lean`).

- The wire content is `WalEnc.WalSnapC` (`Proof/go_etcd_io/etcd/server/v3/storage/WalPbSnapWire.lean`):
  `Index`, `Term` nil or set, `ConfState` nil or a `raftpb.ConfState`'s content (`WalCsC`), the
  unknown fields of both levels. Its model is `SnapshotMetadataM` (`WalSnapC.model`: what the getters
  read, a nil conf state as the zero one).
- `snapRoC l c`: a frozen `*walpb.Snapshot` holding exactly `c` (field-wise persistent points-tos, its
  conf state frozen too, `walCsRoC`), each level's hidden fields (`state`, `sizeCache`,
  `unknownFields`) in an invariant (`snapHidden`, `walCsHidden`: the shape of raft's `pbMsg`, which
  the part cannot import; **at C6** the conf state the server passes is raft's own snapshot
  metadata's, `storage.go:62-66` `ConfState: snap.Metadata.GetConfState()`, whose hidden fields are in
  raft's `pbMsg raftpb.ConfState` invariant: `walCsHidden` must then be that one, as it is word for
  word but the schema's name, `walCsSchema` for `pbSchemaOf raftpb.ConfState`).
- `snapOwnC l c`: the decoded object, owned whole (as `recOwnC`): what `proto.Unmarshal` leaves.
- **The encoder is a transparent Lean function** (`WalEnc.snapEnc`), the decoder `snapDecode` opaque.

**Trusted, pending the user's review** (two axioms, as for every registered type):
- `snapEncC_ok`: protobuf-go decodes `snapEnc c` back to `c`'s model when both levels' unknown
  fields are valid at their schemas. Measured: `examples/stdlib/walpb/snapshot_test.go`
  (`TestSnapshotEncoder`: 200,000 random contents, `proto.Marshal`/`proto.Size` against
  `snapEnc`/`snapSize`, `proto.Unmarshal(snapEnc c)` giving back exactly `c` at both levels;
  `TestSnapshotSchema`: the descriptors against `walSnapSchema`/`walCsSchema`).
- `pbSnapC_reg`: the registration, of the exact shape `pbModelOf GF walpb.Snapshot.ty = some …`.

**The WAL's snapshot predicates** (the part's, in place of the main tree's `WalDisk.lean` ones, which
`etc/gen-part-copies.py` omits from the part's copy; same names):
- `walSnapAt Mr sp md cs`: a frozen snapshot at a content `c` of model `md`, `Index` and `Term` set,
  conf state non-nil iff `cs`, **whose encoding is `Mr.encSnap md`** (the marshaller parameter is the
  client's: one wire form per snapshot metadata, an obligation of the server at C6, ledger
  2026-11-13 "`walSnapAt` ties the object's encoding to `Mr.encSnap`");
- `walSnapIdTerm sp s`: a frozen snapshot whose getters read index and term `s`;
- `walSnapsAt ps snaps`: a list of those.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.walpb.PbRecord
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.WalEncRecs
public import Proof.go_etcd_io.etcd.server.v3.storage.WalPbSnapWire

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.wal go_etcd_io.raft.v3 WalEnc

/-! ## The model -/

/-- The zero conf state (what a nil one reads as). -/
def walCsZero : ConfStateM := ConfStateM.mk [] [] [] [] false

/-- **A conf state's model**: the lists, `AutoLeave` false if nil. -/
def WalEnc.WalCsC.model (c : WalCsC) : ConfStateM :=
  ⟨c.voters, c.learners, c.votersOutgoing, c.learnersNext, c.autoLeave.getD false⟩

/-- **A `walpb.Snapshot`'s model**: what `GetConfState()`, `GetIndex()`, `GetTerm()` read. -/
def WalEnc.WalSnapC.model (s : WalSnapC) : SnapshotMetadataM :=
  ⟨(s.confState.map WalCsC.model).getD walCsZero, s.index.getD (W64 0), s.term.getD (W64 0)⟩

/-- **Decoding a `walpb.Snapshot`'s bytes** (opaque: `proto.Unmarshal`): the model, or `none`. -/
opaque snapDecode (bs : List w8) : Option SnapshotMetadataM

/-- **The trust boundary: `walpb.Snapshot`'s encoding** (pending the user's review; see the file
header). -/
axiom snapEncC_ok (c : WalSnapC) : (∀ p ∈ c.levels, ufWire p.1 p.2) → snapSize c < 2 ^ 63 →
    snapDecode (snapEnc c) = some c.model

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-! ## The frozen object -/

/-- **The hidden fields of a `*walpb.Snapshot`** (as `recHidden`). -/
def snapHidden (l : Loc) (uf : List w8) : IProp GF :=
  iprop(inv (nroot.@"protobuf") iprop(∃ (st : google_golang_org.protobuf.internal.impl.MessageState)
      (sc : w32) (us : GoSlice),
    l.[walpb.Snapshot, go!"state"] ↦ st ∗ l.[walpb.Snapshot, go!"sizeCache"] ↦ sc ∗
      l.[walpb.Snapshot, go!"unknownFields"] ↦ us ∗ us ↦* uf) ∗ ⌜ufWire walSnapSchema uf⌝)

/-- **The hidden fields of a `*raftpb.ConfState`** (raft's `pbMsg raftpb.ConfState` word for word,
at `walCsSchema`; see the file header). -/
def walCsHidden (l : Loc) (uf : List w8) : IProp GF :=
  iprop(inv (nroot.@"protobuf") iprop(∃ (st : google_golang_org.protobuf.internal.impl.MessageState)
      (sc : w32) (us : GoSlice),
    l.[raftpb.ConfState, go!"state"] ↦ st ∗ l.[raftpb.ConfState, go!"sizeCache"] ↦ sc ∗
      l.[raftpb.ConfState, go!"unknownFields"] ↦ us ∗ us ↦* uf) ∗ ⌜ufWire walCsSchema uf⌝)

instance snapHidden_persistent (l : Loc) (uf : List w8) :
    Persistent (snapHidden (GF := GF) l uf) := by unfold snapHidden; infer_instance
instance walCsHidden_persistent (l : Loc) (uf : List w8) :
    Persistent (walCsHidden (GF := GF) l uf) := by unfold walCsHidden; infer_instance

/-- **A frozen `*raftpb.ConfState` holding exactly `c`.** -/
def walCsRoC (p : Loc) (c : WalCsC) : IProp GF :=
  iprop(∃ (sv sl so sn : GoSlice) (pa : Loc),
    ⌜p ≠ null⌝ ∗
    p.[raftpb.ConfState, go!"Voters"] ↦□ sv ∗ sv ↦*□ c.voters ∗
    p.[raftpb.ConfState, go!"Learners"] ↦□ sl ∗ sl ↦*□ c.learners ∗
    p.[raftpb.ConfState, go!"VotersOutgoing"] ↦□ so ∗ so ↦*□ c.votersOutgoing ∗
    p.[raftpb.ConfState, go!"LearnersNext"] ↦□ sn ∗ sn ↦*□ c.learnersNext ∗
    p.[raftpb.ConfState, go!"AutoLeave"] ↦□ pa ∗ recCell pa c.autoLeave ∗
    walCsHidden p c.uf)

/-- A frozen conf state pointer: nil, or a frozen `*raftpb.ConfState`. -/
def walCsOptRoC (p : Loc) : Option WalCsC → IProp GF
  | none => iprop(⌜p = null⌝)
  | some c => walCsRoC p c

set_option synthInstance.maxSize 512 in
set_option synthInstance.maxHeartbeats 200000 in
instance walCsRoC_persistent (p : Loc) (c : WalCsC) : Persistent (walCsRoC (GF := GF) p c) := by
  unfold walCsRoC; infer_instance

instance walCsOptRoC_persistent (p : Loc) (o : Option WalCsC) :
    Persistent (walCsOptRoC (GF := GF) p o) := by
  cases o <;> unfold walCsOptRoC <;> infer_instance

/-- **A frozen `*walpb.Snapshot` at `l` holding exactly `c`.** -/
def snapRoC (l : Loc) (c : WalSnapC) : IProp GF :=
  iprop(∃ (pi pt pc : Loc),
    ⌜l ≠ null⌝ ∗
    l.[walpb.Snapshot, go!"Index"] ↦□ pi ∗ recCell pi c.index ∗
    l.[walpb.Snapshot, go!"Term"] ↦□ pt ∗ recCell pt c.term ∗
    l.[walpb.Snapshot, go!"ConfState"] ↦□ pc ∗ walCsOptRoC pc c.confState ∗
    snapHidden l c.uf)

set_option synthInstance.maxSize 512 in
set_option synthInstance.maxHeartbeats 200000 in
instance snapRoC_persistent (l : Loc) (c : WalSnapC) : Persistent (snapRoC (GF := GF) l c) := by
  unfold snapRoC; infer_instance

/-- A set cell's points-to. -/
theorem recCell_of_eq_some {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] (p : Loc)
    {o : Option V} {v : V} (h : o = some v) : recCell (GF := GF) p o ⊢ p ↦□ v := by
  subst h; unfold recCell; exact .rfl

/-- A frozen conf state pointer is nil iff the content has none. -/
theorem walCsOptRoC_null (p : Loc) (o : Option WalCsC) :
    walCsOptRoC (GF := GF) p o ⊢ ⌜p = null ↔ o = none⌝ := by
  cases o with
  | none => unfold walCsOptRoC; iintro %H; ipureintro; simp [H]
  | some c =>
    unfold walCsOptRoC walCsRoC
    iintro ⟨%sv, %sl, %so, %sn, %pa, %Hn, -⟩
    ipureintro; simp [Hn]

/-- A frozen snapshot is not nil. -/
theorem snapRoC_ne (l : Loc) (c : WalSnapC) : snapRoC (GF := GF) l c ⊢ ⌜l ≠ null⌝ := by
  unfold snapRoC
  iintro ⟨%pi, %pt, %pc, %Hn, -⟩
  ipureintro; exact Hn

/-- A frozen snapshot's unknown fields are valid at both levels. -/
theorem snapRoC_uf (l : Loc) (c : WalSnapC) :
    snapRoC (GF := GF) l c ⊢ ⌜∀ p ∈ c.levels, ufWire p.1 p.2⌝ := by
  unfold snapRoC snapHidden
  iintro ⟨%pi, %pt, %pc, -, -, -, -, -, -, Hc, -, %Hu⟩
  rcases hc : c.confState with _ | cs
  · iclear Hc
    ipureintro
    intro p hp
    simp only [WalSnapC.levels, hc, List.mem_singleton] at hp
    subst hp; exact Hu
  · iunfold walCsOptRoC at Hc
    iunfold walCsRoC at Hc
    iunfold walCsHidden at Hc
    icases Hc with ⟨%sv, %sl, %so, %sn, %pa, -, -, -, -, -, -, -, -, -, -, -, -, %Hcu⟩
    ipureintro
    intro p hp
    simp only [WalSnapC.levels, hc, List.mem_cons, List.mem_singleton, List.not_mem_nil,
      or_false] at hp
    rcases hp with rfl | rfl
    · exact Hu
    · exact Hcu

/-! ## The decoded object -/

/-- A decoded conf state pointer, owned: nil, or a `*raftpb.ConfState` holding exactly `c`. -/
def walCsOwnC (p : Loc) : Option WalCsC → IProp GF
  | none => iprop(⌜p = null⌝)
  | some c => iprop(∃ v : raftpb.ConfState,
      p ↦ v ∗ v.Voters' ↦* c.voters ∗ v.Learners' ↦* c.learners ∗
      v.VotersOutgoing' ↦* c.votersOutgoing ∗ v.LearnersNext' ↦* c.learnersNext ∗
      recCell v.AutoLeave' c.autoLeave ∗ v.unknownFields' ↦* c.uf ∗ ⌜ufWire walCsSchema c.uf⌝)

/-- **A decoded `*walpb.Snapshot` at `l` holding exactly `c`, owned whole** (as `recOwnC`: the
decoded message is fresh, and protobuf-go keeps no reference to it after `Unmarshal` returns). -/
def snapOwnC (l : Loc) (c : WalSnapC) : IProp GF :=
  iprop(∃ v : walpb.Snapshot,
    l ↦ v ∗ recCell v.Index' c.index ∗ recCell v.Term' c.term ∗ walCsOwnC v.ConfState' c.confState ∗
    v.unknownFields' ↦* c.uf ∗ ⌜ufWire walSnapSchema c.uf⌝)

/-! ## The registered instance -/

/-- **The store of a conf state** (always allocated; its lists `nil` if empty, `AutoLeave` `nil`
if `false`), as rafthttp's `csTree`. -/
def walCsTree (c : ConfStateM) : VTree :=
  .ptr raftpb.ConfState.ty (.strct raftpb.ConfState.ty
    [(go!"Voters", go.GoType.SliceType go.uint64), (go!"Learners", go.GoType.SliceType go.uint64),
     (go!"VotersOutgoing", go.GoType.SliceType go.uint64),
     (go!"LearnersNext", go.GoType.SliceType go.uint64),
     (go!"AutoLeave", go.GoType.PointerType go.bool)]
    [bytesTree go.uint64 c.Voters', bytesTree go.uint64 c.Learners',
     bytesTree go.uint64 c.VotersOutgoing', bytesTree go.uint64 c.LearnersNext',
     cellTree go.bool c.AutoLeave'])

/-- **The store of a snapshot's metadata** (each scalar `nil` if zero, the conf state allocated). -/
def walSnapTree (m : SnapshotMetadataM) : VTree :=
  .strct walpb.Snapshot.ty
    [(go!"Index", go.GoType.PointerType go.uint64), (go!"Term", go.GoType.PointerType go.uint64),
     (go!"ConfState", go.GoType.PointerType raftpb.ConfState.ty)]
    [cellTree go.uint64 m.Index', cellTree go.uint64 m.Term', walCsTree m.ConfState']

/-- **`walpb.Snapshot` at its wire content: the data** (no axiom). -/
def pbSnapM : PbModelC GF where
  ty := walpb.Snapshot.ty
  M := SnapshotMetadataM
  ro l m := iprop(∃ c, snapRoC l c ∗ ⌜c.model = m⌝)
  ro_persistent _ _ := inferInstance
  marshals _ := True
  wire m bs := snapDecode bs = some m
  eqv m m' := m = m'
  blank l := iprop(l ↦ (zero_val walpb.Snapshot))
  dec l m := iprop(∃ c, snapOwnC l c ∗ ⌜c.model = m⌝)
  C := WalSnapC
  roC := snapRoC
  roC_persistent _ _ := inferInstance
  modelOf := WalSnapC.model
  levels := WalSnapC.levels
  size := snapSize
  tree := walSnapTree
  decOk _ := True
  ro_iff _ _ := .rfl
  roC_ufValid l c := snapRoC_uf l c
  decC l c := snapOwnC l c
  decC_dec l c _ := by
    iintro H
    iexists c
    iframe H
    ipureintro; rfl

/-- **`walpb.Snapshot` at its wire content** (the registered instance): the data and the encoder
`snapEnc`, whose `enc_ok` is `snapEncC_ok`. -/
def pbSnapC : PbTypeC GF where
  data := pbSnapM
  encd := { enc := snapEnc
            enc_ok := fun c _ hu hs => ⟨snapEncC_ok c hu hs, rfl⟩ }

@[simp] theorem pbEncC_pbSnapC (c : WalSnapC) : pbEncC (pbSnapC (GF := GF)) c = snapEnc c := rfl
@[simp] theorem pbSnapC_ty : (pbSnapC (GF := GF)).data.ty = walpb.Snapshot.ty := rfl
@[simp] theorem pbSnapC_roC : (pbSnapC (GF := GF)).data.roC = snapRoC := rfl
@[simp] theorem pbSnapC_C : (pbSnapC (GF := GF)).data.C = WalSnapC := rfl
@[simp] theorem pbSnapC_modelOf : (pbSnapC (GF := GF)).data.modelOf = WalSnapC.model := rfl
@[simp] theorem pbSnapC_size : (pbSnapC (GF := GF)).data.size = snapSize := rfl
@[simp] theorem pbSnapC_decC (l : Loc) (c : WalSnapC) :
    (pbSnapC (GF := GF)).data.decC l c = snapOwnC l c := rfl

/-! ## The WAL's snapshot predicates (see the file header) -/

/-- **`sp` points to a frozen `walpb.Snapshot` of metadata `md`, with `Index` and `Term` set, whose
conf state is non-nil iff `cs` and whose encoding is `Mr.encSnap md`** (persistent). -/
def walSnapAt (Mr : WalMarshal) (sp : Loc) (md : SnapshotMetadataM) (cs : Bool) : IProp GF :=
  iprop(∃ c : WalSnapC, snapRoC sp c ∗
    ⌜c.model = md ∧ c.index = some md.Index' ∧ c.term = some md.Term' ∧
      cs = c.confState.isSome ∧ snapEnc c = Mr.encSnap md⌝)

/-- **`sp` points to a frozen `walpb.Snapshot` whose getters read index and term `s`**
(persistent). -/
def walSnapIdTerm (sp : Loc) (s : w64 × w64) : IProp GF :=
  iprop(∃ c : WalSnapC, snapRoC sp c ∗ ⌜(c.model.Index', c.model.Term') = s⌝)

/-- **The pointers `ps` point to `walpb.Snapshot`s of indexes and terms `snaps`**, in order
(persistent). -/
def walSnapsAt (ps : List Loc) (snaps : List (w64 × w64)) : IProp GF :=
  iprop([∗list] p; s ∈ ps; snaps, walSnapIdTerm p s)

instance walSnapAt_persistent (Mr : WalMarshal) (sp : Loc) (md : SnapshotMetadataM) (cs : Bool) :
    Persistent (walSnapAt (GF := GF) Mr sp md cs) := by unfold walSnapAt; infer_instance
instance walSnapIdTerm_persistent (sp : Loc) (s : w64 × w64) :
    Persistent (walSnapIdTerm (GF := GF) sp s) := by unfold walSnapIdTerm; infer_instance

/-- A snapshot of metadata `md` reads index and term `md`'s. -/
theorem walSnapAt_idTerm (Mr : WalMarshal) (sp : Loc) (md : SnapshotMetadataM) (cs : Bool) :
    walSnapAt (GF := GF) Mr sp md cs ⊢ walSnapIdTerm sp (md.Index', md.Term') := by
  unfold walSnapAt walSnapIdTerm
  iintro ⟨%c, #H, %Hm, -⟩
  iexists c
  iframe H
  ipureintro; rw [Hm]

end defs

/-- **The registration** of `pbSnapC` (exact shape; pending the user's review). -/
axiom pbSnapC_reg [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
    {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [go.Semantics] :
    pbModelOf GF walpb.Snapshot.ty = some (pbSnapC (GF := GF))

end EtcdGrove
end Perennial
