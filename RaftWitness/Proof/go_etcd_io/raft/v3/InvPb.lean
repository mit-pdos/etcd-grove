/-
The ownership of raftpb's protobuf-go v2 messages (raft v3.7 retarget, stage R1:
`notes/raft-retarget-plan.md`, "Design", D2 to D5, and the decisions on its open questions).

In raft v3.7 every raftpb message is a struct of pointers (`*uint64`, `*bool`, `*EntryType`,
...), slices and nested message pointers, read through nil-safe getters, plus three fields of
protobuf's runtime (`state`, `sizeCache`, `unknownFields`). Raft never writes *through* a scalar
pointer field: a field is set by storing a fresh `new(x)` into it (`raft.go:817-819`, every
`&pb.Message{...}`, `Ensure*`), and cells are shared between objects (a response's `To` is the
request's `From` cell). So:

* **`cellRO p v`**: a scalar field's cell, persistent: `nil` with `v` the zero value (what the
  getter returns for a `nil` field), or `p ↦□ v`. Every scalar field of every predicate below
  is a `cellRO`; only the struct's own field (the pointer) is owned, at the predicate's
  fraction.
* **`pbMsg T l uf`**, the hidden fields (decision on Q4): an invariant per protobuf object `l`
  of Go type `T`, holding its `state`, `sizeCache` and `unknownFields` (whose bytes are `uf`),
  which only the trust-boundary axioms of `google.golang.org/protobuf/proto`
  (`Spec/google_golang_org/protobuf/proto/*Entry.lean`, ...) take. Verified code never touches
  those fields; protobuf's runtime does, and on shared objects: `proto.Size` stores the size
  cache atomically into log entries several holders read (`entsSize`, `limitSize`), so a
  persistent read-only entry fact is consistent only with the hidden fields outside it. Made
  once per object (`pbMsg_alloc`, from the fresh struct's hidden fields), persistent. The
  unknown fields are the invariant's index because `proto.Equal` compares them
  (`ConfState.Equivalent`): a `ConfState` raft handles has none (`csPts`, below; the issue
  `raft-confstate-unknown-fields-panic`).

The predicates, each composed structurally of its nested objects' (one `pbMsg` per object), with
the model records of `PbModel.lean` as indices:

* `entPts l dq e`: a `*pb.Entry` holding `e`; `entRO l e` (`dq = □`) is the persistent fact of a
  log entry (raft writes an entry only between its allocation and its append, D2), `entOwn l e`
  (`dq = 1`) a fresh one being filled (`appendEntry`'s clone). `Data`'s bytes are the record's
  (D6) and read-only for good (`ds ↦*□ e.Data'`, at every `dq`): raft never writes them.
* `msgPts l dq dqe ms`: a `*pb.Message` holding `ms : MsgSt` (the scalars `ms.msg : MessageM`, the
  entries, the snapshot, the context bytes, the responses' pointers); its pointer fields at
  `dq` (raft replaces them: `m.To = new(...)`, `send`), its `Entries` slice at `dqe` (read-only
  `□` for a message built from the log, owned for a proposal, whose slots `stepLeader`
  replaces), each entry `entRO`, `Context` read-only bytes, `Snapshot` as `snapOpt`; `msgOwn l dq
  ms` is `dqe = □`. The responses' own ownership is the holder's (a `MsgStorage*` message's).
  (Stage R4: `msgPts` is `msgPtsC l dq dqe false ms`; `msgPtsC ... true` also owns the `Entries`
  slice's capacity, and `msgIn l dqe ms`, a message `raft.Step` receives, is it at `dq = 1`.
  The `Message` getters' specs are on `msgPtsC` at any `cap`; the lemmas on messages that need
  the snapshots' persistence are in `InvPbMsg.lean`.)
* `csPts p dq c al`: a `*pb.ConfState` (the four lists at `dq`, `AutoLeave` a cell, `al`: its
  pointer is set); `ownCSM p dq c` is `al = false`. `smPts`, `ownSnapM`: a snapshot's metadata
  and the snapshot (its `Data` bytes at `dq`), nil nested pointers reading as the zero record
  (`csOpt`, `smOpt`); `snapOpt p dq o`: a nil-or-owned snapshot. A snapshot's nested conf state
  is `csOptA` (D7, stage R4): nil, owned at the snapshot's fraction, or read-only for good with
  its `AutoLeave` set (`MemoryStorage.InitialState` freezes the storage's, which `newRaft` keeps;
  nothing writes a conf state in place once its `AutoLeave` is set).
* `hsRO p hs`: a hard state, persistent (fresh per `hardState()`, never written after).
* `ccsPts`/`ccsRO`: a `*pb.ConfChangeSingle`; `ownCCV1`, `ownCCV2`: a `*pb.ConfChange`,
  `*pb.ConfChangeV2` (their `Context` bytes read-only, shared by `ConfChange.AsV2`); `ownCCI`: a
  `ConfChangeI` interface holding a pointer to either.
-/
module

public import RaftWitness.Proof.go_etcd_io.raft.v3.Defs
public import RaftWitness.Proof.go_etcd_io.raft.v3.CCModel
public import RaftWitness.Proof.go_etcd_io.raft.v3.ProjSimps

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

/-! ## The records -/

/-- What a `*pb.Message` holds beyond its scalars (D3): its scalar fields as the model reads them
(`msg`), the entries behind `Entries`, the snapshot behind `Snapshot` (`none`: `nil`), the bytes
behind `Context`, and the pointers in `Responses` (whose objects the holder owns). -/
structure MsgSt [FfiSyntax] where
  msg : MessageM
  ents : List EntryM
  snap : Option SnapshotM
  ctx : List w8
  resps : List Loc

/-! ## Pure: conf states compared (`ConfState.Equivalent`)

`CSLists.Perm`, `CSLists.Bounded` (from the old `InvStorage.lean`) and `SortedW64`,
`sorted_perm_eq` (from the old `InvRaftpb.lean`, whose `confStateDeepEq` is gone with
`reflect.DeepEqual`), moved here verbatim: `ConfState.Equivalent`'s spec states them. -/

section pure

/-- Each list a permutation of the other's. -/
def CSLists.Perm (a b : CSLists) : Prop :=
  a.voters ≡ₚ b.voters ∧ a.learners ≡ₚ b.learners ∧ a.outgoing ≡ₚ b.outgoing ∧
  a.learnersNext ≡ₚ b.learnersNext

/-- Each list at most `2^62` long (`slices.Sort`'s bound). -/
def CSLists.Bounded (a : CSLists) : Prop :=
  (a.voters.length : Int) ≤ 2 ^ 62 ∧ (a.learners.length : Int) ≤ 2 ^ 62 ∧
  (a.outgoing.length : Int) ≤ 2 ^ 62 ∧ (a.learnersNext.length : Int) ≤ 2 ^ 62

/-- The four lists of a conf state, as `CSLists` (the old proof's lists behind a `ConfState`'s
slices). -/
def ConfStateM.lists (c : ConfStateM) : CSLists :=
  ⟨c.Voters', c.Learners', c.VotersOutgoing', c.LearnersNext'⟩

/-- Sorted by `uint.Z`, as `slices.Sort`'s spec states it (`Spec/slices_Sort.lean`). -/
def SortedW64 (xs : List w64) : Prop :=
  ∀ (i j : Nat) (xi xj : w64), xs[i]? = some xi → xs[j]? = some xj → i < j →
    uint.Z xi ≤ uint.Z xj

theorem sortedW64_iff_pairwise (xs : List w64) :
    SortedW64 xs ↔ xs.Pairwise (fun a b => uint.Z a ≤ uint.Z b) := by
  rw [List.pairwise_iff_getElem]
  constructor
  · intro h i j hi hj hij
    exact h i j _ _ (List.getElem?_eq_getElem hi) (List.getElem?_eq_getElem hj) hij
  · intro h i j xi xj hxi hxj hij
    obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.1 hxi
    obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.1 hxj
    exact h i j hi hj hij

theorem w64_eq_of_le_le {a b : w64} (h1 : uint.Z a ≤ uint.Z b) (h2 : uint.Z b ≤ uint.Z a) :
    a = b := by
  word

/-- Two sorted permutations of each other are equal: what makes `Equivalent`'s sorted
copies of permuted lists equal. -/
theorem sorted_perm_eq : ∀ (xs ys : List w64), xs ≡ₚ ys →
    xs.Pairwise (fun a b => uint.Z a ≤ uint.Z b) →
    ys.Pairwise (fun a b => uint.Z a ≤ uint.Z b) → xs = ys
  | [], ys, hp, _, _ => (List.Perm.nil_eq hp).symm ▸ rfl
  | _ :: _, [], hp, _, _ => absurd (List.Perm.length_eq hp) (by simp)
  | x :: xs, y :: ys, hp, hx, hy => by
    rw [List.pairwise_cons] at hx hy
    have hxy : x = y := by
      have hxin : x ∈ y :: ys := hp.subset (List.mem_cons_self ..)
      have hyin : y ∈ x :: xs := hp.symm.subset (List.mem_cons_self ..)
      rcases List.mem_cons.1 hxin with h | h
      · exact h
      rcases List.mem_cons.1 hyin with h' | h'
      · exact h'.symm
      exact w64_eq_of_le_le (hx.1 y h') (hy.1 x h)
    subst hxy
    have hp' : xs ≡ₚ ys := List.Perm.cons_inv hp
    rw [sorted_perm_eq xs ys hp' hx.2 hy.2]

/-- What `(*ConfChange).AsV2` makes of a `ConfChange` holding `m`: the one change
`{Type, NodeId}`, the `Auto` transition, the same context (`raftpb/confchange.go:58`). -/
def CCV1M.asV2 [FfiSyntax] (m : CCV1M) : CCV2M :=
  { transition := W32 0, changes := [ConfChangeSingleM.mk m.type m.nodeId], context := m.context }

end pure

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-! ## Cells and hidden fields -/

/-- A scalar field's cell (`*uint64`, `*bool`, `*EntryType`, ...): `nil`, read as the zero value,
or a persistent points-to (raft never writes through such a pointer). -/
def cellRO {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] (p : Loc) (v : V) : IProp GF :=
  iprop(⌜p = null ∧ v = zero_val V⌝ ∨ p ↦□ v)

/-- The namespace of the hidden-field invariants. -/
def pbN : Namespace := nroot.@"protobuf"

/-- **The hidden fields** of the protobuf object at `l` of Go type `T` (the Lean struct of a
generated message), its unknown fields' bytes `uf`: an invariant only the `proto.*` axioms take
(see the file header). -/
def pbMsg (T : Type) (l : Loc) (uf : List w8) : IProp GF :=
  inv pbN iprop(∃ (st : google_golang_org.protobuf.internal.impl.MessageState) (sc : w32)
      (us : GoSlice),
    l.[T, go!"state"] ↦ st ∗ l.[T, go!"sizeCache"] ↦ sc ∗ l.[T, go!"unknownFields"] ↦ us ∗
      us ↦* uf)

instance cellRO_persistent {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] (p : Loc) (v : V) :
    Persistent (cellRO (GF := GF) p v) := by
  unfold cellRO; infer_instance

theorem cellRO_cases {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] (p : Loc) (v : V) :
    cellRO (GF := GF) p v ⊢ ⌜p = null ∧ v = zero_val V⌝ ∨ (p ↦□ v ∗ ⌜p ≠ null⌝) := by
  unfold cellRO
  iintro (%H | #H)
  · ileft; ipureintro; exact H
  · ihave %Hn := typedPointsto_not_null $$ H
    iright; iframe H; ipureintro; exact Hn

theorem cellRO_null {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] :
    ⊢ cellRO (GF := GF) null (zero_val V) := by
  unfold cellRO; ileft; ipureintro; exact ⟨rfl, rfl⟩

instance pbMsg_persistent (T : Type) (l : Loc) (uf : List w8) :
    Persistent (pbMsg (GF := GF) T l uf) := by
  unfold pbMsg; infer_instance

/-! ## Entries -/

/-- A `*pb.Entry` at `l` holding `e`, its fields at `dq` (see the file header). -/
def entPts (l : Loc) (dq : DFrac) (e : EntryM) : IProp GF :=
  iprop(∃ (pt pi pty : Loc) (ds : GoSlice) (uf : List w8) (ps : Loc),
    "%Hnn" ∷ ⌜l ≠ null⌝ ∗
    "HT" ∷ l.[raftpb.Entry, go!"Term"] ↦{dq} pt ∗ "#cT" ∷ cellRO pt e.Term' ∗
    "HI" ∷ l.[raftpb.Entry, go!"Index"] ↦{dq} pi ∗ "#cI" ∷ cellRO pi e.Index' ∗
    "HY" ∷ l.[raftpb.Entry, go!"Type"] ↦{dq} pty ∗ "#cY" ∷ cellRO pty e.Type' ∗
    "HD" ∷ l.[raftpb.Entry, go!"Data"] ↦{dq} ds ∗ "#Hd" ∷ ds ↦*□ e.Data' ∗
    "HS" ∷ l.[raftpb.Entry, go!"Subterm"] ↦{dq} ps ∗ "#cS" ∷ cellRO ps e.Subterm' ∗
    "#Hpb" ∷ pbMsg raftpb.Entry l uf)

/-- A log entry: read-only for good (D2). -/
abbrev entRO (l : Loc) (e : EntryM) : IProp GF := entPts l DFrac.discard e

/-- A fresh entry, owned (`appendEntry`'s clone, before it is stamped and appended). -/
abbrev entOwn (l : Loc) (e : EntryM) : IProp GF := entPts l (DFrac.own 1) e

set_option synthInstance.maxSize 512 in
instance entRO_persistent (l : Loc) (e : EntryM) : Persistent (entRO (GF := GF) l e) := by
  unfold entRO entPts; infer_instance

/-! ## Conf states, snapshots, hard states -/

/-- A `*pb.ConfState` at `p` holding `c`: its four id slices and their lists at `dq`, its
`AutoLeave` a cell (`al`: the pointer is set, as `Equivalent` makes it before `proto.Equal`), no
unknown fields (`proto.Equal` compares them; see the file header). -/
def csPts (p : Loc) (dq : DFrac) (c : ConfStateM) (al : Bool) : IProp GF :=
  iprop(∃ (sv sl so sn : GoSlice) (pa pw pwo : Loc),
    "%Hnn" ∷ ⌜p ≠ null⌝ ∗
    "HV" ∷ p.[raftpb.ConfState, go!"Voters"] ↦{dq} sv ∗ "Hv" ∷ sv ↦*{dq} c.Voters' ∗
    "HL" ∷ p.[raftpb.ConfState, go!"Learners"] ↦{dq} sl ∗ "Hl" ∷ sl ↦*{dq} c.Learners' ∗
    "HO" ∷ p.[raftpb.ConfState, go!"VotersOutgoing"] ↦{dq} so ∗
      "Ho" ∷ so ↦*{dq} c.VotersOutgoing' ∗
    "HN" ∷ p.[raftpb.ConfState, go!"LearnersNext"] ↦{dq} sn ∗
      "Hn" ∷ sn ↦*{dq} c.LearnersNext' ∗
    "HA" ∷ p.[raftpb.ConfState, go!"AutoLeave"] ↦{dq} pa ∗ "#cA" ∷ cellRO pa c.AutoLeave' ∗
      "%Hal" ∷ ⌜al = true → pa ≠ null⌝ ∗
    "HW" ∷ p.[raftpb.ConfState, go!"Witness"] ↦{dq} pw ∗ "#cW" ∷ cellRO pw c.Witness' ∗
    "HWO" ∷ p.[raftpb.ConfState, go!"WitnessOutgoing"] ↦{dq} pwo ∗ "#cWO" ∷ cellRO pwo (W64 0) ∗
    "#Hpb" ∷ pbMsg raftpb.ConfState p [])

/-- A `*pb.ConfState`, owned at `dq`. -/
abbrev ownCSM (p : Loc) (dq : DFrac) (c : ConfStateM) : IProp GF := csPts p dq c false

/-- A nested conf state: `nil` (read as the zero record) or owned. -/
def csOpt (p : Loc) (dq : DFrac) (c : ConfStateM) : IProp GF :=
  iprop(⌜p = null ∧ c = ConfStateM.mk [] [] [] [] false (W64 0)⌝ ∨ ownCSM p dq c)

/-- A snapshot's nested conf state (D7, stage R4): `nil` (read as the zero record), owned at the
snapshot's fraction, or read-only for good with its `AutoLeave` set (frozen by
`MemoryStorage.InitialState`; nothing writes a conf state in place once `AutoLeave` is set:
`EnsureConfState` writes only a nil one). -/
def csOptA (p : Loc) (dq : DFrac) (c : ConfStateM) : IProp GF :=
  iprop(⌜p = null ∧ c = ConfStateM.mk [] [] [] [] false (W64 0)⌝ ∨ csPts p dq c false ∨
    csPts p DFrac.discard c true)

/-- A `*pb.SnapshotMetadata` at `p` holding `md`, at `dq`. -/
def smPts (p : Loc) (dq : DFrac) (md : SnapshotMetadataM) : IProp GF :=
  iprop(∃ (pc pi pt : Loc) (uf : List w8),
    "%Hnn" ∷ ⌜p ≠ null⌝ ∗
    "HC" ∷ p.[raftpb.SnapshotMetadata, go!"ConfState"] ↦{dq} pc ∗ "Hc" ∷ csOptA pc dq md.ConfState' ∗
    "HI" ∷ p.[raftpb.SnapshotMetadata, go!"Index"] ↦{dq} pi ∗ "#cI" ∷ cellRO pi md.Index' ∗
    "HT" ∷ p.[raftpb.SnapshotMetadata, go!"Term"] ↦{dq} pt ∗ "#cT" ∷ cellRO pt md.Term' ∗
    "#Hpb" ∷ pbMsg raftpb.SnapshotMetadata p uf)

/-- A nested snapshot metadata: `nil` (read as the zero record) or owned. -/
def smOpt (p : Loc) (dq : DFrac) (md : SnapshotMetadataM) : IProp GF :=
  iprop(⌜p = null ∧ md = SnapshotMetadataM.mk (ConfStateM.mk [] [] [] [] false (W64 0)) (W64 0) (W64 0)⌝ ∨
    smPts p dq md)

/-- A `*pb.Snapshot` at `p` holding `s`, owned at `dq` (D4): its `Data` bytes and its metadata. -/
def ownSnapM (p : Loc) (dq : DFrac) (s : SnapshotM) : IProp GF :=
  iprop(∃ (ds : GoSlice) (pm : Loc) (uf : List w8),
    "%Hnn" ∷ ⌜p ≠ null⌝ ∗
    "HD" ∷ p.[raftpb.Snapshot, go!"Data"] ↦{dq} ds ∗ "Hd" ∷ ds ↦*{dq} s.Data' ∗
    "HM" ∷ p.[raftpb.Snapshot, go!"Metadata"] ↦{dq} pm ∗ "Hm" ∷ smOpt pm dq s.Metadata' ∗
    "#Hpb" ∷ pbMsg raftpb.Snapshot p uf)

/-- A snapshot pointer that may be `nil` (`none`), e.g. a message's or a `Ready`'s. -/
def snapOpt (p : Loc) (dq : DFrac) : Option SnapshotM → IProp GF
  | none => iprop(⌜p = null⌝)
  | some s => ownSnapM p dq s

/-- A `*pb.HardState` at `p` holding `hs`: read-only for good (D4: fresh per `hardState()`,
never written after, shared by `Ready`, `prevHardSt`, `MemoryStorage`). -/
def hsRO (p : Loc) (hs : HardStateM) : IProp GF :=
  iprop(∃ (pt pv pc : Loc) (uf : List w8),
    "%Hnn" ∷ ⌜p ≠ null⌝ ∗
    "HT" ∷ p.[raftpb.HardState, go!"Term"] ↦□ pt ∗ "#cT" ∷ cellRO pt hs.Term' ∗
    "HV" ∷ p.[raftpb.HardState, go!"Vote"] ↦□ pv ∗ "#cV" ∷ cellRO pv hs.Vote' ∗
    "HC" ∷ p.[raftpb.HardState, go!"Commit"] ↦□ pc ∗ "#cC" ∷ cellRO pc hs.Commit' ∗
    "#Hpb" ∷ pbMsg raftpb.HardState p uf)

/-! ## Messages -/

/-- A `*pb.Message` at `l` holding `ms` (D3): its pointer fields at `dq`, its `Entries` slice's
elements at `dqe` (see the file header), each entry read-only, its `Context` bytes read-only, its
snapshot owned at `dq`, its `Responses` slice's elements at `dq`; and, when `cap`, the capacity
of its `Entries` slice, owned (stage R4: a message `Step` receives, `msgIn`, whose array
`unstable.truncateAndAppend` may adopt). -/
def msgPtsC (l : Loc) (dq dqe : DFrac) (cap : Bool) (ms : MsgSt) : IProp GF :=
  iprop(∃ (pty pto pfr pte plt pix pco pvo prj prh : Loc) (es : GoSlice) (els : List Loc)
      (ps : Loc) (cs rs : GoSlice) (uf : List w8),
    "%Hnn" ∷ ⌜l ≠ null⌝ ∗
    "HTy" ∷ l.[raftpb.Message, go!"Type"] ↦{dq} pty ∗ "#cTy" ∷ cellRO pty ms.msg.Type' ∗
    "HTo" ∷ l.[raftpb.Message, go!"To"] ↦{dq} pto ∗ "#cTo" ∷ cellRO pto ms.msg.To' ∗
    "HFr" ∷ l.[raftpb.Message, go!"From"] ↦{dq} pfr ∗ "#cFr" ∷ cellRO pfr ms.msg.From' ∗
    "HTe" ∷ l.[raftpb.Message, go!"Term"] ↦{dq} pte ∗ "#cTe" ∷ cellRO pte ms.msg.Term' ∗
    "HLt" ∷ l.[raftpb.Message, go!"LogTerm"] ↦{dq} plt ∗ "#cLt" ∷ cellRO plt ms.msg.LogTerm' ∗
    "HIx" ∷ l.[raftpb.Message, go!"Index"] ↦{dq} pix ∗ "#cIx" ∷ cellRO pix ms.msg.Index' ∗
    "HCo" ∷ l.[raftpb.Message, go!"Commit"] ↦{dq} pco ∗ "#cCo" ∷ cellRO pco ms.msg.Commit' ∗
    "HVo" ∷ l.[raftpb.Message, go!"Vote"] ↦{dq} pvo ∗ "#cVo" ∷ cellRO pvo ms.msg.Vote' ∗
    "HRj" ∷ l.[raftpb.Message, go!"Reject"] ↦{dq} prj ∗ "#cRj" ∷ cellRO prj ms.msg.Reject' ∗
    "HRh" ∷ l.[raftpb.Message, go!"RejectHint"] ↦{dq} prh ∗
      "#cRh" ∷ cellRO prh ms.msg.RejectHint' ∗
    "HEs" ∷ l.[raftpb.Message, go!"Entries"] ↦{dq} es ∗ "Hes" ∷ es ↦*{dqe} els ∗
      "#Hents" ∷ ([∗list] p;e ∈ els;ms.ents, entRO p e) ∗
      "Hes_cap" ∷ (if cap then ownSliceCap Loc es (DFrac.own 1) else emp) ∗
    "HSn" ∷ l.[raftpb.Message, go!"Snapshot"] ↦{dq} ps ∗ "Hsn" ∷ snapOpt ps dq ms.snap ∗
    "HCx" ∷ l.[raftpb.Message, go!"Context"] ↦{dq} cs ∗ "#Hcs" ∷ cs ↦*□ ms.ctx ∗
    "HRs" ∷ l.[raftpb.Message, go!"Responses"] ↦{dq} rs ∗ "Hrs" ∷ rs ↦*{dq} ms.resps ∗
    "#Hpb" ∷ pbMsg raftpb.Message l uf)

/-- A message without its `Entries` capacity (R1's `msgPts`). -/
abbrev msgPts (l : Loc) (dq dqe : DFrac) (ms : MsgSt) : IProp GF := msgPtsC l dq dqe false ms

/-- A message whose entries slice is read-only (every message raft builds, D3). -/
abbrev msgOwn (l : Loc) (dq : DFrac) (ms : MsgSt) : IProp GF := msgPts l dq DFrac.discard ms

/-- Whether a received message of type `ty` carries its `Entries` slice's capacity (stage R5):
only a `MsgApp`, whose array `unstable.truncateAndAppend` may adopt (`handleAppendEntries` →
`logSliceFromMsgApp` → `raftLog.maybeAppend`); no other path reads the capacity.
Stated on the message, not its type, so that rewriting `m.Type'` (by a hypothesis
`m.Type' = MsgBeat`) leaves a `msgIn` intact. -/
@[reducible] def needsCap (m : MessageM) : Bool := decide (m.Type' = MsgApp)

theorem needsCap_of_eq {m : MessageM} (h : m.Type' = MsgApp) : needsCap m = true := by
  simp [needsCap, h]

theorem needsCap_of_ne {m : MessageM} (h : m.Type' ≠ MsgApp) : needsCap m = false := by
  simp [needsCap, h]

/-- A message `raft.Step` receives (stage R4, Q3): the struct at `1` (`stepFollower` replaces
`To`, `send` `From`/`Term`), the `Entries` slice's elements at `dqe` (`1` for a `MsgProp`,
whose slots `stepLeader` replaces; `□` otherwise) and, for a `MsgApp` only (`needsCap`, stage
R5), the slice's capacity at `1` (a `MsgApp`'s array is adopted by
`unstable.truncateAndAppend`), the snapshot at `1` (`EnsureSnapshot`/`EnsureConfState` write
its nil fields). Taken for good. -/
abbrev msgIn (l : Loc) (dqe : DFrac) (ms : MsgSt) : IProp GF :=
  msgPtsC l (DFrac.own 1) dqe (needsCap ms.msg) ms

/-! ## Conf changes -/

/-- A `*pb.ConfChangeSingle` at `p` holding `c`, at `dq`. -/
def ccsPts (p : Loc) (dq : DFrac) (c : ConfChangeSingleM) : IProp GF :=
  iprop(∃ (pt pn : Loc) (uf : List w8),
    "%Hnn" ∷ ⌜p ≠ null⌝ ∗
    "HT" ∷ p.[raftpb.ConfChangeSingle, go!"Type"] ↦{dq} pt ∗ "#cT" ∷ cellRO pt c.Type' ∗
    "HN" ∷ p.[raftpb.ConfChangeSingle, go!"NodeId"] ↦{dq} pn ∗ "#cN" ∷ cellRO pn c.NodeId' ∗
    "#Hpb" ∷ pbMsg raftpb.ConfChangeSingle p uf)

/-- A conf change of a `ConfChangeV2`'s list: read-only (built once, `toConfChangeSingle`, `AsV2`). -/
abbrev ccsRO (p : Loc) (c : ConfChangeSingleM) : IProp GF := ccsPts p DFrac.discard c

/-- A `*pb.ConfChange` at `p` holding `m`, at `dq`; its `Context` bytes read-only. -/
def ownCCV1 (p : Loc) (dq : DFrac) (m : CCV1M) : IProp GF :=
  iprop(∃ (pt pn pi : Loc) (cs : GoSlice) (uf : List w8),
    "%Hnn" ∷ ⌜p ≠ null⌝ ∗
    "HT" ∷ p.[raftpb.ConfChange, go!"Type"] ↦{dq} pt ∗ "#cT" ∷ cellRO pt m.type ∗
    "HN" ∷ p.[raftpb.ConfChange, go!"NodeId"] ↦{dq} pn ∗ "#cN" ∷ cellRO pn m.nodeId ∗
    "HI" ∷ p.[raftpb.ConfChange, go!"Id"] ↦{dq} pi ∗ "#cI" ∷ cellRO pi m.id ∗
    "HC" ∷ p.[raftpb.ConfChange, go!"Context"] ↦{dq} cs ∗ "#Hcs" ∷ cs ↦*□ m.context ∗
    "#Hpb" ∷ pbMsg raftpb.ConfChange p uf)

/-- A `*pb.ConfChangeV2` at `p` holding `m`, at `dq`: its changes read-only, its `Context`
bytes read-only. -/
def ownCCV2 (p : Loc) (dq : DFrac) (m : CCV2M) : IProp GF :=
  iprop(∃ (pt : Loc) (chs : GoSlice) (ls : List Loc) (cs : GoSlice) (uf : List w8),
    "%Hnn" ∷ ⌜p ≠ null⌝ ∗
    "HT" ∷ p.[raftpb.ConfChangeV2, go!"Transition"] ↦{dq} pt ∗ "#cT" ∷ cellRO pt m.transition ∗
    "HCh" ∷ p.[raftpb.ConfChangeV2, go!"Changes"] ↦{dq} chs ∗ "Hch" ∷ chs ↦*{dq} ls ∗
      "#Hccs" ∷ ([∗list] q;c ∈ ls;m.changes, ccsRO q c) ∗
    "HC" ∷ p.[raftpb.ConfChangeV2, go!"Context"] ↦{dq} cs ∗ "#Hcs" ∷ cs ↦*□ m.context ∗
    "#Hpb" ∷ pbMsg raftpb.ConfChangeV2 p uf)

/-- A `ConfChangeI` interface value `c` holding `o` (`MarshalConfChange`'s argument): `nil`
(`none`), or a non-`nil` `*ConfChange` or `*ConfChangeV2` holding the content, at `dq`. -/
def ownCCI (c : GoInterface) (dq : DFrac) : Option CCMsg → IProp GF
  | none => iprop(⌜c = interface.nil⌝)
  | some (.v1 m) => iprop(∃ p : Loc,
      ⌜c = interface.mkOk (go.GoType.PointerType raftpb.ConfChange.ty) #p⌝ ∗ ownCCV1 p dq m)
  | some (.v2 m) => iprop(∃ p : Loc,
      ⌜c = interface.mkOk (go.GoType.PointerType raftpb.ConfChangeV2.ty) #p⌝ ∗ ownCCV2 p dq m)

end defs

/-! ## Lemmas -/

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

open Iris.ProofMode

instance hsRO_persistent (p : Loc) (hs : HardStateM) : Persistent (hsRO (GF := GF) p hs) := by
  unfold hsRO; infer_instance

set_option synthInstance.maxSize 1024 in
instance csPts_persistent (p : Loc) (c : ConfStateM) (al : Bool) :
    Persistent (csPts (GF := GF) p DFrac.discard c al) := by
  unfold csPts; infer_instance

instance ccsRO_persistent (p : Loc) (c : ConfChangeSingleM) :
    Persistent (ccsRO (GF := GF) p c) := by
  unfold ccsRO ccsPts; infer_instance

instance ownCCV1_persistent (p : Loc) (m : CCV1M) :
    Persistent (ownCCV1 (GF := GF) p DFrac.discard m) := by
  unfold ownCCV1; infer_instance

theorem cellRO_agree {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] (p : Loc) (v1 v2 : V) :
    cellRO (GF := GF) p v1 ∗ cellRO p v2 ⊢ ⌜v1 = v2⌝ := by
  iintro ⟨#H1, #H2⟩
  ihave (⟨%Hp1, %Hv1⟩ | ⟨#P1, %Hn1⟩) := cellRO_cases $$ H1
  · ihave (⟨%Hp2, %Hv2⟩ | ⟨#P2, %Hn2⟩) := cellRO_cases $$ H2
    · ipureintro; rw [Hv1, Hv2]
    · exact absurd Hp1 Hn2
  · ihave (⟨%Hp2, %Hv2⟩ | ⟨#P2, %Hn2⟩) := cellRO_cases $$ H2
    · exact absurd Hp2 Hn1
    · icombine P1 P2 gives %H
      ipureintro; exact H

/-- A fresh cell, frozen: raft stores `new(x)` into a field and never writes through it. -/
theorem cellRO_alloc {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] (p : Loc) (v : V) :
    (p ↦ v : IProp GF) ⊢ |==> cellRO p v := by
  iintro H
  imod (typedPointsto_dfractional (GF := GF) p v).dfractional_persist _ $$ H with #H
  imodintro
  unfold cellRO
  iright; iexact H

/-- The hidden fields of a protobuf object made into its invariant (once, at allocation). -/
theorem pbMsg_alloc (T : Type) (l : Loc) (st : google_golang_org.protobuf.internal.impl.MessageState)
    (sc : w32) (us : GoSlice) (uf : List w8) (E : CoPset) :
    (l.[T, go!"state"] ↦ st ∗ l.[T, go!"sizeCache"] ↦ sc ∗ l.[T, go!"unknownFields"] ↦ us ∗
      us ↦* uf : IProp GF) ⊢ |={E}=> pbMsg T l uf := by
  iintro ⟨H1, H2, H3, H4⟩
  unfold pbMsg
  iapply inv_alloc
  inext
  iexists st, sc, us
  iframe

/-! ### Entries -/

/-- A fresh entry, once filled, is frozen into a log entry (D2). -/
theorem entOwn_freeze (l : Loc) (e : EntryM) : entOwn (GF := GF) l e ⊢ |==> entRO l e := by
  iintro H
  iNamed H
  imod (typedPointsto_dfractional (GF := GF) _ pt).dfractional_persist _ $$ HT with #HT
  imod (typedPointsto_dfractional (GF := GF) _ pi).dfractional_persist _ $$ HI with #HI
  imod (typedPointsto_dfractional (GF := GF) _ pty).dfractional_persist _ $$ HY with #HY
  imod (typedPointsto_dfractional (GF := GF) _ ds).dfractional_persist _ $$ HD with #HD
  imod (typedPointsto_dfractional (GF := GF) _ ps).dfractional_persist _ $$ HS with #HS
  imodintro
  simp only [entRO]
  iunfold entPts
  iexists pt, pi, pty, ds, uf, ps
  isplitr
  · ipureintro; exact Hnn
  iframe HT cT HI cI HY cY HD Hd HS cS Hpb

/-- A freshly allocated `*pb.Entry` (its hidden fields zero), its pointer fields set to cells
holding `e`'s scalars and its `Data` to a slice holding `e.Data'` read-only, is an owned entry
holding `e`. -/
theorem entOwn_of_struct (l : Loc) (v : raftpb.Entry) (e : EntryM) (E : CoPset)
    (Hu : v.unknownFields' = slice.nil) :
    (l ↦ v ∗ cellRO v.Term' e.Term' ∗ cellRO v.Index' e.Index' ∗ cellRO v.Type' e.Type' ∗
      v.Data' ↦*□ e.Data' ∗ cellRO v.Subterm' e.Subterm' : IProp GF) ⊢
      |={E}=> entOwn l e := by
  iintro ⟨Hl, #cT, #cI, #cY, #Hd, #cS⟩
  ihave %Hnn := typedPointsto_not_null $$ Hl
  icases typedPointsto_split _ _ _ $$ Hl with Hl
  simp only [TypedPointsto.typedPointstoDef]
  icases Hl with ⟨state, Term, Index, Ty, Data, Subterm, unknownFields, sizeCache, -⟩
  rw [Hu]
  ihave Hnil : (slice.nil ↦* ([] : List w8) : IProp GF) $$ []
  · iapply ownSlice_nil
  imod pbMsg_alloc raftpb.Entry l v.state' v.sizeCache' slice.nil [] E $$ [state sizeCache unknownFields Hnil] with #Hpb
  · iframe
  imodintro
  simp only [entOwn]
  iunfold entPts
  iexists v.Term', v.Index', v.Type', v.Data', [], v.Subterm'
  isplitr
  · ipureintro; exact Hnn
  iframe
  iframe cT cI cY Hd cS Hpb

/-! ### Conf states, snapshots, hard states -/

theorem csPts_weaken (p : Loc) (dq : DFrac) (c : ConfStateM) (al : Bool) :
    csPts (GF := GF) p dq c al ⊢ ownCSM p dq c := by
  iintro H
  iNamed H
  simp only [ownCSM]
  iunfold csPts
  iexists sv, sl, so, sn, pa, pw, pwo
  isplitr
  · ipureintro; exact Hnn
  iframe HV Hv HL Hl HO Ho HN Hn HA cA HW cW HWO cWO Hpb
  ipureintro; intro h; cases h

/-- A freshly allocated `*pb.ConfState` (hidden fields zero), its slices holding `c`'s lists
and its `AutoLeave` a cell holding `c.AutoLeave'`, is an owned conf state holding `c`; `al`
when that cell is set. -/
theorem csPts_of_struct (p : Loc) (v : raftpb.ConfState) (c : ConfStateM) (E : CoPset)
    (Hu : v.unknownFields' = slice.nil) :
    (p ↦ v ∗ v.Voters' ↦* c.Voters' ∗ v.Learners' ↦* c.Learners' ∗
      v.VotersOutgoing' ↦* c.VotersOutgoing' ∗ v.LearnersNext' ↦* c.LearnersNext' ∗
      cellRO v.AutoLeave' c.AutoLeave' ∗ cellRO v.Witness' c.Witness' ∗
      cellRO v.WitnessOutgoing' (W64 0) : IProp GF) ⊢
      |={E}=> csPts p (DFrac.own 1) c (decide (v.AutoLeave' ≠ null)) := by
  iintro ⟨Hp, Hv, Hl, Ho, Hn, #cA, #cW, #cWO⟩
  ihave %Hnn := typedPointsto_not_null $$ Hp
  icases typedPointsto_split _ _ _ $$ Hp with Hp
  simp only [TypedPointsto.typedPointstoDef]
  icases Hp with ⟨state, Voters, Learners, VotersOutgoing, LearnersNext, AutoLeave, Witness, WitnessOutgoing, unknownFields, sizeCache, -⟩
  rw [Hu]
  ihave Hnil : (slice.nil ↦* ([] : List w8) : IProp GF) $$ []
  · iapply ownSlice_nil
  imod pbMsg_alloc raftpb.ConfState p v.state' v.sizeCache' slice.nil [] E $$ [state sizeCache unknownFields Hnil] with #Hpb
  · iframe
  imodintro
  iunfold csPts
  iexists v.Voters', v.Learners', v.VotersOutgoing', v.LearnersNext', v.AutoLeave', v.Witness',
    v.WitnessOutgoing'
  isplitr
  · ipureintro; exact Hnn
  iframe
  iframe cA cW cWO Hpb
  ipureintro; intro h; simpa using h

/-- `csPts_of_struct` at read-only slices, the conf state frozen read-only for good: a conf state
built once from shared lists (the register's `InitialState` returns `&pb.ConfState{Voters:
s.voters}`, the voters slice shared by a cluster's storages). `al` as there. (2026-10-16, from the
register's `Lemmas.lean`.) -/
theorem csPts_of_struct_ro (p : Loc) (v : raftpb.ConfState) (c : ConfStateM) (E : CoPset)
    (Hu : v.unknownFields' = slice.nil) :
    (p ↦ v ∗ v.Voters' ↦*□ c.Voters' ∗ v.Learners' ↦*□ c.Learners' ∗
      v.VotersOutgoing' ↦*□ c.VotersOutgoing' ∗ v.LearnersNext' ↦*□ c.LearnersNext' ∗
      cellRO v.AutoLeave' c.AutoLeave' ∗ cellRO v.Witness' c.Witness' ∗
      cellRO v.WitnessOutgoing' (W64 0) : IProp GF) ⊢
      |={E}=> csPts p DFrac.discard c (decide (v.AutoLeave' ≠ null)) := by
  iintro ⟨Hp, #Hv, #Hl, #Ho, #Hn, #cA, #cW, #cWO⟩
  ihave %Hnn := typedPointsto_not_null $$ Hp
  icases typedPointsto_split _ _ _ $$ Hp with Hp
  simp only [TypedPointsto.typedPointstoDef]
  icases Hp with ⟨state, Voters, Learners, VotersOutgoing, LearnersNext, AutoLeave, Witness, WitnessOutgoing, unknownFields, sizeCache, -⟩
  rw [Hu]
  ihave Hnil : (slice.nil ↦* ([] : List w8) : IProp GF) $$ []
  · iapply ownSlice_nil
  imod pbMsg_alloc raftpb.ConfState p v.state' v.sizeCache' slice.nil [] E $$ [state sizeCache unknownFields Hnil] with #Hpb
  · iframe
  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ Voters with #Voters
  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ Learners with #Learners
  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ VotersOutgoing with #VotersOutgoing
  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ LearnersNext with #LearnersNext
  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ AutoLeave with #AutoLeave
  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ Witness with #Witness
  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ WitnessOutgoing with #WitnessOutgoing
  imodintro
  iunfold csPts
  iexists v.Voters', v.Learners', v.VotersOutgoing', v.LearnersNext', v.AutoLeave', v.Witness',
    v.WitnessOutgoing'
  isplitr
  · ipureintro; exact Hnn
  iframe Voters Hv Learners Hl VotersOutgoing Ho LearnersNext Hn AutoLeave cA Witness cW
    WitnessOutgoing cWO Hpb
  ipureintro; intro h; simpa using h

/-- A message's pointer is not `nil` (kept). -/
theorem msgPtsC_nn (l : Loc) (dq dqe : DFrac) (cap : Bool) (ms : MsgSt) :
    msgPtsC (GF := GF) l dq dqe cap ms ⊢ ⌜l ≠ null⌝ ∗ msgPtsC l dq dqe cap ms := by
  iintro H
  ihave %Hnn : ⌜l ≠ null⌝ $$ [H]
  · iunfold msgPtsC at H
    iNamed H
    ipureintro; exact Hnn
  iframe H
  ipureintro; exact Hnn

/-- The `From` field of a message, lent (`&pb.Message{To: m.From, ...}` reads the pointer: the new
message shares the read-only cell). -/
theorem msgPtsC_From_acc (l : Loc) (dq dqe : DFrac) (cap : Bool) (ms : MsgSt) :
    msgPtsC (GF := GF) l dq dqe cap ms ⊢
      ∃ p : Loc, l.[raftpb.Message, go!"From"] ↦{dq} p ∗ cellRO p ms.msg.From' ∗
        (l.[raftpb.Message, go!"From"] ↦{dq} p -∗ msgPtsC l dq dqe cap ms) := by
  iintro H
  iunfold msgPtsC at H
  iNamed H
  iexists pfr
  iframe HFr cFr
  iintro HFr
  iunfold msgPtsC
  iexists pty, pto, pfr, pte, plt, pix, pco, pvo, prj, prh, es, els, ps, cs, rs, uf
  isplitr
  · ipureintro; exact Hnn
  iframe
  iframe cTy cTo cFr cTe cLt cIx cCo cVo cRj cRh Hents Hcs Hpb

theorem csPts_nn (p : Loc) (dq : DFrac) (c : ConfStateM) (al : Bool) :
    csPts (GF := GF) p dq c al ⊢ csPts p dq c al ∗ ⌜p ≠ null⌝ := by
  iintro H
  iNamed H
  isplitl
  · iunfold csPts
    iexists sv, sl, so, sn, pa, pw, pwo
    isplitr
    · ipureintro; exact Hnn
    iframe HV Hv HL Hl HO Ho HN Hn HA cA HW cW HWO cWO Hpb
    ipureintro; exact Hal
  · ipureintro; exact Hnn

/-- An owned-or-nil conf state is a snapshot's nested conf state (`csOptA`'s first two cases). -/
theorem csOpt_csOptA (p : Loc) (dq : DFrac) (c : ConfStateM) :
    csOpt (GF := GF) p dq c ⊢ csOptA p dq c := by
  iunfold csOpt
  iunfold csOptA
  iintro (%H | H)
  · ileft; ipureintro; exact H
  · iright; ileft; iexact H

/-- A freshly allocated `*pb.SnapshotMetadata` (hidden fields zero) whose conf state and cells
hold `md`'s is an owned metadata holding `md`. -/
theorem smPts_of_struct (p : Loc) (v : raftpb.SnapshotMetadata) (md : SnapshotMetadataM)
    (E : CoPset) (Hu : v.unknownFields' = slice.nil) :
    (p ↦ v ∗ csOpt v.ConfState' (DFrac.own 1) md.ConfState' ∗ cellRO v.Index' md.Index' ∗
      cellRO v.Term' md.Term' : IProp GF) ⊢ |={E}=> smPts p (DFrac.own 1) md := by
  iintro ⟨Hp, Hc, #cI, #cT⟩
  ihave Hc := csOpt_csOptA _ _ _ $$ Hc
  ihave %Hnn := typedPointsto_not_null $$ Hp
  icases typedPointsto_split _ _ _ $$ Hp with Hp
  simp only [TypedPointsto.typedPointstoDef]
  icases Hp with ⟨state, ConfState, Index, Term, unknownFields, sizeCache, -⟩
  rw [Hu]
  ihave Hnil : (slice.nil ↦* ([] : List w8) : IProp GF) $$ []
  · iapply ownSlice_nil
  imod pbMsg_alloc raftpb.SnapshotMetadata p v.state' v.sizeCache' slice.nil [] E $$ [state sizeCache unknownFields Hnil] with #Hpb
  · iframe
  imodintro
  iunfold smPts
  iexists v.ConfState', v.Index', v.Term', []
  isplitr
  · ipureintro; exact Hnn
  iframe
  iframe cI cT Hpb

/-- A freshly allocated `*pb.Snapshot` (hidden fields zero) whose data and metadata hold
`s`'s is an owned snapshot holding `s`. -/
theorem ownSnapM_of_struct (p : Loc) (v : raftpb.Snapshot) (s : SnapshotM) (E : CoPset)
    (Hu : v.unknownFields' = slice.nil) :
    (p ↦ v ∗ v.Data' ↦* s.Data' ∗ smOpt v.Metadata' (DFrac.own 1) s.Metadata' : IProp GF) ⊢
      |={E}=> ownSnapM p (DFrac.own 1) s := by
  iintro ⟨Hp, Hd, Hm⟩
  ihave %Hnn := typedPointsto_not_null $$ Hp
  icases typedPointsto_split _ _ _ $$ Hp with Hp
  simp only [TypedPointsto.typedPointstoDef]
  icases Hp with ⟨state, Data, Metadata, unknownFields, sizeCache, -⟩
  rw [Hu]
  ihave Hnil : (slice.nil ↦* ([] : List w8) : IProp GF) $$ []
  · iapply ownSlice_nil
  imod pbMsg_alloc raftpb.Snapshot p v.state' v.sizeCache' slice.nil [] E $$ [state sizeCache unknownFields Hnil] with #Hpb
  · iframe
  imodintro
  iunfold ownSnapM
  iexists v.Data', v.Metadata', []
  isplitr
  · ipureintro; exact Hnn
  iframe
  iframe Hpb

/-- A freshly allocated `*pb.HardState` (hidden fields zero) whose cells hold `hs`'s, frozen
(D4: a hard state is never written after `hardState()` builds it). -/
theorem hsRO_of_struct (p : Loc) (v : raftpb.HardState) (hs : HardStateM) (E : CoPset)
    (Hu : v.unknownFields' = slice.nil) :
    (p ↦ v ∗ cellRO v.Term' hs.Term' ∗ cellRO v.Vote' hs.Vote' ∗ cellRO v.Commit' hs.Commit' :
      IProp GF) ⊢ |={E}=> hsRO p hs := by
  iintro ⟨Hp, #cT, #cV, #cC⟩
  ihave %Hnn := typedPointsto_not_null $$ Hp
  icases typedPointsto_split _ _ _ $$ Hp with Hp
  simp only [TypedPointsto.typedPointstoDef]
  icases Hp with ⟨state, Term, Vote, Commit, unknownFields, sizeCache, -⟩
  rw [Hu]
  ihave Hnil : (slice.nil ↦* ([] : List w8) : IProp GF) $$ []
  · iapply ownSlice_nil
  imod pbMsg_alloc raftpb.HardState p v.state' v.sizeCache' slice.nil [] E $$ [state sizeCache unknownFields Hnil] with #Hpb
  · iframe
  imod (typedPointsto_dfractional (GF := GF) _ v.Term').dfractional_persist _ $$ Term with #Term
  imod (typedPointsto_dfractional (GF := GF) _ v.Vote').dfractional_persist _ $$ Vote with #Vote
  imod (typedPointsto_dfractional (GF := GF) _ v.Commit').dfractional_persist _ $$ Commit with #Commit
  imodintro
  iunfold hsRO
  iexists v.Term', v.Vote', v.Commit', []
  isplitr
  · ipureintro; exact Hnn
  iframe Term cT Vote cV Commit cC Hpb

/-! ### Conf changes -/

/-- A freshly allocated `*pb.ConfChangeSingle` (hidden fields zero) whose cells hold `c`'s,
frozen. -/
theorem ccsRO_of_struct (p : Loc) (v : raftpb.ConfChangeSingle) (c : ConfChangeSingleM)
    (E : CoPset) (Hu : v.unknownFields' = slice.nil) :
    (p ↦ v ∗ cellRO v.Type' c.Type' ∗ cellRO v.NodeId' c.NodeId' : IProp GF) ⊢
      |={E}=> ccsRO p c := by
  iintro ⟨Hp, #cT, #cN⟩
  ihave %Hnn := typedPointsto_not_null $$ Hp
  icases typedPointsto_split _ _ _ $$ Hp with Hp
  simp only [TypedPointsto.typedPointstoDef]
  icases Hp with ⟨state, Ty, NodeId, unknownFields, sizeCache, -⟩
  rw [Hu]
  ihave Hnil : (slice.nil ↦* ([] : List w8) : IProp GF) $$ []
  · iapply ownSlice_nil
  imod pbMsg_alloc raftpb.ConfChangeSingle p v.state' v.sizeCache' slice.nil [] E $$ [state sizeCache unknownFields Hnil] with #Hpb
  · iframe
  imod (typedPointsto_dfractional (GF := GF) _ v.Type').dfractional_persist _ $$ Ty with #HTy
  imod (typedPointsto_dfractional (GF := GF) _ v.NodeId').dfractional_persist _ $$ NodeId with #HN
  imodintro
  simp only [ccsRO]
  iunfold ccsPts
  iexists v.Type', v.NodeId', []
  isplitr
  · ipureintro; exact Hnn
  iframe HTy cT HN cN Hpb

/-- A freshly allocated `*pb.ConfChangeV2` (hidden fields zero): its transition cell, its
changes (read-only) and its context bytes holding `m`'s. -/
theorem ownCCV2_of_struct (p : Loc) (v : raftpb.ConfChangeV2) (m : CCV2M) (ls : List Loc)
    (E : CoPset) (Hu : v.unknownFields' = slice.nil) :
    (p ↦ v ∗ cellRO v.Transition' m.transition ∗ v.Changes' ↦* ls ∗
      ([∗list] q;c ∈ ls;m.changes, ccsRO q c) ∗ v.Context' ↦*□ m.context : IProp GF) ⊢
      |={E}=> ownCCV2 p (DFrac.own 1) m := by
  iintro ⟨Hp, #cT, Hch, #Hccs, #Hcs⟩
  ihave %Hnn := typedPointsto_not_null $$ Hp
  icases typedPointsto_split _ _ _ $$ Hp with Hp
  simp only [TypedPointsto.typedPointstoDef]
  icases Hp with ⟨state, Transition, Changes, Context, unknownFields, sizeCache, -⟩
  rw [Hu]
  ihave Hnil : (slice.nil ↦* ([] : List w8) : IProp GF) $$ []
  · iapply ownSlice_nil
  imod pbMsg_alloc raftpb.ConfChangeV2 p v.state' v.sizeCache' slice.nil [] E $$ [state sizeCache unknownFields Hnil] with #Hpb
  · iframe
  imodintro
  iunfold ownCCV2
  iexists v.Transition', v.Changes', ls, v.Context', []
  isplitr
  · ipureintro; exact Hnn
  iframe
  iframe cT Hccs Hcs Hpb

/-- A freshly allocated `*pb.ConfChange` (hidden fields zero) holding `m`. -/
theorem ownCCV1_of_struct (p : Loc) (v : raftpb.ConfChange) (m : CCV1M) (E : CoPset)
    (Hu : v.unknownFields' = slice.nil) :
    (p ↦ v ∗ cellRO v.Type' m.type ∗ cellRO v.NodeId' m.nodeId ∗ cellRO v.Id' m.id ∗
      v.Context' ↦*□ m.context : IProp GF) ⊢ |={E}=> ownCCV1 p (DFrac.own 1) m := by
  iintro ⟨Hp, #cT, #cN, #cI, #Hcs⟩
  ihave %Hnn := typedPointsto_not_null $$ Hp
  icases typedPointsto_split _ _ _ $$ Hp with Hp
  simp only [TypedPointsto.typedPointstoDef]
  icases Hp with ⟨state, Ty, NodeId, Context, Id, unknownFields, sizeCache, -⟩
  rw [Hu]
  ihave Hnil : (slice.nil ↦* ([] : List w8) : IProp GF) $$ []
  · iapply ownSlice_nil
  imod pbMsg_alloc raftpb.ConfChange p v.state' v.sizeCache' slice.nil [] E $$ [state sizeCache unknownFields Hnil] with #Hpb
  · iframe
  imodintro
  iunfold ownCCV1
  iexists v.Type', v.NodeId', v.Id', v.Context', []
  isplitr
  · ipureintro; exact Hnn
  iframe
  iframe cT cN cI Hcs Hpb

/-- A `*pb.ConfChange` frozen read-only for good (what the register's `run` sends on `confc`
through `node.ApplyConfChange`: raft reads it on its own goroutine). (2026-10-16, from the
register's `Lemmas.lean`.) -/
theorem ownCCV1_persist (p : Loc) (dq : DFrac) (m : CCV1M) :
    ownCCV1 (GF := GF) p dq m ⊢ |==> ownCCV1 p DFrac.discard m := by
  iintro H
  iNamed H
  imod (typedPointsto_dfractional (GF := GF) _ pt).dfractional_persist _ $$ HT with #HT
  imod (typedPointsto_dfractional (GF := GF) _ pn).dfractional_persist _ $$ HN with #HN
  imod (typedPointsto_dfractional (GF := GF) _ pi).dfractional_persist _ $$ HI with #HI
  imod (typedPointsto_dfractional (GF := GF) _ cs).dfractional_persist _ $$ HC with #HC
  imodintro
  iunfold ownCCV1
  iexists pt, pn, pi, cs, uf
  isplitr
  · ipureintro; exact Hnn
  iframe HT cT HN cN HI cI HC Hcs Hpb

/-! ### Splitting a fraction -/

theorem csPts_split (p : Loc) (dq1 dq2 : DFrac) (c : ConfStateM) (al : Bool) :
    csPts (GF := GF) p (dq1 • dq2) c al ⊢ csPts p dq1 c al ∗ csPts p dq2 c al := by
  iintro H
  iNamed H
  icases (typedPointsto_dfractional (GF := GF) _ _).dfractional dq1 dq2 |>.1 $$ HV with ⟨HV1, HV2⟩
  icases (ownSlice_dfractional (GF := GF) _ _).dfractional dq1 dq2 |>.1 $$ Hv with ⟨Hv1, Hv2⟩
  icases (typedPointsto_dfractional (GF := GF) _ _).dfractional dq1 dq2 |>.1 $$ HL with ⟨HL1, HL2⟩
  icases (ownSlice_dfractional (GF := GF) _ _).dfractional dq1 dq2 |>.1 $$ Hl with ⟨Hl1, Hl2⟩
  icases (typedPointsto_dfractional (GF := GF) _ _).dfractional dq1 dq2 |>.1 $$ HO with ⟨HO1, HO2⟩
  icases (ownSlice_dfractional (GF := GF) _ _).dfractional dq1 dq2 |>.1 $$ Ho with ⟨Ho1, Ho2⟩
  icases (typedPointsto_dfractional (GF := GF) _ _).dfractional dq1 dq2 |>.1 $$ HN with ⟨HN1, HN2⟩
  icases (ownSlice_dfractional (GF := GF) _ _).dfractional dq1 dq2 |>.1 $$ Hn with ⟨Hn1, Hn2⟩
  icases (typedPointsto_dfractional (GF := GF) _ _).dfractional dq1 dq2 |>.1 $$ HA with ⟨HA1, HA2⟩
  icases (typedPointsto_dfractional (GF := GF) _ _).dfractional dq1 dq2 |>.1 $$ HW with ⟨HW1, HW2⟩
  icases (typedPointsto_dfractional (GF := GF) _ _).dfractional dq1 dq2 |>.1 $$ HWO with ⟨HWO1, HWO2⟩
  isplitl [HV1 Hv1 HL1 Hl1 HO1 Ho1 HN1 Hn1 HA1 HW1 HWO1]
  · iunfold csPts
    iexists sv, sl, so, sn, pa, pw, pwo
    isplitr
    · ipureintro; exact Hnn
    iframe
    iframe cA cW cWO Hpb
    ipureintro; exact Hal
  · iunfold csPts
    iexists sv, sl, so, sn, pa, pw, pwo
    isplitr
    · ipureintro; exact Hnn
    iframe
    iframe cA cW cWO Hpb
    ipureintro; exact Hal

/-- A snapshot's nested conf state is `nil` holding the zero record, or not `nil`. -/
theorem csOptA_nn (p : Loc) (dq : DFrac) (c : ConfStateM) :
    csOptA (GF := GF) p dq c ⊢
      csOptA p dq c ∗ ⌜(p = null ∧ c = ConfStateM.mk [] [] [] [] false (W64 0)) ∨ p ≠ null⌝ := by
  iunfold csOptA
  iintro (%H | H | #H)
  · isplitl []
    · ileft; ipureintro; exact H
    · ipureintro; exact .inl H
  · icases csPts_nn _ _ _ _ $$ H with ⟨H, %Hnn⟩
    isplitl [H]
    · iright; ileft; iexact H
    · ipureintro; exact .inr Hnn
  · icases csPts_nn _ _ _ _ $$ H with ⟨-, %Hnn⟩
    isplitl []
    · iright; iright; iexact H
    · ipureintro; exact .inr Hnn

theorem csOptA_split (p : Loc) (dq1 dq2 : DFrac) (c : ConfStateM) :
    csOptA (GF := GF) p (dq1 • dq2) c ⊢ csOptA p dq1 c ∗ csOptA p dq2 c := by
  iunfold csOptA
  iintro (%H | H | #H)
  · isplitl [] <;> ileft <;> ipureintro <;> exact H
  · icases csPts_split _ _ _ _ _ $$ H with ⟨H1, H2⟩
    isplitl [H1]
    · iright; ileft; iexact H1
    · iright; ileft; iexact H2
  · isplitl [] <;> iright <;> iright <;> iexact H

theorem smPts_split (p : Loc) (dq1 dq2 : DFrac) (md : SnapshotMetadataM) :
    smPts (GF := GF) p (dq1 • dq2) md ⊢ smPts p dq1 md ∗ smPts p dq2 md := by
  iintro H
  iNamed H
  icases (typedPointsto_dfractional (GF := GF) _ _).dfractional dq1 dq2 |>.1 $$ HC with ⟨HC1, HC2⟩
  icases csOptA_split _ _ _ _ $$ Hc with ⟨Hc1, Hc2⟩
  icases (typedPointsto_dfractional (GF := GF) _ _).dfractional dq1 dq2 |>.1 $$ HI with ⟨HI1, HI2⟩
  icases (typedPointsto_dfractional (GF := GF) _ _).dfractional dq1 dq2 |>.1 $$ HT with ⟨HT1, HT2⟩
  isplitl [HC1 Hc1 HI1 HT1]
  · iunfold smPts
    iexists pc, pi, pt, uf
    isplitr
    · ipureintro; exact Hnn
    iframe
    iframe cI cT Hpb
  · iunfold smPts
    iexists pc, pi, pt, uf
    isplitr
    · ipureintro; exact Hnn
    iframe
    iframe cI cT Hpb

theorem smOpt_split (p : Loc) (dq1 dq2 : DFrac) (md : SnapshotMetadataM) :
    smOpt (GF := GF) p (dq1 • dq2) md ⊢ smOpt p dq1 md ∗ smOpt p dq2 md := by
  iunfold smOpt
  iintro (%H | H)
  · isplitl [] <;> ileft <;> ipureintro <;> exact H
  · icases smPts_split _ _ _ _ $$ H with ⟨H1, H2⟩
    isplitl [H1]
    · iright; iexact H1
    · iright; iexact H2

theorem ownSnapM_split (p : Loc) (dq1 dq2 : DFrac) (sn : SnapshotM) :
    ownSnapM (GF := GF) p (dq1 • dq2) sn ⊢ ownSnapM p dq1 sn ∗ ownSnapM p dq2 sn := by
  iintro H
  iNamed H
  icases (typedPointsto_dfractional (GF := GF) _ _).dfractional dq1 dq2 |>.1 $$ HD with ⟨HD1, HD2⟩
  icases (ownSlice_dfractional (GF := GF) _ _).dfractional dq1 dq2 |>.1 $$ Hd with ⟨Hd1, Hd2⟩
  icases (typedPointsto_dfractional (GF := GF) _ _).dfractional dq1 dq2 |>.1 $$ HM with ⟨HM1, HM2⟩
  icases smOpt_split _ _ _ _ $$ Hm with ⟨Hm1, Hm2⟩
  isplitl [HD1 Hd1 HM1 Hm1]
  · iunfold ownSnapM
    iexists ds, pm, uf
    isplitr
    · ipureintro; exact Hnn
    iframe
    iframe Hpb
  · iunfold ownSnapM
    iexists ds, pm, uf
    isplitr
    · ipureintro; exact Hnn
    iframe
    iframe Hpb

theorem snapOpt_split (p : Loc) (dq1 dq2 : DFrac) (o : Option SnapshotM) :
    snapOpt (GF := GF) p (dq1 • dq2) o ⊢ snapOpt p dq1 o ∗ snapOpt p dq2 o := by
  rcases o with _ | sn
  · simp only [snapOpt]
    iintro %H
    isplitl [] <;> ipureintro <;> exact H
  · simp only [snapOpt]
    iapply ownSnapM_split

/-- A message's fraction splits (D3: e.g. a `Ready`'s view and raft's own until `acceptReady`). -/
theorem msgOwn_split (l : Loc) (dq1 dq2 : DFrac) (ms : MsgSt) :
    msgOwn (GF := GF) l (dq1 • dq2) ms ⊢ msgOwn l dq1 ms ∗ msgOwn l dq2 ms := by
  iintro H
  simp only [msgOwn, msgPts]
  iNamed H
  icases (typedPointsto_dfractional (GF := GF) _ _).dfractional dq1 dq2 |>.1 $$ HTy with ⟨HTy1, HTy2⟩
  icases (typedPointsto_dfractional (GF := GF) _ _).dfractional dq1 dq2 |>.1 $$ HTo with ⟨HTo1, HTo2⟩
  icases (typedPointsto_dfractional (GF := GF) _ _).dfractional dq1 dq2 |>.1 $$ HFr with ⟨HFr1, HFr2⟩
  icases (typedPointsto_dfractional (GF := GF) _ _).dfractional dq1 dq2 |>.1 $$ HTe with ⟨HTe1, HTe2⟩
  icases (typedPointsto_dfractional (GF := GF) _ _).dfractional dq1 dq2 |>.1 $$ HLt with ⟨HLt1, HLt2⟩
  icases (typedPointsto_dfractional (GF := GF) _ _).dfractional dq1 dq2 |>.1 $$ HIx with ⟨HIx1, HIx2⟩
  icases (typedPointsto_dfractional (GF := GF) _ _).dfractional dq1 dq2 |>.1 $$ HCo with ⟨HCo1, HCo2⟩
  icases (typedPointsto_dfractional (GF := GF) _ _).dfractional dq1 dq2 |>.1 $$ HVo with ⟨HVo1, HVo2⟩
  icases (typedPointsto_dfractional (GF := GF) _ _).dfractional dq1 dq2 |>.1 $$ HRj with ⟨HRj1, HRj2⟩
  icases (typedPointsto_dfractional (GF := GF) _ _).dfractional dq1 dq2 |>.1 $$ HRh with ⟨HRh1, HRh2⟩
  icases (typedPointsto_dfractional (GF := GF) _ _).dfractional dq1 dq2 |>.1 $$ HEs with ⟨HEs1, HEs2⟩
  icases (typedPointsto_dfractional (GF := GF) _ _).dfractional dq1 dq2 |>.1 $$ HSn with ⟨HSn1, HSn2⟩
  icases snapOpt_split _ _ _ _ $$ Hsn with ⟨Hsn1, Hsn2⟩
  icases (typedPointsto_dfractional (GF := GF) _ _).dfractional dq1 dq2 |>.1 $$ HCx with ⟨HCx1, HCx2⟩
  icases (typedPointsto_dfractional (GF := GF) _ _).dfractional dq1 dq2 |>.1 $$ HRs with ⟨HRs1, HRs2⟩
  icases (ownSlice_dfractional (GF := GF) _ _).dfractional dq1 dq2 |>.1 $$ Hrs with ⟨Hrs1, Hrs2⟩
  ihave #Hes := Hes
  iclear Hes_cap
  isplitl [HTy1 HTo1 HFr1 HTe1 HLt1 HIx1 HCo1 HVo1 HRj1 HRh1 HEs1 HSn1 Hsn1 HCx1 HRs1 Hrs1]
  · iunfold msgPtsC
    iexists pty, pto, pfr, pte, plt, pix, pco, pvo, prj, prh, es, els, ps, cs, rs, uf
    isplitr
    · ipureintro; exact Hnn
    iframe
    iframe cTy cTo cFr cTe cLt cIx cCo cVo cRj cRh Hes Hents Hcs Hpb
    simp only [named, Bool.false_eq_true, ↓reduceIte]; iempintro
  · iunfold msgPtsC
    iexists pty, pto, pfr, pte, plt, pix, pco, pvo, prj, prh, es, els, ps, cs, rs, uf
    isplitr
    · ipureintro; exact Hnn
    iframe
    iframe cTy cTo cFr cTe cLt cIx cCo cVo cRj cRh Hes Hents Hcs Hpb
    simp only [named, Bool.false_eq_true, ↓reduceIte]; iempintro

end lemmas

end EtcdGrove
end Perennial
