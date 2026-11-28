/-
**The raft network** (D21 stage M2, 2026-10-19; D21b (A), `notes/decisions.md`, "D21 M2: the
network contract designed"). Lean-first (no Rocq counterpart). `rafthttp` is names-only: these
are the terms of its trust-boundary contract (`Transport.Start`, `AddPeer`, `AddRemote` and the
started transport's `Send`), not a proof of rafthttp.

A cluster's network has names `γn` (`NetNames`): what a message carries (`NetPayload`: a
persistent part `P`, read by every delivery of the message, and a one-shot part `O`, with
`once` the messages delivered at most once and `dup` the one-shot part of any other message
anew), the members' slots (`netSlot γn id`, exclusive: the transport started for member `id`
holds it) and the URL directory `dir` (member `id`'s peer URLs). A sender gives each message's
bundle to `Send` (`netBundle`); the receiving transport calls its `Raft`'s `Process` with a fresh
copy of a message sent to it (`netRecv`), with the bundle. Generic in the payload so that D20 (b)'s
proposal ticket changes the server's instance (`srvNet`), not the axioms.

**The snapshot stream** (D22 S-i, 2026-10-19; `notes/decisions.md`, "D22 S-i carried out"). A
`MsgSnap` goes by `SendSnapshot`, never by `Send` (`netBundle` excludes it: rafthttp would post it
to the message handler, which saves no database file): a merged message (`snap.msgIs`) whose raft
message carries its bundle and whose reader streams a bbolt image of some `D` with the payload's
image certificate `N.img i D` at the snapshot's index `i` (`netSnapBundle`). The receiving
transport saves the stream before it calls `Process` (`SaveDBFrom`: a temporary file, synced,
linked to `snapDBPath sd i` (`os.Link`, then the directory synced), `sd` its directory, unless a file of that index is there, which it keeps). A member's
**snapshot directory** is an invariant the receiver allocates and gives `Transport.Start`
(`snapDirInvH sd γd img Rm`, its contents `snapDirBody`, `snapDir_init`): the `.snap.db` files present (`M`, each with its
`fileAt`, the claim on its name in the tree's shared mode with the file, S5; until then the abstract `srvFileHolds`, and `□ img i D`) and the indices ever saved (`E`, a ghost map with persistent elements
`snapSaved γd i`), each saved index absent from `M` with the receiver's removal fact `Rm i`. The
transport only adds to it (a file it created, at an index absent from `M`); the receiver removes
from it (a file taken to be opened, `OpenSnapshotBackend`, or `ReleaseSnapDBs`'s files below a
released index), each removal with `Rm i`. `Process` of a `MsgSnap` gets `snapSaved γd i`
(`netRecv`): a file of its index was in the directory after the message arrived, so it is in `M`
still, or the receiver removed it (`Rm i`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Defs
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvSnapshot
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.FileDur
public import Perennial.Ghost.Token
public import Perennial.GooseLang.NotCrashed
public import Proof.go_etcd_io.etcd.server.v3.storage.SnapHeld
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.snap.Defs
public import Proof.go_etcd_io.raft.v3.InvNodeCtx
public import Proof.go_etcd_io.raft.v3.ApiVocab
public import Proof.go_etcd_io.raft.v3.InvPb
public import Proof.go_etcd_io.raft.v3.PbMessage
public import Proof.go_etcd_io.raft.v3.MsgOut
public import Perennial.Ghost.GhostMap
public import Perennial.Ghost.MonoNat
public import Perennial.Proof.ThreadPool

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

/-- **The most peers a member's transport serves** (2026-11-03, named by the final whole-`bootOk`
review's M2; the bound since rafthttp stage 6d, 2026-10-24): each peer's goroutines borrow eight of
`lgMu`'s reader slots, so `peersMax` peers borrow `2 ^ 23`. `NewServer`'s premise
(`rafthttp.bootCfg`). -/
@[word_unfold] def peersMax : Nat := 2 ^ 20

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **What a message carries over the network** (see the file header). -/
structure NetPayload (GF : BundledGFunctors) [GooseExts] where
  P : MsgSt → IProp GF
  O : MsgSt → IProp GF
  once : MsgSt → Prop
  P_pers : ∀ st, Persistent (P st)
  dup : ∀ st, ¬ once st → ⊢ |==> O st
  /-- (raft-entsize §4, 2026-11-10) whether the messages are of bounded size (`msgSizeOk`): the
  size facts of the bundle, the frames and the received copy hold when `Sz` does (the server's: its
  cluster states a bound on proposed data, `γ.cl.maxData ≠ none`), and are vacuous otherwise -/
  Sz : Prop
  /-- (D22 S-i) what a snapshot message's database image `D` of index `i` carries (persistent):
  the sender's certificate, kept with the saved file in the receiver's directory -/
  img : w64 → backend.Data → IProp GF
  img_pers : ∀ i D, Persistent (img i D)

def streamRegN : Namespace := nroot.@"rafthttp_stream_reg"

/-- A stream's type (`streamType`). -/
inductive StreamTy where
  | msgAppV2
  | message
  deriving DecidableEq

instance : Pos.Countable StreamTy :=
  .ofInjective (fun t => match t with | .msgAppV2 => 1 | .message => 2)
    (by intro a b h; cases a <;> cases b <;> first | rfl | exact absurd h (by decide))

/-- **A stream connection's ghost names**: the reader's tokens `γw`, the type and the reader. -/
abbrev StreamKey := GName × StreamTy × w64

/-- **A network's names** (see the file header). (2026-10-23, rafthttp stage 6a, D39) `reg`: the
streams' registry (`Stream.lean`'s `streamRegInv`), one for the network, so that a member's
stream reader and its peer's stream handler agree on a connection. -/
structure NetNames (GF : BundledGFunctors) [GooseExts] where
  N : NetPayload GF
  slots : GName
  dir : w64 → List GoString
  reg : GName

end defs

section defsG1
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [Gg : GooseGlobalGS HasLC.hasLC GF] [GoLocalContext]
variable [sem : go.Semantics]
attribute [local instance] GooseGlobalGS.gooseInvGS

/-- **Member `id`'s slot** (exclusive): held by the transport started for `id`
(`Transport.Start`), so that one transport receives what is sent to `id`. -/
def netSlot (γn : NetNames GF) (id : w64) : IProp GF :=
  ghostMapElem γn.slots id (DFrac.own 1) ()

-- (2026-11-12, trace-check B4) `wireEq`, a received copy's agreement with the message sent, is in
-- raft's `PbMessage.lean` (imported above), beside the wire model that proves it.

end defsG1

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]


/-- **A message handed to `Send`**, with its bundle: read-only for good (the transport's writer
goroutines marshal it after `Send` returns), its persistent part and its one-shot part; (D22 S-i)
not a `MsgSnap`, which goes by `SendSnapshot` (`netSnapBundle`). (2026-10-22, D38a) With no
responses: what marshals (`MsgMarshals`), so that the receiver's copy has none either (`netRecv`).
(2026-10-24, rafthttp stage 6d) Of the sender `lid`: a `MsgApp` of raft's shape (`AppShape`) from
`lid`, what rafthttp's msgappv2 stream carries whole (raft's `isRaftMsg` says both of its messages).
(raft-entsize §4, 2026-11-10) Frozen at a content of `st` (`msgRoC`; its snapshot's conf state
without unknown fields), of bounded size when the payload says so (`N.Sz`): the content the
transport encodes, which the receiver decodes back (`proto.Unmarshal`'s D2). (2026-11-10, the
coordinator's decision) Of bounded size whatever the payload (until then only when `N.Sz`): the
transport's encoders need a bound, and the server's cluster bounds proposed data. -/
def netBundle (N : NetPayload GF) (lid : w64) (m : Loc) : IProp GF :=
  iprop(∃ st : MsgSt, msgOwn m DFrac.discard st ∗ (□ N.P st) ∗ N.O st ∗
    ⌜st.msg.Type' ≠ MsgSnap ∧ st.resps = [] ∧
      (st.msg.Type' = MsgApp → AppShape st ∧ st.msg.From' = lid)⌝ ∗
    ∃ c : MsgC, msgRoC m c ∗ ⌜c.model = st ∧ c.csUfNil ∧ msgSizeOk c⌝)

/-- **A message's content for the encoders** (persistent; raft-entsize §4, 2026-11-10): the
message `ml` frozen at a content of `st` without unknown fields in its snapshot's conf state, below
`2^47` bytes (what `swMsgBound` says, `msgSzC_swMsgBound`), and of bounded size when `Sz`
(`msgSizeOk`): one content for both, so that the bytes the encoders write are the encoding of a
content of bounded size, which the receiver decodes back (`proto.Unmarshal`'s D2). -/
def msgSzC (Sz : Prop) (ml : Loc) (st : MsgSt) : IProp GF :=
  iprop(∃ c : MsgC, msgRoC ml c ∗
    ⌜c.model = st ∧ c.csUfNil ∧ msgSize c < 2 ^ 47 ∧ (Sz → msgSizeOk c)⌝)

instance msgSzC_persistent (Sz : Prop) (ml : Loc) (st : MsgSt) :
    Persistent (msgSzC (GF := GF) Sz ml st) := by
  unfold msgSzC; infer_instance

/-- **A snapshot message handed to `SendSnapshot`** (D22 S-i): the raft message `ml` of the merged
message, a `MsgSnap` with a snapshot of index `i`, with its bundle (read-only for good, as
`netBundle`'s), and the right to read the merged message's reader `rc` (`readerStreams`), whose
complete streams are bbolt images of some `D` (`boltImage`) with the payload's certificate
`N.img i D` (for the server, `srvImage`: the committed state through `i`). (raft-entsize [r3c],
2026-11-10) Frozen at a content below `2^47` bytes (`msgSzC False`, `swMsgBound`'s meaning): what
the envelope's encoder needs (`createSnapBody`), derived by the sender
(`createMergedSnapshotMessage`; until then the deleted axiom `swMsgBound_phys`'s). -/
def netSnapBundle (N : NetPayload GF) (ml : Loc) (rc : GoInterface) : IProp GF :=
  iprop(∃ (st : MsgSt) (sn : SnapshotM) (D : backend.Data), msgOwn ml DFrac.discard st ∗
    msgSzC False ml st ∗
    (□ N.P st) ∗ N.O st ∗ ⌜st.msg.Type' = MsgSnap ∧ st.snap = some sn ∧ st.resps = []⌝ ∗
    backend.readerStreams rc (fun bs => backend.boltImage bs D) ∗
    □ N.img sn.Metadata'.Index' D)

/-! ### A member's snapshot directory (D22 S-i; see the file header) -/

/-- The namespace of a member's snapshot directory. -/
def snapDirN : Namespace := nroot .@ "rafthttp_snap_dir"

/-- **The index `i` was saved** in the directory of names `γd` (persistent): a `.snap.db` file of
index `i` was there at some point. -/
def snapSaved (γd : GName) (i : w64) : IProp GF := ghostMapElem γd i DFrac.discard ()

instance snapSaved_persistent (γd : GName) (i : w64) :
    Persistent (snapSaved (GF := GF) γd i) := by
  unfold snapSaved; infer_instance

/-- **The names of the snapshot files of every index, free, after every crash too** (S5, 2026-11-18;
D6-T6, 2026-11-25: `backend.fileFreeDur`, the name free in every crash, in place of `backend.fileFree`):
the claim on the name of each index's database snapshot (`p i`), naming no file, for a finite map `F` of
indices that has every index (`w64` is finite): what a fresh data directory's snapshot directory has
(`bootOk`'s, a premise; `bootstrapSnapshot` carves it from the new directory, whose `mkdir` its
`TouchDirAll` committed). -/
def snapFreeAll (p : w64 → GoString) : IProp GF :=
  iprop(∃ F : GMap w64 Unit, ⌜∀ i, F.lookup i ≠ none⌝ ∗ [∗map] i ↦ _x ∈ F, backend.fileFreeDur (p i))

/-- **A file of the snapshot directory `sd` at index `i`, holding `D`** (D6-T6, 2026-11-25): durable
(`backend.fileAtDur`: its bytes and its name survive every crash) when its index is saved (`E`), linked
but not yet durable (`backend.fileAtPend`: its bytes durable, its name maybe not, `SaveDBFrom` between its
`os.Link` and its directory sync) otherwise. -/
def snapFileAt (sd : GoString) (E : GMap w64 Unit) (i : w64) (D : backend.Data) : IProp GF :=
  iprop((⌜E.lookup i ≠ none⌝ ∗ backend.fileAtDur (snap.snapDBPath sd i) D) ∨
    (⌜E.lookup i = none⌝ ∗ backend.fileAtPend (snap.snapDBPath sd i) D))

/-- **The snapshot directory `sd`'s contents** (see the file header; D6-T6 rounds 2-4, 2026-11-24/25,
`notes/etcd-dist-d6.md` §T6): the files present `M` (`snapFileAt`), each holding its data with its
certificate (`img`); the indices saved `E` (`snapSaved`, the ghost map `γd`), whose files are durable:
**saved means durable** (`SaveDBFrom`'s ghost steps: at its `os.Link` the index joins `M` only, the
file pending; at its directory sync, and at a kept file after that branch's sync, it joins `E`); a saved
index not in `M` has the receiver's removal fact `Rm i` (`ReleaseSnapDBs` removing a file of `M` gives
`Rm i` and, the file pending, adds its index to `E`: a removal is not durable before a sync of the
directory, so a crash may bring the file back, which `Rm i` then covers; `nonissues/
etcd-snapdb-removed-before-dirsync.md`); the names of the indices in neither, free in every crash
(`backend.fileFreeDur`), one claim each (`F`, exactly those indices). -/
@[no_expose] def snapDirBody (sd : GoString) (γd : GName) (img : w64 → backend.Data → IProp GF)
    (Rm : w64 → IProp GF) : IProp GF :=
  iprop(∃ (M : GMap w64 backend.Data) (E F : GMap w64 Unit),
    ghostMapAuth γd 1 E ∗ ⌜∀ i, F.lookup i ≠ none ↔ (E.lookup i = none ∧ M.lookup i = none)⌝ ∗
    ([∗map] i ↦ D ∈ M, snapFileAt sd E i D ∗ □ img i D) ∗
    ([∗map] i ↦ _x ∈ F, backend.fileFreeDur (snap.snapDBPath sd i)) ∗
    □ (∀ i, ⌜E.lookup i ≠ none⌝ → snapSaved γd i) ∗
    □ (∀ i, ⌜E.lookup i ≠ none ∧ M.lookup i = none⌝ → Rm i))

/-- **The snapshot directory `sd`'s invariant, its crash token `γk`** (see the file header): the
directory's right (`snap.snapDirOwn`) and its contents (`snapDirBody`), or, once the crash law has
taken the contents (`snapDir_crash_law_holds`, `rafthttp/SnapDirCrash.lean`), the generation's
`crashed` with the token `γk` (the WAL's shape, `walInv`): a thread of the running generation, which
holds `notCrashed`, finds the contents (`snapDir_take`). (restart S6a, M1, approved by the user
2026-11-13 via etcd-grove-81; claim #34, 2026-11-23, approved by the owner via the coordinator) The
right is the claim on every other name of the directory, held here for good, so that no one else
creates a file under a non-canonical `.snap.db` or a `tmp*` name there (what `ReleaseSnapDBs` removes and
`SaveDBFrom` writes its temporary file under) and every invariant the snapshot axioms take over these
paths is this one. (wal-link L2, T1, decided by etcd-grove-03, 2026-11-17: sealed. Its laws are
`snapDir_init`, the take `snapDir_take`, which hands out no `fileHolds`, only the sealed
`storage.snapHeld`, and the crash law; the snapshot axioms (`SaveDBFrom`, `ReleaseSnapDBs`,
`storage.Release`) take its handle `snapDirInvH` whole. Until then a client could take a file out with
its `fileHolds` and keep it across a `Release` that Go, listing the directory, removes it in:
`notes/axiom-review/releasesnapdbs.md`.) (wal-link, 2026-11-19, approved by the user via
etcd-grove-03: over the directory string `sd`: `notes/snapdir-crossworld.md`.) -/
@[no_expose] def snapDirInvK (sd : GoString) (γd γk : GName) (img : w64 → backend.Data → IProp GF)
    (Rm : w64 → IProp GF) : IProp GF :=
  iprop(snap.snapDirOwn (snap.snapDBPath sd) ∗
    (snapDirBody sd γd img Rm ∨ crashed (hC := hG.goose_localGS.goose_crashGS) ∗ token γk))

/-- **The snapshot directory `sd`'s invariant** (persistent; D6-T6 round 3, 2026-11-24, the lead's
decision: an existential handle, in place of `snapDirInvH …`): the invariant at some
crash token. What every holder but the crash frame has (the snapshot axioms', `Transport.Start`'s, the
apply thread's). -/
def snapDirInvH (sd : GoString) (γd : GName) (img : w64 → backend.Data → IProp GF)
    (Rm : w64 → IProp GF) : IProp GF :=
  iprop(∃ γk : GName, inv snapDirN (snapDirInvK sd γd γk img Rm))

instance snapDirInvH_persistent (sd : GoString) (γd : GName) (img : w64 → backend.Data → IProp GF)
    (Rm : w64 → IProp GF) : Persistent (snapDirInvH (GF := GF) sd γd img Rm) := by
  unfold snapDirInvH; infer_instance

/-- **The snapshot directory's invariant with its crash token** (exclusive; D6-T6): what the crash frame
keeps (`snapDir_init` gives it; the crash law takes it at the old generation and gives it at the new). -/
def snapDirKeep (sd : GoString) (γd : GName) (img : w64 → backend.Data → IProp GF)
    (Rm : w64 → IProp GF) : IProp GF :=
  iprop(∃ γk : GName, inv snapDirN (snapDirInvK sd γd γk img Rm) ∗ token γk)

/-- The handle of a kept invariant. -/
theorem snapDirKeep_handle (sd : GoString) (γd : GName) (img : w64 → backend.Data → IProp GF)
    (Rm : w64 → IProp GF) :
    snapDirKeep (GF := GF) sd γd img Rm ⊢ snapDirInvH sd γd img Rm ∗ snapDirKeep sd γd img Rm := by
  unfold snapDirKeep snapDirInvH
  iintro ⟨%γk, #Hi, Ht⟩
  isplitr
  · iexists γk; iexact Hi
  · iexists γk; iframe Hi Ht

/-- **A snapshot at index `j` or above was opened** (persistent; D22 receiver epochs, S8d,
2026-10-24; the orchestrator's decision on W1, `notes/decisions.md`): a lower bound of the
monotone counter `γt` of the highest snapshot index `applySnapshot` has opened, whose authority the
apply thread keeps at most its applied index. The server's removal fact of its snapshot directory
(`snapDirBody`'s `Rm`): `OpenSnapshotBackend(i)` takes the file `i` after raising the counter to
`i`, and `storage.Release(i)` removes the files below `i`, whose `Rm j` follows from `Rm i`. -/
def snapTakenLb (γt : GName) (j : w64) : IProp GF := monoNatLbOwn γt (uint.nat j)

instance snapTakenLb_persistent (γt : GName) (j : w64) :
    Persistent (snapTakenLb (GF := GF) γt j) := by
  unfold snapTakenLb; infer_instance

/-- **What `Process` gets of a received message besides its bundle** (D22 S-i): for a `MsgSnap`,
its snapshot's index saved in the receiver's directory (`γd`). -/
def netSnapRecv (γd : GName) (st : MsgSt) : IProp GF :=
  iprop(⌜st.msg.Type' = MsgSnap⌝ → ∃ sn : SnapshotM, ⌜st.snap = some sn⌝ ∗
    snapSaved γd sn.Metadata'.Index')

instance netSnapRecv_persistent (γd : GName) (st : MsgSt) :
    Persistent (netSnapRecv (GF := GF) γd st) := by
  unfold netSnapRecv; infer_instance

/-- **A message received by member `id`** at `ml`: a fresh copy, owned with its entries' slots
and capacity, of a message `st` sent into the network to `id`, with its bundle; (D22 S-i) a
`MsgSnap`'s database saved in `id`'s snapshot directory `γd` (`netSnapRecv`). (2026-10-22, D38a)
Unmarshalled from the wire, the copy has no responses (the wire carries none: `MsgMarshals`).
(raft-entsize §4, 2026-11-10) The copy is owned at a content `c` (`msgPtsCC`) of the message's wire
fields with no responses and no unknown fields in its snapshot's conf state (until then
`msgPtsC ml 1 1 true st'` with `wireEq st st'` and no responses, the same by `msgPtsC_iff_CC`), of
bounded size when the payload says so (`N.Sz`), but for a `MsgSnap`: what `stepIn_intro` takes. -/
def netRecv (γn : NetNames GF) (id : w64) (γd : GName) (ml : Loc) : IProp GF :=
  iprop(∃ (st : MsgSt) (c : MsgC), msgPtsCC ml (DFrac.own 1) (DFrac.own 1) true c ∗
    ⌜c.model = ⟨st.msg, st.ents, st.snap, st.ctx, []⟩ ∧ c.csUfNil ∧ st.msg.To' = id ∧
      (γn.N.Sz → st.msg.Type' ≠ MsgSnap → msgSizeOk c)⌝ ∗
    (□ γn.N.P st) ∗ γn.N.O st ∗ netSnapRecv γd st)

/-- **The receiver's `Raft`** (`rafthttp.Raft`, persistent): `Process` of a received message with
a context the node API takes, given one of the receiver's resources `R` (back after the call),
returns raft's error (`nodeErr`: `nil`, `ErrStopped` or the context's; 2026-10-23, rafthttp stage 4:
the pipeline handler's error branch reads it, until then some error); `IsIDRemoved` (`false`: no
member is removed, the server's static membership; 2026-10-23, rafthttp stage 6, so the stream
handler never answers `410`), `ReportUnreachable`, `ReportSnapshot` from `True`, with no `R` (2026-10-23, rafthttp stage 6a: the
server's need none; only `Process` reads its logger under `lgMu`). (D22 S-i) `γd` names the receiver's snapshot directory (`netRecv`). -/
def netRaftOk (γn : NetNames GF) (id : w64) (γd : GName) (R : IProp GF) (r : GoInterface) :
    IProp GF :=
  iprop(∃ ri : GoInterfaceOk, ⌜r = GoInterface.ok ri⌝ ∗
    □ (∀ (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (ml : Loc),
      {{ nodeCtx ctx cd ∗ R ∗ netRecv γn id γd ml }}
        (App (App (Val #(methods ri.ty go!"Process" ri.v)) (Val #(GoInterface.ok ctx))) (Val #ml))
      {{ (err : GoInterface), RET #err; nodeErr cd err ∗ R }}) ∗
    □ (∀ x : w64, {{ True }} (App (Val #(methods ri.ty go!"IsIDRemoved" ri.v)) (Val #x))
      {{ RET #false; True }}) ∗
    □ (∀ x : w64, {{ True }} (App (Val #(methods ri.ty go!"ReportUnreachable" ri.v)) (Val #x))
      {{ RET #(); True }}) ∗
    □ (∀ (x : w64) (s : w64), {{ True }}
      (App (App (Val #(methods ri.ty go!"ReportSnapshot" ri.v)) (Val #x)) (Val #s))
      {{ RET #(); True }}))

/-- **A started transport `tr` of the network `γn`** (persistent; the started transport's part of
`Transport.Start`'s axiom, D21 M2): `Send` takes the slice of messages, each with its bundle, which
the transport puts into the network (delivered to the slot holder of its `To`, possibly lost);
`Stop` returns; (D22 S-i) `SendSnapshot` takes a merged snapshot message (`snap.msgIs m ml rc`)
with its bundle (`netSnapBundle`), which the transport streams to the slot holder of its `To`
(possibly lost), closing the message (`CloseWithError`: its reader closed, one value on its
`closeC`) when done, or at once with `errMemberNotFound` if no peer is added for `To`.
(2026-10-24, rafthttp stage 6d, the user's choice) `Send` borrows `T`, its caller's resource: the
transport's read lock needs one of the mutex's reader tokens (the server's raft loop holds one).
(2026-10-24) Of the member `lid`: its messages are `lid`'s (`netBundle`). (2026-10-26, D43 M5c,
the user's (A)) `Stop` consumes `TS`, its caller's right to stop the transport: a transport whose
owner may still add peers is stopped only by that owner (Go's `AddPeer` panics on a stopped
transport); a frozen one's `TS` is `True`. -/
def netTransport (γn : NetNames GF) (lid : w64) (tr : GoInterface) (T TS : IProp GF) : IProp GF :=
  iprop(∃ ti : GoInterfaceOk, ⌜tr = GoInterface.ok ti⌝ ∗
    □ (∀ (sl : GoSlice) (msL : List Loc),
      {{ sl ↦* msL ∗ ([∗list] m ∈ msL, netBundle γn.N lid m) ∗ T }}
        (App (Val #(methods ti.ty go!"Send" ti.v)) (Val #sl))
      {{ RET #(); T }}) ∗
    □ ({{ TS }} (App (Val #(methods ti.ty go!"Stop" ti.v)) (Val #())) {{ RET #(); True }}) ∗
    □ (∀ (m ml : Loc) (rc : GoInterface),
      {{ snap.msgIs m ml rc ∗ netSnapBundle γn.N ml rc }}
        (App (Val #(methods ti.ty go!"SendSnapshot" ti.v)) (Val #m))
      {{ RET #(); True }}))

instance netTransport_persistent (γn : NetNames GF) (lid : w64) (tr : GoInterface)
    (T TS : IProp GF) : Persistent (netTransport γn lid tr T TS) := by
  unfold netTransport; infer_instance

/-- **The transport's concurrency bound** (D21 M2, the user's (A)): at most `2 ^ 29` calls
into a receiver's `Raft` at a time, each with one of the `netProcSlots` resources `R` the receiver
gives `Transport.Start`. True of Go physically (each call is a goroutine with its own stack), not
from rafthttp's structure. -/
def netProcSlots : Nat := 2 ^ 29

instance netRaftOk_persistent (γn : NetNames GF) (id : w64) (γd : GName) (R : IProp GF)
    (r : GoInterface) : Persistent (netRaftOk γn id γd R r) := by
  unfold netRaftOk; infer_instance

/-! ### The pool of `R`s (J8a-6, 2026-11-01; `notes/decisions.md`, "The transport's `R`s from a
thread pool") -/

/-- The namespace of the receiver's pool of `R`s. -/
def raftPoolN : Namespace := nroot .@ "rafthttp_raft_pool"

/-- **The receiver's pool of `R`s** (persistent): a thread pool (Perennial's `threadPool`) of the
resources its `Raft`'s `Process` borrows, from which a goroutine that calls `Process` borrows one
with its thread token for its life (`raftPool_borrow`) and gives it back when it exits
(`raftLoan_giveBack`), so no copy is ever lost; the transport's (`trFixed`), given to `Start`.
(revoke-open Q3 (i), 2026-11-06) At level 1 (`threadPool.isThreadPoolL`): a holder of a whole token
lends its level 1 (`raftPool_borrow`), a holder of level 1 alone borrows with it
(`raftPool_borrowL`: `GoAttach`'s stopped branch, the revocation's outer goroutine). -/
def raftPool (R : IProp GF) : IProp GF :=
  iprop(∃ γ : GName, threadPool.isThreadPoolL raftPoolN 1 γ R)

instance raftPool_persistent (R : IProp GF) : Persistent (raftPool R) := by
  unfold raftPool; infer_instance

/-- **An `R` lent out by the pool for a whole thread token** (exclusive): what a borrower gives back
with the `R`: the loan and (revoke-open, 2026-11-06) the token's levels not lent. -/
def raftLoan (R : IProp GF) : IProp GF :=
  iprop(∃ γ : GName, threadPool.isThreadPoolL raftPoolN 1 γ R ∗ threadPool.ownThreadLoan γ ∗
    levelTok 0 ∗ threadTokFrom 2)

/-- **An `R` lent out by the pool for a level-1 token** (exclusive; revoke-open, 2026-11-06). -/
def raftLoanL (R : IProp GF) : IProp GF :=
  iprop(∃ γ : GName, threadPool.isThreadPoolL raftPoolN 1 γ R ∗ threadPool.ownThreadLoan γ)

end defs

section pool
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]

/-- A pool from `n` copies of `R`, `threadBound GF ≤ n + 1` (`threadPool.initL`). -/
theorem raftPool_init (R : IProp GF) (E : CoPset) (n : Nat) (Hn : threadBound GF ≤ n + 1) :
    ([∗list] _x ∈ List.replicate n (), R) ⊢ |={E}=> raftPool R := by
  iintro HR
  imod threadPool.initL raftPoolN 1 R E n Hn $$ HR with ⟨%γ, #Hp⟩
  imodintro
  iunfold raftPool
  iexists γ
  iexact Hp

/-- **Borrow an `R`** with a thread token (and a later credit). -/
theorem raftPool_borrow (R : IProp GF) (E : CoPset) (HN : ↑raftPoolN ⊆ E) :
    £ 1 ∗ raftPool R ∗ threadTok ⊢ |={E}=> R ∗ raftLoan R := by
  iintro ⟨Hlc, #Hp, Htt⟩
  iunfold raftPool at Hp
  icases Hp with ⟨%γ, #Hp⟩
  icases (threadTok_level0 (GF := GF)).1 $$ Htt with ⟨H0, Ht1⟩
  icases (threadTokFrom_succ (GF := GF) 1 (threadBound_gt (GF := GF))).1 $$ Ht1 with ⟨H1, H2⟩
  imod threadPool.borrowL_lc raftPoolN 1 γ R E HN $$ [Hlc Hp H1] with ⟨HR, Hl⟩
  · iframe; iframe #
  imodintro
  iframe HR
  iunfold raftLoan
  iexists γ
  iframe; iframe #

/-- **Give a borrowed `R` back**, for the thread token. -/
theorem raftLoan_giveBack (R : IProp GF) (E : CoPset) (HN : ↑raftPoolN ⊆ E) :
    raftLoan R ∗ R ⊢ |={E}=> threadTok := by
  iintro ⟨Hl, HR⟩
  iunfold raftLoan at Hl
  icases Hl with ⟨%γ, #Hp, Hl, H0, H2⟩
  imod threadPool.giveBackL raftPoolN 1 γ R E HN $$ [Hp Hl HR] with H1
  · iframe; iframe #
  imodintro
  iapply (threadTok_level0 (GF := GF)).2
  iframe H0
  iapply (threadTokFrom_succ (GF := GF) 1 (threadBound_gt (GF := GF))).2
  iframe

/-- **Borrow an `R`** with a level-1 token (and a later credit; revoke-open, 2026-11-06). -/
theorem raftPool_borrowL (R : IProp GF) (E : CoPset) (HN : ↑raftPoolN ⊆ E) :
    £ 1 ∗ raftPool R ∗ levelTok 1 ⊢ |={E}=> R ∗ raftLoanL R := by
  iintro ⟨Hlc, #Hp, H1⟩
  iunfold raftPool at Hp
  icases Hp with ⟨%γ, #Hp⟩
  imod threadPool.borrowL_lc raftPoolN 1 γ R E HN $$ [Hlc Hp H1] with ⟨HR, Hl⟩
  · iframe; iframe #
  imodintro
  iframe HR
  iunfold raftLoanL
  iexists γ
  iframe; iframe #

/-- **Give an `R` borrowed with a level-1 token back**, for the token (revoke-open, 2026-11-06). -/
theorem raftLoanL_giveBack (R : IProp GF) (E : CoPset) (HN : ↑raftPoolN ⊆ E) :
    raftLoanL R ∗ R ⊢ |={E}=> levelTok 1 := by
  iintro ⟨Hl, HR⟩
  iunfold raftLoanL at Hl
  icases Hl with ⟨%γ, #Hp, Hl⟩
  iapply threadPool.giveBackL raftPoolN 1 γ R E HN $$ [Hp Hl HR]
  iframe; iframe #

end pool


/-! ### A frozen message's content form is its read-only content (raft-entsize §4) -/

section contentRo
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

theorem bytesCC_bytesC (ds : GoSlice) (o : Option (List w8)) :
    bytesCC (GF := GF) ds DFrac.discard o ⊢ bytesC ds o := by
  rcases o with _ | bs
  · simp only [bytesCC, bytesC]; iintro %H; ipureintro; exact H
  · simp only [bytesCC, bytesC]; iintro ⟨%H, #Hs⟩; iframe Hs; ipureintro; exact H

theorem csPtsCC_csRoC (p : Loc) (c : CSC) (al : Bool) :
    csPtsCC (GF := GF) p DFrac.discard c al ⊢ csRoC p c := by
  unfold csPtsCC csRoC
  iintro ⟨%sv, %sl, %so, %sn, %pa, %Hnn, #HV, #Hv, #HL, #Hl, #HO, #Ho, #HN, #Hn, #HA, #cA, -, #Hpb⟩
  iexists sv, sl, so, sn, pa
  iframe HV Hv HL Hl HO Ho HN Hn HA cA Hpb
  ipureintro; exact Hnn

theorem csOptCC_csOptC (p : Loc) (o : Option CSC) :
    csOptCC (GF := GF) p DFrac.discard o ⊢ csOptC p o := by
  rcases o with _ | c
  · simp only [csOptCC, csOptC]; iintro %H; ipureintro; exact H
  · simp only [csOptCC, csOptC]
    iintro (H | H)
    · iapply csPtsCC_csRoC $$ H
    · iapply csPtsCC_csRoC $$ H

theorem smPtsCC_metaRoC (p : Loc) (m : SnapMetaC) :
    smPtsCC (GF := GF) p DFrac.discard m ⊢ metaRoC p m := by
  unfold smPtsCC metaRoC
  iintro ⟨%pc, %pi, %pt, %Hnn, #HC, Hc, #HI, #cI, #HT, #cT, #Hpb⟩
  ihave #Hc := csOptCC_csOptC _ _ $$ Hc
  iexists pc, pi, pt
  iframe HC Hc HI cI HT cT Hpb
  ipureintro; exact Hnn

theorem smOptCC_metaOptC (p : Loc) (o : Option SnapMetaC) :
    smOptCC (GF := GF) p DFrac.discard o ⊢ metaOptC p o := by
  rcases o with _ | m
  · simp only [smOptCC, metaOptC]; iintro %H; ipureintro; exact H
  · simp only [smOptCC, metaOptC]; iapply smPtsCC_metaRoC

theorem ownSnapCC_snapRoC (p : Loc) (s : SnapC) :
    ownSnapCC (GF := GF) p DFrac.discard s ⊢ snapRoC p s := by
  unfold ownSnapCC snapRoC
  iintro ⟨%ds, %pm, %Hnn, #HD, Hd, #HM, Hm, #Hpb⟩
  ihave #Hd := bytesCC_bytesC _ _ $$ Hd
  ihave #Hm := smOptCC_metaOptC _ _ $$ Hm
  iexists ds, pm
  iframe HD Hd HM Hm Hpb
  ipureintro; exact Hnn

theorem snapOptCC_snapOptC (p : Loc) (o : Option SnapC) :
    snapOptCC (GF := GF) p DFrac.discard o ⊢ snapOptC p o := by
  rcases o with _ | s
  · simp only [snapOptCC, snapOptC]; iintro %H; ipureintro; exact H
  · simp only [snapOptCC, snapOptC]; iapply ownSnapCC_snapRoC

/-- **A read-only message at its content, without responses, is frozen at that content**
(`msgRoC`): what a handed-out message (`msgOut`) gives the network's bundle. -/
theorem msgPtsCC_msgRoC (l : Loc) (c : MsgC) (hr : c.resps = []) :
    msgPtsCC (GF := GF) l DFrac.discard DFrac.discard false c ⊢ msgRoC l c := by
  cases c with
  | mk f rs =>
  simp only [MsgC.resps] at hr
  subst hr
  unfold msgPtsCC
  iintro ⟨%pty, %pto, %pfr, %pte, %plt, %pix, %pco, %pvo, %prj, %prh, %es, %els, %ps, %cs,
    %rsl, %Hnn, #HTy, #cTy, #HTo, #cTo, #HFr, #cFr, #HTe, #cTe, #HLt, #cLt, #HIx, #cIx, #HCo, #cCo,
    #HVo, #cVo, #HRj, #cRj, #HRh, #cRh, #HEs, #Hes, #Hents, -, #HSn, Hsn, #HCx, #Hcx, #HRs, #Hrs,
    #Hpb⟩
  ihave #Hsn := snapOptCC_snapOptC _ _ $$ Hsn
  simp only [msgRoC, respsRoC, MsgC.f, MsgC.resps, List.map_nil] at *
  isplitl
  · unfold msgFRoC
    iexists pty, pto, pfr, pte, plt, pix, pco, pvo, prj, prh, es, els, ps, cs, rsl
    iframe HTy cTy HTo cTo HFr cFr HTe cTe HLt cLt HIx cIx HCo cCo HVo cVo HRj cRj HRh cRh
    iframe HEs Hes Hents HSn Hsn HCx Hcx HRs Hrs Hpb
    ipureintro; exact Hnn
  iempintro

end contentRo


section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

end lemmas

section lemmasG1
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [Gg : GooseGlobalGS HasLC.hasLC GF] [GoLocalContext]
variable [sem : go.Semantics]
attribute [local instance] GooseGlobalGS.gooseInvGS

/-- **A network's names, allocated** for the members `S` (the closed theorem's, once per
cluster): its payload and directory chosen, a slot per member, the streams' registry (empty;
stage 6a). -/
theorem netNames_alloc (N : NetPayload GF) (dir : w64 → List GoString) (S : GMap w64 Unit)
    (E : CoPset) :
    ⊢ |={E}=> ∃ γn : NetNames GF, ⌜γn.N = N ∧ γn.dir = dir⌝ ∗
      ([∗map] id ↦ _u ∈ S, netSlot γn id) ∗
      inv streamRegN iprop(∃ m : GMap GName StreamKey, ghostMapAuth γn.reg 1 m) := by
  imod ghost_map_alloc (GF := GF) S with ⟨%g, -, Hs⟩
  imod ghost_map_alloc_empty (GF := GF) (K := GName) (V := StreamKey) with ⟨%gr, Hr⟩
  imod (inv_alloc streamRegN E iprop(∃ m : GMap GName StreamKey, ghostMapAuth gr 1 m)) $$ [Hr]
    with #Hi
  · iexists _; iexact Hr
  imodintro
  iexists ⟨N, g, dir, gr⟩
  iframe Hi
  isplitr
  · ipureintro; exact ⟨rfl, rfl⟩
  unfold netSlot
  iexact Hs

end lemmasG1

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]


/-- **A member's snapshot directory, at names allocated before** (2026-10-26, D22 J2, R-loc: the
names are raft's `RaftNames.reSnapLoc`, fixed before the member starts): from the directory's right
(`snap.snapDirOwn` at the data directory `dd`'s paths, `bootOk`'s; restart S6a, M1),
(S5) the claims on every index's snapshot name, free (`snapFreeAll`, `bootOk`'s), and the directory
map's authority, empty, the directory's invariant (a fresh data directory: no `.snap.db` file), which
keeps the right (claim #34, 2026-11-23: the claim on the directory's other names; until then the right
named the map). -/
theorem snapDir_init (sd : GoString)
    (γd : GName) (img : w64 → backend.Data → IProp GF) (Rm : w64 → IProp GF) (E : CoPset) :
    ⊢ snap.snapDirOwn (snap.snapDBPath sd) -∗ snapFreeAll (snap.snapDBPath sd) -∗
      ghostMapAuth γd 1 (∅ : GMap w64 Unit) ={E}=∗
      snapDirKeep sd γd img Rm := by
  iintro Ho Hfree Ha
  imod token_alloc (GF := GF) with ⟨%γk, Ht⟩
  imod (inv_alloc snapDirN E (snapDirInvK sd γd γk img Rm)) $$ [Ho Ha Hfree] with #Hi
  · iunfold snapDirInvK
    iframe Ho
    ileft
    iunfold snapDirBody
    iunfold snapFreeAll at Hfree
    icases Hfree with ⟨%F, %hF, HF⟩
    iexists (∅ : GMap w64 backend.Data), (∅ : GMap w64 Unit), F
    iframe Ha HF
    isplitr
    · ipureintro; intro i; simp only [GMap.lookup_empty]; exact ⟨fun _ => by simp, fun _ => hF i⟩
    isplitr
    · iapply BigSepM.bigSepM_empty.2; itrivial
    isplitr
    · imodintro; iintro %i %h; exact absurd (GMap.lookup_empty i) h
    · imodintro; iintro %i %h; exact absurd (GMap.lookup_empty i) h.1
  imodintro
  iunfold snapDirKeep
  iexists γk
  iframe Hi Ht

/-- **The snapshot's file taken from the directory, sealed** (wal-link L2, T1, decided by
etcd-grove-03, 2026-11-17; until then `SnapRO.snapDir_take`, which handed out `fileHolds` and the
raised counter: `notes/axiom-review/releasesnapdbs.md`; since the merge of lean's S5, 2026-11-19, the
file is the directory's `fileAt`, the claim on its name with the file; D6-T6 round 3, 2026-11-24: a
crash-token update `|NC={⊤}=>`, the invariant having a crash side, which the running generation's
`notCrashed` rules out). A saved index `i` whose removal fact the
taker's `R` refutes is present in the directory; the taker's basic update makes `□ Rm i` (stored in
the invariant, which lets the file leave `M`) and `R'`; the file and `R'` are sealed together
(`storage.snapHeld`), which only `OpenSnapshotBackend` opens, at its rename; the image's certificate
is the taker's. The data `D` is fixed here. Why it is safe for `ReleaseSnapDBs`, which removes by
listing the directory: before the update no one holds `Rm i` (it contradicts `R`); the update is a
basic update (no invariant opened), so no other thread's resources change; `R'`, the only thing the
taker could make `Rm i` from, is sealed in the token (the seal gated by `etc/import-all.txt`). The
argument is for a removal fact that only ghost updates make (as the server's `snapRmM`, a counter's
lower bound): a `Rm` that a physical step or a pure fact could make true would escape "no other
thread's resources change". The refutation `R -∗ Rm i -∗ False` is a plain wand: it is used only where
the file is absent (it consumes `R` against the invariant's `Rm i`), and the other branch drops it and
spends `R` on the update. A later credit strips the invariant's later (`fileAt` is not
timeless). -/
theorem snapDir_take (sd : GoString) (γd : GName) (img : w64 → backend.Data → IProp GF)
    (Rm : w64 → IProp GF) (i : w64) (R R' : IProp GF) :
    ⊢ £ 1 -∗ snapDirInvH sd γd img Rm -∗ snapSaved γd i -∗ R -∗
      (R -∗ Rm i -∗ False) -∗ (R ==∗ R' ∗ □ Rm i) -∗
      |NC={⊤}=> ∃ D : backend.Data, storage.snapHeld (snap.snapDBPath sd i) D R' ∗ □ img i D := by
  iintro Hlc #Hh #Hsv HR Hno Hup Hnc
  iunfold snapDirInvH at Hh
  icases Hh with ⟨%γk, #Hinv⟩
  iinv Hinv with Hi Hclose
  imod (lc_fupd_elim_later (P := snapDirInvK sd γd γk img Rm)) $$ Hlc Hi with Hi
  iunfold snapDirInvK at Hi
  icases Hi with ⟨Hdi, Hb⟩
  icases Hb with (Hb | ⟨Hc, -⟩)
  rotate_left
  · iexfalso; iapply notCrashed_crashed $$ Hnc Hc
  iunfold snapDirBody at Hb
  icases Hb with ⟨%M, %Es, %F, Ha, %HF, HM, HFr, #HEs, #HRm⟩
  iunfold snapSaved at Hsv
  ihave %HEi := ghost_map_lookup $$ Ha Hsv
  have hEi : Es.lookup i ≠ none := by simp [HEi]
  cases hMi : M.lookup i with
  | none =>
    have hp : Es.lookup i ≠ none ∧ M.lookup i = none := ⟨hEi, hMi⟩
    ihave #Hr := HRm $$ %i %hp
    iexfalso
    iapply Hno $$ HR Hr
  | some D =>
    imod Hup $$ HR with ⟨HR', #Hrm⟩
    icases (BigSepM.bigSepM_delete (Φ := fun (j : w64) (D : backend.Data) => iprop(snapFileAt sd Es j D ∗
      □ img j D)) hMi).1 $$ HM with ⟨⟨Hf, #Himg⟩, HM⟩
    iunfold snapFileAt at Hf
    icases Hf with (⟨-, Hf⟩ | ⟨%hn, -⟩)
    rotate_left
    · exact absurd hn hEi
    imod Hclose $$ [Hdi Ha HM HFr] with -
    · inext
      iunfold snapDirInvK
      iframe Hdi
      ileft
      iunfold snapDirBody
      iexists GMap.delete i M, Es, F
      iframe Ha HM HFr HEs
      isplitr
      · ipureintro
        intro j
        by_cases hji : i = j
        · subst hji
          rw [GMap.lookup_delete M i]
          constructor
          · intro h; exact absurd ((HF i).1 h).1 hEi
          · intro h; exact absurd h.1 hEi
        · rw [GMap.lookup_delete_ne M hji]; exact HF j
      iintro !> %j %hj
      by_cases hji : i = j
      · subst hji
        iexact Hrm
      · rw [GMap.lookup_delete_ne M hji] at hj
        iapply HRm $$ %j %hj
    imodintro
    iframe Hnc
    iexists D
    iframe Himg
    iapply storage.snapHeld_intro
    iframe HR'
    iapply backend.fileAtDur_fileAt $$ Hf

-- (2026-10-27) `snapLocal_of_saved` (`snapSaved` as raft's `snapLocal`, by `RaftNames.reSnapLoc`)
-- deleted with the server's port onto raft's node API: the server's clusters send no snapshot.

-- (restart S6a, M1, 2026-11-13: the axiom review's M1, approved by the user via etcd-grove-81)
-- `snapDir_alloc` (an invariant for any `ss` from a fresh ghost map, no right to the directory)
-- deleted, unused: a second invariant over one directory made `SaveDBFrom`'s kept-file branch give
-- `snapSaved` of an index the second invariant did not know. The directory's right
-- (`snap.snapDirOwn`, `bootOk`) is consumed by `snapDir_init`, and the invariant holds it (claim #34,
-- 2026-11-23: the file extension's claim on the directory's other names; until then the record
-- `snap.snapDirIs` it made).

end lemmas

/-! ### The transport's slot in the boot hub

(2026-11-03, the final whole-`bootOk` review's M2; the slot convention the user approved,
`notes/spec-first-plan.md`, "The slot convention".) `NewServer.spec` names what it asks of a
member's URL directory only through `rafthttp.bootCfg`, sealed (`etc/import-all.txt`). It is a
coupling with raft's peers, which the transport owns (the convention's first form): the transport
adds every other peer of raft's configuration to itself, so its handler finds the sender of any
request only if the directory names exactly raft's peers, and it serves at most `peersMax` of them;
raft's peers are the slot's parameter. Not a condition on the configuration (the directory is the
network's name, `NetNames.dir`), so it takes none. -/

/-- **A one-member directory** (rafthttp stage 6d; the one-member examples'): the member `id`'s one
peer URL `url`, no other member. -/
def dirOne (id : w64) (url : GoString) (i : w64) : List GoString := if i = id then [url] else []

/-- **The transport's condition on its URL directory `dir`, of raft's peers `ps`** (sealed): the
members `dir` names are exactly `ps`, at most `peersMax` of them. -/
@[no_expose] def rafthttp.bootCfg (dir : w64 → List GoString) (ps : List w64) : Prop :=
  (∀ f, dir f ≠ [] ↔ f ∈ ps) ∧ ps.length ≤ peersMax

/-- `rafthttp.bootCfg` of a one-member directory (`dirOne`) and its member. -/
theorem rafthttp.bootCfg_dirOne (id : w64) (url : GoString) :
    rafthttp.bootCfg (dirOne id url) [id] := by
  unfold rafthttp.bootCfg
  refine ⟨fun f => ?_, by unfold peersMax; simp⟩
  unfold dirOne
  by_cases h : f = id <;> simp [h]

/-- `rafthttp.bootCfg` from the directory's members (`hdir`), at most three (the examples'
clusters). -/
theorem rafthttp.bootCfg_of (dir : w64 → List GoString) (ps : List w64)
    (hdir : ∀ f, dir f ≠ [] ↔ f ∈ ps) (hlen : ps.length ≤ 3) : rafthttp.bootCfg dir ps :=
  ⟨hdir, by unfold peersMax; omega⟩

/-- `rafthttp.bootCfg` from the directory's members (`hdir`), at most `peersMax` of them (the
clusters of any size, `examples/etcd/putgetN`; the clusterN Scope, 2026-11-15). -/
theorem rafthttp.bootCfg_of_le (dir : w64 → List GoString) (ps : List w64)
    (hdir : ∀ f, dir f ≠ [] ↔ f ∈ ps) (hlen : ps.length ≤ peersMax) : rafthttp.bootCfg dir ps :=
  ⟨hdir, hlen⟩

/-- **What the server's proof takes from `rafthttp.bootCfg`**: the directory's members are raft's
peers (the transport's `AddPeer`s and its handler's sender lookup). -/
theorem rafthttp.bootCfg_mem {dir : w64 → List GoString} {ps : List w64}
    (h : rafthttp.bootCfg dir ps) (f : w64) : dir f ≠ [] ↔ f ∈ ps := h.1 f

/-- **What the server's proof takes from `rafthttp.bootCfg`**: at most `peersMax` peers (the
transport's reader slots; raft's peer count within `int`). -/
theorem rafthttp.bootCfg_len {dir : w64 → List GoString} {ps : List w64}
    (h : rafthttp.bootCfg dir ps) : ps.length ≤ peersMax := h.2

end EtcdGrove
end Perennial
