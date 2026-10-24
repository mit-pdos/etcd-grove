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
renamed to `snapDBPath ss i` unless a file of that index is there, which it keeps). A member's
**snapshot directory** is an invariant the receiver allocates and gives `Transport.Start`
(`snapDirInv ss γd img Rm`, `snapDir_alloc`): the `.snap.db` files present (`M`, each with its
`fileHolds` and `□ img i D`) and the indices ever saved (`E`, a ghost map with persistent elements
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
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.snap.Defs
public import Proof.go_etcd_io.raft.v3.InvNodeCtx
public import Proof.go_etcd_io.raft.v3.InvPb
public import Perennial.Ghost.GhostMap
public import Perennial.Ghost.MonoNat

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **What a message carries over the network** (see the file header). -/
structure NetPayload (GF : BundledGFunctors) [FfiSyntax] where
  P : MsgSt → IProp GF
  O : MsgSt → IProp GF
  once : MsgSt → Prop
  P_pers : ∀ st, Persistent (P st)
  dup : ∀ st, ¬ once st → ⊢ |==> O st
  /-- (D22 S-i) what a snapshot message's database image `D` of index `i` carries (persistent):
  the sender's certificate, kept with the saved file in the receiver's directory -/
  img : w64 → backend.Data → IProp GF
  img_pers : ∀ i D, Persistent (img i D)

/-- **A network's names** (see the file header). -/
structure NetNames (GF : BundledGFunctors) [FfiSyntax] where
  N : NetPayload GF
  slots : GName
  dir : w64 → List GoString

/-- **Member `id`'s slot** (exclusive): held by the transport started for `id`
(`Transport.Start`), so that one transport receives what is sent to `id`. -/
def netSlot (γn : NetNames GF) (id : w64) : IProp GF :=
  ghostMapElem γn.slots id (DFrac.own 1) ()

/-- **A received copy agrees with the message sent**: its scalars, entries, snapshot and context
(not the `Responses` pointers: an unmarshalled copy's are fresh). -/
def wireEq (st st' : MsgSt) : Prop :=
  st'.msg = st.msg ∧ st'.ents = st.ents ∧ st'.snap = st.snap ∧ st'.ctx = st.ctx

/-- **A message handed to `Send`**, with its bundle: read-only for good (the transport's writer
goroutines marshal it after `Send` returns), its persistent part and its one-shot part; (D22 S-i)
not a `MsgSnap`, which goes by `SendSnapshot` (`netSnapBundle`). -/
def netBundle (N : NetPayload GF) (m : Loc) : IProp GF :=
  iprop(∃ st : MsgSt, msgOwn m DFrac.discard st ∗ (□ N.P st) ∗ N.O st ∗
    ⌜st.msg.Type' ≠ MsgSnap⌝)

/-- **A snapshot message handed to `SendSnapshot`** (D22 S-i): the raft message `ml` of the merged
message, a `MsgSnap` with a snapshot of index `i`, with its bundle (read-only for good, as
`netBundle`'s), and the right to read the merged message's reader `rc` (`readerStreams`), whose
complete streams are bbolt images of some `D` (`boltImage`) with the payload's certificate
`N.img i D` (for the server, `srvImage`: the committed state through `i`). -/
def netSnapBundle (N : NetPayload GF) (ml : Loc) (rc : GoInterface) : IProp GF :=
  iprop(∃ (st : MsgSt) (sn : SnapshotM) (D : backend.Data), msgOwn ml DFrac.discard st ∗
    (□ N.P st) ∗ N.O st ∗ ⌜st.msg.Type' = MsgSnap ∧ st.snap = some sn⌝ ∗
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

/-- **The snapshot directory of the snapshotter `ss`** (see the file header): the files present
`M`, each holding its data with its certificate (`img`), and the indices ever saved `E`
(`snapSaved`), which include `M`'s; a saved index not in `M` has the receiver's removal fact
`Rm i`. -/
def snapDirInv (ss : Loc) (γd : GName) (img : w64 → backend.Data → IProp GF)
    (Rm : w64 → IProp GF) : IProp GF :=
  iprop(∃ (M : GMap w64 backend.Data) (E : GMap w64 Unit),
    ghostMapAuth γd 1 E ∗ ⌜∀ i, M.lookup i ≠ none → E.lookup i ≠ none⌝ ∗
    ([∗map] i ↦ D ∈ M, backend.fileHolds (snap.snapDBPath ss i) D ∗ □ img i D) ∗
    □ (∀ i, ⌜E.lookup i ≠ none⌝ → snapSaved γd i) ∗
    □ (∀ i, ⌜E.lookup i ≠ none ∧ M.lookup i = none⌝ → Rm i))

/-- **A snapshot at index `j` or above was opened** (persistent; D22 receiver epochs, S8d,
2026-10-24; the orchestrator's decision on W1, `notes/decisions.md`): a lower bound of the
monotone counter `γt` of the highest snapshot index `applySnapshot` has opened, whose authority the
apply thread keeps at most its applied index. The server's removal fact of its snapshot directory
(`snapDirInv`'s `Rm`): `OpenSnapshotBackend(i)` takes the file `i` after raising the counter to
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
`MsgSnap`'s database saved in `id`'s snapshot directory `γd` (`netSnapRecv`). -/
def netRecv (γn : NetNames GF) (id : w64) (γd : GName) (ml : Loc) : IProp GF :=
  iprop(∃ st st' : MsgSt, msgPtsC ml (DFrac.own 1) (DFrac.own 1) true st' ∗
    ⌜wireEq st st' ∧ st.msg.To' = id⌝ ∗ (□ γn.N.P st) ∗ γn.N.O st ∗ netSnapRecv γd st)

/-- **The receiver's `Raft`** (`rafthttp.Raft`, persistent): `Process` of a received message with
a context the node API takes, given one of the receiver's resources `R` (back after the call),
returns some error; `IsIDRemoved`, `ReportUnreachable`, `ReportSnapshot` from `True`, each with
an `R` too. (D22 S-i) `γd` names the receiver's snapshot directory (`netRecv`). -/
def netRaftOk (γn : NetNames GF) (id : w64) (γd : GName) (R : IProp GF) (r : GoInterface) :
    IProp GF :=
  iprop(∃ ri : GoInterfaceOk, ⌜r = GoInterface.ok ri⌝ ∗
    □ (∀ (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (ml : Loc),
      {{ nodeCtx ctx cd ∗ R ∗ netRecv γn id γd ml }}
        (App (App (Val #(methods ri.ty go!"Process" ri.v)) (Val #(GoInterface.ok ctx))) (Val #ml))
      {{ (err : GoInterface), RET #err; R }}) ∗
    □ (∀ x : w64, {{ R }} (App (Val #(methods ri.ty go!"IsIDRemoved" ri.v)) (Val #x))
      {{ (b : Bool), RET #b; R }}) ∗
    □ (∀ x : w64, {{ R }} (App (Val #(methods ri.ty go!"ReportUnreachable" ri.v)) (Val #x))
      {{ RET #(); R }}) ∗
    □ (∀ (x : w64) (s : w64), {{ R }}
      (App (App (Val #(methods ri.ty go!"ReportSnapshot" ri.v)) (Val #x)) (Val #s))
      {{ RET #(); R }}))

/-- **The peers right of member `id`'s transport** (opaque, exclusive; D22 receiver epochs, S8c,
2026-10-24): `Transport.Start`'s, for the member `id` it is started for; the transport's `Stop`
takes it (`netTransport`), so its holder knows the transport is not stopped, which `AddPeer` needs
(it panics on a stopped transport, `transport.go:300-302`). The server's apply thread holds it
(`applySnapshot`'s `AddPeer` loop), and gives it to the raft node's stop when `run` returns
(`raftNode.stop`, through the `stopped` channel, to `onStop`'s `Stop`). -/
opaque netPeers (γn : NetNames GF) (id : w64) : IProp GF

/-- The opaque core of `netTrIs`. -/
opaque netTrIsCore (γn : NetNames GF) (id : w64) (tr : GoInterface) : IProp GF

/-- **`tr` is the transport started for member `id`** (persistent, opaque; S8c): only
`Transport.Start`'s axiom gives it, once per transport (it consumes the member's `netSlot`), so
the `id` is the transport's own. -/
def netTrIs (γn : NetNames GF) (id : w64) (tr : GoInterface) : IProp GF :=
  iprop(□ netTrIsCore γn id tr)

instance netTrIs_persistent (γn : NetNames GF) (id : w64) (tr : GoInterface) :
    Persistent (netTrIs (GF := GF) γn id tr) := by
  unfold netTrIs; infer_instance

/-- **A started transport `tr` of the network `γn`** (persistent; the started transport's part of
`Transport.Start`'s axiom, D21 M2): `Send` takes the slice of messages, each with its bundle, which
the transport puts into the network (delivered to the slot holder of its `To`, possibly lost);
`Stop` returns, taking the transport's peers right (D22 receiver epochs, S8c, 2026-10-24: until then
it took nothing; `netPeers`); (D22 S-i) `SendSnapshot` takes a merged snapshot message (`snap.msgIs m ml rc`)
with its bundle (`netSnapBundle`), which the transport streams to the slot holder of its `To`
(possibly lost), closing the message (`CloseWithError`: its reader closed, one value on its
`closeC`) when done, or at once with `errMemberNotFound` if no peer is added for `To`. -/
def netTransport (γn : NetNames GF) (tr : GoInterface) : IProp GF :=
  iprop(∃ ti : GoInterfaceOk, ⌜tr = GoInterface.ok ti⌝ ∗
    □ (∀ (sl : GoSlice) (msL : List Loc),
      {{ sl ↦* msL ∗ [∗list] m ∈ msL, netBundle γn.N m }}
        (App (Val #(methods ti.ty go!"Send" ti.v)) (Val #sl))
      {{ RET #(); True }}) ∗
    □ (∀ id : w64, {{ netPeers γn id ∗ netTrIs γn id tr }}
      (App (Val #(methods ti.ty go!"Stop" ti.v)) (Val #())) {{ RET #(); True }}) ∗
    □ (∀ (m ml : Loc) (rc : GoInterface),
      {{ snap.msgIs m ml rc ∗ netSnapBundle γn.N ml rc }}
        (App (Val #(methods ti.ty go!"SendSnapshot" ti.v)) (Val #m))
      {{ RET #(); True }}))

instance netTransport_persistent (γn : NetNames GF) (tr : GoInterface) :
    Persistent (netTransport γn tr) := by
  unfold netTransport; infer_instance

/-- **The transport's concurrency bound** (D21 M2, the user's (A)): at most `2 ^ 29` calls
into a receiver's `Raft` at a time, each with one of the `netProcSlots` resources `R` the receiver
gives `Transport.Start`. True of Go physically (each call is a goroutine with its own stack), not
from rafthttp's structure. -/
def netProcSlots : Nat := 2 ^ 29

instance netRaftOk_persistent (γn : NetNames GF) (id : w64) (γd : GName) (R : IProp GF)
    (r : GoInterface) : Persistent (netRaftOk γn id γd R r) := by
  unfold netRaftOk; infer_instance

end defs

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]

/-- **A network's names, allocated** for the members `S` (the closed theorem's, once per
cluster): its payload and directory chosen, a slot per member. -/
theorem netNames_alloc (N : NetPayload GF) (dir : w64 → List GoString) (S : GMap w64 Unit) :
    ⊢ |==> ∃ γn : NetNames GF, ⌜γn.N = N ∧ γn.dir = dir⌝ ∗
      [∗map] id ↦ _u ∈ S, netSlot γn id := by
  imod ghost_map_alloc (GF := GF) S with ⟨%g, -, Hs⟩
  imodintro
  iexists ⟨N, g, dir⟩
  isplitr
  · ipureintro; exact ⟨rfl, rfl⟩
  unfold netSlot
  iexact Hs

/-- **A member's snapshot directory, allocated empty** (D22 S-i): what the receiver gives
`Transport.Start` for its snapshotter `ss`, at the payload's certificate and its removal fact
`Rm` (a fresh data directory: its snapshot directory has no `.snap.db` file). -/
theorem snapDir_alloc (ss : Loc) (img : w64 → backend.Data → IProp GF) (Rm : w64 → IProp GF)
    (E : CoPset) : ⊢ |={E}=> ∃ γd : GName, inv snapDirN (snapDirInv ss γd img Rm) := by
  imod ghost_map_alloc_empty (GF := GF) (K := w64) (V := Unit) with ⟨%γd, Ha⟩
  imod (inv_alloc snapDirN E (snapDirInv ss γd img Rm)) $$ [Ha] with #Hi
  · iunfold snapDirInv
    iexists (∅ : GMap w64 backend.Data), (∅ : GMap w64 Unit)
    iframe Ha
    isplitr
    · ipureintro; intro i h; exact absurd (GMap.lookup_empty i) h
    isplitr
    · iapply BigSepM.bigSepM_empty.2; itrivial
    isplitr
    · imodintro; iintro %i %h; exact absurd (GMap.lookup_empty i) h
    · imodintro; iintro %i %h; exact absurd (GMap.lookup_empty i) h.1
  imodintro
  iexists γd
  iexact Hi

end lemmas

end EtcdGrove
end Perennial
