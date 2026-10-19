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
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Defs
public import Proof.go_etcd_io.raft.v3.InvNodeCtx
public import Proof.go_etcd_io.raft.v3.InvPb
public import Perennial.Ghost.GhostMap

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

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
goroutines marshal it after `Send` returns), its persistent part and its one-shot part. -/
def netBundle (N : NetPayload GF) (m : Loc) : IProp GF :=
  iprop(∃ st : MsgSt, msgOwn m DFrac.discard st ∗ (□ N.P st) ∗ N.O st)

/-- **A message received by member `id`** at `ml`: a fresh copy, owned with its entries' slots
and capacity, of a message `st` sent into the network to `id`, with its bundle. -/
def netRecv (γn : NetNames GF) (id : w64) (ml : Loc) : IProp GF :=
  iprop(∃ st st' : MsgSt, msgPtsC ml (DFrac.own 1) (DFrac.own 1) true st' ∗
    ⌜wireEq st st' ∧ st.msg.To' = id⌝ ∗ (□ γn.N.P st) ∗ γn.N.O st)

/-- **The receiver's `Raft`** (`rafthttp.Raft`, persistent): `Process` of a received message with
a context the node API takes, given one of the receiver's resources `R` (back after the call),
returns some error; `IsIDRemoved`, `ReportUnreachable`, `ReportSnapshot` from `True`, each with
an `R` too. -/
def netRaftOk (γn : NetNames GF) (id : w64) (R : IProp GF) (r : GoInterface) : IProp GF :=
  iprop(∃ ri : GoInterfaceOk, ⌜r = GoInterface.ok ri⌝ ∗
    □ (∀ (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (ml : Loc),
      {{ nodeCtx ctx cd ∗ R ∗ netRecv γn id ml }}
        (App (App (Val #(methods ri.ty go!"Process" ri.v)) (Val #(GoInterface.ok ctx))) (Val #ml))
      {{ (err : GoInterface), RET #err; R }}) ∗
    □ (∀ x : w64, {{ R }} (App (Val #(methods ri.ty go!"IsIDRemoved" ri.v)) (Val #x))
      {{ (b : Bool), RET #b; R }}) ∗
    □ (∀ x : w64, {{ R }} (App (Val #(methods ri.ty go!"ReportUnreachable" ri.v)) (Val #x))
      {{ RET #(); R }}) ∗
    □ (∀ (x : w64) (s : w64), {{ R }}
      (App (App (Val #(methods ri.ty go!"ReportSnapshot" ri.v)) (Val #x)) (Val #s))
      {{ RET #(); R }}))

/-- **A started transport `tr` of the network `γn`** (persistent; the started transport's part of
`Transport.Start`'s axiom, D21 M2): `Send` takes the slice of messages, each with its bundle, which
the transport puts into the network (delivered to the slot holder of its `To`, possibly lost);
`Stop` returns. -/
def netTransport (γn : NetNames GF) (tr : GoInterface) : IProp GF :=
  iprop(∃ ti : GoInterfaceOk, ⌜tr = GoInterface.ok ti⌝ ∗
    □ (∀ (sl : GoSlice) (msL : List Loc),
      {{ sl ↦* msL ∗ [∗list] m ∈ msL, netBundle γn.N m }}
        (App (Val #(methods ti.ty go!"Send" ti.v)) (Val #sl))
      {{ RET #(); True }}) ∗
    □ ({{ True }} (App (Val #(methods ti.ty go!"Stop" ti.v)) (Val #())) {{ RET #(); True }}))

instance netTransport_persistent (γn : NetNames GF) (tr : GoInterface) :
    Persistent (netTransport γn tr) := by
  unfold netTransport; infer_instance

/-- **The transport's concurrency bound** (D21 M2, the user's (A)): at most `2 ^ 29` calls
into a receiver's `Raft` at a time, each with one of the `netProcSlots` resources `R` the receiver
gives `Transport.Start`. True of Go physically (each call is a goroutine with its own stack), not
from rafthttp's structure. -/
def netProcSlots : Nat := 2 ^ 29

instance netRaftOk_persistent (γn : NetNames GF) (id : w64) (R : IProp GF) (r : GoInterface) :
    Persistent (netRaftOk γn id R r) := by
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

end lemmas

end EtcdGrove
end Perennial
