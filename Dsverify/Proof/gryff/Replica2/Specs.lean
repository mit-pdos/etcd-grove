/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/Replica2/Specs.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

# Stage 2: a replica's code-level specs (interface, draft; `sorry` proofs)

Over `Replica2/State.lean`'s abstraction. One statement per Go function the model transcribes or
that another package calls; `notes/stage2-interface-code.md` lists each spec's callers and the
unit that proves it.

**The shape of a handler's spec** (`stepSpec`): under the replica's lock, with the heap at `s`
(`replicaOwn ρ k r s`), the event's Go value projecting to `e`, the step's result
`stepR k s e = .ok (s', outs)` and the obligations to send `outs` (`pendingOuts γ ρ k r t outs`,
from `replica_step` + `pendingOuts_step`), the handler ends with the heap at `s'` and nothing
owed. The step's result is computed symbolically before the handler runs (the prophecy is
resolved and `replica_step` taken first; the handler then refines the step).

**Cross-package calls** (`gryff` ↔ `gryffcommon` through `IGryffCoordinator` /
`IGryffParticipant`, implemented by `*gryff.Replica`): the callbacks' specs are predicates on the
interface value (`icoordOk`, `ipartiOk`), parameterized by what the callbacks act on (`C vt o`:
the participant's store at `vt` and the obligations `o`; `V v`: the store's value). The
coordinator's and the participant's methods are specified against the model's steps of the
events they implement (`stepClientRead`, `stepRead1Reply`, ..., `stepRead1`, ...): they consume
the obligations their callbacks discharge.

**`genericsmr`** (called by `gryff`): `SendMsg` (one owed message to a peer), `GetClientWriter`,
`RegisterRPC`, `ConnectToPeers`, `replicaListener`, `serveClient`, `WaitForClientConnections`,
`NewReplicaDurable`; their resources beyond `Replica2/State.lean` are unit N's slots.
-/
module

public import Dsverify.Proof.gryff.Replica2.State
public import Dsverify.Proof.gryff.N.StateLaws
public import Dsverify.Proof.gryff.N.SpecsDefs
public import Dsverify.Proof.gryff.N.Register
public import Dsverify.Proof.gryff.N.Listener
public import Dsverify.Proof.gryff.N.Build
public import Dsverify.Proof.gryff.N.Reply
public import Dsverify.Proof.gryff.Replica.Tarjan
public import Dsverify.Proof.gryff.B.Run
public import Net.Proof.net.ConnIo
public import Dsverify.GeneratedProof.gryff.examples.gryffnet

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.replica2

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net proto
open Perennial.gryff.model (RState Copy LB RecoveryInstance Proposal ReadOp WriteOp OngoingOp
  Msg Ev Ext Out Cmd Deps AMap StepRes)
open Perennial.gryff.replica (XS TInv Post)
open github_com.goose_lang.primitive (ProphId)

attribute [local instance] GooseGlobalGS.gooseInvGS

/-! ## Pure helpers -/

/-- `HandleOverwrite(0, v, t)` on the store's value-tag `vt` (`RState.overwrite`'s). -/
def ovw (vt : model.ValTag) (v : w64) (t : model.Tag) : model.ValTag :=
  if vt.t.lt t then ⟨v, t⟩ else vt

theorem overwrite_storeVT (s : RState) (v : w64) (t : model.Tag) :
    (s.overwrite v t).storeVT = ovw s.storeVT v t ∧ (s.overwrite v t).ongoing = s.ongoing := by
  unfold RState.overwrite ovw RState.storeVT; split <;> simp_all

/-- The `Read1Proxied` a coordinator (replica id `k`, store `vt`) sends for read op `ro`
(`SendRead1`: `D` is never set, the zero `Dep`). -/
def read1Msg (k : Fin 3) (ro : ReadOp) (vt : model.ValTag) : model.Read1ProxiedM :=
  ⟨ro.requestId, ro.clientId, 0, model.dep0, rid32 k, vt⟩
/-- The `Read2Proxied` of read op `ro` (`SendRead2`), its read value-tag `rv`. -/
def read2Msg (k : Fin 3) (ro : ReadOp) (rv : model.ValTag) : model.Read2ProxiedM :=
  ⟨ro.requestId, ro.clientId, 0, rv, rid32 k⟩
/-- The `Write1Proxied` of write op `w` (`SendWrite1`: `D` is the op's `Dep`, the client's). -/
def write1Msg (k : Fin 3) (w : WriteOp) : model.Write1ProxiedM :=
  ⟨w.requestId, w.clientId, 1, 0, w.dep, rid32 k⟩
/-- The `Write2Proxied` of write op `w` with its tag `t` (`SendWrite2`). -/
def write2Msg (k : Fin 3) (w : WriteOp) (t : model.Tag) : model.Write2ProxiedM :=
  ⟨w.requestId, w.clientId, 0, ⟨w.writeValue, t⟩, rid32 k⟩

/-- The outputs of sending `m` to each of `rs` in turn (own id: its channel; else `SendMsg`). -/
def sendsTo (rs : List w32) (m : Msg) : Option (List Out) := rs.mapM (fun q => model.sendTo q m)

/-- The literal `StatsMap` keys of `int` entries (`Max`, `Add`, `Increment`) in `gryff`,
`gryffcommon`, `genericsmr` (fork branch `verify2`; H1-R5, N-3). -/
def statsIntKeys : List GoString :=
  [go!"conflicts_map_size", go!"fast_path", go!"fast_writes_0", go!"fast_reads_0",
    go!"slow_path", go!"slow_writes_0", go!"slow_reads_0", go!"rmw_queue_length",
    go!"preempted_prepare", go!"preempted_propose", go!"rmw_sleep",
    go!"fast_overwrites_timeout", go!"fast_overwrites_timeout_0",
    go!"shortcircuit_reads", go!"shortcircuit_reads_0", go!"shortcircuit_writes",
    go!"shortcircuit_writes_0", go!"fast_reads", go!"slow_reads", go!"fast_writes",
    go!"slow_writes", go!"failed_fast_overwrite_quorum_condition",
    go!"shortcircuit_writes_timeout", go!"shortcircuit_writes_timeout_0",
    go!"fulfilled_shortcircuit_quorum_condition", go!"failed_shortcircuit_quorum_condition",
    go!"tag_map_size"]

/-- The literal `StatsMap` keys of `map[string]int` entries (`IncrementStrInt`; the
coordinator's). -/
def statsMapKeys : List GoString :=
  [go!"read_1_quorum", go!"read_2_sent", go!"read_2_quorum", go!"write_1_quorum",
    go!"write_2_sent", go!"write_2_quorum"]

/-- A key of an `int` entry: a literal one, or one `genericsmr`'s listeners format
(`fmt.Sprintf("server_rpc_%d_chan_length", ..)`, `"client_rpc_%d_chan_length"`: a prefix
suffices, none of `statsMapKeys` starts with either). -/
def statsIntKey (key : GoString) : Prop :=
  key ∈ statsIntKeys ∨ go!"server_rpc_" <+: key ∨ go!"client_rpc_" <+: key

/-- The two kinds are disjoint. -/
theorem statsIntKey_not_map (key : GoString) (h : statsIntKey key) : key ∉ statsMapKeys := by
  intro hm
  simp only [statsMapKeys, List.mem_cons, List.not_mem_nil, or_false] at hm
  unfold statsIntKey at h
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;> revert h <;> decide

section
variable [GooseExts] [GoGlobalContext] [GoSemanticsFunctions]

/-- An interface method call `ic.f(args)` (`MethodResolve` on the interface type `T`). -/
abbrev icall (T : go.GoType) (f : GoString) (ic : GoInterface) : Expr :=
  App (Val (GoInstruction (MethodResolve T f))) (Val #ic)

/-- A participant method value. -/
abbrev partiM (pa : Loc) (f : GoString) : Expr :=
  Val (pa @!! go.GoType.PointerType src.gryffcommon.GryffParticipant.ty @!! f)

/-- A coordinator method value. -/
abbrev coordM (co : Loc) (f : GoString) : Expr :=
  Val (co @!! go.GoType.PointerType src.gryffcommon.GryffCoordinator.ty @!! f)

/-- A `genericsmr.Replica` method value. -/
abbrev genM (gR : Loc) (f : GoString) : Expr :=
  Val (gR @!! go.GoType.PointerType src.genericsmr.Replica.ty @!! f)

/-- A `*gryff.Replica` method value. -/
abbrev repM (r : Loc) (f : GoString) : Expr :=
  Val (r @!! go.GoType.PointerType src.gryff.Replica.ty @!! f)

/-- An `*EPaxosRMWHandler` method value. -/
abbrev epM (h : Loc) (f : GoString) : Expr :=
  Val (h @!! go.GoType.PointerType src.gryff.EPaxosRMWHandler.ty @!! f)

end

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics]
variable [gA : examples.gryffnet.Assumptions] [fa : src.fastrpc.Assumptions] [wire.BufioSpecs GF]
/- The harness's trusted models the code calls (H1-R6, N-1): `io.ReadFull` / `ReadAtLeast` in every
`Unmarshal`, `binary.PutVarint` / `ReadVarint` in the command slices' `Marshal` / `Unmarshal`,
`strings.Index` (`waitForPeerConnections`), `time.Sleep` (`ConnectToPeers`,
`waitForPeerConnections`, `SetForceWrite`), `sort.Slice` (`ShortCircuit`). The nodes'
`nodeAssumptions` (`GryffNetSpec.lean`) contain all of them: `replica_boot` (`Server/Boot.lean`)
takes them from its `Node.Assumptions` hypothesis and passes them to `NewReplica.wp`
(`Server/Specs.lean`), whose proof reaches these specs. -/
variable [binA : wire.BinaryVarintHyps GF]
variable [strconvA : strconv.Assumptions] -- N-5 (`IncrementStrInt`'s `strconv.Itoa`)


/-! ## `stats` (called by `gryffcommon` and `genericsmr`) -/

/-- **Unit H's slot.** A `*stats.StatsMap` (persistent: its mutex and the map under it). -/
@[irreducible] def statsOk (_st : Loc) : IProp GF := netN.statsOkB _st

omit binA strconvA in -- a law, no code (H1-R6 / N-1)
/-- `statsOk` is persistent (H2-R3; its body is a sealed slot, unit N's). -/
instance statsOk_persistent (st : Loc) : Persistent (statsOk st : IProp GF) := by
  unfold statsOk netN.statsOkB; infer_instance

/-- `Increment` / `Max` on a key of an `int` entry (H1-R5, N-3: `Max` / `Add` type-assert the
entry to `int`, `IncrementStrInt` to `map[string]int`, so a key used by both kinds panics). -/
theorem StatsMap.Increment.wp (st : Loc) (key : GoString) (hk : statsIntKey key) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.stats ∗ statsOk st }}
      (App (Val (st @!! go.GoType.PointerType src.stats.StatsMap.ty @!! go!"Increment"))
        (Val #key))
    {{ (n : w64), RET #n; True }} := by
  unfold statsOk; exact netN.wp_Increment st key (statsIntKey_not_map key hk)

/-- `IncrementStrInt` on a key of a `map[string]int` entry (H1-R5). -/
theorem StatsMap.IncrementStrInt.wp (st : Loc) (key : GoString) (idx : w64)
    (hk : key ∈ statsMapKeys) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.stats ∗ statsOk st }}
      (App (App (Val (st @!! go.GoType.PointerType src.stats.StatsMap.ty @!! go!"IncrementStrInt"))
        (Val #key)) (Val #idx))
    {{ (n : w64), RET #n; True }} := by
  unfold statsOk; exact netN.wp_IncrementStrInt st key idx hk

theorem StatsMap.Max.wp (st : Loc) (key : GoString) (v : w64) (hk : statsIntKey key) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.stats ∗ statsOk st }}
      (App (App (Val (st @!! go.GoType.PointerType src.stats.StatsMap.ty @!! go!"Max"))
        (Val #key)) (Val #v))
    {{ (n : w64), RET #n; True }} := by
  unfold statsOk; exact netN.wp_Max st key v (statsIntKey_not_map key hk)

/-! ## The callbacks' specs (`gryffcommon`'s interfaces, implemented by `*gryff.Replica`) -/


/-- A Hoare triple as a (persistent) proposition of the logic, for the method specs stated as
predicates on interface values: `specT P e Q` is `{{ P }} e {{ v, RET v; Q v }}`. -/
def specT (P : IProp GF) (e : Expr) (Q : val → IProp GF) : IProp GF :=
  iprop(□ ∀ Φ : val → IProp GF, P -∗ ▷ (∀ v, Q v -∗ Φ v) -∗ WP e {{ v, Φ v }})

/-- **`ip` implements `IGryffParticipant`** over the store's value `V v` (key 0 only):
`GetCurrentValue` / `SetCurrentValue` read / write it; `Printf` and `GetStats` are harmless;
`HandleWrite1Overwrite` and `SendWrite1Timeout` are never called in this configuration (only for
a Write1 that is not forced, or an `OngoingWrites` entry not yet answered: the model's
invariant, `partiOwn`). -/
def ipartiOk (ip : GoInterface) (V : w64 → IProp GF) : IProp GF :=
  iprop(
    (∀ v : w64, specT iprop(V v) (App (icall src.gryffcommon.IGryffParticipant.ty go!"GetCurrentValue" ip) (Val #(W64 0))) (fun ret => iprop(⌜ret = #v⌝ ∗ V v))) ∗
    (∀ (v : w64) (v' : w64), specT iprop(V v) (App (App (icall src.gryffcommon.IGryffParticipant.ty go!"SetCurrentValue" ip)
        (Val #(W64 0))) (Val #v')) (fun ret => iprop(⌜ret = #()⌝ ∗ V v'))) ∗
    (∀ (f : GoString) (a : GoSlice), specT iprop(True) (App (App (icall src.gryffcommon.IGryffParticipant.ty go!"Printf" ip) (Val #f)) (Val #a)) (fun ret => iprop(⌜ret = #()⌝ ∗ True))) ∗
    specT iprop(True) (App (icall src.gryffcommon.IGryffParticipant.ty go!"GetStats" ip) (Val #())) (fun ret => iprop(∃ st : Loc, ⌜ret = #st⌝ ∗ statsOk st)) ∗
    (∀ (c : w32) (w : Loc), specT iprop(False) (App (App (icall src.gryffcommon.IGryffParticipant.ty go!"HandleWrite1Overwrite" ip)
        (Val #c)) (Val #w)) (fun ret => iprop(⌜ret = #()⌝ ∗ True))) ∗
    (∀ w : Loc, specT iprop(False) (App (icall src.gryffcommon.IGryffParticipant.ty go!"SendWrite1Timeout" ip) (Val #w)) (fun ret => iprop(⌜ret = #()⌝ ∗ True))))

/-- **`ic` implements `IGryffCoordinator`** for replica id `k` over `C vt o` (the participant's
store at `vt`, the obligations `o` still to discharge, in order): each send consumes the owed
messages it sends (`SendRead1` / `SendRead2` / `SendWrite1` / `SendWrite2`: one per replica of
`replicas`, in order), `CompleteRead` / `CompleteWrite` an owed client reply (its client id's
writer is known), `HandleOverwrite` moves the store; `GetReplicasByRank` (thrifty only),
`SendWrite2ConcurrentTimeout`, `SetForceWrite` are never called by the coordinator here. -/
def icoordOk (ρ : Repl2Names) (ic : GoInterface) (k : Fin 3)
    (C : model.ValTag → List Out → IProp GF) : IProp GF :=
  iprop(
    (∀ (rop : Loc) (ro : ReadOp) (sl : GoSlice) (rs : List w32) (vt : model.ValTag)
        (outs o : List Out), ⌜sendsTo rs (.read1 (read1Msg k ro vt)) = some outs⌝ -∗
      specT iprop(C vt (outs ++ o) ∗ readOpRep ρ rop ro ∗ sl ↦* rs) (App (App (icall src.gryffcommon.IGryffCoordinator.ty go!"SendRead1" ic) (Val #rop))
          (Val #sl)) (fun ret => iprop(⌜ret = #()⌝ ∗ C vt o ∗ readOpRep ρ rop ro ∗ sl ↦* rs))) ∗
    (∀ (rop : Loc) (ro : ReadOp) (rv : model.ValTag) (sl : GoSlice) (rs : List w32)
        (vt : model.ValTag) (outs o : List Out),
        ⌜ro.readValTag = some rv ∧ sendsTo rs (.read2 (read2Msg k ro rv)) = some outs⌝ -∗
      specT iprop(C vt (outs ++ o) ∗ readOpRep ρ rop ro ∗ sl ↦* rs) (App (App (icall src.gryffcommon.IGryffCoordinator.ty go!"SendRead2" ic) (Val #rop))
          (Val #sl)) (fun ret => iprop(⌜ret = #()⌝ ∗ C vt o ∗ readOpRep ρ rop ro ∗ sl ↦* rs))) ∗
    (∀ (co wop : Loc) (w : WriteOp) (mat : src.gryffproto.Tag) (sl : GoSlice) (rs : List w32)
        (vt : model.ValTag) (outs o : List Out),
        ⌜sendsTo rs (.write1 (write1Msg k w)) = some outs⌝ -∗
      specT iprop(C vt (outs ++ o) ∗ writeOpRep ρ co wop w ∗
          co.[src.gryffcommon.GryffCoordinator, go!"maxAppliedTag"] ↦ mat ∗ sl ↦*□ rs) (App (App (icall src.gryffcommon.IGryffCoordinator.ty go!"SendWrite1" ic) (Val #wop))
          (Val #sl)) (fun ret => iprop(⌜ret = #()⌝ ∗ C vt o ∗ writeOpRep ρ co wop w ∗
          co.[src.gryffcommon.GryffCoordinator, go!"maxAppliedTag"] ↦ mat))) ∗
    (∀ (co wop : Loc) (w : WriteOp) (t : model.Tag) (sl : GoSlice) (rs : List w32)
        (vt : model.ValTag) (outs o : List Out),
        ⌜w.writeTag = some t ∧ sendsTo rs (.write2 (write2Msg k w t)) = some outs⌝ -∗
      specT iprop(C vt (outs ++ o) ∗ writeOpRep ρ co wop w ∗ sl ↦*□ rs) (App (App (icall src.gryffcommon.IGryffCoordinator.ty go!"SendWrite2" ic) (Val #wop))
          (Val #sl)) (fun ret => iprop(⌜ret = #()⌝ ∗ C vt o ∗ writeOpRep ρ co wop w))) ∗
    (∀ (rid cid : w32) (v : w64) (vt : model.ValTag) (o : List Out) (w : Loc),
      specT iprop(C vt (.ext (.readReply cid rid v 1) :: o) ∗ writerIs ρ cid w) (App (App (App (App (icall src.gryffcommon.IGryffCoordinator.ty go!"CompleteRead" ic)
          (Val #rid)) (Val #cid)) (Val #true)) (Val #v)) (fun ret => iprop(⌜ret = #()⌝ ∗ C vt o))) ∗
    (∀ (rid cid : w32) (vt : model.ValTag) (o : List Out) (w : Loc),
      specT iprop(C vt (.ext (.writeReply cid rid 1) :: o) ∗ writerIs ρ cid w) (App (App (App (icall src.gryffcommon.IGryffCoordinator.ty go!"CompleteWrite" ic)
          (Val #rid)) (Val #cid)) (Val #true)) (fun ret => iprop(⌜ret = #()⌝ ∗ C vt o))) ∗
    (∀ (v : w64) (tp : Loc) (gt : src.gryffproto.Tag) (vt : model.ValTag) (o : List Out),
      specT iprop(C vt o ∗ tp ↦□ gt) (App (App (App (icall src.gryffcommon.IGryffCoordinator.ty go!"HandleOverwrite" ic)
          (Val #(W64 0))) (Val #v)) (Val #tp)) (fun ret => iprop(⌜ret = #()⌝ ∗ C (ovw vt v (tagOf gt)) o))) ∗
    (∀ (f : GoString) (a : GoSlice), specT iprop(True) (App (App (icall src.gryffcommon.IGryffCoordinator.ty go!"Printf" ic) (Val #f)) (Val #a)) (fun ret => iprop(⌜ret = #()⌝ ∗ True))) ∗
    specT iprop(True) (App (icall src.gryffcommon.IGryffCoordinator.ty go!"GetStats" ic) (Val #())) (fun ret => iprop(∃ st : Loc, ⌜ret = #st⌝ ∗ statsOk st)) ∗
    specT iprop(False) (App (icall src.gryffcommon.IGryffCoordinator.ty go!"GetReplicasByRank" ic) (Val #())) (fun ret => iprop(⌜ret = #()⌝ ∗ True)) ∗
    (∀ w : Loc, specT iprop(False) (App (icall src.gryffcommon.IGryffCoordinator.ty go!"SendWrite2ConcurrentTimeout" ic)
        (Val #w)) (fun ret => iprop(⌜ret = #()⌝ ∗ True))) ∗
    specT iprop(False) (App (icall src.gryffcommon.IGryffCoordinator.ty go!"SetForceWrite" ic) (Val #())) (fun ret => iprop(⌜ret = #()⌝ ∗ True)))

omit binA strconvA in -- a law, no code (H1-R6 / N-1)
instance ipartiOk_persistent (ip : GoInterface) (V : w64 → IProp GF) :
    Persistent (ipartiOk ip V) := by
  unfold ipartiOk specT; infer_instance
attribute [local instance] unitS.pureWand_persistent in
set_option synthInstance.maxSize 2000 in
set_option synthInstance.maxHeartbeats 800000 in
omit binA strconvA in -- a law, no code (H1-R6 / N-1)
instance icoordOk_persistent (ρ : Repl2Names) (ic : GoInterface) (k : Fin 3)
    (C : model.ValTag → List Out → IProp GF) : Persistent (icoordOk ρ ic k C) := by
  unfold icoordOk specT; infer_instance

/-! ## The participant (`gryffcommon`, called by `gryff`) -/


/-! ## The coordinator (`gryffcommon`, called by `gryff`)

Each method against the model's step of the event it implements; `C` moves with the
participant's store (`HandleOverwrite`) and the obligations (the callbacks'). -/


-- `GryffCoordinator.HandleWrite1Reply.wp`, `HandleWrite2Reply.wp`, `ShortCircuit.wp`: in
-- `Replica2/Link.lean` (C-H1; proved by unit H1's `*.wp_proof`).

/-! ## `*gryff.Replica` implements the interfaces -/

-- `Replica_ipartiOk` (the participant's callbacks): in `Replica2/Link.lean` (H1b-R2: it takes
-- `h1Fixed`, stated below).

/-- What the coordinator's callbacks act on, in a handler of replica `k` at trace `t` (after the
step): the participant's store at `vt` (its ongoing writes `ong` unchanged by the coordinator),
the scratch messages, the obligations `o`. -/
def coordCtx (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r pa : Loc) (t : List Ev)
    (ong : AMap 32 w32) (vt : model.ValTag) (o : List Out) : IProp GF :=
  iprop(∃ gR : Loc, r.[src.gryff.Replica, go!"Replica"] ↦□ gR ∗
    partiOwn pa (replicaIface r) k vt.t ong ∗ valOwn gR vt.v ∗ scratchOwn r ∗
    pendingOuts γ ρ k r t o)

-- `Replica_icoordOk` moved to `Replica2/Link.lean` (C-H1c; statement text unchanged).

/-! ## `genericsmr` (called by `gryff`)

Their resources beyond `Replica2/State.lean` are unit N's slots (sealed, bodies in Prove). -/

/-- **Unit N's slot.** The reader `rd` of replica id `k`'s connection with peer `q` has returned
the encodings of `q`'s first messages `ms` to `k` (`peerStream_recv`: they are `q`'s stream's). -/
@[irreducible] def peerReaderAt (_γ : GryffNames GF) (_q _k : Fin 3) (_rd : Loc)
    (_ms : List Msg) : IProp GF := netN.peerReaderB _γ _q _k _rd _ms

/-- **Unit N's slot.** An accepted client connection at replica id `k` (the client's handshake,
its id `hs`, read): stage 1's client-side resources (`clientConnAt`, the acceptor's fresh end,
the reader over the client stream protocol `clientReqsOk`, the connection's write end and its
writer contract for the writer `serveClient` makes). Port (`Net/`): the connection is a
`*TCPConn` `t` with `net.connAt t cn true a la ra` (accepted at any address `a` the wildcard
listener at `lisAddrOf a0` takes; its protocols are `a0`'s, `lisProto`); the reader is
dsv-bufio's over the connection (`net.conn_readerOk`'s contract, read errors `connReadE`, so that
`serveClient` can log them), the reader's peek an update of the
reader resource (`wire.readNext`'s shape); the writer contract is `net.conn_streamWriterOk`'s
(`J := sendTok cn true Q`, `Q := gryffWireQ γ a0 cn`, write errors `connWriteE`); the lab's
`sharedInvs` is `protoInvs` (Gryff's and the placers' invariants). -/
@[irreducible] def clientConnIn (_γ : GryffNames GF) (_ρ : Repl2Names) (_k : Fin 3)
    (_conn : GoInterface) (_rd : Loc) (_hs : w32) : IProp GF :=
  iprop(∃ (t : Loc) (c : Nat) (a a0 : GoString) (la ra ed eof : GoInterface)
      (I : List w8 → IProp GF),
    ⌜_conn = interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #t ∧ a0 ∈ replicaAddrs⌝ ∗
    net.connAt t c true a la ra ∗ globalAddr io.EOF ↦□ eof ∗
    wire.readerOk ⟨Perennial.net.connIface t, Perennial.net.connReadE eof la ra ed⟩ I ∗
    wire.ownReader _rd ⟨Perennial.net.connIface t, Perennial.net.connReadE eof la ra ed⟩ I
      (u32Le _hs) ∗
    □ (∀ Y, wire.ownReader _rd ⟨Perennial.net.connIface t, Perennial.net.connReadE eof la ra ed⟩ I
        (u32Le _hs ++ Y) ={⊤}=∗
      wire.ownReader _rd ⟨Perennial.net.connIface t, Perennial.net.connReadE eof la ra ed⟩ I
        (u32Le _hs ++ Y) ∗
      ∃ (last : Int) (body : List w8), clientReqsOk _γ _hs last body ∗ ⌜Y <+: body⌝) ∗
    wire.writerOk ⟨net.connIface t, Perennial.net.connWriteE la ra ed, 4096⟩
      (sendTok c true (gryffWireQ _γ a0)) (gryffWireQ _γ a0 c) ∗
    sendTok c true (gryffWireQ _γ a0) [] ∗
    □ (∀ Y, msgsOk (clientReplyOk _γ _hs) Y -∗ gryffWireQ _γ a0 c Y) ∗
    clientConnAt _γ _hs c ∗ connFresh c true ∗ □ protoInvs _γ)

/-- **Unit N's slot.** What `ConnectToPeers` starts from (replica id `k`, node's address `a0`):
the right to listen at `a0`'s wildcard `lisAddrOf a0` with `a0`'s protocols (`lisProto`: the
start set them once for every address the listener takes), the peers' addresses
(`PeerAddrList`, each with its protocols), the cursors of the peers' streams to `k` (`rxCurTok γ
q k 0`, for its listeners), `k`'s prediction for the dialed handshakes (`peerStream_nil_upd`),
the slices `Peers`, `PeerReaders`, `PeerWriters`, `Alive` (written without the lock, before the
run loop), `Listener`. Port: the lab's `nodeIp ip ∗ addrTok (ip:port)` (it listened at its exact
address) is `lisProto`; `addrProtoG` is `Net/`'s `addrProto` with Gryff's wire protocols. -/
@[irreducible] def connectRes (_γ : GryffNames GF) (_ρ : Repl2Names) (_k : Fin 3) (_r _gR : Loc) :
    IProp GF :=
  iprop(∃ (pal pS rS wS aS : GoSlice) (nodes : List GoString) (a0 : GoString) (ws : List w64),
    _gR.[src.genericsmr.Replica, go!"PeerAddrList"] ↦□ pal ∗ pal ↦*□ nodes ∗
    ⌜nodes.length = 3 ∧ nodes[_k.val]? = some a0⌝ ∗
    ([∗list] i ↦ a ∈ nodes, portId _γ a (W32 i) ∗
      addrProto a (gryffWireP _γ a) (gryffWireQ _γ a) ∗ ⌜a ∈ replicaAddrs⌝) ∗
    ([∗list] i ↦ a ∈ nodes, ⌜i < _k.val⌝ -∗ peerRole _γ a (rid32 _k)) ∗
    lisProto (lisAddrOf a0) (gryffWireP _γ a0) (gryffWireQ _γ a0) ∗ □ protoInvs _γ ∗
    _gR.[src.genericsmr.Replica, go!"Peers"] ↦□ pS ∗ pS ↦* List.replicate 3 interface.nil ∗
    _gR.[src.genericsmr.Replica, go!"PeerReaders"] ↦□ rS ∗ rS ↦* List.replicate 3 null ∗
    _gR.[src.genericsmr.Replica, go!"PeerWriters"] ↦□ wS ∗ wS ↦* List.replicate 3 null ∗
    _gR.[src.genericsmr.Replica, go!"Alive"] ↦□ aS ∗ aS ↦* List.replicate 3 false ∗
    _gR.[src.genericsmr.Replica, go!"Listener"] ↦ interface.nil ∗
    ([∗list] q ∈ peers _k, rxCurTok _γ.proto q _k 0) ∗ rxCurTok _γ.proto _k _k 0 ∗
    predIdIs _γ.proto _k ws ∗
    ghostVar _ρ.boot (1 : Qp).half true ∗ bootRest _γ _ρ _k _r ∗ clientsOwn _γ _ρ _k _gR)

/-- **Unit N's slot.** The listener `WaitForClientConnections` accepts on (set by
`waitForPeerConnections`, handed over through `done`). Port: `Net/`'s listener (`isListener`,
`netLisOn`, its state `netLis`, owned) at the wildcard `lisAddrOf a0` with `a0`'s protocols. -/
@[irreducible] def listenerOwn (_γ : GryffNames GF) (_ρ : Repl2Names) (_k : Fin 3) (_gR : Loc) :
    IProp GF :=
  iprop(∃ (li : GoInterface) (l : w64) (a0 : GoString) (o : Bool),
    _gR.[src.genericsmr.Replica, go!"Listener"] ↦□ li ∗ net.isListener li l ∗
    netLisOn (extLocalGS netExt (L := hG.goose_localGS)) l (lisAddrOf a0) ∗
    netLis (extLocalGS netExt (L := hG.goose_localGS)) l (lisAddrOf a0) o ∗
    lisProto (lisAddrOf a0) (gryffWireP _γ a0) (gryffWireQ _γ a0) ∗
    ⌜a0 ∈ replicaAddrs⌝ ∗ portId _γ a0 (rid32 _k) ∗ □ protoInvs _γ)

/-- **Unit N's slot.** A generic replica as `NewReplicaDurable` builds it (id `id`, addresses
`nodes`; nothing registered beyond `GEN_PING`, `monitorPings` running), with the rpc
registrations `regs` made so far (code, object, channel: N-2, the listener's `Obj.New()` /
`Unmarshal` decode the registered object's type) and the client registrations `cregs`. -/
@[irreducible] def genericBuilt (_gR : Loc) (_id : w64) (_nodes : List GoString)
    (_regs : List (w8 × GoInterface × Loc)) (_cregs : List (w8 × Loc)) : IProp GF :=
  netN.genericBuiltB _gR _id _nodes _regs _cregs


/-- **`SendMsg(q, code, m)`** (every send to a peer, under the lock: `send*To`, `reply*Replica`,
`replyPreAccept`, `bcast*`, ...): the next owed message to `q` goes on `q`'s writer. -/
theorem Replica.SendMsg.wp (γ : GryffNames GF) (ρ : Repl2Names) (k q : Fin 3) (r gR h : Loc)
    (t : List Ev) (m : Msg) (p : Loc) (code : w8) (outs : List Out) (hq : q ≠ k) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.genericsmr ∗ genericOk γ ρ k r gR h ∗
        r.[src.gryff.Replica, go!"Replica"] ↦□ gR ∗ rpcCodeIs (msgKind m) code ∗ msgAt p m ∗
        pendingOuts γ ρ k r t (.send q m :: outs) }}
      (App (App (App (genM gR go!"SendMsg") (Val #(rid32 q))) (Val #code))
        (Val #(interface.mkOk (msgTy m) #p)))
    {{ RET #(); msgAt p m ∗ pendingOuts γ ρ k r t outs }} := by
  exact SendMsg_wp γ ρ k q r gR h t m p code outs hq

/-- `GetClientWriter(cid)` (`Complete*`, `HandleRMW`): the client id's writer. -/
theorem Replica.GetClientWriter.wp (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3)
    (r gR h : Loc) (cid : w32) (w : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.genericsmr ∗ genericOk γ ρ k r gR h ∗
        writerIs ρ cid w }}
      (App (genM gR go!"GetClientWriter") (Val #cid))
    {{ RET #w; True }} := by
  exact GetClientWriter_wp γ ρ k r gR h cid w

/-- `RegisterRPC(obj, ch)` (`gryff.NewReplica`, `NewEPaxosRMWHandler`): the next code, the
registered object recorded (N-2). Fewer than 248 registrations (N-2: the `uint8` code, from 8,
would wrap; `NewReplica` registers 22). -/
theorem Replica.RegisterRPC.wp (gR : Loc) (id : w64) (nodes : List GoString)
    (regs : List (w8 × GoInterface × Loc)) (cregs : List (w8 × Loc)) (obj : GoInterface)
    (ch : Loc) (hlen : regs.length < 248) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.genericsmr ∗ genericBuilt gR id nodes regs cregs }}
      (App (App (genM gR go!"RegisterRPC") (Val #obj)) (Val #ch))
    {{ (code : w8), RET #code; genericBuilt gR id nodes (regs ++ [(code, obj, ch)]) cregs ∗
        ⌜∀ c ∈ regs, c.1 ≠ code⌝ }} := by
  unfold genericBuilt; exact netN.RegisterRPC_wp gR id nodes regs cregs obj ch hlen

/-- `RegisterClientRPC(obj, opCode, ch)` (`gryff.NewReplica`). -/
theorem Replica.RegisterClientRPC.wp (gR : Loc) (id : w64) (nodes : List GoString)
    (regs : List (w8 × GoInterface × Loc)) (cregs : List (w8 × Loc)) (obj : GoInterface) (op : w8)
    (ch : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.genericsmr ∗ genericBuilt gR id nodes regs cregs }}
      (App (App (App (genM gR go!"RegisterClientRPC") (Val #obj)) (Val #op)) (Val #ch))
    {{ RET #(); genericBuilt gR id nodes regs (cregs ++ [(op, ch)]) }} := by
  unfold genericBuilt; exact netN.RegisterClientRPC_wp gR id nodes regs cregs obj op ch

/-- **`replicaListener(rid, reader)`** (peer `q`'s messages to `k`): each message read gets its
receive token (`peerStream_recv`, `recv_msg`) and goes, with it, on its kind's channel
(`msgChanP`). Never returns normally but on a read error. -/
theorem Replica.replicaListener.wp (γ : GryffNames GF) (ρ : Repl2Names) (k q : Fin 3)
    (r gR rd : Loc) (ms : List Msg) (hq : q ≠ k) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.genericsmr ∗ isReplica γ ρ k r ∗
        r.[src.gryff.Replica, go!"Replica"] ↦□ gR ∗ peerReaderAt γ q k rd ms ∗
        rxCurTok γ.proto q k ms.length }}
      (App (App (genM gR go!"replicaListener") (Val #(W64 q.val))) (Val #rd))
    {{ RET #(); True }} := by
  unfold peerReaderAt; exact replicaListener_wp γ ρ k q r gR rd ms hq

/-! ## The handlers (`gryff`; the model transcribes each)

Internal to `gryff` (their callers are `Loop`, in the same package); stated here because each is
a model step's refinement, the unit of the H proofs. -/

/-- **A handler's spec**: under the lock, from the heap at `s` and the obligations of the step
`stepR k s e = .ok (s', outs)` (at trace `t`, already extended by `e`), with `Pre` (the event's
Go value), the code ends with the heap at `s'` and nothing owed. -/
def stepSpec (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r : Loc) (call : Expr)
    (Pre : IProp GF) (e : Ev) : Prop :=
  ∀ (t : List Ev) (s s' : RState) (outs : List Out), model.stepR k s e = .ok (s', outs) →
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗ isReplica γ ρ k r ∗
        replicaOwn ρ k r s ∗ pendingOuts γ ρ k r t outs ∗ Pre }}
      call
    {{ RET #(); replicaOwn ρ k r s' ∗ pendingOuts γ ρ k r t [] }}


/-- A message handler `recv.f(p)` on message `m` at `p` (the run loop's `X := XS.(*T)`). -/
def msgHandlerSpec (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r : Loc) (fn : Expr)
    (m : Msg) : Prop :=
  ∀ p : Loc, stepSpec γ ρ k r (App fn (Val #p)) (msgAt p m) (.msg m)

/-- The EPaxos handler `h` of `r`. -/
def handlerOf (r h : Loc) : IProp GF :=
  iprop(r.[src.gryff.Replica, go!"rmwHandler"] ↦□ handlerIface h)

/-! ### The fixed fields the EPaxos handlers read (H2-R3, H3-R2: laws of unit N's `genericOk`) -/

/-- The generic replica's and the handler's fixed fields the EPaxos handlers read (replica id
`k`; all persistent): `Thrifty` false, `Exec` true (`Alive`: the lock's `aliveAt`, N1-3),
`PreferredPeerOrder`
`[(k+1)%3, (k+2)%3, k]` (N-9), `PeerAddrList` (3 addresses, for `dlog.Printf`'s arguments), `Stats`
(`statsOk`), the broadcast optimization off, and the rpc codes of the kinds they send (H2-R3,
unit H2's statement). -/
def h2Fixed (k : Fin 3) (gR h : Loc) : IProp GF :=
  iprop(∃ (pS alS : GoSlice) (addrs : List GoString) (st : Loc)
      (cPA cA cC cCS cPAR cPAO cAR cEx : w8),
    gR.[src.genericsmr.Replica, go!"Thrifty"] ↦□ false ∗
    gR.[src.genericsmr.Replica, go!"Exec"] ↦□ true ∗ -- `Alive`: N1-3 (`aliveAt`)
    gR.[src.genericsmr.Replica, go!"PreferredPeerOrder"] ↦□ pS ∗
      pS ↦*□ [W32 (((k.val : Int) + 1) % 3), W32 (((k.val : Int) + 2) % 3), rid32 k] ∗ -- N-9
    gR.[src.genericsmr.Replica, go!"PeerAddrList"] ↦□ alS ∗ alS ↦*□ addrs ∗
      ⌜addrs.length = 3⌝ ∗
    gR.[src.genericsmr.Replica, go!"Stats"] ↦□ st ∗ statsOk st ∗
    h.[src.gryff.EPaxosRMWHandler, go!"broadcastOptimizationEnabled"] ↦□ false ∗
    h.[src.gryff.EPaxosRMWHandler, go!"preAcceptRPC"] ↦□ cPA ∗ rpcCodeIs "preAccept" cPA ∗
    h.[src.gryff.EPaxosRMWHandler, go!"acceptRPC"] ↦□ cA ∗ rpcCodeIs "accept" cA ∗
    h.[src.gryff.EPaxosRMWHandler, go!"commitRPC"] ↦□ cC ∗ rpcCodeIs "commit" cC ∗
    h.[src.gryff.EPaxosRMWHandler, go!"commitShortRPC"] ↦□ cCS ∗
    h.[src.gryff.EPaxosRMWHandler, go!"preAcceptReplyRPC"] ↦□ cPAR ∗
      rpcCodeIs "preAcceptReply" cPAR ∗
    h.[src.gryff.EPaxosRMWHandler, go!"preAcceptOKRPC"] ↦□ cPAO ∗ rpcCodeIs "preAcceptOK" cPAO ∗
    h.[src.gryff.EPaxosRMWHandler, go!"acceptReplyRPC"] ↦□ cAR ∗ rpcCodeIs "acceptReply" cAR ∗
    h.[src.gryff.EPaxosRMWHandler, go!"executedRPC"] ↦□ cEx ∗ rpcCodeIs "executed" cEx ∗
    gR.[src.genericsmr.Replica, go!"Dreply"] ↦□ true) -- H2c-R3

/-- The rpc codes of `Prepare` / `PrepareReply` (H3-R2, unit H3's statement). -/
def prepCodes (h : Loc) : IProp GF :=
  iprop(∃ c c' : w8, h.[src.gryff.EPaxosRMWHandler, go!"prepareRPC"] ↦□ c ∗
    rpcCodeIs "prepare" c ∗
    h.[src.gryff.EPaxosRMWHandler, go!"prepareReplyRPC"] ↦□ c' ∗ rpcCodeIs "prepareReply" c')

omit binA strconvA in -- a law, no code (H1-R6 / N-1)
/-- **The fixed fields** (H2-R3): a law of `genericOk` (unit N's sealed body). -/
theorem genericOk_h2Fixed (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r gR h : Loc) :
    genericOk γ ρ k r gR h ⊢ □ h2Fixed k gR h := by
  iintro #H
  ihave #Hf := genericOk_fixed γ ρ k r gR h $$ H
  unfold genericFixed
  icases Hf with ⟨%pS, %alS, %addrs, %st, %cPA, %cA, %cC, %cCS, %cPAR, %cPAO, %cAR, %cEx,
    %cP, %cPR, %cR1, %cR2, %cW1, %cW2, %cR1R, %cR2R, %cW1R, %cW2R, #H1, #H2, #H5, #H6,
    #H7, #H8, %H9, #H10, #H11, #H12, #H13, %H14, #H15, %H16, #H17, %H18, #H19, #H20, %H21, #H22,
    %H23, #H24, %H25, #H26, %H27, -⟩
  imodintro
  unfold h2Fixed statsOk rpcCodeIs
  iexists pS, alS, addrs, st, cPA, cA, cC, cCS, cPAR, cPAO, cAR, cEx
  ihave #HDr : gR.[src.genericsmr.Replica, go!"Dreply"] ↦□ true $$ []
  · ihave #Hf2 := genericOk_fixed γ ρ k r gR h $$ H
    unfold genericFixed
    icases Hf2 with ⟨%pS', %alS', %addrs', %st', %cPA', %cA', %cC', %cCS', %cPAR', %cPAO',
      %cAR', %cEx', %cP', %cPR', %cR1', %cR2', %cW1', %cW2', %cR1R', %cR2R', %cW1R', %cW2R',
      -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
      -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #HDr, -⟩
    iexact HDr
  iframe #
  ipureintro
  exact ⟨H9, H14, H16, H18, H21, H23, H25, H27⟩

omit binA strconvA in -- a law, no code (H1-R6 / N-1)
/-- **The prepare codes** (H3-R2): a law of `genericOk` (unit N's sealed body). -/
theorem genericOk_prepCodes (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r gR h : Loc) :
    genericOk γ ρ k r gR h ⊢ □ prepCodes h := by
  iintro #H
  ihave #Hf := genericOk_fixed γ ρ k r gR h $$ H
  unfold genericFixed
  icases Hf with ⟨%pS, %alS, %addrs, %st, %cPA, %cA, %cC, %cCS, %cPAR, %cPAO, %cAR, %cEx,
    %cP, %cPR, %cR1, %cR2, %cW1, %cW2, %cR1R, %cR2R, %cW1R, %cW2R,
    -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    #HP, %HPc, #HPR, %HPRc, -⟩
  imodintro
  unfold prepCodes rpcCodeIs
  iexists cP, cPR
  iframe #
  ipureintro; exact ⟨HPc, HPRc⟩

/-- The fixed fields the coordinator's callbacks read (H1-R7, unit H1's statement; all
persistent): `Stats` (`GetStats`), the rpc codes of the proxied kinds in the `gryff.Replica`'s
code fields (`send*To`, `reply*Replica`: `r.read1RPC`, ...). The self sends' channels are
`replicaChans`' bags (`isReplica_open`), their elements' tokens `pendingOuts_self`'s. -/
def h1Fixed (r gR : Loc) : IProp GF :=
  iprop(∃ (st : Loc) (cR1 cR2 cW1 cW2 cR1R cR2R cW1R cW2R : w8),
    gR.[src.genericsmr.Replica, go!"Stats"] ↦□ st ∗ statsOk st ∗
    r.[src.gryff.Replica, go!"read1RPC"] ↦□ cR1 ∗ rpcCodeIs "read1" cR1 ∗
    r.[src.gryff.Replica, go!"read2RPC"] ↦□ cR2 ∗ rpcCodeIs "read2" cR2 ∗
    r.[src.gryff.Replica, go!"write1RPC"] ↦□ cW1 ∗ rpcCodeIs "write1" cW1 ∗
    r.[src.gryff.Replica, go!"write2RPC"] ↦□ cW2 ∗ rpcCodeIs "write2" cW2 ∗
    r.[src.gryff.Replica, go!"read1ReplyRPC"] ↦□ cR1R ∗ rpcCodeIs "read1Reply" cR1R ∗
    r.[src.gryff.Replica, go!"read2ReplyRPC"] ↦□ cR2R ∗ rpcCodeIs "read2Reply" cR2R ∗
    r.[src.gryff.Replica, go!"write1ReplyRPC"] ↦□ cW1R ∗ rpcCodeIs "write1Reply" cW1R ∗
    r.[src.gryff.Replica, go!"write2ReplyRPC"] ↦□ cW2R ∗ rpcCodeIs "write2Reply" cW2R)

omit binA strconvA in -- a law, no code (H1-R6 / N-1)
/-- **The coordinator callbacks' fixed fields** (H1-R7): a law of `genericOk` (unit N's sealed
body). -/
theorem genericOk_h1Fixed (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r gR h : Loc) :
    genericOk γ ρ k r gR h ⊢ □ h1Fixed r gR := by
  iintro #H
  ihave #Hf := genericOk_fixed γ ρ k r gR h $$ H
  unfold genericFixed
  icases Hf with ⟨%pS, %alS, %addrs, %st, %cPA, %cA, %cC, %cCS, %cPAR, %cPAO, %cAR, %cEx,
    %cP, %cPR, %cR1, %cR2, %cW1, %cW2, %cR1R, %cR2R, %cW1R, %cW2R,
    -, -, -, -, -, -, -, #Hst, #Hsto, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -,
    #A1, %a1, #A2, %a2, #A3, %a3, #A4, %a4, #A5, %a5, #A6, %a6, #A7, %a7, #A8, %a8, -⟩
  imodintro
  unfold h1Fixed statsOk rpcCodeIs
  iexists st, cR1, cR2, cW1, cW2, cR1R, cR2R, cW1R, cW2R
  iframe #
  ipureintro
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩

/-- **`r.CompleteRead(rid, cid, true, v)`** (H1-R7; the coordinator's callback, through
`icoordOk`): the owed reply to read `rid` of client `cid` (`ok` 1, value `v`; the model drops the
reply's `MaxSeenTag`, `r.maxSeenTag`, never written after `NewReplica`) goes on the client's
writer `w` (`GetClientWriter(cid)`, `writerIs`; unit N's `clientsOwn` holds it, with
`clientReplyOk`). Unit N's (as `completeRMWWriter.wp`). -/
theorem Replica.CompleteRead.wp (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r gR h : Loc)
    (t : List Ev) (cid rid : w32) (w : Loc) (v : w64) (outs : List Out) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗ genericOk γ ρ k r gR h ∗
        r.[src.gryff.Replica, go!"Replica"] ↦□ gR ∗ writerIs ρ cid w ∗
        pendingOuts γ ρ k r t (.ext (.readReply cid rid v (W8 1)) :: outs) }}
      (App (App (App (App (repM r go!"CompleteRead") (Val #rid)) (Val #cid)) (Val #true))
        (Val #v))
    {{ RET #(); pendingOuts γ ρ k r t outs }} := by
  exact CompleteRead_wp γ ρ k r gR h t cid rid w v outs

/-- **`r.CompleteWrite(rid, cid, true)`** (H1-R7): the owed reply to write `rid` of client `cid`
(`ok` 1) goes on the client's writer `w`. Unit N's. -/
theorem Replica.CompleteWrite.wp (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r gR h : Loc)
    (t : List Ev) (cid rid : w32) (w : Loc) (outs : List Out) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗ genericOk γ ρ k r gR h ∗
        r.[src.gryff.Replica, go!"Replica"] ↦□ gR ∗ writerIs ρ cid w ∗
        pendingOuts γ ρ k r t (.ext (.writeReply cid rid (W8 1)) :: outs) }}
      (App (App (App (repM r go!"CompleteWrite") (Val #rid)) (Val #cid)) (Val #true))
    {{ RET #(); pendingOuts γ ρ k r t outs }} := by
  exact CompleteWrite_wp γ ρ k r gR h t cid rid w outs

/-- **`r.completeRMWWriter(rid, w, v)`** (H2-R4; `incrementNumReplicasExecuted`, in
`handleExecuted` / `executeOverwrite`): the owed reply to RMW `rid` of client `cid` (`ok` 1; the
model drops `OldValue` and `ReplicaId`) goes on the client's writer `w` (`writerIs`: unit N's
`clientsOwn` holds it, with `clientReplyOk`). Unit N's. -/
theorem completeRMWWriter.wp (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r gR h : Loc)
    (t : List Ev) (cid rid : w32) (w : Loc) (v : w64) (outs : List Out) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗ genericOk γ ρ k r gR h ∗
        r.[src.gryff.Replica, go!"Replica"] ↦□ gR ∗ writerIs ρ cid w ∗
        pendingOuts γ ρ k r t (.ext (.rmwReply cid rid (W8 1)) :: outs) }}
      (App (App (App (repM r go!"completeRMWWriter") (Val #rid)) (Val #w)) (Val #v))
    {{ RET #(); pendingOuts γ ρ k r t outs }} := by
  exact completeRMWWriter_wp γ ρ k r gR h t cid rid w v outs

-- `handleRead.wp`, `handleWrite.wp`, `handleForceWrite.wp` and the eight proxied/reply handlers'
-- `*.wp`: in `Replica2/Link.lean` (C-H1; proved by unit H1's `*.wp_proof`).

/-- An EPaxos message handler `h.f(p)` (`h` the replica's handler). -/
def epHandlerSpec (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r h : Loc) (f : GoString)
    (m : Msg) : Prop :=
  ∀ p : Loc, stepSpec γ ρ k r (App (epM h f) (Val #p)) iprop(handlerOf r h ∗ msgAt p m) (.msg m)

-- `handlePreAcceptReply.wp`, `handlePreAcceptOK.wp`, `handleExecuted.wp`, `executeOverwrite.wp`:
-- in `Replica2/Link.lean` (unit H2c2's proofs; C-H2c2, C-H2c2b).

/-! ## The trace prophecy's resolutions (`proph.go`, internal to `gryff`)

Each `resolveX` resolves its event's words, `evCodec.enc e`, one `ResolveU64` at a time
(`replicaProph_resolve`); the word order is the model's projection's (`Model/Codec.lean`). -/

/-- A resolution's spec: `call` resolves the words of `e` (`Pre`: read access to the Go value). -/
def resolveSpec (γ : GryffNames GF) (k : Fin 3) (r : Loc) (call : Expr) (Pre : IProp GF)
    (e : Ev) : Prop :=
  ∀ (p : ProphId) (t : List Ev) (ws : List w64),
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗
        r.[src.gryff.Replica, go!"proph"] ↦□ p ∗ replicaProph γ.proto k p t ws ∗ Pre }}
      call
    {{ RET #(); replicaProph γ.proto k p t (ws ++ model.evCodec.enc e) ∗ Pre }}

theorem resolveRead1.wp (γ : GryffNames GF) (k : Fin 3) (r p : Loc) (m : model.Read1ProxiedM) :
    resolveSpec γ k r (App (repM r go!"resolveRead1") (Val #p)) (msgAt p (.read1 m)) (.msg (.read1 m)) := by
  exact unitB.resolveRead1_proof γ k r p _
theorem resolveRead2.wp (γ : GryffNames GF) (k : Fin 3) (r p : Loc) (m : model.Read2ProxiedM) :
    resolveSpec γ k r (App (repM r go!"resolveRead2") (Val #p)) (msgAt p (.read2 m)) (.msg (.read2 m)) := by
  exact unitB.resolveRead2_proof γ k r p _
theorem resolveRead1Reply.wp (γ : GryffNames GF) (k : Fin 3) (r p : Loc) (m : model.Read1ReplyM) :
    resolveSpec γ k r (App (repM r go!"resolveRead1Reply") (Val #p)) (msgAt p (.read1Reply m)) (.msg (.read1Reply m)) := by
  exact unitB.resolveRead1Reply_proof γ k r p _
theorem resolveRead2Reply.wp (γ : GryffNames GF) (k : Fin 3) (r p : Loc) (m : model.Read2ReplyM) :
    resolveSpec γ k r (App (repM r go!"resolveRead2Reply") (Val #p)) (msgAt p (.read2Reply m)) (.msg (.read2Reply m)) := by
  exact unitB.resolveRead2Reply_proof γ k r p _
theorem resolveWrite1.wp (γ : GryffNames GF) (k : Fin 3) (r p : Loc) (m : model.Write1ProxiedM) :
    resolveSpec γ k r (App (repM r go!"resolveWrite1") (Val #p)) (msgAt p (.write1 m)) (.msg (.write1 m)) := by
  exact unitB.resolveWrite1_proof γ k r p _
theorem resolveWrite2.wp (γ : GryffNames GF) (k : Fin 3) (r p : Loc) (m : model.Write2ProxiedM) :
    resolveSpec γ k r (App (repM r go!"resolveWrite2") (Val #p)) (msgAt p (.write2 m)) (.msg (.write2 m)) := by
  exact unitB.resolveWrite2_proof γ k r p _
theorem resolveWrite1Reply.wp (γ : GryffNames GF) (k : Fin 3) (r p : Loc) (m : model.Write1ReplyM) :
    resolveSpec γ k r (App (repM r go!"resolveWrite1Reply") (Val #p)) (msgAt p (.write1Reply m)) (.msg (.write1Reply m)) := by
  exact unitB.resolveWrite1Reply_proof γ k r p _
theorem resolveWrite2Reply.wp (γ : GryffNames GF) (k : Fin 3) (r p : Loc) (m : model.Write2ReplyM) :
    resolveSpec γ k r (App (repM r go!"resolveWrite2Reply") (Val #p)) (msgAt p (.write2Reply m)) (.msg (.write2Reply m)) := by
  exact unitB.resolveWrite2Reply_proof γ k r p _
theorem resolvePreAccept.wp (γ : GryffNames GF) (k : Fin 3) (r p : Loc) (m : model.PreAcceptM) :
    resolveSpec γ k r (App (repM r go!"resolvePreAccept") (Val #p)) (msgAt p (.preAccept m)) (.msg (.preAccept m)) := by
  exact unitB.resolvePreAccept_proof γ k r p _
theorem resolvePreAcceptReply.wp (γ : GryffNames GF) (k : Fin 3) (r p : Loc) (m : model.PreAcceptReplyM) :
    resolveSpec γ k r (App (repM r go!"resolvePreAcceptReply") (Val #p)) (msgAt p (.preAcceptReply m)) (.msg (.preAcceptReply m)) := by
  exact unitB.resolvePreAcceptReply_proof γ k r p _
theorem resolvePreAcceptOK.wp (γ : GryffNames GF) (k : Fin 3) (r p : Loc) (m : model.PreAcceptOKM) :
    resolveSpec γ k r (App (repM r go!"resolvePreAcceptOK") (Val #p)) (msgAt p (.preAcceptOK m)) (.msg (.preAcceptOK m)) := by
  exact unitB.resolvePreAcceptOK_proof γ k r p _
theorem resolveAccept.wp (γ : GryffNames GF) (k : Fin 3) (r p : Loc) (m : model.EAcceptM) :
    resolveSpec γ k r (App (repM r go!"resolveAccept") (Val #p)) (msgAt p (.accept m)) (.msg (.accept m)) := by
  exact unitB.resolveAccept_proof γ k r p _
theorem resolveAcceptReply.wp (γ : GryffNames GF) (k : Fin 3) (r p : Loc) (m : model.AcceptReplyM) :
    resolveSpec γ k r (App (repM r go!"resolveAcceptReply") (Val #p)) (msgAt p (.acceptReply m)) (.msg (.acceptReply m)) := by
  exact unitB.resolveAcceptReply_proof γ k r p _
theorem resolveCommit.wp (γ : GryffNames GF) (k : Fin 3) (r p : Loc) (m : model.ECommitM) :
    resolveSpec γ k r (App (repM r go!"resolveCommit") (Val #p)) (msgAt p (.commit m)) (.msg (.commit m)) := by
  exact unitB.resolveCommit_proof γ k r p _
theorem resolvePrepare.wp (γ : GryffNames GF) (k : Fin 3) (r p : Loc) (m : model.PrepareM) :
    resolveSpec γ k r (App (repM r go!"resolvePrepare") (Val #p)) (msgAt p (.prepare m)) (.msg (.prepare m)) := by
  exact unitB.resolvePrepare_proof γ k r p _
theorem resolvePrepareReply.wp (γ : GryffNames GF) (k : Fin 3) (r p : Loc) (m : model.PrepareReplyM) :
    resolveSpec γ k r (App (repM r go!"resolvePrepareReply") (Val #p)) (msgAt p (.prepareReply m)) (.msg (.prepareReply m)) := by
  exact unitB.resolvePrepareReply_proof γ k r p _
theorem resolveExecuted.wp (γ : GryffNames GF) (k : Fin 3) (r p : Loc) (m : model.ExecutedM) :
    resolveSpec γ k r (App (repM r go!"resolveExecuted") (Val #p)) (msgAt p (.executed m)) (.msg (.executed m)) := by
  exact unitB.resolveExecuted_proof γ k r p _
theorem resolveExecuteOverwrite.wp (γ : GryffNames GF) (k : Fin 3) (r p : Loc) (m : model.ExecuteOverwriteM) :
    resolveSpec γ k r (App (repM r go!"resolveExecuteOverwrite") (Val #p)) (msgAt p (.executeOverwrite m)) (.msg (.executeOverwrite m)) := by
  exact unitB.resolveExecuteOverwrite_proof γ k r p _
theorem resolveRead.wp (γ : GryffNames GF) (k : Fin 3) (r p : Loc) (g : src.gryffproto.Read) :
    resolveSpec γ k r (App (repM r go!"resolveRead") (Val #p)) iprop(p ↦ g) (readEvOf g) := by
  exact unitB.resolveRead_proof γ k r p _
theorem resolveWrite.wp (γ : GryffNames GF) (k : Fin 3) (r p : Loc) (g : src.gryffproto.Write) :
    resolveSpec γ k r (App (repM r go!"resolveWrite") (Val #p)) iprop(p ↦ g) (writeEvOf g) := by
  exact unitB.resolveWrite_proof γ k r p _
theorem resolveRMW.wp (γ : GryffNames GF) (k : Fin 3) (r p : Loc) (g : src.gryffproto.RMW) :
    resolveSpec γ k r (App (repM r go!"resolveRMW") (Val #p)) iprop(p ↦ g) (rmwEvOf g) := by
  exact unitB.resolveRMW_proof γ k r p _
theorem resolveForceWrite.wp (γ : GryffNames GF) (k : Fin 3) (r : Loc) :
    resolveSpec γ k r (App (repM r go!"resolveForceWrite") (Val #())) iprop(True) .forceWrite := by
  exact unitB.resolveForceWrite_proof γ k r
theorem resolveRecover.wp (γ : GryffNames GF) (k : Fin 3) (r : Loc) (q i : w32) :
    resolveSpec γ k r (App (App (repM r go!"resolveRecover") (Val #q)) (Val #i)) iprop(True)
      (.recover q i) := by
  exact unitB.resolveRecover_proof γ k r q i
theorem resolveExec.wp (γ : GryffNames GF) (k : Fin 3) (r : Loc) (q i : w32) :
    resolveSpec γ k r (App (App (repM r go!"resolveExec") (Val #q)) (Val #i)) iprop(True)
      (.exec q i) := by
  exact unitB.resolveExec_proof γ k r q i

/-! ## The run loop -/

omit binA strconvA in -- a law, no code (H1-R6 / N-1)
/-- **The critical section's step** (each case of `Loop` with an event, after its resolution;
`strongconnect`'s execution): the step's result, a pure conjunct of the precondition, from the
per-kind laws (`step_ok_msg`; `step_ok_req` with `reqChanP`'s `Ev.Producible`; `step_ok_recover`
with `recoverChanP` and `epaxosOwn_crtLb_le`; `step_ok_exec` with the popped component;
`stepR_forceWrite`), `replica_step` moves the invariant, `pendingOuts_step` turns its results into
the obligations. The trace's model state is the step's. -/
theorem critical_step (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r : Loc) (p : ProphId)
    (t : List Ev) (e : Ev) (s' : RState) (outs : List Out) :
    ⌜model.stepR k (pure.stOf k t) e = .ok (s', outs)⌝ ∗
        gryffInv2 γ.proto ∗ predsSet γ.proto ∗ traceHalf γ.proto k t ∗
        replicaProph γ.proto k p t (model.evCodec.enc e) ∗ evTok γ.proto k e ∗ £ 2 ∗
        pendingOuts γ ρ k r t [] ⊢
      |={⊤}=> traceHalf γ.proto k (t ++ [e]) ∗ replicaProph γ.proto k p (t ++ [e]) [] ∗
        pendingOuts γ ρ k r (t ++ [e]) outs ∗ ⌜pure.stOf k (t ++ [e]) = s'⌝ := by
  exact unitB.critical_step_proof γ ρ k r p t e s' outs

/-- `SetForceWrite()` (the force-write ticker goroutine; `forceWriteChan`'s elements carry
nothing). -/
theorem SetForceWrite.wp (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗ isReplica γ ρ k r }}
      (App (repM r go!"SetForceWrite") (Val #()))
    {{ RET #(); True }} := by
  exact unitB.SetForceWrite_proof γ ρ k r

/-! ## The executor

`executeCommands.wp` and `strongconnect.wp` are in `Replica2/Link.lean` (statements unchanged but
H-X-2 (b)), proved by unit X (`GryffProof/X/Final.lean`). -/

end specs

end Perennial.gryff.replica2
