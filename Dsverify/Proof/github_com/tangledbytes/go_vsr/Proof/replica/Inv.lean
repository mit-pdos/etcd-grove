/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Proof/replica/Inv.lean (lab master 915f964;
notes/dsv-vr.md): over any `GF`, on the net extension; the codec class `models_lab.jsoncodec.JsonCodec`,
`codecSet`/`kitCodecOk` of `Spec/jsonlib.lean`, the logger `Dsverify/Spec/log/slog/Logger.lean`'s. Definitions the lab's.
-/
/-
The replica's representation (the body of the sealed `replica.isReplica`): the Go state of a
`*Replica` (its fields, the client table, the pending PrepareOK / StartViewChange /
DoViewChange maps, the timers, the submission queue, the log slice) related to replica `r`'s
model state (`repOwn γ r (repOf v log)`) and the local invariant: the persistent facts the
replica holds (its commit number's `committedBy`, its executed prefix's `linPrefix` and
`committedBy`, its store `storeOf` of the executed prefix, valid PrepareOKs counted in the
current view, valid DoViewChanges collected, valid replies recorded) and the pure relations the
handlers need (the client table covers the executed prefix, and the log when the replica is the
normal primary: the dedup premise of `stepAppend`).

Pure helpers are in `VsrReplica` (namespace); the Iris predicates are `replica.*` in the Go
package's namespace.
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.network
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.time
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.vsrkv
public import Dsverify.Spec.log.slog.Logger
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.pkg.replica.Base

@[expose] public section

noncomputable section


namespace Perennial.github_com.tangledbytes.go_vsr.pkg

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net VsrModel

attribute [local instance] GooseGlobalGS.gooseInvGS

/-! ## Pure: the Go status, the model state of the Go fields, the client table's coverage -/

/-- The model's status of a Go `ReplicaStatus` (`0` normal, `1` view change, `3` state
transfer; `2`, recovery, is never used: the invariant rules it out). -/
def replica.statusOf (s : w64) : Status :=
  if s = W64 0 then .normal else if s = W64 1 then .viewChange else .stateTransfer

/-- A status value the replica uses. -/
def replica.StatusOk (s : w64) : Prop := s = W64 0 ∨ s = W64 1 ∨ s = W64 3

/-- The model state of the replica `v` whose log holds `log`. -/
def replica.repOf [GooseExts] (v : replica.Replica) (log : List Entry) : Rep :=
  ⟨uint.nat v.state'.ViewNumber', replica.statusOf v.state'.Status', log,
    uint.nat v.internal'.lastStableViewNumber'⟩

/-- The client table `tbl` covers the entries `l`: each entry's client has a recorded request
number at least the entry's. -/
def replica.Covers [GooseExts] (tbl : GMap w64 replica.ClientTableData) (l : List Entry) : Prop :=
  ∀ e ∈ l, ∃ d, tbl !! (W64 e.cid) = some d ∧ e.req ≤ uint.nat d.RequestNumber'

/-- The replica is the normal primary of its view (among `n` replicas). -/
def replica.IsNormalPrimary [GooseExts] (n : Nat) (v : replica.Replica) (r : Nat) : Prop :=
  replica.statusOf v.state'.Status' = .normal ∧ primary n (uint.nat v.state'.ViewNumber') = r

/-- A pending DoViewChange entry for view `w` is live: `w` is after the replica's view, or it
is the replica's view and the replica is changing to it (only a live entry may be finalized). -/
def replica.Live [GooseExts] (v : replica.Replica) (w : w64) : Prop :=
  uint.nat v.state'.ViewNumber' < uint.nat w ∨
    (v.state'.ViewNumber' = w ∧ replica.statusOf v.state'.Status' = .viewChange)

/-- The upper bound of the views by which the executed prefix is committed: the last normal
view in a view change, the view otherwise. -/
def replica.mineView [GooseExts] (v : replica.Replica) : Nat :=
  if replica.statusOf v.state'.Status' = .viewChange then uint.nat v.internal'.lastStableViewNumber'
  else uint.nat v.state'.ViewNumber'

open Classical

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : replica.Assumptions] [π : NetProtoGS]
variable [encoding.json.DecoderRep GF]

/-! ## The submission queue's elements -/

/-- What an element of the submission queue carries: a received (or internally made) event of a
valid message, from an `addrOk` source, with its `Logs` capacity; an internal PrepareOK (type
`InternalPrepareOK` = 101) of a valid PrepareOK, with its client's address; or a
`ProposeViewChange` (type 100, no data). -/
def replica.sqElem (γ : VsrGhost.Names) (tcp : Loc) (ne : events.NetworkEvent) :
    IProp GF :=
  iprop((∃ m : Msg, events.isEvent ne.Event' m ∗ VsrGhost.fact γ (.msg m) ∗
      network.addrOk tcp ne.Src' ∗ events.evCap ne.Event' m) ∨
    (∃ d : replica.InternalPrepareOKData,
      ne.Event' ↦□ events.Event.mk (W8 101)
        (interface.mkOk replica.InternalPrepareOKData.ty #d) ∗
      VsrGhost.fact γ (.msg (.prepareOK (uint.nat d.pok'.ViewNum') (uint.nat d.pok'.OpNum')
        (uint.nat d.pok'.ReplicaID'))) ∗
      network.addrOk tcp d.clientaddr') ∨
    (ne.Event' ↦□ events.Event.mk (W8 100) interface.nil))

/-! ## The pending maps' entries -/

/-- A pending PrepareOK entry of op `k`: its responses' map, its client address (one `Send` may
be given, or the empty string: no reply), and, when the replica is the normal primary, every
response is a valid PrepareOK of the current view for `k`. -/
def replica.pokOk (γ : VsrGhost.Names) (n : Nat) (tcp : Loc) (v : replica.Replica) (r : Nat) (k : w64)
    (e : replica.PendingPrepareOK) : IProp GF :=
  iprop(∃ rs : GMap w64 Unit, e.Responses' ↦$ rs ∗
    (network.addrOk tcp e.ClientAddr' ∨ ⌜e.ClientAddr'.str' = []⌝) ∗
    if decide (replica.IsNormalPrimary n v r) then
      [∗map] j ↦ _u ∈ rs, VsrGhost.fact γ (.msg (.prepareOK (uint.nat v.state'.ViewNumber')
        (uint.nat k) (uint.nat j)))
    else iprop(True))

/-- A collected DoViewChange for view `w` from replica `rid`: the Go value `x` is a valid
DoViewChange's (its log read-only), with its log's capacity. -/
def replica.dvcOk (γ : VsrGhost.Names) (w rid : w64) (x : events.DoViewChange) :
    IProp GF :=
  iprop(∃ d : Dvc, ⌜d.view = uint.nat w ∧ d.rid = uint.nat rid ∧
      uint.nat x.ViewNum' = d.view ∧ uint.nat x.LastStableViewNum' = d.lnv ∧
      uint.nat x.OpNum' = d.log.length ∧ uint.nat x.CommitNum' = d.commit ∧
      uint.nat x.ReplicaID' = d.rid⌝ ∗
    log.ownLogs x.Logs' DFrac.discard d.log ∗ VsrGhost.fact γ (.msg (.doViewChange d)) ∗
    ownSliceCap log.Log x.Logs' (DFrac.own 1))

/-- A pending DoViewChange entry for view `w`: when live, its responses' map, each a valid
DoViewChange of `w` from the replica its key names. -/
def replica.dvOk (γ : VsrGhost.Names) (v : replica.Replica) (w : w64)
    (e : replica.PendingDoViewChange) : IProp GF :=
  if decide (replica.Live v w) then
    iprop(∃ rsp : GMap w64 events.DoViewChange, e.Responses' ↦$ rsp ∗
      [∗map] rid ↦ x ∈ rsp, replica.dvcOk γ w rid x)
  else iprop(True)

/-- A pending StartViewChange entry: its responses' map. -/
def replica.svOk (e : replica.PendingStartViewChange) : IProp GF :=
  iprop(∃ rs : GMap w64 Unit, e.Responses' ↦$ rs)

/-- A client table entry: a finished one's result is a valid reply (of some view). -/
def replica.tblOk (γ : VsrGhost.Names) (c : w64) (d : replica.ClientTableData) :
    IProp GF :=
  if d.Finished' then
    iprop(∃ w : Nat, VsrGhost.fact γ (.msg (.reply (uint.nat d.RequestNumber') (uint.nat c) w
      d.Result')))
  else iprop(True)

instance replica.tblOk_persistent (γ : VsrGhost.Names) (c : w64) (d : replica.ClientTableData) :
    Persistent (replica.tblOk (GF := GF) γ c d) := by
  unfold replica.tblOk; split <;> infer_instance

/-- The get-state timer: none, or a timer holding `[view, op, target]`, only while the replica
is not changing views and is not its view's primary. -/
def replica.gstOk (n : Nat) (v : replica.Replica) (r : Nat) : IProp GF :=
  iprop(⌜v.internal'.getStateTimer' = null⌝ ∨
    ((∃ a : GoArray w64 3, time.isTimer v.internal'.getStateTimer'
        (interface.mkOk (go.ArrayType 3 go.uint64) #a)) ∗
      ⌜replica.statusOf v.state'.Status' ≠ .viewChange ∧
        primary n (uint.nat v.state'.ViewNumber') ≠ r⌝))

/-! ## The replica -/

/-- The Go value `v` of the `*Replica` is replica `r` of `γ` over `tcp` (everything but the
points-to of the struct itself). -/
def replica.repInv (γ : VsrGhost.Names) (r : Nat) (tcp : Loc) (v : replica.Replica) :
    IProp GF :=
  iprop(∃ (lg mine : List Entry) (cw mw : Nat) (me : GoString)
      (C : models_lab.jsoncodec.JsonCodec GF) (F : List w8 → Bool → w64 × w64) (P : VsrModel.Store → IProp GF)
      (ms : List ipv4port.IPv4Port) (tbl : GMap w64 replica.ClientTableData)
      (pk : GMap w64 replica.PendingPrepareOK) (sv : GMap w64 replica.PendingStartViewChange)
      (dv : GMap w64 replica.PendingDoViewChange) (vst cst : GoInterface) (n : Nat),
    -- what never changes
    "%Hid" ∷ ⌜uint.nat v.state'.ID' = r ∧ r < n⌝ ∗
    "#Hms" ∷ v.state'.ClusterMembers' ↦*□ ms ∗
    "%Hmslen" ∷ ⌜ms.length = n⌝ ∗
    "#Hsize" ∷ VsrGhost.fact γ (.size n) ∗
    "#Haddrs" ∷ ([∗list] m ∈ ms, network.addrOk tcp m) ∗
    "%Hnet" ∷ ⌜v.network' = interface.mkOk (go.GoType.PointerType network.TCP.ty) #tcp⌝ ∗
    "#HisTCP" ∷ network.isTCP tcp γ me ∗
    "Hsender" ∷ network.tcpSender tcp ∗
    "#Hprotos" ∷ network.netProtos γ ∗
    "%Htime" ∷ ⌜time.isTime v.time'⌝ ∗
    "#Hlogger" ∷ log.slog.isLogger v.logger' ∗
    "#Hsrv" ∷ examples.vsrkv.srvOk v.srvhandler' P ∗
    "#Hcodec" ∷ encoding.json.codecSet (GF := GF) ∗
    "#Hkit" ∷ encoding.json.kitCodecOk (jc := C) F ∗
    "#Hsys" ∷ VsrGhost.sysInv γ ∗
    "#HregI" ∷ VsrGhost.regInv γ ∗
    "#Hsq" ∷ queue.isQueue events.NetworkEvent.ty v.internal'.sq' (replica.sqElem γ tcp) ∗
    -- the model state
    "Hrep" ∷ VsrGhost.repOwn γ r (replica.repOf v lg) ∗
    "%Hstatus" ∷ ⌜replica.StatusOk v.state'.Status'⌝ ∗
    "%Hst" ∷ ⌜replica.statusOf v.state'.Status' = .stateTransfer →
      primary n (uint.nat v.state'.ViewNumber') ≠ r⌝ ∗
    -- the log
    "#Hlog" ∷ log.ownLogs v.state'.Logs' DFrac.discard lg ∗
    "Hcap" ∷ ownSliceCap log.Log v.state'.Logs' (DFrac.own 1) ∗
    "%Hopnum" ∷ ⌜uint.nat v.state'.OpNum' = lg.length⌝ ∗
    -- the commit number
    "%Hcommit" ∷ ⌜uint.nat v.state'.CommitNumber' ≤ lg.length ∧
      cw ≤ uint.nat v.state'.ViewNumber'⌝ ∗
    "#Hcfact" ∷ VsrGhost.fact γ (.committedBy cw (lg.take (uint.nat v.state'.CommitNumber'))) ∗
    -- the executed prefix and the store
    "%Hmine" ∷ ⌜mine.length = uint.nat v.internal'.lastExecutedOpNum' ∧ mine <+: lg ∧
      mw ≤ replica.mineView v⌝ ∗
    "#Hmlin" ∷ VsrGhost.fact γ (.linPrefix mine) ∗
    "#Hmcom" ∷ VsrGhost.fact γ (.committedBy mw mine) ∗
    "Hstore" ∷ P (storeOf mine) ∗
    -- the client table
    "Htbl" ∷ v.state'.ClientTable' ↦$ tbl ∗
    "%Htmine" ∷ ⌜replica.Covers tbl mine⌝ ∗
    "%Htlog" ∷ ⌜replica.IsNormalPrimary n v r → replica.Covers tbl lg⌝ ∗
    "#Htres" ∷ ([∗map] c ↦ d ∈ tbl, replica.tblOk γ c d) ∗
    -- the pending maps
    "Hpk" ∷ v.internal'.pendingPOKs' ↦$ pk ∗
    "Hpks" ∷ ([∗map] k ↦ e ∈ pk, replica.pokOk γ n tcp v r k e) ∗
    "Hsv" ∷ v.internal'.pendingStartViewChange' ↦$ sv ∗
    "Hsvs" ∷ ([∗map] _w ↦ e ∈ sv, replica.svOk e) ∗
    "Hdv" ∷ v.internal'.pendingDoViewChange' ↦$ dv ∗
    "Hdvs" ∷ ([∗map] w ↦ e ∈ dv, replica.dvOk γ v w e) ∗
    -- the timers
    "Hvct" ∷ time.isTimer v.internal'.viewChangeTimer' vst ∗
    "Hct" ∷ time.isTimer v.internal'.commitTimer' cst ∗
    "Hgst" ∷ replica.gstOk n v r)

/-- The replica during a round of its event loop (any `running` flag): what the handlers'
specs are stated over. -/
def replica.ownR (rp : Loc) (γ : VsrGhost.Names) (r : Nat) (tcp : Loc) : IProp GF :=
  iprop(∃ v : replica.Replica, rp ↦ v ∗ replica.repInv γ r tcp v)

/-- The body of `replica.isReplica`: between rounds, not running. -/
def replica.own (rp : Loc) (γ : VsrGhost.Names) (r : Nat) (tcp : Loc) : IProp GF :=
  iprop(∃ v : replica.Replica, rp ↦ v ∗ ⌜v.internal'.running' = false⌝ ∗ replica.repInv γ r tcp v)

end defs

end Perennial.github_com.tangledbytes.go_vsr.pkg
