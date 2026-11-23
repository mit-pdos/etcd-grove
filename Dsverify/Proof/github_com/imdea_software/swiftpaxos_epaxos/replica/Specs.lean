/-
The replica package's internal specs (`notes/prove-replica.md`): the goroutines and helpers
that only the package calls (`serveConn`, `clientListener`, `replicaListener`,
`waitForPeerConnections`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.replica.Core
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.replica.SliceElems
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Interface.ReplicaSpec

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net github_com.imdea_software.swiftpaxos_epaxos.kvs model

attribute [local instance] GooseGlobalGS.gooseInvGS

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]
variable [epaxos.Assumptions] [HasExt netExt] [π : NetProtoGS]

/-- The acceptor's end of a new connection `cid` (as the `net.Conn` `conn`) to replica `id`'s
address, as `Accept` returns it. -/
def accEnd (γ : EpNames) (id : Nat) (L : List GoString) (conn : GoInterface) (cid : Nat) :
    IProp GF :=
  iprop(connIf conn cid true ∗ sendTok cid true (repAccP γ (L.getD id [])) [] ∗
    recvTok cid true (repDialP γ (L.getD id [])) [] ∗ connFresh cid true)

/-- What every goroutine of the framework holds: the read-only fields and the lock. -/
def fwRun0 (γ : EpNames) (r : Loc) (id : Nat) (L : List GoString) (p : FwPtrs)
    (Rext : IProp GF) : IProp GF :=
  iprop(fwRO γ r id L p ∗ sync.isMutex (fld r go!"M") (fwLockInv γ id L p Rext))

instance fwRun0_persistent (γ : EpNames) (r : Loc) (id : Nat) (L : List GoString) (p : FwPtrs)
    (Rext : IProp GF) : Persistent (fwRun0 γ r id L p Rext) := by
  unfold fwRun0; infer_instance

/-- The cells and slot of peer `j` while connecting. -/
def pendCells (γ : EpNames) (id : Nat) (L : List GoString) (p : FwPtrs) (j : Nat) :
    IProp GF :=
  iprop(∃ (c : GoInterface) (rd w : Loc) (a : Bool),
    typedPointsto (sliceIndexRef GoInterface (j : Int) p.peers) c (DFrac.own 1) ∗
    typedPointsto (sliceIndexRef Loc (j : Int) p.readers) rd (DFrac.own 1) ∗
    typedPointsto (sliceIndexRef Loc (j : Int) p.writers) w (DFrac.own 1) ∗
    typedPointsto (sliceIndexRef Bool (j : Int) p.alive) a (DFrac.own 1) ∗
    pendSlot γ id L p.ewma j c rd w)

/-- The listener goroutine's part while connecting: the higher peers' cells and slots. -/
def wfOwn (γ : EpNames) (id : Nat) (L : List GoString) (p : FwPtrs) : IProp GF :=
  iprop([∗list] j ∈ List.range L.length, if id < j then pendCells γ id L p j else iprop(True))

/-- `r.clientListener(conn, first)`: a client's connection whose first bytes `first` (in the
slice `fsl`) were read; one `PROPOSE` (the protocol allows no more), its proposal sent on
`ProposeChan`. -/
def replica.Replica.clientListener.spec : Prop :=
  ∀ (γ : EpNames) (r : Loc) (id : Nat) (L : List GoString) (p : FwPtrs) (Rext : IProp GF)
    (conn : GoInterface) (cid : Nat) (c : w64) (i : KvI) (fsl : GoSlice) (first : List w8)
    (t : Loc) (la ra ed eof : GoInterface),
  {{ pkgInit_replica ∗ fwRun0 γ r id L p Rext ∗ connIn conn cid true t la ra ed eof ∗
      sendTok cid true (repAccP γ (L.getD id [])) [] ∗
      recvTok cid true (repDialP γ (L.getD id [])) first ∗ opTok γ cid ∗ clientConn γ cid c i ∗
      ⌜first <+: proposeBytes c i⌝ ∗ fsl ↦* first }}
    (App (App (Val (r @!! go.GoType.PointerType replica.Replica.ty @!! go!"clientListener"))
      (Val #conn)) (Val #fsl))
  {{ RET #(); True }}

/-- `r.replicaListener(j, rd)`: the reader goroutine of peer `j`'s connection. -/
def replica.Replica.replicaListener.spec : Prop :=
  ∀ (γ : EpNames) (r : Loc) (id : Nat) (L : List GoString) (p : FwPtrs) (Rext : IProp GF)
    (j : Nat) (c : GoInterface) (cid : Nat) (side : Bool) (rd : Loc),
  {{ pkgInit_replica ∗ fwRun0 γ r id L p Rext ∗ fwFrozen γ r id p ∗ fwPhase1 γ id ∗
      ⌜j < L.length ∧ j ≠ id⌝ ∗ lisRes γ id L p.ewma j c cid side rd }}
    (App (App (Val (r @!! go.GoType.PointerType replica.Replica.ty @!! go!"replicaListener"))
      (Val #(W64 j))) (Val #rd))
  {{ RET #(); True }}

/-- `r.serveConn(conn, true)` (from `WaitForClientConnections`): a late peer is installed (and
its reader started), anything else is served as a client. -/
def replica.Replica.serveConn.spec : Prop :=
  ∀ (γ : EpNames) (r : Loc) (id : Nat) (L : List GoString) (p : FwPtrs) (Rext : IProp GF)
    (conn : GoInterface) (cid : Nat),
  {{ pkgInit_replica ∗ isReplicaFw γ r id L p Rext ∗ accEnd γ id L conn cid }}
    (App (App (Val (r @!! go.GoType.PointerType replica.Replica.ty @!! go!"serveConn"))
      (Val #conn)) (Val #true))
  {{ RET #(); True }}

/-- `r.serveConn(conn, false)` (from `waitForPeerConnections`, while dialing): a peer is
installed in the listener goroutine's cells (its reader kept for `ConnectToPeers`). -/
def replica.Replica.serveConnDial.spec : Prop :=
  ∀ (γ : EpNames) (r : Loc) (id : Nat) (L : List GoString) (p : FwPtrs) (Rext : IProp GF)
    (conn : GoInterface) (cid : Nat),
  {{ pkgInit_replica ∗ fwRun0 γ r id L p Rext ∗ wfOwn γ id L p ∗ accEnd γ id L conn cid }}
    (App (App (Val (r @!! go.GoType.PointerType replica.Replica.ty @!! go!"serveConn"))
      (Val #conn)) (Val #false))
  {{ RET #(); wfOwn γ id L p }}

end heap

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
