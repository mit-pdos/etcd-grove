/-
Lean-first (no Rocq counterpart).

# A running replica and the cluster (2026-10-29, kvreconf-final)

`Defs.lean` has a replica's replicated state (`repOwn`, `repShared`, `lockInv`) and the persistent
`isReplica` the proved `Replica` methods take. This module adds what the remaining functions need,
in their own predicates so that the proved methods stay as they are.

## A replica (`isReplicaR`, `isRep`)

`isReplicaR … ρ` is `isReplica` together with `context`'s `isClosedchanInit` (`context.WithTimeout`'s premise: `propose`,
`read` and the network's `step` time out) and the replica's fields that `newReplica` sets and
`run`/`ticker`/`stop` read: the tick interval, the three channels, and the storage's registration
(`kvrStorRec`, `KvrStorage.lean`) with its `MemoryStorage`'s invariant at the API's justifications
(`memStorInvP … (kvrJ γ id)`). The names live in a record `ρ : RepNames`, so that the tokens below
can refer to them:

- `stopc` is closed once, by `stop` (Perennial's broadcast idiom, `Q := True`). Its `Pending` token
  is the stopper's;
- `runDone` carries the loop's `nodeRunning n γ N 1` to `stop`, a handoff (cache's `Handoff.lean`).
  The producer's token belongs to `run`, the consumer's to the stopper;
- `tickDone` is the same with `True`, the producer being `ticker`.

`isRep γr vs id r` hides the node, storage, stats and names (persistent). `repStop γr vs r` is
`isReplicaR` together with the stopper's three tokens (exclusive): what `Replica.stop` takes.
`runStart` is what `run` starts with. The replica's own resources are its node's driver, running
token and configuration view, the replicated state at the empty prefix, the producer's token of
`runDone`, and the `MemoryStorage`'s hard state (`memStorMeta`, what `RestartNode`'s boot bundle
returns as its frame `Q`) and stored snapshot (`memSnapExact`, the empty one).

## The applier's storage (`frozenTo`)

`frozenTo γs c D`: every delivered entry above the known compaction point `c` is frozen in the
storage, with the delivered log's terms (`memLog γs (c+1) □ …`). `maybeSnapshot` takes the frozen
entry at the applied index (its term the committed one, `snapshotValid`), and `maybeCompact` the
one at its target. It is indexed by the delivered log `D` (invariant-design review 1, H4), not just
by a range.

## The network (`sendSpec`)

`sendSpec γr id f`: `f` delivers replica `id`'s messages, as `Ready` hands them out (`readyRest`):
the slice of their pointers, each message at `readyDq`, sent by `id`, with its credits.

## The cluster (`isClusterC`, `clusterLockInv`)

`isClusterC γr vs c` (persistent) holds the store's cluster (`kvrCluster`), `γ.dup = true` (the
allocation's choice, so that a duplicated `MsgProp` keeps its credits: `msgCredits_copy`), the
storage registry, the read-only fields (`opts`, `boot`, the `Stats`), and the lock. The lock's
invariant holds the replica map (keys exactly `1 … nextID-1`, so `random` never meets an empty
map, `vs` being non-empty), the next id with its lower-bound authority (`γr.nid`: a sender's id is
below it, so `send`'s `c.replica(from)` is not `nil`), the next operation id with the other half of
the store invariant's `γr.opn`, the read-sequence elements of the ids not started yet (`freshIds`:
a new replica's `lockInv` takes its own), `joinAuth` of the started ids (`startNew` joins a fresh one), each
replica's `isRep`, and, until the stopper takes them (`γr.stp`), every replica's stop tokens.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.KvrStorage
public import Proof.go_etcd_io.raft.v3.InvMemstorage
public import Perennial.Golang.Theory.Chan.Idioms.Broadcast
public import Perennial.Ghost.MonoNat
public import Perennial.Proof.context.Base

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvreconf

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

/-- The store's options struct. -/
abbrev ROptions [GooseExts] := github_com.mit_pdos.etcd_grove.examples.kvreconf.Options

/-- The options a cluster may run with (`RandomOptions`): one to five voters, a positive window
of inflight messages, and a size limit that is not zero for both (raft's `RestartNode` premises). -/
def OptsOk [GooseExts] (o : ROptions) : Prop :=
  1 ≤ uint.Z o.Voters' ∧ uint.Z o.Voters' ≤ 5 ∧
  0 < sint.Z o.MaxInflightMsgs' ∧ sint.Z o.MaxInflightMsgs' ≤ 256 ∧
  (o.MaxCommittedSizePerReady' ≠ W64 0 ∨ o.MaxSizePerMsg' ≠ W64 0)

/-- The bootstrap voters of `k` voters: `1, …, k`. -/
def bootVoters (k : Nat) : List w64 := (List.range k).map (fun i : Nat => W64 ((i : Int) + 1))

/-- The ids from `k` to `9` (`maxReplicas`): those not started yet, whose read-sequence elements the
cluster's lock holds. -/
def freshIds (k : Nat) : List w64 := ((List.range 10).filter (fun i => k ≤ i)).map (fun i : Nat => W64 (i : Int))

/-- The bootstrap configuration's conf state: the voters `vs`. -/
def bootCS [GooseExts] (vs : List w64) : ConfStateM := ConfStateM.mk vs [] [] [] false

/-- A replica's names (see the file header). -/
structure RepNames where
  /-- the embedded `MemoryStorage` -/
  ms : Loc
  /-- its names -/
  γs : MemStorNames
  /-- `stopc` -/
  stopc : Loc
  /-- `stopc`'s channel names (broadcast) -/
  sc : ChanNames
  /-- `runDone` -/
  rdc : Loc
  /-- `runDone`'s handoff names -/
  rd : HandoffNames
  /-- `tickDone` -/
  tdc : Loc
  /-- `tickDone`'s handoff names -/
  td : HandoffNames

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvreconf.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [AllG GF] [KvrStor GF]

attribute [local instance] kvrStorageModel

/-- The applier's frozen delivered entries above the compaction point `c` (see the file header). -/
def frozenTo (γs : MemStorNames) (c : Nat) (D : List LogEntry) : IProp GF :=
  memLog γs (c + 1) DFrac.discard ((LogEntry.toEntries D 0).drop c)

instance frozenTo_persistent (γs : MemStorNames) (c : Nat) (D : List LogEntry) :
    Persistent (frozenTo (GF := GF) γs c D) := by
  unfold frozenTo; infer_instance

/-- **Replica `id` at `r`, running** (persistent; see the file header). -/
def isReplicaR (γr : RNames) (vs : List w64) (id : w64) (r n st sts : Loc) (ρ : RepNames) :
    IProp GF :=
  iprop(
    "#Hrep" ∷ isReplica γr vs id r n st sts ∗
    "#Hcci" ∷ context.isClosedchanInit ∗
    "#Htick" ∷ (∃ tk : time.Duration, r.[RReplica, go!"tick"] ↦□ tk ∗ ⌜0 < sint.Z tk⌝) ∗
    "#Hstopc" ∷ r.[RReplica, go!"stopc"] ↦□ ρ.stopc ∗
    "#Hrdc" ∷ r.[RReplica, go!"runDone"] ↦□ ρ.rdc ∗
    "#Htdc" ∷ r.[RReplica, go!"tickDone"] ↦□ ρ.tdc ∗
    "#HstopB" ∷ ownBroadcastChan ρ.stopc ρ.sc iprop(True) .Unknown ∗
    "#HrdH" ∷ isHandoff (V := Unit) ρ.rd ρ.rdc (fun _ => nodeRunning n γr.cluster kvrRaftN 1)
      iprop(True) iprop(False) ∗
    "#HtdH" ∷ isHandoff (V := Unit) ρ.td ρ.tdc (fun _ => iprop(True)) iprop(True) iprop(False) ∗
    "#HstRec" ∷ kvrStorRec st ρ.ms ρ.γs ∗
    "#HmsInv" ∷ memStorInvP ρ.ms ρ.γs (kvrJ γr.cluster id))

set_option synthInstance.maxHeartbeats 400000 in
set_option synthInstance.maxSize 4096 in
instance isReplicaR_persistent (γr : RNames) (vs : List w64) (id : w64) (r n st sts : Loc)
    (ρ : RepNames) : Persistent (isReplicaR (GF := GF) γr vs id r n st sts ρ) := by
  unfold isReplicaR; infer_instance

/-- Replica `id` at `r`, running, its node and storage hidden (persistent). -/
def isRep (γr : RNames) (vs : List w64) (id : w64) (r : Loc) : IProp GF :=
  iprop(∃ (n st sts : Loc) (ρ : RepNames), isReplicaR γr vs id r n st sts ρ)

instance isRep_persistent (γr : RNames) (vs : List w64) (id : w64) (r : Loc) :
    Persistent (isRep (GF := GF) γr vs id r) := by
  unfold isRep; infer_instance

/-- **The stopper's share of replica `r`** (exclusive; see the file header). -/
def repStop (γr : RNames) (vs : List w64) (r : Loc) : IProp GF :=
  iprop(∃ (id : w64) (n st sts : Loc) (ρ : RepNames),
    isReplicaR γr vs id r n st sts ρ ∗
    ownBroadcastChan ρ.stopc ρ.sc iprop(True) .Pending ∗
    handoffConsumer ρ.rd false ∗ handoffConsumer ρ.td false)

/-- **What `run` starts with** (see the file header). -/
def runStart (γr : RNames) (vs : List w64) (id : w64) (r n st : Loc) (ρ : RepNames) : IProp GF :=
  iprop(∃ (csp mA : Loc) (hs : HardStateM),
    nodeDriver n γr.cluster kvrRaftN (NodeDriverState.init (kvrStorIface st)) ∗
    nodeRunning n γr.cluster kvrRaftN 1 ∗
    nodeConfig n γr.cluster kvrRaftN ⟨0, Membership.simple (GMap.listToSet vs)⟩ ∗
    repOwn γr r [] (W64 0) csp (Membership.simple (GMap.listToSet vs)) mA ∅ ∗
    handoffProducer ρ.rd false ∗
    memStorMeta ρ.ms ρ.γs hs ∗ memSnapExact ρ.γs memSnapEmpty)

/-- **`f` is replica `id`'s transport** (persistent; see the file header). -/
def sendSpec (γr : RNames) (id : w64) (f : GoFunc) : IProp GF :=
  iprop(□ ∀ (msl : GoSlice) (ms : List QMsg),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kvreconf ∗
        ownSlice msl (ms.map QMsg.loc) (DFrac.own 1) ∗
        [∗list] q ∈ ms, msgOwn q.loc (readyDq q.st) q.st ∗ sentMsg γr.cluster kvrRaftN id q.st ∗
          msgCredits γr.cluster kvrRaftN q.st }}
      (App (Val #f) (Val #msl))
    {{ RET #(); True }})

instance sendSpec_persistent (γr : RNames) (id : w64) (f : GoFunc) :
    Persistent (sendSpec (GF := GF) γr id f) := by
  unfold sendSpec; infer_instance

/-- Replica `id` was started: it is below the cluster's next id (persistent). -/
def repKnown (γr : RNames) (id : w64) : IProp GF :=
  iprop(⌜id ≠ W64 0⌝ ∗ monoNatLbOwn γr.nid (uint.nat id + 1))

instance repKnown_persistent (γr : RNames) (id : w64) : Persistent (repKnown (GF := GF) γr id) := by
  unfold repKnown; infer_instance

/-- The stopper's token: the replicas' stop tokens are still in the cluster's lock. -/
def stopper (γr : RNames) : IProp GF := ghostVar γr.stp (1 : Qp).half false

/-- **The cluster's lock invariant** (see the file header). -/
def clusterLockInv (γr : RNames) (vs : List w64) (c : Loc) : IProp GF :=
  iprop(∃ (mR : Loc) (R : GMap w64 Loc) (nid nop : w64) (U : GSet w64) (b : Bool),
    "HmR" ∷ c.[RCluster, go!"replicas"] ↦ mR ∗
    "HR" ∷ mR ↦$ R ∗
    "Hnid" ∷ c.[RCluster, go!"nextID"] ↦ nid ∗
    "Hnop" ∷ c.[RCluster, go!"nextOp"] ↦ nop ∗
    "Hopn" ∷ ghostVar γr.opn (1 : Qp).half nop ∗
    "HnidA" ∷ monoNatAuthOwn γr.nid 1 (uint.nat nid) ∗
    "Hjoin" ∷ joinAuth γr.cluster U ∗
    "%Hdom" ∷ ⌜(∀ i, (R !! i).isSome ↔ 1 ≤ uint.nat i ∧ uint.nat i < uint.nat nid) ∧
      (∀ i, i ∈ U ↔ 1 ≤ uint.nat i ∧ uint.nat i < uint.nat nid) ∧
      vs.length < uint.nat nid ∧ uint.nat nid ≤ 10⌝ ∗
    "Hreps" ∷ ([∗map] id ↦ r ∈ R, isRep γr vs id r) ∗
    "Hrseq" ∷ ([∗list] i ∈ freshIds (uint.nat nid), i ↪[γr.rseq] W64 0) ∗
    "Hstp" ∷ ghostVar γr.stp (1 : Qp).half b ∗
    "Htoks" ∷ (if b then iprop(True) else [∗map] _id ↦ r ∈ R, repStop γr vs r))

/-- **The cluster at `c`** (persistent; see the file header), of the bootstrap voters `vs`. -/
def isClusterC (γr : RNames) (vs : List w64) (c : Loc) : IProp GF :=
  iprop(∃ (o : ROptions) (bp : Loc),
    "#Hpkg" ∷ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kvreconf ∗
    "#Hcl" ∷ kvrCluster γr vs ∗
    "#Hcci" ∷ context.isClosedchanInit ∗
    "%Hdup" ∷ ⌜γr.cluster.dup = true⌝ ∗
    "#HstorInv" ∷ kvrStorInv ∗
    "#Hopts" ∷ c.[RCluster, go!"opts"] ↦□ o ∗
    "%Ho" ∷ ⌜OptsOk o ∧ vs = bootVoters (uint.nat o.Voters')⌝ ∗
    "#Hboot" ∷ c.[RCluster, go!"boot"] ↦□ bp ∗
    "#HbootCS" ∷ ownCSM bp DFrac.discard (bootCS vs) ∗
    "#Hstats" ∷ isStats (c.[RCluster, go!"Stats"]) ∗
    "#Hmu" ∷ sync.isMutex (c.[RCluster, go!"mu"]) (clusterLockInv γr vs c))

set_option synthInstance.maxHeartbeats 400000 in
set_option synthInstance.maxSize 4096 in
instance isClusterC_persistent (γr : RNames) (vs : List w64) (c : Loc) :
    Persistent (isClusterC (GF := GF) γr vs c) := by
  unfold isClusterC; infer_instance

end defs

end kvreconf
end EtcdGrove
end Perennial
