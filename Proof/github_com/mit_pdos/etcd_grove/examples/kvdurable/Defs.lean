/-
Lean-first (no Rocq counterpart).

# The durable store's predicates (2026-11-01, durability stage I, layer 4: statements)

kvdurable is kvreconf (`Proof/github_com/mit_pdos/etcd_grove/examples/kvreconf/Defs.lean`,
`DefsCluster.lean`) with each replica's raft storage kept in a file of the `durable` package and
replicas crashing and restarting from their files. This module states its invariants over raft's
durable node API (`notes/raft-durability-proof-plan.md` §3; candidate 12 §8): kvreconf's store-level
predicates at kvdurable's structs (the model, `kvreconf.Base`'s pure definitions and kvreconf's
`RNames`, is the same), and the durable part.

## The durable part

- **The file of replica `id`** (`kdFileInv`, an invariant per id, `kdRepN .@ id`): the file's
  contents `o` (`dfile`, the files' invariant's entry: none before the replica's first write, or the
  bytes `encStor f` of contents `f`), the replica's durable raft state `S` (`raftState`), the storage
  the file restores holding `S` (`StorageHolds S (kdContents o)`: a lagging commit index allowed), the
  contents' shape (`KdFileOk`: what `openStorage` checks), and the stored snapshot's certificate
  (`kdSnapCert`: valid for raft's storage contract, and the store's encoded state of a committed
  prefix at the snapshot's configuration). Half of a ghost variable at `(S, o)`; the other half,
  `kdWriter`, is the right to move them: the incarnation's `dmu` holds it, also once crashed (its
  `run` enters commit-only batches until it stops), until `crash`'s last critical section, after
  `stop`, takes it out for the restarter.
- **`dmu`'s lock invariant** (`kdDmuInv`, per incarnation): half of `crashed` (the other half, at
  `false`, is the crasher's token in `repStop`); the storage's image (`Storage.img`,
  `ownImage`) holding the contents `M`, the `MemoryStorage`'s hard state `M`'s (`memStorMeta`);
  the writer's half at `(S, o)` (once crashed, either it or, after `crash` took it, `run`'s claim);
  and (also after the crash: the loop and the
  snapshotter go on changing the storage until `stop`) `M`'s shape and snapshot certificate, and the
  pending batch (`KdPhase`): none (`M` holds `S`), a cut batch whose
  *enter* (`readyEnter`) has not fired (`M` holds the batch's durable state: `persist` fires it inside
  `durable.Write`'s atomic update, with its caller's share of `nodeRunning`), or one fired by the
  snapshotter's `persist`, its results (`nodeDriver`, `readyMsgs`) left for `run`. A commit-only batch
  is entered at once (`run`'s `dmu` section): it changes only `S.commit`, which the file may lag.
- **The storage's contents** `M` (a `StorFile`) are the image's (`Image.lean`), which the replica
  changes with each of its storage changes (the `Storage` wrappers: the image's change, then the
  `MemoryStorage`'s) and `encode` writes: the replica never reads the `MemoryStorage` back for its
  file, so `encode` needs no share of the log raft's storage contract owns between `Ready`s, nor
  to know which snapshot `MemoryStorage.Snapshot` returns (API gaps G2/G3 of `stageI-5-clients.md`,
  which an earlier version, reading the `MemoryStorage`, met). The image relates to raft's durable
  state only through the batches (`kdPhaseInv`'s `StorageHolds … (kdContents (some M))`).

## Incarnations

`c.replicas[id]` is the current incarnation; an old one's persistent `isReplica` stays (its node
stopped). `Cluster.restart` crashes the current one (its `nodeVacant` back from `stop`), and starts
the next from the file (`Cluster.start`: `durable.Read`, `openStorage`, `RestartNode` with an update
firing over the file's invariant).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvdurable.KdStorage
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvdurable.Codec
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvdurable.Image
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.DefsCluster
public import Proof.github_com.mit_pdos.etcd_grove.examples.durable.Files

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvdurable

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

/-- The store's structs. -/
abbrev KReplica [GooseExts] := github_com.mit_pdos.etcd_grove.examples.kvdurable.Replica
abbrev KCluster [GooseExts] := github_com.mit_pdos.etcd_grove.examples.kvdurable.Cluster
abbrev KReadSeqs [GooseExts] := github_com.mit_pdos.etcd_grove.examples.kvdurable.readSeqs
abbrev KStats [GooseExts] := github_com.mit_pdos.etcd_grove.examples.kvdurable.Stats
abbrev KSnapReq [GooseExts] := github_com.mit_pdos.etcd_grove.examples.kvdurable.snapReq

abbrev kReplicaTy [GooseExts] [GoGlobalContext] : go.GoType :=
  github_com.mit_pdos.etcd_grove.examples.kvdurable.Replica.ty
abbrev kClusterTy [GooseExts] [GoGlobalContext] : go.GoType :=
  github_com.mit_pdos.etcd_grove.examples.kvdurable.Cluster.ty
abbrev kReadSeqsTy [GooseExts] [GoGlobalContext] : go.GoType :=
  github_com.mit_pdos.etcd_grove.examples.kvdurable.readSeqs.ty

instance KSnapReq.countable [GooseExts] : Pos.Countable KSnapReq :=
  countableOfLeftInverse (fun q : KSnapReq => (q.index', q.cs', q.data', q.compact'))
    (fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩) (fun _ => rfl)

/-- The namespaces: raft's cluster, the store's invariant, the snapshots' registry, the conf
decisions, the files, the replicas' file invariants, the statistics. -/
def kdRaftN : Namespace := nroot.@"kvdurable_raft"
def kdRkvN : Namespace := nroot.@"kvdurable_rkv"
def kdSnapN : Namespace := nroot.@"kvdurable_snaps"
def kdConfN : Namespace := nroot.@"kvdurable_conf"
def kdFilesN : Namespace := nroot.@"kvdurable_files"
def kdRepN : Namespace := nroot.@"kvdurable_rep"
def kdStatsN : Namespace := nroot.@"kvdurable_stats"

/-- What an operation's atomic update may open (kvreconf's `kvrMask`, and the files'). -/
def kdMask : CoPset :=
  (((((⊤ \ ↑kdRaftN) \ ↑kdRkvN) \ ↑kdSnapN) \ ↑kdConfN) \ ↑kdFilesN) \ ↑kdRepN

/-- **The durable store's ghost names**: kvreconf's (raft's cluster, the store's history, the
minted operations and reads, ...), the files' (`durableFilesInv`), and per replica id the file's
writer variable (`kdWriter`). -/
structure KdNames where
  r : kvreconf.RNames
  files : GName
  wr : w64 → GName

/-- **An incarnation's `dmu` names** (2026-11-01, stage II (h)): the pending batch's claim, and the
monotone lower bounds of the image's frozen bound (`fz`: the image's entries up to it are frozen in
the `MemoryStorage`, and it is at most the image's commit index) and of its snapshot's index, which
the snapshot requests (`snapReqOk`) and the snapshotter's `known` cite. -/
structure KdDmuNames where
  /-- the pending batch's claim (`ghostVar` of `Option GName × RaftState`, halves: `dmu`'s and
  `run`'s; the durable state is `dmu`'s once the batch, if any, is entered) -/
  ph : GName
  /-- the image's frozen bound (`monoNat`) -/
  ic : GName
  /-- the image's snapshot index (`monoNat`) -/
  is : GName
  /-- the image's hard state (`ghostVar`, halves: `dmu`'s and `run`'s; only `run`'s `SetHardState`
  moves it, so `run` knows it is its driver's: 2026-11-01, stage II (j), G12) -/
  cm : GName

/-- A replica incarnation's names (`DefsCluster`'s `RepNames`, with the storage's key and the
`dmu` names). -/
structure KdRepNames where
  ms : Loc
  γs : MemStorNames
  stopc : Loc
  sc : ChanNames
  rdc : Loc
  rd : HandoffNames
  tdc : Loc
  td : HandoffNames
  snc : Loc
  sn : ChanNames
  sdc : Loc
  sd : HandoffNames
  /-- the key raft named the storage by at the attach (`RestartNode`'s post) -/
  key : GName
  /-- the `dmu` names (the pending batch's claim, the image's lower bounds) -/
  ph : KdDmuNames

/-! ## The file's contents (pure) -/

section pure
variable [GooseExts]

/-- The empty storage (`NewMemoryStorage`'s, with the replica's zero hard state): no file. -/
def kdEmpty : StorContents :=
  ⟨HardStateM.mk (W64 0) (W64 0) (W64 0), none, entryID.mk (W64 0) (W64 0), []⟩

/-- **What a file restores** (`openStorage`): the contents' hard state, snapshot (none at index
`0`), log base (the index and term of the log's start) and entries; the empty storage if there is
no file. -/
def kdContents : Option StorFile → StorContents
  | none => kdEmpty
  | some f => ⟨f.hs, if f.snap.Metadata'.Index' = W64 0 then none else some f.snap,
      entryID.mk f.prevTerm f.prev, f.ents⟩

/-- **The contents `openStorage` accepts** (its checks): the entries consecutive from the log's
start, the start below `maxIndex` and the entries within it, the snapshot and the commit index
within the log; and the bytes decode back (`StorWf`). -/
def KdFileOk (f : StorFile) : Prop :=
  StorWf f ∧ uint.Z f.prev < 2 ^ 61 ∧ (f.ents.length : Int) ≤ 2 ^ 61 - uint.Z f.prev ∧
  (∀ (i : Nat) (e : EntryM), f.ents[i]? = some e → uint.nat e.Index' = uint.nat f.prev + 1 + i) ∧
  uint.Z f.prev ≤ uint.Z f.snap.Metadata'.Index' ∧
  uint.nat f.snap.Metadata'.Index' ≤ uint.nat f.prev + f.ents.length ∧
  uint.Z f.prev ≤ uint.Z f.hs.Commit' ∧ uint.nat f.hs.Commit' ≤ uint.nat f.prev + f.ents.length

/-- The file's bytes (`durable.Write(file, string(encode()))`). -/
def kdFileVal (o : Option StorFile) : Option GoString := o.map encStor

/-- **The pending batch** of an incarnation's `dmu` (see the file header). -/
inductive KdPhase where
  /-- nothing pending: the storage holds the file's durable state -/
  | idle
  /-- a cut batch, from the driver state `st` to `st'` with messages `ms`, not entered yet; its
  results saved at `γb` (what `run` gets back) -/
  | waiting (st st' : NodeDriverState) (ms : List QMsg) (γb : GName)
  /-- a batch entered by another writer's `persist`, its results (saved at `γb`) left for `run` -/
  | fired (γb : GName)

end pure

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt durableExt]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvdurable.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [AllG GF] [KdStor GF]

attribute [local instance] kdStorageModel

/-! ## The store's model (kvreconf's, at kvdurable's namespaces) -/

/-- The client's half of the store's state `m` (kvreconf's `rkvVal`). -/
def rkvVal (γ : KdNames) (m : kvreconf.KVMap) : IProp GF :=
  iprop(∃ H : List (List w8), ghostVar γ.r.val (1 : Qp).half H ∗ ⌜kvreconf.kvFold H = m⌝)

/-- An operation's atomic update over the store's state. -/
def opAu (γ : KdNames) (f : kvreconf.KVMap → kvreconf.KVMap) (k : List w8)
    (Φ : List w8 → IProp GF) : IProp GF :=
  iprop(AU <{ ∃∃ (x : kvreconf.KVMap), rkvVal γ x }> @ kdMask, ∅
    <{ rkvVal γ (f x), COMM Φ (f x k) }>)

/-- An operation's slot. -/
def opSlot (γ : KdNames) (d : List w8) (γp : GName × GName) (H : List (List w8)) : IProp GF :=
  iprop(∃ Φ : List w8 → IProp GF, savedPredOwn γp.1 DFrac.discard Φ ∗
    ( (⌜d ∉ H⌝ ∗ £ 1 ∗ opAu γ (fun x => kvreconf.kvApply x d) (kvreconf.dkey d) Φ)
    ∨ (∃ H0, ⌜H0 ++ [d] <+: H ∧ d ∉ H0⌝ ∗
        (Φ (kvreconf.kvFold (H0 ++ [d]) (kvreconf.dkey d)) ∨ token γp.2)) ))

/-- The timeless part of the store's invariant. -/
def kvCore (γ : KdNames) (ops : List LogEntry) (n : w64) (Mi : GMap w64 (List w8))
    (RS : GMap w64 w64) (RMi : GMap (w64 × w64) (List w8)) (O : GMap (List w8) (GName × GName))
    (U : GSet (List w8)) : IProp GF :=
  iprop(ownCommittedOps γ.r.cluster ops ∗ ghostVar γ.r.val (1 : Qp).half (kvreconf.logHist ops) ∗
    ownReadCtxs γ.r.cluster U ∗ ghostVar γ.r.opn (1 : Qp).half n ∗
    ghostMapAuth γ.r.mint 1 Mi ∗ ghostMapAuth γ.r.rseq 1 RS ∗ ghostMapAuth γ.r.rmint 1 RMi ∗
    ghostMapAuth γ.r.ops 1 O ∗ ⌜kvreconf.MintOk n Mi RS RMi O U⌝ ∗
    ⌜∀ d, some d ∈ ops.map kvreconf.odOf → kvreconf.MintedOp Mi d⌝ ∗
    ⌜∀ e ∈ ops, e.isConfChange → kvreconf.ConfShaped e⌝)

/-- A read's slot. -/
def readSlot (γ : KdNames) (γΦ : GName) (s : kvreconf.ReadRec) (H : List (List w8)) : IProp GF :=
  iprop(∃ Φ : List w8 → IProp GF, savedPredOwn γΦ DFrac.discard Φ ∗
    ( (⌜∀ H', s.start <+: H' → H' <+: H → s.ans ≠ some (kvreconf.kvFold H' s.key)⌝ ∗ £ 1 ∗
        AU <{ ∃∃ (x : kvreconf.KVMap), rkvVal γ x }> @ kdMask, ∅
          <{ rkvVal γ x, COMM Φ (x s.key) }>)
    ∨ (∃ v, ⌜s.ans = some v⌝ ∗ Φ v) ))

/-- The registry of the reads in flight. -/
def readReg (γ : KdNames) (H : List (List w8)) : IProp GF :=
  iprop(∃ RD : GMap GName kvreconf.ReadRec, ghostMapAuth γ.r.rds 1 RD ∗
    [∗map] γΦ ↦ s ∈ RD, readSlot γ γΦ s H)

def rkvInvBody (γ : KdNames) : IProp GF :=
  iprop(∃ (ops : List LogEntry) (n : w64) (Mi : GMap w64 (List w8)) (RS : GMap w64 w64)
      (RMi : GMap (w64 × w64) (List w8)) (O : GMap (List w8) (GName × GName)) (U : GSet (List w8)),
    kvCore γ ops n Mi RS RMi O U ∗
    ([∗map] d ↦ γp ∈ O, opSlot γ d γp (kvreconf.logHist ops)) ∗ readReg γ (kvreconf.logHist ops))

/-- The store's invariant (kvreconf's `rkvInv`). -/
def rkvInv (γ : KdNames) : IProp GF := inv kdRkvN (rkvInvBody γ)

/-- What a waiter learns with the value `v`. -/
def waitP (γ : KdNames) (d : List w8) (v : List w8) : IProp GF :=
  iprop(∃ (l : List LogEntry), isCommittedLogLb γ.r.cluster l ∗ ⌜kvreconf.AnsOk (kvreconf.logHist l) d v⌝)

/-- A lower bound on the store's history (persistent). -/
def kvLb (γ : KdNames) (L : List (List w8)) : IProp GF :=
  iprop(∃ (l : List LogEntry), isCommittedLogLb γ.r.cluster l ∗ ⌜L = kvreconf.logHist l⌝)

/-- What the applier answers a read of the context `c` with. -/
def readAns (γ : KdNames) (c : List w8) (v : List w8) : IProp GF :=
  iprop(∃ (i : w64) (ap : List LogEntry) (key : List w8),
    readStateOk γ.r.cluster kdRaftN c i ∗ isCommittedLogLb γ.r.cluster ap ∗
    ⌜uint.Z i ≤ (ap.length : Int) ∧ (∃ rp s, kvreconf.decodeReadCtxB c = some (rp, s, key)) ∧
      v = kvreconf.kvFold (kvreconf.logHist ap) key⌝)

/-- A `ReadState` as `Ready` hands it out (persistent). -/
def rsOk (γ : Cluster) (v : ReadState) : IProp GF :=
  iprop(∃ c : List w8, v.RequestCtx' ↦*□ c ∗ readStateOk γ kdRaftN c v.Index')

/-- A read's entry in the replica's lock: the context `c` minted at `(id, s)`. -/
def readWaiterOk (γ : KdNames) (id s : w64) (ch : Loc) : IProp GF :=
  iprop(∃ (c : List w8) (γh : HandoffNames),
    (id, s) ↪[γ.r.rmint]□ c ∗
    isHandoff γh ch (readAns γ c) iprop(True) iprop(False) ∗ handoffProducer γh false)

/-- An operation's entry in the replica's lock. -/
def waiterOk (γ : KdNames) (d : List w8) (ch : Loc) : IProp GF :=
  iprop(∃ (γh : HandoffNames),
    isHandoff γh ch (waitP γ d) iprop(True) iprop(False) ∗ handoffProducer γh false)

/-- The applier's half of an incarnation's replicated state (kvreconf's `repOwn`), at the committed
prefix `ap`: since a restarted incarnation starts at its stored snapshot's prefix, `ap` is any
committed prefix, not the empty one. -/
def repOwn (γ : KdNames) (r : Loc) (ap : List LogEntry)
    (idx : w64) (csp : Loc) (m : Membership) (mA : Loc) (A : GMap (List w8) (List w8)) :
    IProp GF :=
  iprop(∃ (mK : Loc) (K : GMap (List w8) (List w8)) (c : ConfStateM),
    "HmK" ∷ r.[KReplica, go!"kv"] ↦ mK ∗
    "HK" ∷ mK ↦$ K ∗
    "HmA" ∷ r.[KReplica, go!"applied"] ↦{DFrac.own (1 : Qp).half} mA ∗
    "HA" ∷ mA ↦${DFrac.own (1 : Qp).half} A ∗
    "Hcs" ∷ r.[KReplica, go!"cs"] ↦{DFrac.own (1 : Qp).half} csp ∗
    "Hidx" ∷ r.[KReplica, go!"index"] ↦{DFrac.own (1 : Qp).half} idx ∗
    "#Hap" ∷ isCommittedLogLb γ.r.cluster ap ∗
    "%Hlen" ∷ ⌜(ap.length : Int) < 2 ^ 61⌝ ∗
    "%Hval" ∷ ⌜∀ k, (K !! k).getD [] = kvreconf.kvFold (kvreconf.logHist ap) k⌝ ∗
    "%HA" ∷ ⌜kvreconf.AppliedOk A (kvreconf.logHist ap)⌝ ∗
    "#HcsO" ∷ csOpt csp DFrac.discard c ∗
    "%Hcsm" ∷ ⌜confStateIs c m⌝ ∗
    "%Hsz" ∷ ⌜GMap.size m.ids < 2 ^ 61⌝ ∗
    "#Hcfg" ∷ confAt γ.r.cluster ap.length m)

/-- The lock's half of an incarnation's replicated state (kvreconf's `repShared`). -/
def repShared (γ : KdNames) (r : Loc) : IProp GF :=
  iprop(∃ (mA : Loc) (A : GMap (List w8) (List w8)) (csp : Loc) (c : ConfStateM) (idx : w64)
      (ap : List LogEntry),
    "HmA" ∷ r.[KReplica, go!"applied"] ↦{DFrac.own (1 : Qp).half} mA ∗
    "HA" ∷ mA ↦${DFrac.own (1 : Qp).half} A ∗
    "Hcs" ∷ r.[KReplica, go!"cs"] ↦{DFrac.own (1 : Qp).half} csp ∗
    "Hidx" ∷ r.[KReplica, go!"index"] ↦{DFrac.own (1 : Qp).half} idx ∗
    "#HcsO" ∷ csOpt csp DFrac.discard c ∗
    "#Hap" ∷ isCommittedLogLb γ.r.cluster ap ∗
    "%HA" ∷ ⌜kvreconf.AppliedOk A (kvreconf.logHist ap)⌝)

/-- An incarnation's `mu` lock invariant (kvreconf's `lockInv` without `nextRead`: the reads'
sequence numbers are the cluster's, `readSeqs`). -/
def lockInv (γ : KdNames) (id : w64) (r : Loc) : IProp GF :=
  iprop(∃ (mW : Loc) (W : GMap (List w8) Loc) (mR : Loc) (Rd : GMap w64 Loc),
    "Hrep" ∷ repShared γ r ∗
    "HmW" ∷ r.[KReplica, go!"waiters"] ↦ mW ∗
    "HW" ∷ mW ↦$ W ∗
    "Hwaiters" ∷ ([∗map] d ↦ ch ∈ W, waiterOk γ d ch) ∗
    "HmR" ∷ r.[KReplica, go!"reads"] ↦ mR ∗
    "HRd" ∷ mR ↦$ Rd ∗
    "Hreads" ∷ [∗map] s ↦ ch ∈ Rd, readWaiterOk γ id s ch)

/-- The applier's view of its node (kvreconf's `appNode`). -/
def appNode (γ : KdNames) (n : Loc) (l : List LogEntry) (k : Nat) (m : Membership) : IProp GF :=
  iprop(∃ v : ConfigView, nodeConfig n γ.r.cluster kdRaftN v ∗
      deliveredLogLb n γ.r.cluster kdRaftN l ∗ skippedIn γ.r.cluster l v.applied k ∗
      ⌜v.membership = m ∧ v.applied ≤ k⌝)

/-- What a snapshot the store made promises (kvreconf's `kvrSnapRecOk`). -/
def kdSnapRecOk (γ : KdNames) (s : SnapRec) : IProp GF :=
  iprop(∃ L : List LogEntry, isCommittedLogLb γ.r.cluster L ∗ confAt γ.r.cluster L.length s.conf ∗
    ⌜L.length = s.index ∧ kvreconf.kvSnapOk L s.data ∧ GMap.size s.conf.ids < 2 ^ 61⌝)

/-- The store's registry of the snapshots made (an invariant). -/
def kdSnapInv (γ : KdNames) : IProp GF :=
  inv kdSnapN iprop(∃ S : List SnapRec, ownSnapsMade γ.r.cluster S ∗
    [∗list] s ∈ S, kdSnapRecOk γ s)

/-- The statistics' counters (kvreconf's, with kvdurable's seven more). -/
def statsFields : List GoString :=
  [go!"SnapshotsTaken", go!"SnapshotsTakenJoint", go!"SnapshotsSent", go!"SnapshotsInstalled",
   go!"SnapshotsInstalledJoint", go!"SnapshotsInstalledLearners", go!"Compactions",
   go!"ConfChangesProposed", go!"ConfChangesApplied", go!"ConfChangesRejected", go!"JointEntered",
   go!"ReplicasStarted", go!"Dropped", go!"Duplicated", go!"Delayed", go!"Retries",
   go!"Crashes", go!"RestartsFromSnapshot", go!"RestartsAppliedBelow", go!"EntriesSkipped",
   go!"FileWrites", go!"LeaderSentFirst", go!"CommitUnwritten"]

/-- Every counter of the `Stats` at `s`. -/
def isStats (s : Loc) : IProp GF :=
  [∗list] f ∈ statsFields, inv kdStatsN iprop(∃ v : w64,
    sync.atomic.ownUint64 (s.[KStats, f]) (DFrac.own 1) v)

/-- **The store's cluster** (persistent): raft's cluster, its conf entries decided by kvreconf's
rule from the bootstrap voters `vs`, the registry of the snapshots made, the store's invariant, and
the files. -/
def kdCluster (γ : KdNames) (vs : List w64) : IProp GF :=
  iprop(isCluster γ.r.cluster kdRaftN ∗ confPolicy γ.r.cluster kdConfN kvreconf.kvrRule ∗
    confAt γ.r.cluster 0 (Membership.simple (GMap.listToSet vs)) ∗ kdSnapInv γ ∗ rkvInv γ ∗
    durableFilesInv γ.files kdFilesN)

/-! ## The durable part -/

/-- **The stored snapshot's certificate** (persistent): none at index `0`; otherwise valid for raft's
storage contract (`snapshotValid`), and the store's encoded state of a committed prefix of its
index at the membership its conf state reports (what `Cluster.start` installs as the restarted
incarnation's replicated state, and `RestartNode`'s `confAt γ a m`). -/
def kdSnapCert (γ : KdNames) (sv : SnapshotM) : IProp GF :=
  iprop(⌜sv.Metadata'.Index' = W64 0⌝ ∨
    snapshotValid γ.r.cluster sv ∗
    ∃ (L : List LogEntry) (m : Membership), isCommittedLogLb γ.r.cluster L ∗
      confAt γ.r.cluster L.length m ∗
      ⌜L.length = uint.nat sv.Metadata'.Index' ∧ kvreconf.kvSnapOk L sv.Data' ∧
        confStateIs sv.Metadata'.ConfState' m ∧ GMap.size m.ids < 2 ^ 61⌝)

/-- **The right to write replica `id`'s file**, which holds `o`, with its durable state `S`
(exclusive; the other half in `kdFileInv`). -/
def kdWriter (γ : KdNames) (id : w64) (S : RaftState) (o : Option StorFile) : IProp GF :=
  ghostVar (γ.wr id) (1 : Qp).half (S, kdFileVal o)

/-- The decimal digits of `n` (`itoa`). -/
def decimalB (n : Nat) : GoString := (Nat.toDigits 10 n).map (fun c => W8 (c.toNat : Int))

/-- The file of replica `id` (the program's string): `dir + "/replica-" + itoa(id)`. -/
def kdFileName (dir : GoString) (id : w64) : GoString :=
  dir ++ go!"/replica-" ++ decimalB (uint.nat id)

/-- **The file of replica `id`** (an invariant; see the file header). -/
def kdFileInv (γ : KdNames) (dir : GoString) (id : w64) : IProp GF :=
  inv (kdRepN .@ uint.nat id) iprop(∃ (S : RaftState) (o : Option StorFile),
    raftState γ.r.cluster id S ∗
    dfile γ.files (kdFileName dir id) (kdFileVal o) ∗
    ghostVar (γ.wr id) (1 : Qp).half (S, kdFileVal o) ∗
    ⌜StorageHolds S (kdContents o) ∧ ∀ f, o = some f → KdFileOk f⌝ ∗
    (∀ f, ⌜o = some f⌝ -∗ kdSnapCert γ f.snap))

/-- **A batch's results** (`readyEnter`'s post but the durable state and the running token): the
loop's token after the `Ready` and its messages sent. -/
def kdBatchRes (γ : KdNames) (id : w64) (n : Loc) (st' : NodeDriverState) (ms : List QMsg) :
    IProp GF :=
  iprop(nodeDriver n γ.r.cluster kdRaftN st' ∗ readyMsgs γ.r.cluster kdRaftN id ms)

/-- **The pending batch's resources** (see the file header), at the file's durable state `S` and
the storage's contents `M`, for the node `n` of replica `id`, `ph` the claim's variable. -/
def kdPhaseInv (γ : KdNames) (id : w64) (n : Loc) (ph : GName) (S : RaftState) (M : StorFile) :
    KdPhase → IProp GF
  | .idle => iprop(ghostVar ph (1 : Qp).half ((none : Option GName), S) ∗
      ⌜StorageHolds S (kdContents (some M))⌝)
  | .waiting st st' ms γb => iprop(ghostVar ph (1 : Qp).half (some γb, st'.durable) ∗
      savedPropOwn γb DFrac.discard (kdBatchRes γ id n st' ms) ∗
      readyEnter n γ.r.cluster kdRaftN id st st' ms ∗
      ⌜st.durable = S ∧ StorageHolds st'.durable (kdContents (some M))⌝)
  | .fired γb => iprop(ghostVar ph (1 : Qp).half (some γb, S) ∗
      (∃ R : IProp GF, savedPropOwn γb DFrac.discard R ∗ R) ∗
      ⌜StorageHolds S (kdContents (some M))⌝)

/-- **An incarnation's `dmu` lock invariant** (see the file header): replica `id`'s incarnation at
`r`, its node `n`, its storage `st` (the `MemoryStorage` `ms`, names `γs`), whose image holds `M`
(also after a crash: `run` goes on changing the storage until it stops). -/
def kdDmuInv (γ : KdNames) (id : w64) (r n st ms : Loc) (γs : MemStorNames) (ph : KdDmuNames) :
    IProp GF :=
  iprop(∃ (crashed : Bool) (ip : Loc) (M : StorFile) (fz : Nat),
    -- half of `crashed`: the other half, at `false`, is the crasher's token (`repStop`) until
    -- `crash` sets it (and drops it, at `true`)
    "Hcr" ∷ r.[KReplica, go!"crashed"] ↦{DFrac.own (1 : Qp).half} crashed ∗
    "#Himg" ∷ st.[KStorage, go!"img"] ↦□ ip ∗
    "Himage" ∷ ownImage ip M ∗
    "Hmeta" ∷ memStorMeta ms γs M.hs ∗
    -- (2026-11-01, stage II (h)) the image's entries up to `fz` frozen in the `MemoryStorage` (the
    -- same entries), `fz` at most the commit index (or the log's start), and the lower bounds' authorities
    "Hic" ∷ monoNatAuthOwn ph.ic 1 fz ∗
    "#Hfz" ∷ memLog γs (uint.nat M.prev + 1) DFrac.discard (M.ents.take (fz - uint.nat M.prev)) ∗
    "%Hfzc" ∷ ⌜fz ≤ uint.nat M.hs.Commit' ∨ fz ≤ uint.nat M.prev⌝ ∗
    "His" ∷ monoNatAuthOwn ph.is 1 (uint.nat M.snap.Metadata'.Index') ∗
    -- (2026-11-01, stage II (j), G12) half of the image's hard state (`run` holds the other)
    "Hcm" ∷ ghostVar ph.cm (1 : Qp).half M.hs ∗
    -- (2026-11-01, stage II (h)) `M`'s shape, certificate and phase also after the crash (the run
    -- loop and the snapshotter go on changing the storage until `stop`, and their changes' premises
    -- are about `M`); the writer's half stays after the crash (`run` enters commit-only batches
    -- until it stops) until `crash`'s last critical section, after `stop`, takes it out, leaving
    -- `run`'s claim (`runDone`'s, through `stop`) in its place: `run` refutes that retired state
    -- with its own claim (three halves of `ph.ph`, with the phase's) (2026-11-01, G6)
    "Hlive" ∷ (∃ (S : RaftState) (o : Option StorFile) (pz : KdPhase),
      (if crashed then iprop(kdWriter γ id S o ∨
          ∃ v : Option GName × RaftState, ghostVar ph.ph (1 : Qp).half v)
        else kdWriter γ id S o) ∗ ⌜KdFileOk M⌝ ∗ kdSnapCert γ M.snap ∗
      -- (2026-11-01, stage II (j), G12) the file's commit index at most the image's
      ⌜∀ f, o = some f → uint.nat f.hs.Commit' ≤ uint.nat M.hs.Commit'⌝ ∗
      kdPhaseInv γ id n ph.ph S M pz))

/-- **The reads' sequence numbers** (`readSeqs`'s lock invariant): the last one issued, at least
every replica's last read sequence number (`γ.r.rseq`, the elements of the ids `0..9`), which
`next` moves to the one it issues for its caller's id. -/
def readSeqsInv (γ : KdNames) (s : Loc) : IProp GF :=
  iprop(∃ last : w64, s.[KReadSeqs, go!"last"] ↦ last ∗
    [∗list] i ∈ kvreconf.freshIds 0, ∃ ns : w64, i ↪[γ.r.rseq] ns ∗ ⌜uint.Z ns ≤ uint.Z last⌝)

/-- The cluster's `readSeqs` at `s` (persistent). -/
def isReadSeqs (γ : KdNames) (s : Loc) : IProp GF :=
  sync.isMutex (s.[KReadSeqs, go!"mu"]) (readSeqsInv γ s)

/-- **Incarnation `r` of replica `id`** (persistent; kvreconf's `isReplica`): its id among the
cluster's (`1 ≤ id ≤ 9`: at most `maxReplicas = 9` replicas are started, ids from `1`; what
`readSeqs.next` takes), its fields read-only (with its file and the cluster's `readSeqs`), its node,
the cluster, its `mu` and `dmu` locks, and its file's invariant. -/
def isReplica (γ : KdNames) (vs : List w64) (dir : GoString) (id : w64) (r n st sts sq : Loc)
    (ms : Loc) (γs : MemStorNames) (ph : KdDmuNames) : IProp GF :=
  iprop(
    "#Hpkg" ∷ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kvdurable ∗
    "%Hidr" ∷ ⌜1 ≤ uint.nat id ∧ uint.nat id ≤ 9⌝ ∗
    "#Hid" ∷ r.[KReplica, go!"id"] ↦□ id ∗
    "#Hfile" ∷ r.[KReplica, go!"file"] ↦□ kdFileName dir id ∗
    "#Hnode" ∷ r.[KReplica, go!"node"] ↦□ interface.mkOk (go.GoType.PointerType node.ty) #n ∗
    "#Hst" ∷ r.[KReplica, go!"storage"] ↦□ st ∗
    "#Hsts" ∷ r.[KReplica, go!"stats"] ↦□ sts ∗
    "#Hsq" ∷ r.[KReplica, go!"seqs"] ↦□ sq ∗
    "#Hstats" ∷ isStats sts ∗
    "#Hseqs" ∷ isReadSeqs γ sq ∗
    "#HisNode" ∷ isNode n γ.r.cluster kdRaftN id ∗
    "#Hcl" ∷ kdCluster γ vs ∗
    "#HfInv" ∷ kdFileInv γ dir id ∗
    "#Hrec" ∷ kdStorRec st ms γs ∗
    "#Hmu" ∷ sync.isMutex (r.[KReplica, go!"mu"]) (lockInv γ id r) ∗
    "#Hdmu" ∷ sync.isMutex (r.[KReplica, go!"dmu"]) (kdDmuInv γ id r n st ms γs ph))

/-- **What a request to the snapshot goroutine carries** (kvreconf's `snapReqOk`, at the storage's
key `K`): for a snapshot, the frozen entry at its index, its validity and the node's committed
index there, the configuration and the encoded state; for a compaction up to `q.compact`, a known
compaction point with the delivered log frozen above it, and the node's applied index. -/
def snapReqOk (γ : KdNames) (K : GName) (γs : MemStorNames) (dn : KdDmuNames) (q : KSnapReq) :
    IProp GF :=
  iprop((⌜q.data' = slice.nil⌝ ∨ ∃ (e : EntryM) (c : ConfStateM) (bs : List w8),
      memLog γs (uint.nat q.index') DFrac.discard [e] ∗
      -- (2026-11-01, stage II (h)) the index at most the image's frozen bound
      monoNatLbOwn dn.ic (uint.nat q.index') ∗
      (kdJ γ.r.cluster K).SV (memSnapMade q.index' e.Term' c bs) ∗
      (kdJ γ.r.cluster K).DL (uint.nat q.index') ∗
      kdSnapCert γ (memSnapMade q.index' e.Term' c bs) ∗
      ownCSM q.cs' DFrac.discard c ∗ q.data' ↦* bs) ∗
    (⌜q.compact' = W64 0⌝ ∨ ∃ (c : Nat) (D : List LogEntry),
      memCompacted γs c ∗ memLog γs (c + 1) DFrac.discard ((LogEntry.toEntries D 0).drop c) ∗
      ⌜uint.nat q.compact' ≤ D.length⌝ ∗
      nodeAppliedLb γ.r.cluster K (uint.nat q.compact')))

/-- **Incarnation `r` of replica `id`, running** (persistent; kvreconf's `isReplicaR`): `isReplica`,
`context`'s premise, the tick, the channels and their protocols (`runDone` and `snapDone` carry
`run`'s and the snapshotter's halves of `nodeRunning` back to `stop`, and `runDone` `run`'s claim
`ρ.ph.ph`, which `crash` leaves in `dmu` when it takes the writer out), the storage's `MemoryStorage`
attached at the key `ρ.key` (`memStorInvP … (kdJ γ ρ.key)`). -/
def isReplicaR (γ : KdNames) (vs : List w64) (dir : GoString) (id : w64) (r n st sts sq : Loc)
    (ρ : KdRepNames) : IProp GF :=
  iprop(
    "#Hrep" ∷ isReplica γ vs dir id r n st sts sq ρ.ms ρ.γs ρ.ph ∗
    "#Hcci" ∷ context.isClosedchanInit ∗
    "#Htick" ∷ (∃ tk : time.Duration, r.[KReplica, go!"tick"] ↦□ tk ∗ ⌜0 < sint.Z tk⌝) ∗
    "#Hstopc" ∷ r.[KReplica, go!"stopc"] ↦□ ρ.stopc ∗
    "#Hrdc" ∷ r.[KReplica, go!"runDone"] ↦□ ρ.rdc ∗
    "#Htdc" ∷ r.[KReplica, go!"tickDone"] ↦□ ρ.tdc ∗
    "#Hsnc" ∷ r.[KReplica, go!"snapc"] ↦□ ρ.snc ∗
    "#Hsdc" ∷ r.[KReplica, go!"snapDone"] ↦□ ρ.sdc ∗
    "#HstopB" ∷ ownBroadcastChan ρ.stopc ρ.sc iprop(True) .Unknown ∗
    "#HrdH" ∷ isHandoff (V := Unit) ρ.rd ρ.rdc
      (fun _ => iprop(nodeRunning n γ.r.cluster kdRaftN (1 : Qp).half ∗
        ∃ v : Option GName × RaftState, ghostVar ρ.ph.ph (1 : Qp).half v)) iprop(True) iprop(False) ∗
    "#HtdH" ∷ isHandoff (V := Unit) ρ.td ρ.tdc (fun _ => iprop(True)) iprop(True) iprop(False) ∗
    "#HsnB" ∷ isChanBag ρ.sn ρ.snc (snapReqOk γ ρ.key ρ.γs ρ.ph) ∗
    "#HsdH" ∷ isHandoff (V := Unit) ρ.sd ρ.sdc
      (fun _ => nodeRunning n γ.r.cluster kdRaftN (1 : Qp).half) iprop(True) iprop(False) ∗
    "#HmsInv" ∷ memStorInvP ρ.ms ρ.γs (kdJ γ.r.cluster ρ.key) ∗
    -- (2026-11-01, stage II (j), G23) the writers' lower bound of the stored snapshot, which
    -- `MemoryStorage.ApplySnapshot` takes (`run`'s snapshot `Ready`; kvreconf's `#HsnLb`)
    "#HsnLb" ∷ memSnapLb ρ.γs 0)

/-- **The stopper's share of incarnation `r`** (exclusive): `isReplicaR` with the stopper's tokens
(what `stop` takes). -/
def repStopper (γ : KdNames) (vs : List w64) (dir : GoString) (id : w64) (r : Loc) : IProp GF :=
  iprop(∃ (n st sts sq : Loc) (ρ : KdRepNames),
    isReplicaR γ vs dir id r n st sts sq ρ ∗
    ownBroadcastChan ρ.stopc ρ.sc iprop(True) .Pending ∗
    handoffConsumer ρ.rd false ∗ handoffConsumer ρ.td false ∗ handoffConsumer ρ.sd false)

/-- **The stopper's and the crasher's share of incarnation `r`** (exclusive; what `crash` takes):
`repStopper` and the crasher's token, the half of `crashed` at `false` (`kdDmuInv` holds the other
half): whoever holds it knows the incarnation has not crashed, so `crash` gets the writer's half
out of `dmu` (2026-11-01, the stopper/crasher split). -/
def repStop (γ : KdNames) (vs : List w64) (dir : GoString) (id : w64) (r : Loc) : IProp GF :=
  iprop(repStopper γ vs dir id r ∗ r.[KReplica, go!"crashed"] ↦{DFrac.own (1 : Qp).half} false)

/-- **What `run` starts with** (kvreconf's `runStart`): the node's driver as `RestartNode` leaves it
(at the committed log `l` of the applied index raft starts at, the stored hard state, the durable
state `S`, the follower's role, the storage's key), its configuration view at `(a, m)`, `run`'s half
of the running token, the replicated state at the stored snapshot's prefix (of length `a`),
`runDone`'s producer, `run`'s half of the image's hard state (the stored one: the term and vote
of `S`), the delivered log `l` at most `ap`, frozen above a known compaction point and at most the
image's frozen bound. -/
def runStart (γ : KdNames) (id : w64) (r n st : Loc) (ρ : KdRepNames) (l : List LogEntry)
    (hs : HardStateM) (S : RaftState) (ap : List LogEntry) (m : Membership) : IProp GF :=
  iprop(∃ (csp mA : Loc) (A : GMap (List w8) (List w8)),
    nodeDriver n γ.r.cluster kdRaftN ⟨kdStorIface st, l, hs, none, ρ.key, S, StateFollower⟩ ∗
    nodeConfig n γ.r.cluster kdRaftN ⟨ap.length, m⟩ ∗
    nodeRunning n γ.r.cluster kdRaftN (1 : Qp).half ∗
    repOwn γ r ap (W64 ap.length) csp m mA A ∗
    handoffProducer ρ.rd false ∗ ghostVar ρ.ph.ph (1 : Qp).half ((none : Option GName), S) ∗
    -- (2026-11-01, stage II (j), G12) `run`'s half of the image's hard state, the stored one, whose
    -- term and vote are the durable state's
    ghostVar ρ.ph.cm (1 : Qp).half hs ∗ ⌜S.term = hs.Term' ∧ S.vote = hs.Vote'⌝ ∗
    -- (2026-11-01, stage II (j), G18-G19) the delivered log `l` raft starts at: at most the
    -- replicated state (`Config.Applied` at most the snapshot's index), frozen in the `MemoryStorage`
    -- above a known compaction point, and at most the image's frozen bound
    ⌜l.length ≤ ap.length⌝ ∗
    (∃ c : Nat, memCompacted ρ.γs c ∗ kvreconf.frozenTo ρ.γs c l ∗ ⌜c ≤ l.length⌝) ∗
    monoNatLbOwn ρ.ph.ic l.length)

/-- **`f` is replica `id`'s transport** (persistent; kvreconf's `sendSpec`). -/
def sendSpec (γ : KdNames) (id : w64) (f : GoFunc) : IProp GF :=
  iprop(□ ∀ (msl : GoSlice) (ms : List QMsg),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kvdurable ∗
        ownSlice msl (ms.map QMsg.loc) (DFrac.own 1) ∗
        [∗list] q ∈ ms, msgOwn q.loc (readyDq q.st) q.st ∗ sentMsg γ.r.cluster kdRaftN id q.st ∗
          msgCredits γ.r.cluster kdRaftN q.st }}
      (App (Val #f) (Val #msl))
    {{ RET #(); True }})

/-- Replica `id` was started: it is below the cluster's next id (persistent). -/
def repKnown (γ : KdNames) (id : w64) : IProp GF :=
  iprop(⌜id ≠ W64 0⌝ ∗ monoNatLbOwn γ.r.nid (uint.nat id + 1))

/-- **The cluster's lock invariant** (kvreconf's `clusterLockInv`, with incarnations): the current
incarnation of each started replica, the ids not started yet with their allocated durable state and
vacant slot (`joinAuth`), and per started id either its current incarnation's stopper share or (while
`Crash` restarts it) nothing. -/
def clusterLockInv (γ : KdNames) (vs : List w64) (dir : GoString) (c : Loc) : IProp GF :=
  iprop(∃ (mR : Loc) (R : GMap w64 Loc) (nid nop : w64) (U : GSet w64),
    "HmR" ∷ c.[KCluster, go!"replicas"] ↦ mR ∗
    "HR" ∷ mR ↦$ R ∗
    "Hnid" ∷ c.[KCluster, go!"nextID"] ↦ nid ∗
    "Hnop" ∷ c.[KCluster, go!"nextOp"] ↦ nop ∗
    "Hopn" ∷ ghostVar γ.r.opn (1 : Qp).half nop ∗
    "HnidA" ∷ monoNatAuthOwn γ.r.nid 1 (uint.nat nid) ∗
    "Hjoin" ∷ joinAuth γ.r.cluster U ∗
    "%Hdom" ∷ ⌜(∀ i, (R !! i).isSome ↔ 1 ≤ uint.nat i ∧ uint.nat i < uint.nat nid) ∧
      (∀ i, i ∈ U ↔ 1 ≤ uint.nat i ∧ uint.nat i < uint.nat nid) ∧
      vs.length < uint.nat nid ∧ uint.nat nid ≤ 10⌝ ∗
    "Hreps" ∷ ([∗map] id ↦ r ∈ R, ∃ (n st sts sq : Loc) (ρ : KdRepNames),
      isReplicaR γ vs dir id r n st sts sq ρ) ∗
    "Hfiles" ∷ ([∗list] i ∈ kvreconf.freshIds (uint.nat nid), dfile γ.files (kdFileName dir i) none ∗
      ∃ g : RaftState × Option GoString, ghostVar (γ.wr i) (1 : Qp) g))

/-- **The cluster at `c`** (persistent; kvreconf's `isClusterC`), of the bootstrap voters `vs`, its
replicas' files in the directory `dir`. -/
def isClusterC (γ : KdNames) (vs : List w64) (dir : GoString) (c : Loc) : IProp GF :=
  iprop(∃ (bp sq : Loc),
    "#Hpkg" ∷ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kvdurable ∗
    "#Hcl" ∷ kdCluster γ vs ∗
    "#Hcci" ∷ context.isClosedchanInit ∗
    "%Hdup" ∷ ⌜γ.r.cluster.dup = true⌝ ∗
    "#HstorInv" ∷ kdStorInv ∗
    "#Hdir" ∷ c.[KCluster, go!"dir"] ↦□ dir ∗
    "#Hboot" ∷ c.[KCluster, go!"boot"] ↦□ bp ∗
    "#HbootCS" ∷ ownCSM bp DFrac.discard (kvreconf.bootCS vs) ∗
    "#Hsq" ∷ c.[KCluster, go!"seqs"] ↦□ sq ∗
    "#Hseqs" ∷ isReadSeqs γ sq ∗
    "#Hstats" ∷ isStats (c.[KCluster, go!"Stats"]) ∗
    "#Hmu" ∷ sync.isMutex (c.[KCluster, go!"mu"]) (clusterLockInv γ vs dir c))

end ghost

end kvdurable
end EtcdGrove
end Perennial
