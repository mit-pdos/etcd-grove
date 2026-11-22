/-
# kvnet's replica predicates (2026-11-22; notes/kvnet-part.md, the replica layer)

The part's own adaptation of kvnet's `Defs.lean` (RaftNoAx's copy of kvdurable's), keeping its
interface (names and parameters: `isReplica`, `isReplicaR`, `isRep`, `repOwn`, `lockInv`, `kdDmuInv`,
`runStart`, `KdRepNames`, ...) so that the proofs of the functions whose Go text is kvnet's
(`Replica.{request,applyOp,answer,propose}`, the storage's) are copies (etc/copy-part.py's
`RENAME_KVNET`, `KVNET_REUSED`), at kvnet's `Replica` struct (`examples/raft/kvnet/replica.go`):

* no stop channels (`stopc`, `runDone`, `tickDone`, `snapDone`) and no crashed flag: a replica ends with
  its process (decision C, notes/kvnet-proof-plan.md); `KdRepNames` keeps the storage's, the snapshot
  channel's, the key's and `dmu`'s names; `run` keeps its half of `nodeRunning`;
* no `seqs`: the reads' sequence numbers are the clients' (`isReplica`'s parameter `sq` stays, unused,
  so that the copies' statements keep their shape);
* the statistics are kvnet's `Stats` (a mutex over an array of counters: `isStats`, `TransportDefs.lean`);
* the file: not in this module yet. kvnet's is over `durableExt` (`durable/Files`); kvnet's is the
  bodied `durable` over fsExt, with the generation's crash invariant (decision C), added with `persist`.
  `kdWriter` (the writer's half of the per-id ghost variable) is file-agnostic and stays.

The store-level predicates (`rkvInv`, `waitP`, `kvLb`, `readAns`, `kdSnapInv`, the names `KdNames`) are
the shared store module's (`Store.lean`, decision B's), the cluster's facts global.
-/
module

public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Store
public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.KdStorage
public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Codec
public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Image
public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvreconf.DefsCluster
public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.TransportDefs
public import KvNet.Proof.github_com.mit_pdos.etcd_grove.examples.lib.durable.Defs

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvnet

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

/-- The store's structs. -/
abbrev KReplica [GooseExts] := github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Replica
abbrev KSnapReq [GooseExts] := github_com.mit_pdos.etcd_grove.examples.raft.kvnet.snapReq

abbrev kReplicaTy [GooseExts] [GoGlobalContext] : go.GoType :=
  github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Replica.ty

instance KSnapReq.countable [GooseExts] : Pos.Countable KSnapReq :=
  countableOfLeftInverse (fun q : KSnapReq => (q.index', q.cs', q.data', q.compact'))
    (fun p => ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩) (fun _ => rfl)

/-- **A generation's file names** (2026-11-22, decision C; ledger, kvnet's `StartNode`): allocated at the
generation's boot, before raft's node exists, with the file invariant (`kdFileInvK`) that the
generation's crash obligation empties. -/
structure KdFileNames where
  /-- `durable`'s names, the file, its roots -/
  γd : DurFs.DurGS
  df : DurFs.DFile
  fR : Fs.Roots
  /-- the writer's variable (`ghostVar` of `KdWv`, halves: the writer's, `kdWriter`, and the file
  invariant's): per generation, so that the dead generation's `dmu` keeps its own -/
  wr : GName
  /-- the file invariant's crash token (`token`): the crash obligation's, which closes the invariant on
  its crashed side -/
  tk : GName
  /-- raft's arm the generation's node is started from (`nodeVacantA`, `nodeArm`) -/
  x : CrashNames

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
  /-- (2026-11-22, decision C) the generation's file names (`KdFileNames`) -/
  fl : KdFileNames

/-- A replica incarnation's names (`DefsCluster`'s `RepNames` without the stop channels, with the
storage's key and the `dmu` names). -/
structure KdRepNames where
  ms : Loc
  γs : MemStorNames
  snc : Loc
  sn : ChanNames
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

/-- **The terms `openStorage` checks** (2026-11-01): the log's start at index `0` is at term `0`
(a `MemoryStorage`'s dummy entry, which it keeps there), and the term of the log at the stored
snapshot's index (`imgTermAt`: the start's at the start, the entry's above it) is the snapshot's
(it applies the snapshot at the start, or takes it again from the log with `CreateSnapshot`, which
reads the term there). -/
def KdSnapTermOk (f : StorFile) : Prop :=
  (f.prev = W64 0 → f.prevTerm = W64 0) ∧
    imgTermAt f f.snap.Metadata'.Index' = f.snap.Metadata'.Term'

/-- **The contents `openStorage` accepts** (its checks): the entries consecutive from the log's
start, the start below `maxIndex` and the entries' indices below it too (raft's storage bound,
`MemoryStorage.Append`'s premise; 2026-11-01, openStorage's proof: was `≤`, which let the last index
be `maxIndex` itself, past what `fits` lets the log reach), the snapshot and the commit index
within the log, the snapshot's term the entry's there (`KdSnapTermOk`); and the bytes decode back
(`StorWf`). -/
def KdFileOk (f : StorFile) : Prop :=
  StorWf f ∧ uint.Z f.prev < 2 ^ 61 ∧ (f.ents.length : Int) < 2 ^ 61 - uint.Z f.prev ∧
  (∀ (i : Nat) (e : EntryM), f.ents[i]? = some e → uint.nat e.Index' = uint.nat f.prev + 1 + i) ∧
  uint.Z f.prev ≤ uint.Z f.snap.Metadata'.Index' ∧
  uint.nat f.snap.Metadata'.Index' ≤ uint.nat f.prev + f.ents.length ∧
  uint.Z f.prev ≤ uint.Z f.hs.Commit' ∧ uint.nat f.hs.Commit' ≤ uint.nat f.prev + f.ents.length ∧
  KdSnapTermOk f

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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [KdStor GF]
variable [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]

attribute [local instance] kdStorageModel

/-- A `ReadState` as `Ready` hands it out (persistent). -/
def rsOk (γ : Cluster) (v : ReadState) : IProp GF :=
  iprop(∃ c : List w8, v.RequestCtx' ↦*□ c ∗ readStateOk γ kdRaftN c v.Index')

/-- **An answer fits a reply frame** (2026-11-22, notes/kvnet-part.md, "The answers' lengths"): the
server writes `1 :: v` with its 8-byte length prefix (`writeFrame`: `make([]byte, 0, 8+len(body))`), so
`len(v) + 9` must be a Go `int`. Every value the replica holds is the tail of a decoded entry, a Go
slice with 17 bytes before it (`decode`), or a snapshot's: the replica's maps keep it (`MapFits`). -/
def MapFits (M : GMap (List w8) (List w8)) : Prop :=
  ∀ k v, M !! k = some v → (v.length : Int) + 9 < 2 ^ 63

theorem MapFits.insert {M : GMap (List w8) (List w8)} (h : MapFits M) (k v : List w8)
    (hv : (v.length : Int) + 9 < 2 ^ 63) : MapFits (<[k := v]> M) := by
  intro k' v' h'
  rcases (GMap.lookup_insert_Some M k k' v v').1 h' with ⟨-, rfl⟩ | ⟨-, h''⟩
  · exact hv
  · exact h k' v' h''

theorem MapFits.getD {M : GMap (List w8) (List w8)} (h : MapFits M) (k : List w8) :
    (((M !! k).getD []).length : Int) + 9 < 2 ^ 63 := by
  cases hk : M !! k with
  | none => simp
  | some v => exact h k v hk

theorem decodeOp_val_len {d : List w8} {i : w64} {kd : w8} {key val : List w8}
    (h : raft_kvreconf.decodeOp d = some (i, kd, key, val)) : val.length + 17 ≤ d.length := by
  unfold raft_kvreconf.decodeOp at h
  split at h
  · split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, -, -, rfl⟩ := h
      simp only [List.length_drop]
      omega
    · cases h
  · cases h

/-- A read's entry in the replica's lock: the context `c` minted at `(id, s)`. -/
def readWaiterOk (γ : KdNames) (id s : w64) (ch : Loc) : IProp GF :=
  iprop(∃ (c : List w8) (γh : HandoffNames),
    (id, s) ↪[γ.r.rmint]□ c ∗
    isHandoff γh ch (fun v => iprop(readAns γ c v ∗ ⌜(v.length : Int) + 9 < 2 ^ 63⌝)) iprop(True)
      iprop(False) ∗ handoffProducer γh false)

/-- An operation's entry in the replica's lock. -/
def waiterOk (γ : KdNames) (d : List w8) (ch : Loc) : IProp GF :=
  iprop(∃ (γh : HandoffNames),
    isHandoff γh ch (fun v => iprop(waitP γ d v ∗ ⌜(v.length : Int) + 9 < 2 ^ 63⌝)) iprop(True)
      iprop(False) ∗ handoffProducer γh false)

/-- The applier's half of an incarnation's replicated state (kvreconf's `repOwn`), at the committed
prefix `ap`: since a restarted incarnation starts at its stored snapshot's prefix, `ap` is any
committed prefix, not the empty one. -/
def repOwn (γ : KdNames) (r : Loc) (ap : List LogEntry)
    (idx : w64) (csp : Loc) (m : Membership) (mA : Loc) (A : GMap (List w8) (List w8)) :
    IProp GF :=
  iprop(∃ (mK : Loc) (K : GMap (List w8) (List w8)) (c : ConfStateM),
    "HmK" ∷ r.[KReplica, go!"kv"] ↦{DFrac.own (1 : Qp).half} mK ∗
    "HK" ∷ mK ↦${DFrac.own (1 : Qp).half} K ∗
    "HmA" ∷ r.[KReplica, go!"applied"] ↦{DFrac.own (1 : Qp).half} mA ∗
    "HA" ∷ mA ↦${DFrac.own (1 : Qp).half} A ∗
    "Hcs" ∷ r.[KReplica, go!"cs"] ↦{DFrac.own (1 : Qp).half} csp ∗
    "Hidx" ∷ r.[KReplica, go!"index"] ↦{DFrac.own (1 : Qp).half} idx ∗
    "#Hap" ∷ isCommittedLogLb γ.r.cluster ap ∗
    "%Hlen" ∷ ⌜(ap.length : Int) < 2 ^ 61⌝ ∗
    "%Hval" ∷ ⌜∀ k, (K !! k).getD [] = raft_kvreconf.kvFold (raft_kvreconf.logHist ap) k⌝ ∗
    "%HKfit" ∷ ⌜MapFits K⌝ ∗
    "%HA" ∷ ⌜raft_kvreconf.AppliedOk A (raft_kvreconf.logHist ap)⌝ ∗
    "#HcsO" ∷ csOpt csp DFrac.discard c ∗
    "%Hcsm" ∷ ⌜confStateIs c m⌝ ∗
    "%Hsz" ∷ ⌜GMap.size m.ids < 2 ^ 61⌝ ∗
    "#Hcfg" ∷ confAt γ.r.cluster ap.length m)

/-- The lock's half of an incarnation's replicated state (kvreconf's `repShared`), with half of the
store's map (2026-11-22: kvnet's `contents` reads it under `mu`; the applier writes it under `mu`). -/
def repShared (γ : KdNames) (r : Loc) : IProp GF :=
  iprop(∃ (mA : Loc) (A : GMap (List w8) (List w8)) (csp : Loc) (c : ConfStateM) (idx : w64)
      (ap : List LogEntry) (mK : Loc) (K : GMap (List w8) (List w8)),
    "HmA" ∷ r.[KReplica, go!"applied"] ↦{DFrac.own (1 : Qp).half} mA ∗
    "HA" ∷ mA ↦${DFrac.own (1 : Qp).half} A ∗
    "Hcs" ∷ r.[KReplica, go!"cs"] ↦{DFrac.own (1 : Qp).half} csp ∗
    "Hidx" ∷ r.[KReplica, go!"index"] ↦{DFrac.own (1 : Qp).half} idx ∗
    "HmK" ∷ r.[KReplica, go!"kv"] ↦{DFrac.own (1 : Qp).half} mK ∗
    "HK" ∷ mK ↦${DFrac.own (1 : Qp).half} K ∗
    "#HcsO" ∷ csOpt csp DFrac.discard c ∗
    "#Hap" ∷ isCommittedLogLb γ.r.cluster ap ∗
    "%HA" ∷ ⌜raft_kvreconf.AppliedOk A (raft_kvreconf.logHist ap)⌝ ∗
    "%HAfit" ∷ ⌜MapFits A⌝ ∗
    "%HKsfit" ∷ ⌜MapFits K⌝)

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
def appNode (γ : KdNames) (n : NodeH) (l : List LogEntry) (k : Nat) (m : Membership) : IProp GF :=
  iprop(∃ v : ConfigView, nodeConfig n γ.r.cluster kdRaftN v ∗
      deliveredLogLb n γ.r.cluster kdRaftN l ∗ skippedIn γ.r.cluster l v.applied k ∗
      ⌜v.membership = m ∧ v.applied ≤ k⌝)

/-- **The store's cluster** (persistent): raft's cluster, its conf entries decided by kvreconf's
rule from the bootstrap voters `vs`, the registry of the snapshots made and the store's invariant (the
files are not here: decision C). -/
def kdCluster (γ : KdNames) (vs : List w64) : IProp GF :=
  iprop(isCluster γ.r.cluster kdRaftN ∗ confPolicy γ.r.cluster kdConfN raft_kvreconf.kvrRule ∗
    confAt γ.r.cluster 0 (Membership.simple (GMap.listToSet vs)) ∗ kdSnapInv γ ∗ rkvInv γ ∗
    -- (2026-11-12, trace-check implementation step 1) an untraced cluster (`cluster_alloc`'s): the
    -- node API's `ReadIndex` is refused at a traced one
    ⌜Cluster.trace γ.r.cluster = none⌝)

open Iris.ProofMode in
/-- (2026-11-12, trace-check implementation step 1) The store's cluster is untraced. -/
theorem kdCluster_untraced (γ : KdNames) (vs : List w64) :
    kdCluster (GF := GF) γ vs ⊢ ⌜Cluster.trace γ.r.cluster = none⌝ := by
  unfold kdCluster
  iintro ⟨-, -, -, -, -, %H⟩
  ipureintro; exact H

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
      ⌜L.length = uint.nat sv.Metadata'.Index' ∧ raft_kvreconf.kvSnapOk L sv.Data' ∧
        confStateIs sv.Metadata'.ConfState' m ∧ GMap.size m.ids < 2 ^ 61⌝)

/-- **A batch's results** (`readyEnter`'s post but the durable state and the running token): the
loop's token after the `Ready` and its messages sent. -/
def kdBatchRes (γ : KdNames) (id : w64) (n : NodeH) (st' : NodeDriverState) (ms : List QMsg) :
    IProp GF :=
  iprop(nodeDriver n γ.r.cluster kdRaftN st' ∗ readyMsgs γ.r.cluster kdRaftN id ms)

/-- **The writer's value** (2026-11-22, decision C): the durable state, the file's client state
(`durable`'s `DurSt`), and, during a write's window (between its rename and its sync), the name of the
pending batch's results (`kdBatchRes`'s saved proposition), the durable state it enters, and the share
`q` of the writer's `nodeRunning` that waits with its *enter* in the file's invariant (raft's
`readyCrashEnter` needs it: the node was not stopped since the cut), and the name `γr` of the saved
proposition (`kdBatchRec` at the writer's node) by which the writer recognizes its batch's record in
the invariant: a node handle (`NodeH`, in `Type 1`) cannot be ghost state, so the record names its node
existentially, and the saved proposition's agreement moves its contents to the writer's node. -/
abbrev KdWv : Type := RaftState × DurFs.DurSt × Option (GName × RaftState × Qp × GName)

/-- **The right to write replica `id`'s file**, which holds `o`, with its durable state `S`, no write in
its window (exclusive; the other half in `kdFileBody`). -/
def kdWriter (fl : KdFileNames) (S : RaftState) (o : Option StorFile) : IProp GF :=
  ghostVar fl.wr (1 : Qp).half ((S, ⟨kdFileVal o, none⟩, none) : KdWv)

/-- **The file's contents `v` hold the durable state `S`**: the encoding of a file `openStorage` accepts
(`KdFileOk`) whose contents hold `S`, with its snapshot's certificate; or no file and `S` the empty
storage's. -/
def fileHolds (γ : KdNames) (S : RaftState) (v : Option GoString) : IProp GF :=
  iprop(∃ o : Option StorFile,
    ⌜v = kdFileVal o ∧ (∀ f, o = some f → KdFileOk f) ∧ StorageHolds S (kdContents o)⌝ ∗
    (∀ f, ⌜o = some f⌝ -∗ kdSnapCert γ f.snap))

/-- **A pending batch's record** in the file's invariant, for the node `n` started from arm `x`: its
*enter* from `S` to `S2` (`readyEnter`), the share `q` of `nodeRunning` that waits with it, and its
results' saved proposition at `γb`: what raft's `readyCrashEnter` takes after a crash. -/
def kdBatchRec (γ : KdNames) (id : w64) (x : CrashNames) (S S2 : RaftState) (q : Qp) (γb : GName)
    (n : NodeH) : IProp GF :=
  iprop(∃ (st st' : NodeDriverState) (ms : List QMsg),
    nodeArm n γ.r.cluster x ∗
    readyEnter n γ.r.cluster kdRaftN id st st' ms ∗ nodeRunning n γ.r.cluster kdRaftN q ∗
    savedPropOwn γb DFrac.discard (kdBatchRes γ id n st' ms) ∗
    ⌜st.durable = S ∧ st'.durable = S2⌝)

/-- **What replica `id`'s file holds** at the client state `s` and durable state `S`
(see `kdFileInvK`): outside a write's window (`alt = none`) the file holds `S`; in it, the old contents
hold `S`, and the new ones either `S` too (a write that moves no durable state) or the state that the
pending batch (its results saved at `γb`) enters (`S2`), whose *enter* (`readyEnter`) waits here
(`kdBatchRec`, at some node, recognized by the writer through the saved proposition at `γr`): at the
sync it fires (`persist`); after a crash the next boot either drops the batch (the file kept the old
contents: raft's `nodeCrash`) or enters it (`readyCrashEnter.law`, `notes/kvnet-part.md`). -/
def kdFileState (γ : KdNames) (id : w64) (x : CrashNames) (S : RaftState) (s : DurFs.DurSt)
    (pb : Option (GName × RaftState × Qp × GName)) : IProp GF :=
  match s.alt with
  | none => iprop(fileHolds γ S s.cur ∗ ⌜pb = none⌝)
  | some old => iprop(fileHolds γ S old ∗
      match pb with
      | none => fileHolds γ S s.cur
      | some (γb, S2, q, γr) => iprop(∃ n : NodeH, kdBatchRec γ id x S S2 q γb n ∗
          savedPropOwn γr DFrac.discard (kdBatchRec γ id x S S2 q γb n) ∗ fileHolds γ S2 s.cur))

/-- The file invariant's body. -/
def kdFileBody (γ : KdNames) (id : w64) (fl : KdFileNames) : IProp GF :=
  iprop(∃ (S : RaftState) (s : DurFs.DurSt) (pb : Option (GName × RaftState × Qp × GName)),
    DurFs.durSt fl.γd s ∗ ghostVar fl.wr (1 : Qp).half ((S, s, pb) : KdWv) ∗
    ((raftState γ.r.cluster id S ∗ kdFileState γ id fl.x S s pb) ∨ crashed ∗ token fl.tk))

/-- **Replica `id`'s file** (an invariant of this generation, allocated at its boot: decision C; ledger
2026-11-22, kvnet's `StartNode`): `durable`'s client state of the file, the writer's other half, and,
until the crash obligation takes them with the token `fl.tk` (the crashed side), the durable state and
what the file holds (`kdFileState`; a pending batch names its node, which `pb` carries). An opener
without the token refutes the crashed side with `notCrashed`, or touches only `durSt` and the writer. -/
def kdFileInvK (γ : KdNames) (id : w64) (fl : KdFileNames) : IProp GF :=
  inv (kdRepN .@ uint.nat id) (kdFileBody γ id fl)

/-- The decimal digits of `n` (`itoa`). -/
def decimalB (n : Nat) : GoString := (Nat.toDigits 10 n).map (fun c => W8 (c.toNat : Int))

/-- The file of replica `id` (the program's string): `dir + "/replica-" + itoa(id)`. -/
def kdFileName (dir : GoString) (id : w64) : GoString :=
  dir ++ go!"/replica-" ++ decimalB (uint.nat id)

/-- **The pending batch's resources** (see the file header), at the file's durable state `S` and
the storage's contents `M`, for the node `n` of replica `id`, `ph` the claim's variable. -/
def kdPhaseInv (γ : KdNames) (id : w64) (n : NodeH) (ph : GName) (S : RaftState) (M : StorFile) :
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
def kdDmuInv (γ : KdNames) (id : w64) (r : Loc) (n : NodeH) (st ms : Loc) (γs : MemStorNames) (ph : KdDmuNames) :
    IProp GF :=
  iprop(∃ (ip : Loc) (M : StorFile) (fz : Nat),
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
    -- (2026-11-22, decision C) the file's handle and a share of its directory's call permission
    -- (`durable.Write`'s: one writer at a time)
    "Hdh" ∷ DurFs.durHandle ph.fl.γd ph.fl.df ph.fl.fR ∗
    "Hcpm" ∷ (∃ qc : Qp, Fs.osCallPerm (Fs.callKey ph.fl.fR ph.fl.df.d) qc) ∗
    -- (2026-11-01, stage II (h)) `M`'s shape, certificate and phase also after the crash (the run
    -- loop and the snapshotter go on changing the storage until `stop`, and their changes' premises
    -- are about `M`); the writer's half stays after the crash (`run` enters commit-only batches
    -- until it stops) until `crash`'s last critical section, after `stop`, takes it out, leaving
    -- `run`'s claim (`runDone`'s, through `stop`) in its place: `run` refutes that retired state
    -- with its own claim (three halves of `ph.ph`, with the phase's) (2026-11-01, G6)
    "Hlive" ∷ (∃ (S : RaftState) (o : Option StorFile) (pz : KdPhase),
      kdWriter ph.fl S o ∗ ⌜KdFileOk M⌝ ∗ kdSnapCert γ M.snap ∗
      -- (2026-11-01, stage II (j), G12) the file's commit index at most the image's
      ⌜∀ f, o = some f → uint.nat f.hs.Commit' ≤ uint.nat M.hs.Commit'⌝ ∗
      kdPhaseInv γ id n ph.ph S M pz))

/-- **Incarnation `r` of replica `id`** (persistent; kvreconf's `isReplica`): its id among the
cluster's (`1 ≤ id ≤ γ.max`: at most `opts.MaxReplicas` replicas are started, ids from `1`; what
`readSeqs.next` takes), its fields read-only (with its file and the cluster's `readSeqs`), its node,
the cluster, its `mu` and `dmu` locks, and its file's invariant. -/
def isReplica (γ : KdNames) (vs : List w64) (dir : GoString) (id : w64) (r : Loc) (n : NodeH) (st sts sq : Loc)
    (ms : Loc) (γs : MemStorNames) (ph : KdDmuNames) : IProp GF :=
  iprop(
    "#Hpkg" ∷ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvnet ∗
    "%Hidr" ∷ ⌜1 ≤ uint.nat id ∧ uint.nat id ≤ γ.max⌝ ∗
    "#Hid" ∷ r.[KReplica, go!"id"] ↦□ id ∗
    "#Hfile" ∷ r.[KReplica, go!"file"] ↦□ kdFileName dir id ∗
    "#Hnode" ∷ r.[KReplica, go!"node"] ↦□ interface.mkOk (go.GoType.PointerType node.ty) #n.loc ∗
    "#Hst" ∷ r.[KReplica, go!"storage"] ↦□ st ∗
    "#Hsts" ∷ r.[KReplica, go!"stats"] ↦□ sts ∗
    "#Hstats" ∷ isStats sts ∗
    "#HisNode" ∷ isNode n γ.r.cluster kdRaftN id ∗
    "#Hcl" ∷ kdCluster γ vs ∗
    "#Hrec" ∷ kdStorRec st ms γs ∗
    "#Hmu" ∷ sync.isMutex (r.[KReplica, go!"mu"]) (lockInv γ id r) ∗
    "#Hdmu" ∷ sync.isMutex (r.[KReplica, go!"dmu"]) (kdDmuInv γ id r n st ms γs ph) ∗
    -- (2026-11-22, decision C) the file: `os`'s and `durable`'s invariants, and the store's
    "#Hos" ∷ Fs.osInv ∗ "#HosS" ∷ Fs.osSharedInv ph.fl.fR ∗ "#Hdi" ∷ DurFs.durInv ph.fl.γd ph.fl.df ∗
    "#HfInv" ∷ kdFileInvK γ id ph.fl ∗
    -- (2026-11-22) the node was started from the generation's arm (a pending batch's record names it)
    "#Harm" ∷ nodeArm n γ.r.cluster ph.fl.x ∗
    "%Hdf" ∷ ⌜ph.fl.df.Ok ∧ ph.fl.df.name = kdFileName dir id⌝ ∗
    -- (raft-entsize §2, 2026-11-09) no bound on proposed data (`cluster_alloc`'s `md = none`): the
    -- node API's size premises hold vacuously
    "%Hmd" ∷ ⌜γ.r.cluster.maxData = none⌝ ∗
    -- (auth-lease S4, 2026-11-16) outside raft's no-snapshot mode (no bootstrap log,
    -- `clusterNoSnap_boot`): the storage's compaction justification (`kdJ`) past index `1`
    "%Hnsn" ∷ ⌜¬ clusterNoSnap γ.r.cluster⌝)

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
def isReplicaR (γ : KdNames) (vs : List w64) (dir : GoString) (id : w64) (r : Loc) (n : NodeH) (st sts sq : Loc)
    (ρ : KdRepNames) : IProp GF :=
  iprop(
    "#Hrep" ∷ isReplica γ vs dir id r n st sts sq ρ.ms ρ.γs ρ.ph ∗
    "#Hcci" ∷ context.isClosedchanInit ∗
    "#Htick" ∷ (∃ tk : time.Duration, r.[KReplica, go!"tick"] ↦□ tk ∗ ⌜0 < sint.Z tk⌝) ∗
    "#Hsnc" ∷ r.[KReplica, go!"snapc"] ↦□ ρ.snc ∗
    "#HsnB" ∷ isChanBag ρ.sn ρ.snc (snapReqOk γ ρ.key ρ.γs ρ.ph) ∗
    "#HmsInv" ∷ memStorInvP ρ.ms ρ.γs (kdJ γ.r.cluster ρ.key) ∗
    -- (2026-11-01, stage II (j), G23) the writers' lower bound of the stored snapshot, which
    -- `MemoryStorage.ApplySnapshot` takes (`run`'s snapshot `Ready`; kvreconf's `#HsnLb`)
    "#HsnLb" ∷ memSnapLb ρ.γs 0)

/-- **What `run` starts with** (kvreconf's `runStart`): the node's driver as `RestartNode` leaves it
(at the committed log `l` of the applied index raft starts at, the stored hard state, the durable
state `S`, the follower's role, the storage's key), its configuration view at `(a, m)`, `run`'s half
of the running token, the replicated state at the stored snapshot's prefix (of length `a`),
`runDone`'s producer, `run`'s half of the image's hard state (the stored one: the term and vote
of `S`), the delivered log `l` at most `ap`, frozen above a known compaction point and at most the
image's frozen bound. -/
def runStart (γ : KdNames) (id : w64) (r : Loc) (n : NodeH) (st : Loc) (ρ : KdRepNames) (l : List LogEntry)
    (hs : HardStateM) (S : RaftState) (ap : List LogEntry) (m : Membership) : IProp GF :=
  iprop(∃ (csp mA : Loc) (A : GMap (List w8) (List w8)),
    nodeDriver n γ.r.cluster kdRaftN ⟨kdStorIface st, l, hs, none, ρ.key, S, StateFollower⟩ ∗
    nodeConfig n γ.r.cluster kdRaftN ⟨ap.length, m⟩ ∗
    nodeRunning n γ.r.cluster kdRaftN (1 : Qp).half ∗
    repOwn γ r ap (W64 ap.length) csp m mA A ∗
    ghostVar ρ.ph.ph (1 : Qp).half ((none : Option GName), S) ∗
    -- (2026-11-01, stage II (j), G12) `run`'s half of the image's hard state, the stored one, whose
    -- term and vote are the durable state's
    ghostVar ρ.ph.cm (1 : Qp).half hs ∗ ⌜S.term = hs.Term' ∧ S.vote = hs.Vote'⌝ ∗
    -- (2026-11-01, stage II (j), G18-G19) the delivered log `l` raft starts at: at most the
    -- replicated state (`Config.Applied` at most the snapshot's index), frozen in the `MemoryStorage`
    -- above a known compaction point, and at most the image's frozen bound
    ⌜l.length ≤ ap.length⌝ ∗
    (∃ c : Nat, memCompacted ρ.γs c ∗ raft_kvreconf.frozenTo ρ.γs c l ∗ ⌜c ≤ l.length⌝) ∗
    monoNatLbOwn ρ.ph.ic l.length)

/-- **`run`'s send callback** (kvdurable's `sendSpec`; 2026-11-22, drafted with no `.lake`): it takes
the `Ready`'s messages, owned, each sent by `id` (`sentMsg`) with its credits. kvnet's is the transport's
`t.Send` (`StartNode` gives it from `Transport.Send.spec`). -/
def sendSpec (γ : KdNames) (id : w64) (f : GoFunc) : IProp GF :=
  iprop(□ ∀ (msl : GoSlice) (ms : List QMsg),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvnet ∗
        ownSlice msl (ms.map QMsg.loc) (DFrac.own 1) ∗
        [∗list] q ∈ ms, msgOwn q.loc (readyDq q.st) q.st ∗ sentMsg γ.r.cluster kdRaftN id q.st ∗
          msgCredits γ.r.cluster kdRaftN q.st }}
      (App (Val #f) (Val #msl))
    {{ RET #(); True }})

/-- **Some incarnation `r` of replica `id`, running** (persistent; kvreconf's `isRep`): what
`c.replicas[id]` holds. -/
def isRep (γ : KdNames) (vs : List w64) (dir : GoString) (id : w64) (r : Loc) : IProp GF :=
  iprop(∃ (n : NodeH) (st sts sq : Loc) (ρ : KdRepNames), isReplicaR γ vs dir id r n st sts sq ρ)

end ghost

end raft_kvnet
end EtcdGrove
end Perennial
