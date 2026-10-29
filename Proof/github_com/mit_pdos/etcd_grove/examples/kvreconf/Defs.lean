/-
Lean-first (no Rocq counterpart).

# The reconfiguring store's predicates (2026-10-29, track C)

`examples/kv`'s design (`Proof/github_com/mit_pdos/etcd_grove/examples/kv/Defs.lean`, whose header
explains the client-facing state, the slots and the minting), changed where kvreconf differs.

## The store's invariant (`rkvInv`)

As kv's: raft's committed requested entries (`ownCommittedOps`; `opsOf` keeps the conf entries and
drops raft's fillers and its empty `ConfChangeV2`s), half of the history's ghost variable at their
data's first occurrences (`logHist`), the read contexts used (`ownReadCtxs`), and the operations'
slots (`opSlot`). A conf entry carries no client datum (`odOf`), so a conf change committing moves
`ownCommittedOps` and leaves the history: `Reconfigure`'s `ProposeConfChange` gives raft an update
that does only that.

**Minting.** An operation's id is the cluster's (`Cluster.do`, `c.nextOp` under `c.mu`), not a
replica's: the invariant holds the cluster's last id (`ghostVar γr.opn`, the other half in the
cluster's lock) and the persistent record of each minted datum by its id (`γr.mint`); a read's
context is minted at `(replica, seq)` (`γr.rmint`), each replica's last read sequence number in
`γr.rseq` (its element in the replica's lock). Every committed datum, slot and used read context was
minted, so a fresh id or sequence number mints a datum nobody had.

**Conf entries' shape.** Every committed requested conf entry decodes to a change of a defined
transition (`ConfShaped`, `Rule.lean`): what `Reconfigure` proposes. With raft's automatic leaves
(outside `opsOf`), every committed conf entry is shaped (`confShaped_of_ops`): `applyEntry` decodes
it, `validConf` takes its transition. These are all the conf entries a committed log holds: the
client's requests (`ProposeConfChange`'s update, `confShaped_proposed`) and raft's automatic leaves
(empty `ConfChangeV2`s, dropped by `opsOf`, decoded by `ccDecodeV2_nil`); there is no bootstrap log,
every replica starting by `RestartNode` on the bootstrap `ConfState`. (So kvreconf needs neither
raft's `committed_confDecodes` nor `committed_emptyV2_joint`.)

## A replica (`lockInv`, `repOwn`)

The applier (the `run` goroutine) writes the replicated state; the other goroutines read some of it
under the lock: `propose` the applied table, `conf` the configuration and the applied index. So the
applier owns the store's map and half of each shared field (`repOwn`, with the precise facts: the
fields are the replicated state of a committed prefix `ap`, `r.index = len ap`, the configuration a
read-only `ConfState` denoting the membership `m` at `ap`'s end, `confAt γ (len ap) m`, with fewer
than `2^61` ids (the store's rule caps every applied change there, `ConfOk`: what a snapshot's
`SnapListsOk` needs, and what the snapshot records keep, `kvrSnapRecOk`); the node never
stops under the applier, which holds a fraction of `nodeRunning`, since `stop` waits for the loop), and the lock the other halves (`repShared`, with what readers need: the applied
table is some committed prefix's). Writing takes the lock. The waiters (keyed by the operation's
datum: `r.waiters` is a `map[string]chan string`) and the waiting reads (by sequence number) are
kv's.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.ConfStep
public import Proof.go_etcd_io.raft.v3.InvNodeRule
public import Spec.go_etcd_io.raft.v3.node__ApplyConfChange
public import Spec.go_etcd_io.raft.v3.node__Advance
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.Stats
public import Proof.go_etcd_io.etcd.cache.v3.Handoff

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvreconf

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

/-- The store's `Storage` struct. -/
abbrev RStorage [GooseExts] := github_com.mit_pdos.etcd_grove.examples.kvreconf.Storage
/-- The store's replica struct. -/
abbrev RReplica [GooseExts] := github_com.mit_pdos.etcd_grove.examples.kvreconf.Replica
/-- The store's cluster struct. -/
abbrev RCluster [GooseExts] := github_com.mit_pdos.etcd_grove.examples.kvreconf.Cluster

abbrev rReplicaTy [GooseExts] [GoGlobalContext] : go.GoType :=
  github_com.mit_pdos.etcd_grove.examples.kvreconf.Replica.ty
abbrev rStorageTy [GooseExts] [GoGlobalContext] : go.GoType :=
  github_com.mit_pdos.etcd_grove.examples.kvreconf.Storage.ty
abbrev rClusterTy [GooseExts] [GoGlobalContext] : go.GoType :=
  github_com.mit_pdos.etcd_grove.examples.kvreconf.Cluster.ty

/-- The namespace of the store's raft cluster. -/
def kvrRaftN : Namespace := nroot.@"kvreconf_raft"
/-- The store's invariant's. -/
def rkvN : Namespace := nroot.@"kvreconf_rkv"
/-- The registry of the snapshots made. -/
def kvrSnapN : Namespace := nroot.@"kvreconf_snaps"

/-- What an operation's atomic update may open: everything but raft's cluster, the store's
invariant, the snapshot registry and the decisions. -/
def kvrMask : CoPset := (((⊤ \ ↑kvrRaftN) \ ↑rkvN) \ ↑kvrSnapN) \ ↑kvrConfN

/-- The ghost names of a store's cluster. -/
structure RNames where
  /-- raft's cluster, in `kvrRaftN` -/
  cluster : Cluster
  /-- the store's history (`ghostVar`, halves: the invariant's and the client's) -/
  val : GName
  /-- the cluster's last operation id (`ghostVar`, halves: the invariant's and the cluster lock's) -/
  opn : GName
  /-- the minted operations, `id ↦ data` (persistent elements) -/
  mint : GName
  /-- each replica's last read sequence number (authority in the invariant) -/
  rseq : GName
  /-- the minted read contexts, `(replica, seq) ↦ context` (persistent elements) -/
  rmint : GName
  /-- the operations' slots, `data ↦ (γq, γk)` -/
  ops : GName
  /-- the cluster's next replica id, a lower bound (`monoNat`: authority in the cluster's lock) -/
  nid : GName
  /-- whether the replicas' stop tokens were taken (`ghostVar` of `Bool`, halves: the cluster's
  lock's and the stopper's, `DefsCluster`) -/
  stp : GName


section mint
variable [GooseExts]

/-- An operation datum's id (`decodeOp`'s first field). -/
def opId (d : List w8) : Option w64 := (decodeOp d).map (·.1)

/-- The datum `d` was minted at its id. -/
def MintedOp (Mi : GMap w64 (List w8)) (d : List w8) : Prop :=
  ∃ i, opId d = some i ∧ Mi !! i = some d

/-- The read context `c` was minted. -/
def MintedRead (RMi : GMap (w64 × w64) (List w8)) (c : List w8) : Prop :=
  ∃ k, RMi !! k = some c

/-- The minting discipline (see the file header). -/
def MintOk (n : w64) (Mi : GMap w64 (List w8)) (RS : GMap w64 w64)
    (RMi : GMap (w64 × w64) (List w8)) (O : GMap (List w8) (GName × GName))
    (U : GSet (List w8)) : Prop :=
  (∀ i d, Mi !! i = some d → uint.Z i ≤ uint.Z n ∧ opId d = some i) ∧
  (∀ r s c, RMi !! (r, s) = some c → ∃ ns, RS !! r = some ns ∧ uint.Z s ≤ uint.Z ns ∧
    ∃ key, (key.length : Int) < 2 ^ 64 ∧ c = readCtxB r s key) ∧
  (∀ d γp, O !! d = some γp → MintedOp Mi d) ∧
  (∀ c, c ∈ U → MintedRead RMi c)

end mint

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvreconf.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]
variable [StorageModel GF] [AllG GF]

/-- The client's half of the store's state `m`. -/
def rkvVal (γr : RNames) (m : KVMap) : IProp GF :=
  iprop(∃ H : List (List w8), ghostVar γr.val (1 : Qp).half H ∗ ⌜kvFold H = m⌝)

/-- An operation's atomic update over the store's state (kv's `opAu`). -/
def opAu (γr : RNames) (f : KVMap → KVMap) (k : List w8) (Φ : List w8 → IProp GF) : IProp GF :=
  iprop(AU <{ ∃∃ (x : KVMap), rkvVal γr x }> @ kvrMask, ∅
    <{ rkvVal γr (f x), COMM Φ (f x k) }>)

/-- An operation's slot (kv's `opSlot`). -/
def opSlot (γr : RNames) (d : List w8) (γp : GName × GName) (H : List (List w8)) : IProp GF :=
  iprop(∃ Φ : List w8 → IProp GF, savedPredOwn γp.1 DFrac.discard Φ ∗
    ( (⌜d ∉ H⌝ ∗ £ 1 ∗ opAu γr (fun x => kvApply x d) (dkey d) Φ)
    ∨ (∃ H0, ⌜H0 ++ [d] <+: H ∧ d ∉ H0⌝ ∗ (Φ (kvFold (H0 ++ [d]) (dkey d)) ∨ token γp.2)) ))

/-- The timeless part of the store's invariant (see the file header). -/
def kvCore (γr : RNames) (ops : List LogEntry) (n : w64) (Mi : GMap w64 (List w8))
    (RS : GMap w64 w64) (RMi : GMap (w64 × w64) (List w8)) (O : GMap (List w8) (GName × GName))
    (U : GSet (List w8)) : IProp GF :=
  iprop(ownCommittedOps γr.cluster ops ∗ ghostVar γr.val (1 : Qp).half (logHist ops) ∗
    ownReadCtxs γr.cluster U ∗ ghostVar γr.opn (1 : Qp).half n ∗
    ghostMapAuth γr.mint 1 Mi ∗ ghostMapAuth γr.rseq 1 RS ∗ ghostMapAuth γr.rmint 1 RMi ∗
    ghostMapAuth γr.ops 1 O ∗ ⌜MintOk n Mi RS RMi O U⌝ ∗
    ⌜∀ d, some d ∈ ops.map odOf → MintedOp Mi d⌝ ∗
    ⌜∀ e ∈ ops, e.isConfChange → ConfShaped e⌝)

instance kvCore_timeless (γr : RNames) (ops : List LogEntry) (n : w64) (Mi : GMap w64 (List w8))
    (RS : GMap w64 w64) (RMi : GMap (w64 × w64) (List w8)) (O : GMap (List w8) (GName × GName))
    (U : GSet (List w8)) : Timeless (kvCore (GF := GF) γr ops n Mi RS RMi O U) := by
  unfold kvCore; infer_instance

def rkvInvBody (γr : RNames) : IProp GF :=
  iprop(∃ (ops : List LogEntry) (n : w64) (Mi : GMap w64 (List w8)) (RS : GMap w64 w64)
      (RMi : GMap (w64 × w64) (List w8)) (O : GMap (List w8) (GName × GName)) (U : GSet (List w8)),
    kvCore γr ops n Mi RS RMi O U ∗ [∗map] d ↦ γp ∈ O, opSlot γr d γp (logHist ops))

/-- The store's invariant (see the file header). -/
def rkvInv (γr : RNames) : IProp GF := inv rkvN (rkvInvBody γr)

instance rkvInv_persistent (γr : RNames) : Persistent (rkvInv (GF := GF) γr) := by
  unfold rkvInv; infer_instance

/-- What a waiter learns with the value `v`: the datum `d`'s answer in a committed log's history
(its key's value right after its first occurrence). -/
def waitP (γr : RNames) (d : List w8) (v : List w8) : IProp GF :=
  iprop(∃ (l : List LogEntry), isCommittedLogLb γr.cluster l ∗ ⌜AnsOk (logHist l) d v⌝)

instance waitP_persistent (γr : RNames) (d v : List w8) : Persistent (waitP (GF := GF) γr d v) := by
  unfold waitP; infer_instance

/-- A lower bound on the store's history (persistent). -/
def kvLb (γr : RNames) (L : List (List w8)) : IProp GF :=
  iprop(∃ (l : List LogEntry), isCommittedLogLb γr.cluster l ∗ ⌜L = logHist l⌝)

instance kvLb_persistent (γr : RNames) (L : List (List w8)) :
    Persistent (kvLb (GF := GF) γr L) := by
  unfold kvLb; infer_instance

/-- What the applier answers a read of the context `c` with (kv's `readAns`): a read state of `c`
at index `i`, and `c`'s key's value after a committed log at least `i` long. -/
def readAns (γr : RNames) (c : List w8) (v : List w8) : IProp GF :=
  iprop(∃ (i : w64) (ap : List LogEntry) (key : List w8),
    readStateOk γr.cluster kvrRaftN c i ∗ isCommittedLogLb γr.cluster ap ∗
    ⌜uint.Z i ≤ (ap.length : Int) ∧ (∃ rp s, decodeReadCtxB c = some (rp, s, key)) ∧
      v = kvFold (logHist ap) key⌝)

/-- A `ReadState` Go value as `Ready` hands it out: its `RequestCtx` slice holds the bytes `c`
read-only, and the read state of `c` at its index (`readStateOk`). Persistent. -/
def rsOk (γ : Cluster) (v : ReadState) : IProp GF :=
  iprop(∃ c : List w8, v.RequestCtx' ↦*□ c ∗ readStateOk γ kvrRaftN c v.Index')

instance rsOk_persistent (γ : Cluster) (v : ReadState) : Persistent (rsOk (GF := GF) γ v) := by
  unfold rsOk; infer_instance

/-- A read's entry in the replica's lock: the context `c` minted at `(id, s)`, and the producer of
its handoff channel. -/
def readWaiterOk (γr : RNames) (id s : w64) (ch : Loc) : IProp GF :=
  iprop(∃ (c : List w8) (γh : HandoffNames),
    (id, s) ↪[γr.rmint]□ c ∗
    isHandoff γh ch (readAns γr c) iprop(True) iprop(False) ∗
    handoffProducer γh false)

/-- An operation's entry in the replica's lock: the producer of its handoff channel. -/
def waiterOk (γr : RNames) (d : List w8) (ch : Loc) : IProp GF :=
  iprop(∃ (γh : HandoffNames),
    isHandoff γh ch (waitP γr d) iprop(True) iprop(False) ∗ handoffProducer γh false)

/-- The applier's half of a replica's replicated state (see the file header), at the committed
prefix `ap`, the configuration `csp` denoting `m` at `ap`'s end (or `nil`, the node stopped), the
index field at `idx` (`len ap` but inside `applyEntry`, which moves it after the entry): the
store's map (the applier's alone), half of each field the other goroutines read under the lock
(`applied`, `cs`, `index`) and half of the applied table, with the precise facts. -/
def repOwn (γr : RNames) (r : Loc) (ap : List LogEntry)
    (idx : w64) (csp : Loc) (m : Membership) (mA : Loc) (A : GMap (List w8) (List w8)) :
    IProp GF :=
  iprop(∃ (mK : Loc) (K : GMap (List w8) (List w8)) (c : ConfStateM),
    "HmK" ∷ r.[RReplica, go!"kv"] ↦ mK ∗
    "HK" ∷ mK ↦$ K ∗
    "HmA" ∷ r.[RReplica, go!"applied"] ↦{DFrac.own (1 : Qp).half} mA ∗
    "HA" ∷ mA ↦${DFrac.own (1 : Qp).half} A ∗
    "Hcs" ∷ r.[RReplica, go!"cs"] ↦{DFrac.own (1 : Qp).half} csp ∗
    "Hidx" ∷ r.[RReplica, go!"index"] ↦{DFrac.own (1 : Qp).half} idx ∗
    "#Hap" ∷ isCommittedLogLb γr.cluster ap ∗
    "%Hlen" ∷ ⌜(ap.length : Int) < 2 ^ 61⌝ ∗
    "%Hval" ∷ ⌜∀ k, (K !! k).getD [] = kvFold (logHist ap) k⌝ ∗
    "%HA" ∷ ⌜AppliedOk A (logHist ap)⌝ ∗
    "#HcsO" ∷ csOpt csp DFrac.discard c ∗
    "%Hcsm" ∷ ⌜confStateIs c m⌝ ∗
    "%Hsz" ∷ ⌜GMap.size m.ids < 2 ^ 61⌝ ∗
    "#Hcfg" ∷ confAt γr.cluster ap.length m)

/-- The lock's half of a replica's replicated state: the other halves of `applied`, `cs`, `index`
and of the applied table, which is the table of some committed prefix (what `propose` answers an
applied operation with); the configuration read-only. -/
def repShared (γr : RNames) (r : Loc) : IProp GF :=
  iprop(∃ (mA : Loc) (A : GMap (List w8) (List w8)) (csp : Loc) (c : ConfStateM) (idx : w64)
      (ap : List LogEntry),
    "HmA" ∷ r.[RReplica, go!"applied"] ↦{DFrac.own (1 : Qp).half} mA ∗
    "HA" ∷ mA ↦${DFrac.own (1 : Qp).half} A ∗
    "Hcs" ∷ r.[RReplica, go!"cs"] ↦{DFrac.own (1 : Qp).half} csp ∗
    "Hidx" ∷ r.[RReplica, go!"index"] ↦{DFrac.own (1 : Qp).half} idx ∗
    "#HcsO" ∷ csOpt csp DFrac.discard c ∗
    "#Hap" ∷ isCommittedLogLb γr.cluster ap ∗
    "%HA" ∷ ⌜AppliedOk A (logHist ap)⌝)

/-- A replica's lock invariant (see the file header). -/
def lockInv (γr : RNames) (id : w64) (r : Loc) : IProp GF :=
  iprop(∃ (ns : w64) (mW : Loc) (W : GMap (List w8) Loc) (mR : Loc) (Rd : GMap w64 Loc),
    "Hrep" ∷ repShared γr r ∗
    "HmW" ∷ r.[RReplica, go!"waiters"] ↦ mW ∗
    "HW" ∷ mW ↦$ W ∗
    "Hwaiters" ∷ ([∗map] d ↦ ch ∈ W, waiterOk γr d ch) ∗
    "Hns" ∷ r.[RReplica, go!"nextRead"] ↦ ns ∗
    "Hseq" ∷ id ↪[γr.rseq] ns ∗
    "HmR" ∷ r.[RReplica, go!"reads"] ↦ mR ∗
    "HRd" ∷ mR ↦$ Rd ∗
    "%HRdom" ∷ ⌜∀ s ch, Rd !! s = some ch → uint.Z s ≤ uint.Z ns⌝ ∗
    "Hreads" ∷ [∗map] s ↦ ch ∈ Rd, readWaiterOk γr id s ch)

/-- **The applier's view of its node** (see the file header), the committed log delivered `l`
applied up to `k` at the membership `m`: the node's configuration view at `m`, every conf entry from
the view's index to `k` rejected (`skippedIn`). -/
def appNode (γr : RNames) (n : Loc) (l : List LogEntry) (k : Nat) (m : Membership) : IProp GF :=
  iprop(∃ v : ConfigView, nodeConfig n γr.cluster kvrRaftN v ∗
      deliveredLogLb n γr.cluster kvrRaftN l ∗ skippedIn γr.cluster l v.applied k ∗
      ⌜v.membership = m ∧ v.applied ≤ k⌝)

/-- What a snapshot the store made promises: a committed prefix `L` of its index, the membership
there, its data the store's encoded state of `L`. -/
def kvrSnapRecOk (γr : RNames) (s : SnapRec) : IProp GF :=
  iprop(∃ L : List LogEntry, isCommittedLogLb γr.cluster L ∗ confAt γr.cluster L.length s.conf ∗
    ⌜L.length = s.index ∧ kvSnapOk L s.data ∧ GMap.size s.conf.ids < 2 ^ 61⌝)

instance kvrSnapRecOk_persistent (γr : RNames) (s : SnapRec) :
    Persistent (kvrSnapRecOk (GF := GF) γr s) := by
  unfold kvrSnapRecOk; infer_instance

/-- **The store's registry of the snapshots made** (an invariant). -/
def kvrSnapInv (γr : RNames) : IProp GF :=
  inv kvrSnapN iprop(∃ S : List SnapRec, ownSnapsMade γr.cluster S ∗
    [∗list] s ∈ S, kvrSnapRecOk γr s)

instance kvrSnapInv_persistent (γr : RNames) : Persistent (kvrSnapInv (GF := GF) γr) := by
  unfold kvrSnapInv; infer_instance

/-- **The store's cluster** (persistent): raft's cluster, its conf entries decided by `kvrRule`
from the bootstrap voters `vs`, the registry of the snapshots made, and the store's invariant. -/
def kvrCluster (γr : RNames) (vs : List w64) : IProp GF :=
  iprop(isCluster γr.cluster kvrRaftN ∗ confPolicy γr.cluster kvrConfN kvrRule ∗
    confAt γr.cluster 0 (Membership.simple (GMap.listToSet vs)) ∗ kvrSnapInv γr ∗ rkvInv γr)

instance kvrCluster_persistent (γr : RNames) (vs : List w64) :
    Persistent (kvrCluster (GF := GF) γr vs) := by
  unfold kvrCluster; infer_instance

/-- **Replica `id` at `r`** (persistent), on node `n` of the store's cluster, with the storage `st`
and the statistics `sts`: its fields read-only, its lock. -/
def isReplica (γr : RNames) (vs : List w64) (id : w64) (r n st sts : Loc) : IProp GF :=
  iprop(
    "#Hpkg" ∷ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kvreconf ∗
    "#Hid" ∷ r.[RReplica, go!"id"] ↦□ id ∗
    "#Hnode" ∷ r.[RReplica, go!"node"] ↦□ interface.mkOk (go.GoType.PointerType node.ty) #n ∗
    "#Hst" ∷ r.[RReplica, go!"storage"] ↦□ st ∗
    "#Hsts" ∷ r.[RReplica, go!"stats"] ↦□ sts ∗
    "#Hstats" ∷ isStats sts ∗
    "#HisNode" ∷ isNode n γr.cluster kvrRaftN id ∗
    "#Hcl" ∷ kvrCluster γr vs ∗
    "#Hmu" ∷ sync.isMutex (r.[RReplica, go!"mu"]) (lockInv γr id r))

set_option synthInstance.maxHeartbeats 400000 in
set_option synthInstance.maxSize 4096 in
instance isReplica_persistent (γr : RNames) (vs : List w64) (id : w64) (r n st sts : Loc) :
    Persistent (isReplica (GF := GF) γr vs id r n st sts) := by
  unfold isReplica; infer_instance

end ghost

end kvreconf
end EtcdGrove
end Perennial
