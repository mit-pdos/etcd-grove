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

## A replica (`lockInv`)

Under its lock, unlike kv's (where the applier owned them): the store's map, the applied table, the
configuration `r.cs` and the applied index `r.index` -- `propose`, `maybeSnapshot`, `conf` and
`contents` read them --, at a committed prefix `ap` (`r.index = len ap`), the map and the table
`ap`'s replicated state (`kvFold`, `AppliedOk` of `logHist ap`); the configuration a read-only
`ConfState` denoting the membership `m` at `ap`'s end (`confAt γ (len ap) m`) -- or, after its
node answered a stopped `ApplyConfChange`, `nil` with the node stopped (`nodeStopped`, `RaftAssume`).
The applier keeps half of a ghost variable at `(len ap, cs)` (`γp.app`), so it knows what it wrote
(a committed prefix is its length's, `isCommittedLogLb_agree`; the membership its, `confAt_agree`).
The waiters (keyed by the operation's datum: `r.waiters` is a `map[string]chan string`) and the
waiting reads (by sequence number) are kv's.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.ConfStep
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.RaftAssume
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

/-- A replica's ghost names: the applier's record of the replicated state it wrote. -/
structure RepNames where
  app : GName

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
    ∃ key, c = readCtxB r s key) ∧
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
    ⌜∀ d, some d ∈ ops.map odOf → MintedOp Mi d⌝)

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

/-- The replicated state a replica's lock holds at the committed prefix `ap` (see the file
header), its configuration `csp` denoting `m` at `ap`'s end, or `nil` with the node stopped. -/
def repState (RA : RaftAssume (GF := GF)) (γr : RNames) (n : Loc) (r : Loc) (ap : List LogEntry)
    (csp : Loc) (m : Membership) : IProp GF :=
  iprop(∃ (mK : Loc) (K : GMap (List w8) (List w8)) (mA : Loc) (A : GMap (List w8) (List w8))
      (c : ConfStateM),
    "HmK" ∷ r.[RReplica, go!"kv"] ↦ mK ∗
    "HK" ∷ mK ↦$ K ∗
    "HmA" ∷ r.[RReplica, go!"applied"] ↦ mA ∗
    "HA" ∷ mA ↦$ A ∗
    "Hcs" ∷ r.[RReplica, go!"cs"] ↦ csp ∗
    "Hidx" ∷ r.[RReplica, go!"index"] ↦ W64 ap.length ∗
    "#Hap" ∷ isCommittedLogLb γr.cluster ap ∗
    "%Hlen" ∷ ⌜(ap.length : Int) < 2 ^ 61⌝ ∗
    "%Hval" ∷ ⌜∀ k, (K !! k).getD [] = kvFold (logHist ap) k⌝ ∗
    "%HA" ∷ ⌜AppliedOk A (logHist ap)⌝ ∗
    "#HcsO" ∷ csOpt csp DFrac.discard c ∗
    "#Hcfg" ∷ ((⌜confStateIs c m⌝ ∗ confAt γr.cluster ap.length m) ∨
               (⌜csp = null⌝ ∗ RA.nodeStopped n γr.cluster kvrRaftN)))

/-- A replica's lock invariant (see the file header). -/
def lockInv (RA : RaftAssume (GF := GF)) (γr : RNames) (γp : RepNames) (id : w64) (n r : Loc) :
    IProp GF :=
  iprop(∃ (ap : List LogEntry) (csp : Loc) (m : Membership) (ns : w64) (mW : Loc)
      (W : GMap (List w8) Loc) (mR : Loc) (Rd : GMap w64 Loc),
    "Hrep" ∷ repState RA γr n r ap csp m ∗
    "Happ" ∷ ghostVar γp.app (1 : Qp).half (ap.length, csp) ∗
    "HmW" ∷ r.[RReplica, go!"waiters"] ↦ mW ∗
    "HW" ∷ mW ↦$ W ∗
    "Hwaiters" ∷ ([∗map] d ↦ ch ∈ W, waiterOk γr d ch) ∗
    "Hns" ∷ r.[RReplica, go!"nextRead"] ↦ ns ∗
    "Hseq" ∷ id ↪[γr.rseq] ns ∗
    "HmR" ∷ r.[RReplica, go!"reads"] ↦ mR ∗
    "HRd" ∷ mR ↦$ Rd ∗
    "%HRdom" ∷ ⌜∀ s ch, Rd !! s = some ch → uint.Z s ≤ uint.Z ns⌝ ∗
    "Hreads" ∷ [∗map] s ↦ ch ∈ Rd, readWaiterOk γr id s ch)

/-- What a snapshot the store made promises: a committed prefix `L` of its index, the membership
there, its data the store's encoded state of `L`. -/
def kvrSnapRecOk (γr : RNames) (s : SnapRec) : IProp GF :=
  iprop(∃ L : List LogEntry, isCommittedLogLb γr.cluster L ∗ confAt γr.cluster L.length s.conf ∗
    ⌜L.length = s.index ∧ kvSnapOk L s.data⌝)

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

end ghost

end kvreconf
end EtcdGrove
end Perennial
