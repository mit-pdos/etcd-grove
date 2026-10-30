/-
Lean-first (no Rocq counterpart).

# The key-value store's predicates (2026-10-10; 2026-10-14, stage R; the store, 2026-10-19)

## The client-facing state (2026-10-27: over raft's node API, `InvNode.lean`)

A cluster of replicas shares raft's cluster `γr.cluster`, in the store's namespace `kvRaftN` (the
caller's, for the draft API). The store's invariant (`rkvInv`) owns raft's committed requested
entries (`ownCommittedOps`: every entry the store asked for that committed, raft's fillers
left out), and the store's history is their data, first occurrences (`logHist`, `Base.lean`); the
invariant keeps half of a ghost variable at the history, and the store's state is its fold
(`kvFold`: every key's value). A client holds `rkvVal γr m`, the other half, at a history whose
fold is `m`. `Put`/`Get`/`Append` hand their atomic update over `rkvVal` to `do`, which mints the
operation and keeps the update in the operation's slot (`opSlot`, with a later credit), and gives
every `Node.Propose` of it -- a retry of a dropped proposal included -- a new atomic update over the
committed requested entries (`kv_propAu`, `Lemmas.lean`; raft fires each at most once): the history
moves by the datum, and at its first occurrence the update runs the client's from the slot -- the
linearization point. The result -- the key's value after the operation -- stays in the slot until
the client collects it with its ticket (`kv_collect`). Raft's own entries (fillers) leave the
committed requested entries alone, so the store gives no update for them.

## Minting

The store mints each operation's datum, and each read's context, at the operation's `(replica,
seq)` (`MintOk`): the invariant holds each replica's last sequence number (`seq`, the replica's
element under its lock) and the persistent record of each minted datum (`mint`); every committed
datum, every slot's datum and every read context used (`ownReadCtxs`, also the invariant's)
was minted (only the store's updates move the committed requested entries). So a new sequence
number mints a datum nobody had: not in the history (its slot starts pending), not a used read
context (`readCtx_commit` takes it). A datum or a read state's context with a minted key is
the one minted there (`kv_committed_minted`, `kv_read_minted`: a read state's context was
committed, `readStateOk_used`).

## Lower bounds on the history

`kvLb γr L` (persistent): the store's history has the prefix `L`: `L` is the history of a
committed log (`isCommittedLogLb`), whose requested entries are a prefix of the store's
(`ownCommittedOps_lb_prefix`); and conversely the history now is such an `L`
(`kvLb_current`). `Read` takes one at its call and returns its key's value after a longer one: it
commits its context, once, to the read seeing the requested entries of `L`'s log
(`kv_mint_read`, `kv_readAu`), and a read state of it gives that back (`readStateOk_ctx`).

## A replica

Its lock protects the next sequence number (a replica that has used up `2^64 - 1` of them
stops, in Go: `do` and `Read` loop forever at `maxSeq`; until 2026-10-19 operation credits,
`opCred`, which a caller had to pass in, bounded them), and the waiters: each a handoff
channel whose producer token the lock holds, for the operation minted at `(id, seq)`, on
which the replica's applier sends the key's value after the operation, with where the
operation's entry first is in a committed log (`waitP`); and (2026-10-13) the reads waiting
for their answer (`readsOwn`): each a handoff channel for the read context minted at `(id,
seq)`, on which the applier sends a read index of the context with its key's value after a
committed log at least that long (`readAns`; the reader, which committed the context, turns it
into a value after its lower bound). The applier's own state -- the store's map, the applied-encodings
table, and the committed prefix it applied (`runOwn`) -- is the `run` goroutine's alone
(only `apply` and `answer` touch those fields, holding the lock for the waiters).

## Raft's `Ready`s

The entries of a `Ready` are the model's records (`EntryM`, what the getters of a `*pb.Entry`
return) of the draft's log entries (`LogEntry.toEntryM`); its messages are owned pointers,
sent (`sendSpec`, `sentMsg`); a `ReadState`'s context is its bytes (`rsOk`).

## The storage

`*kv.Storage` is a raft `Storage` (`KvStorage.lean`, `KVStorageInstance.lean`; 2026-10-30, stage F
of the client repair, from kvreconf's): the instance of `StorageModel` for the store
(`kvStorageModel`), given a registry (`KVStor`: a ghost map from a `Storage` struct to its
`MemoryStorage` and that storage's ghost names, whose authority is in `kvStorInv`), so that a
storage's ranges are of its own names. What the applier holds of it (`runStor`) is persistent:
the storage's invariant at the API's justifications (`kvJ`), the stored snapshot open for writes
(`memSnapLb γs 0`), and the voters.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kv.KvStorage
public import Proof.go_etcd_io.raft.v3.ConfPolicy
public import Proof.go_etcd_io.etcd.cache.v3.Handoff

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

/-- The store's replica struct, `KV`. -/
abbrev RKV [GooseExts] := github_com.mit_pdos.etcd_grove.examples.kv.KV

abbrev rKVTy [GooseExts] [GoGlobalContext] : go.GoType :=
  github_com.mit_pdos.etcd_grove.examples.kv.KV.ty

/-! ## The store's ghost state -/

/-- The ghost names of a store's cluster. -/
structure RKVNames where
  /-- raft's cluster (`Cluster`), in the store's namespace `kvRaftN` -/
  cluster : Cluster
  /-- the store's history (`ghostVar`, halves: `rkvInv`'s and the client's, `rkvVal`) -/
  val : GName
  /-- each replica's last sequence number (a ghost map, its authority in `rkvInv`) -/
  seq : GName
  /-- the minted operations and read contexts, `(replica, seq) ↦ data` (persistent elements) -/
  mint : GName
  /-- the operations' slots, `data ↦ (γq, γk)` (persistent elements, authority in `rkvInv`): each
  holds the client's atomic update until the datum's first committed occurrence, then its result
  or the client's ticket `γk` (`opSlot`) -/
  ops : GName

/-- The namespace the store allocates its raft cluster in (the caller's, for raft's draft API). -/
def kvRaftN : Namespace := nroot.@"kv_raft"

def rkvN : Namespace := nroot.@"rkv"

/-- What `Put`/`Get`/`Append`'s atomic update may open: everything but raft's cluster and the
store's invariant. -/
def kvMask : CoPset := (⊤ \ ↑kvRaftN) \ ↑rkvN

theorem rkvN_raftN : (↑rkvN : CoPset) ⊆ ⊤ \ ↑kvRaftN :=
  mask_ndot_ne' nroot "rkv" "kv_raft" (by decide)

theorem raftN_regN : (↑kvRaftN : CoPset) ⊆ ⊤ \ ↑rkvN :=
  mask_ndot_ne' nroot "kv_raft" "rkv" (by decide)

/-- The datum `d` was minted, at its key (its replica and sequence number). -/
def Minted [GooseExts] (Mi : GMap (w64 × w64) (List w8)) (d : List w8) : Prop :=
  ∃ k, opKey d = some k ∧ Mi !! k = some d

/-- The minting discipline (see the file header): every minted key is at most its replica's last
sequence number; the operations' slots `O` and the read contexts used `U` are minted. -/
def MintOk [GooseExts] (S : GMap w64 w64) (Mi : GMap (w64 × w64) (List w8))
    (O : GMap (List w8) (GName × GName)) (U : GSet (List w8)) : Prop :=
  (∀ i s d, Mi !! (i, s) = some d → ∃ n, S !! i = some n ∧ uint.Z s ≤ uint.Z n) ∧
  (∀ d γp, O !! d = some γp → Minted Mi d) ∧
  (∀ c, c ∈ U → Minted Mi c)

section ccfg
variable [GooseExts]

/-- The voters of the store's cluster. -/
abbrev kvVoters : List w64 := [W64 1, W64 2, W64 3]

/-- **The committed requested entries are normal** (2026-10-30, stage F: the store proposes no
configuration change since `RemoveMember` was removed, D4): every entry the store asked for is a
`Node.Propose`'s (`kv_propAu`), of type `0`. What `run` needs to refute a committed conf entry (with
`committed_emptyV2_joint` for raft's own empty `ConfChangeV2`, which no simple configuration
has). Until 2026-10-30 `RmReqs`: `RemoveMember`'s changes of non-voters. -/
def NormalReqs (ops : List LogEntry) : Prop :=
  ∀ e ∈ ops, e.type = W32 0

end ccfg

/-- A replica's ghost names: none of its own (2026-10-27: until then its raft node's, which raft's
draft API keeps). -/
structure RepNames where

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kv.Assumptions]
variable [KVStor GF]

/-- The client's half of the store's state `m`: half of the history's ghost variable, at a
history whose fold is `m`. -/
def rkvVal (γr : RKVNames) (m : KVMap) : IProp GF :=
  iprop(∃ H : List (List w8), ghostVar γr.val (1 : Qp).half H ∗ ⌜kvFold H = m⌝)

/-- An operation's atomic update over the store's state, the state moving by `f`, answering
key `k`'s value after it (`Put`/`Get`/`Append` give `kvNext kind key val` and `key`; a slot
keeps it as `kvApply · d` and `dkey d`). -/
def opAu (γr : RKVNames) (f : KVMap → KVMap) (k : List w8) (Φ : List w8 → IProp GF) : IProp GF :=
  iprop(AU <{ ∃∃ (x : KVMap), rkvVal γr x }> @ kvMask, ∅
    <{ rkvVal γr (f x), COMM Φ (f x k) }>)

/-- An operation's slot, for the store's history `H`: the result predicate (tied to `γp.1`), and
either the client's update with a later credit, while `d` is not in the history, or -- once `d`
first occurred, after the history `H0` -- the update's result at the key's value after
`H0 ++ [d]` or the client's ticket `γp.2`. -/
def opSlot (γr : RKVNames) (d : List w8) (γp : GName × GName) (H : List (List w8)) : IProp GF :=
  iprop(∃ Φ : List w8 → IProp GF, savedPredOwn γp.1 DFrac.discard Φ ∗
    ( (⌜d ∉ H⌝ ∗ £ 1 ∗ opAu γr (fun x => kvApply x d) (dkey d) Φ)
    ∨ (∃ H0, ⌜H0 ++ [d] <+: H ∧ d ∉ H0⌝ ∗ (Φ (kvFold (H0 ++ [d]) (dkey d)) ∨ token γp.2)) ))

/-- The timeless part of the store's invariant: raft's committed requested entries `ops` (the
client's, `ownCommittedOps`) -- the history is their data's (`logHist`) --, half of the
history's ghost variable, the read contexts used (`ownReadCtxs`), the sequence numbers, the
mint and the slots' registry. -/
def kvCore (γr : RKVNames) (ops : List LogEntry) (S : GMap w64 w64)
    (Mi : GMap (w64 × w64) (List w8)) (O : GMap (List w8) (GName × GName)) (U : GSet (List w8)) :
    IProp GF :=
  iprop(ownCommittedOps γr.cluster ops ∗ ghostVar γr.val (1 : Qp).half (logHist ops) ∗
    ownReadCtxs γr.cluster U ∗
    ghostMapAuth γr.seq 1 S ∗ ghostMapAuth γr.mint 1 Mi ∗ ghostMapAuth γr.ops 1 O ∗
    ⌜MintOk S Mi O U⌝ ∗
    -- every datum committed was minted (only the store's updates move `ops`)
    ⌜∀ d, some d ∈ ops.map odOf → Minted Mi d⌝ ∗
    -- the store proposes no conf change
    ⌜NormalReqs ops⌝)

instance kvCore_timeless (γr : RKVNames) (ops : List LogEntry) (S : GMap w64 w64)
    (Mi : GMap (w64 × w64) (List w8)) (O : GMap (List w8) (GName × GName)) (U : GSet (List w8)) :
    Timeless (kvCore (GF := GF) γr ops S Mi O U) := by
  unfold kvCore; infer_instance

def rkvInvBody (γr : RKVNames) : IProp GF :=
  iprop(∃ (ops : List LogEntry) (S : GMap w64 w64) (Mi : GMap (w64 × w64) (List w8))
      (O : GMap (List w8) (GName × GName)) (U : GSet (List w8)),
    kvCore γr ops S Mi O U ∗ [∗map] d ↦ γp ∈ O, opSlot γr d γp (logHist ops))

/-- See the file header. -/
def rkvInv (γr : RKVNames) : IProp GF := inv rkvN (rkvInvBody γr)

instance rkvInv_persistent (γr : RKVNames) : Persistent (rkvInv (GF := GF) γr) := by
  unfold rkvInv; infer_instance

/-- What a waiter learns with the value `v`: the operation's datum `d` first occurs at
`m` in a committed log, and `v` is its key's value after it. -/
def waitP (γr : RKVNames) (d : List w8) (v : List w8) : IProp GF :=
  iprop(∃ (l : List LogEntry) (ods : List (Option (List w8))) (m : Nat),
    isCommittedLogLb γr.cluster l ∗ ⌜ods = l.map odOf⌝ ∗
    ⌜ods[m]? = some (some d) ∧ d ∉ histOf (ods.take m) ∧
      v = kvFold (histOf (ods.take m) ++ [d]) (dkey d)⌝)

/-- A lower bound on the store's history (see the file header; persistent). -/
def kvLb (γr : RKVNames) (L : List (List w8)) : IProp GF :=
  iprop(∃ (l : List LogEntry), isCommittedLogLb γr.cluster l ∗ ⌜L = logHist l⌝)

instance kvLb_persistent (γr : RKVNames) (L : List (List w8)) :
    Persistent (kvLb (GF := GF) γr L) := by
  unfold kvLb; infer_instance

/-- What the applier answers a read of the context `c` with: a read state of `c` at index `i`
(`readStateOk`), and the value `v` of `c`'s key after a committed log `ap` at least `i`
long. The reader, which committed `c` to its predicate (`isReadCtx`), turns it into a value
after its lower bound. -/
def readAns (γr : RKVNames) (c : List w8) (v : List w8) : IProp GF :=
  iprop(∃ (i : w64) (ap : List LogEntry),
    readStateOk γr.cluster kvRaftN c i ∗ isCommittedLogLb γr.cluster ap ∗
    ⌜uint.Z i ≤ (ap.length : Int) ∧ v = kvFold (logHist ap) (dkey c)⌝)

/-- A read's entry in the lock's invariant: the context `c` minted at `(id, s)`, and the producer
of its handoff channel. -/
def readWaiterOk (γr : RKVNames) (id s : w64) (ch : Loc) : IProp GF :=
  iprop(∃ (c : List w8) (γh : HandoffNames),
    (id, s) ↪[γr.mint]□ c ∗
    isHandoff γh ch (readAns γr c) iprop(True) iprop(False) ∗
    handoffProducer γh false)

/-- A replica's waiting reads (the lock's), each of a sequence number at most `ns`. -/
def readsOwn (γr : RKVNames) (id : w64) (r : Loc) (ns : w64) : IProp GF :=
  iprop(∃ (mR : Loc) (Rd : GMap w64 Loc),
    "HmR" ∷ r.[RKV, go!"reads"] ↦ mR ∗
    "HRd" ∷ mR ↦$ Rd ∗
    "%HRdom" ∷ ⌜∀ s ch, Rd !! s = some ch → uint.Z s ≤ uint.Z ns⌝ ∗
    "Hreads" ∷ [∗map] s ↦ ch ∈ Rd, readWaiterOk γr id s ch)

theorem readsOwn_mono (γr : RKVNames) (id : w64) (r : Loc) (ns ns' : w64)
    (h : uint.Z ns ≤ uint.Z ns') :
    readsOwn (GF := GF) γr id r ns ⊢ readsOwn γr id r ns' := by
  iintro H
  unfold readsOwn
  iNamed H
  iexists mR, Rd
  iframe HmR HRd Hreads
  ipureintro
  intro s ch Hs
  have := HRdom s ch Hs
  omega

/-- A waiter's entry in the lock's invariant: the operation minted at `(id, s)`, and the
producer of its handoff channel. -/
def waiterOk (γr : RKVNames) (id s : w64) (ch : Loc) : IProp GF :=
  iprop(∃ (d : List w8) (γh : HandoffNames), (id, s) ↪[γr.mint]□ d ∗
    isHandoff γh ch (waitP γr d) iprop(True) iprop(False) ∗ handoffProducer γh false)

/-- A replica's lock invariant (see the file header). -/
def lockInv (γr : RKVNames) (γp : RepNames) (id : w64) (r : Loc) : IProp GF :=
  iprop(∃ (ns : w64) (mW : Loc) (W : GMap w64 Loc),
    "Hns" ∷ r.[RKV, go!"nextSeq"] ↦ ns ∗
    "HmW" ∷ r.[RKV, go!"waiters"] ↦ mW ∗
    "HW" ∷ mW ↦$ W ∗
    "Hseq" ∷ id ↪[γr.seq] ns ∗
    "%HWdom" ∷ ⌜∀ s ch, W !! s = some ch → uint.Z s ≤ uint.Z ns⌝ ∗
    "Hwaiters" ∷ ([∗map] s ↦ ch ∈ W, waiterOk γr id s ch) ∗
    "Hrds" ∷ readsOwn γr id r ns)

end ghost

/-! ## The store's cluster (2026-10-28, stage U4a: raft's cluster with snapshots and
reconfiguration, `InvNodeRule.lean`; 2026-10-30, stage F: the decisions through `confPolicy`)

The store's raft cluster is `isCluster`'s, its conf entries decided by the store's rule `kvRule`
(each conf entry's change as `proto.Unmarshal` decodes it), recorded by raft's decision authority
(`confPolicy γ kvConfN kvRule`, `ConfPolicy.lean`), from the voters' membership `kvMembership`.
The store proposes no conf change (`NormalReqs`), so no committed entry is one and every position
keeps `kvMembership` (`skippedIn_noConf`, `confAt_skipped`). The snapshots the replicas make are in
raft's registry (`ownSnapsMade`), which the store keeps in an invariant (`kvSnapInv`), each record
with what it promises (`kvSnapRecOk`, kvreconf's: until 2026-10-30 also the voters' membership and
no conf entry in the prefix): the committed prefix it covers, the membership there, its data the
store's encoded state of that prefix (`kvSnapOk`). -/

section cluster
variable [GooseExts]

/-- The store's rule: a conf entry's change, decoded (`ccDecode`). -/
def kvRule : ConfRule := fun _ _ e => ccDecode e

/-- The membership of the store's voters. -/
abbrev kvMembership : Membership := Membership.simple (GMap.listToSet kvVoters)

end cluster

def kvSnapN : Namespace := nroot.@"kv_snaps"

/-- The namespace of the store's decision authority (`confPolicy`). -/
def kvConfN : Namespace := nroot.@"kv_conf"

section clusterI
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kv.Assumptions]
variable [KVStor GF]

/-- What a snapshot the store made promises: a committed prefix `L` of its index, the membership
there, its data the store's encoded state of `L`. -/
def kvSnapRecOk (γr : RKVNames) (s : SnapRec) : IProp GF :=
  iprop(∃ L : List LogEntry, isCommittedLogLb γr.cluster L ∗ confAt γr.cluster L.length s.conf ∗
    ⌜L.length = s.index ∧ kvSnapOk L s.data⌝)

instance kvSnapRecOk_persistent (γr : RKVNames) (s : SnapRec) :
    Persistent (kvSnapRecOk (GF := GF) γr s) := by
  unfold kvSnapRecOk; infer_instance

instance kvSnapRecOk_timeless (γr : RKVNames) (s : SnapRec) :
    Timeless (kvSnapRecOk (GF := GF) γr s) := by
  unfold kvSnapRecOk; infer_instance

/-- **The store's registry of the snapshots made** (an invariant). -/
def kvSnapInv (γr : RKVNames) : IProp GF :=
  inv kvSnapN iprop(∃ S : List SnapRec, ownSnapsMade γr.cluster S ∗
    [∗list] s ∈ S, kvSnapRecOk γr s)

instance kvSnapInv_persistent (γr : RKVNames) : Persistent (kvSnapInv (GF := GF) γr) := by
  unfold kvSnapInv; infer_instance

/-- **The store's cluster** (persistent): raft's cluster with snapshots and reconfiguration, its
conf entries decided by `kvRule`, the membership of no entry the voters', and the store's registry
of the snapshots made. -/
def kvCluster (γr : RKVNames) : IProp GF :=
  iprop(isCluster γr.cluster kvRaftN ∗ confPolicy γr.cluster kvConfN kvRule ∗
    confAt γr.cluster 0 kvMembership ∗ kvSnapInv γr)

instance kvCluster_persistent (γr : RKVNames) : Persistent (kvCluster (GF := GF) γr) := by
  unfold kvCluster; infer_instance

end clusterI

section ghost2
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kv.Assumptions]
variable [KVStor GF]

/-- Replica `id` at `r`, on node `n` of the store's cluster (`kvCluster`),
with the storage `st` (persistent). -/
def isReplica (γr : RKVNames) (γp : RepNames) (r : Loc) (id : w64) (n st : Loc) : IProp GF :=
  iprop(
    "#Hpkg" ∷ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kv ∗
    "#Hid" ∷ r.[RKV, go!"id"] ↦□ id ∗
    "#Hnode" ∷ r.[RKV, go!"node"] ↦□ interface.mkOk (go.GoType.PointerType node.ty) #n ∗
    "#Hst" ∷ r.[RKV, go!"storage"] ↦□ st ∗
    "#Hsrec" ∷ (∃ (ms : Loc) (γs : MemStorNames), kvStorRec st ms γs) ∗
    "#HisNode" ∷ isNode n γr.cluster kvRaftN id ∗
    "#Hcl" ∷ kvCluster γr ∗
    "#Hmu" ∷ sync.isMutex (r.[RKV, go!"mu"]) (lockInv γr γp id r) ∗
    "#Hinv" ∷ rkvInv γr)

set_option synthInstance.maxHeartbeats 400000 in
set_option synthInstance.maxSize 4096 in
instance isReplica_persistent (γr : RKVNames) (γp : RepNames) (r : Loc) (id : w64) (n st : Loc) :
    Persistent (isReplica (GF := GF) γr γp r id n st) := by
  unfold isReplica; infer_instance

/-- A replica (persistent; what `Put`, `Get`, `Append` and `Read` take). -/
def isKV (γr : RKVNames) (γp : RepNames) (r : Loc) : IProp GF :=
  iprop(∃ (id : w64) (n st : Loc), isReplica γr γp r id n st)

instance isKV_persistent (γr : RKVNames) (γp : RepNames) (r : Loc) :
    Persistent (isKV (GF := GF) γr γp r) := by
  unfold isKV; infer_instance

/-- The `send` callback (`func([]*pb.Message)`): it takes the messages of a `Ready` as `Ready`
hands them out: the slice of their pointers, owned, each message owned at `readyDq`, sent
(`sentMsg`), with its credits (`msgCredits`). Delivering them to the peers'
`Node.Step` is the transport's. -/
def sendSpec (f : GoFunc) (γ : Cluster) : IProp GF :=
  iprop(□ ∀ (src : w64) (msl : GoSlice) (ms : List QMsg),
    {{ msl ↦* ms.map QMsg.loc ∗
        [∗list] q ∈ ms, msgOwn q.loc (readyDq q.st) q.st ∗ sentMsg γ kvRaftN src q.st ∗
          msgCredits γ kvRaftN q.st }}
      (App (Val #f) (Val #msl))
    {{ RET #(); True }})

instance sendSpec_persistent (f : GoFunc) (γ : Cluster) :
    Persistent (sendSpec (GF := GF) f γ) := by
  unfold sendSpec; infer_instance

/-- A `ReadState` Go value as `Ready` hands it out: its `RequestCtx` slice holds the bytes `c`
read-only, and the read state of `c` at its index (`readStateOk`). Persistent. -/
def rsOk (γ : Cluster) (v : ReadState) : IProp GF :=
  iprop(∃ c : List w8, v.RequestCtx' ↦*□ c ∗ readStateOk γ kvRaftN c v.Index')

instance rsOk_persistent (γ : Cluster) (v : ReadState) : Persistent (rsOk (GF := GF) γ v) := by
  unfold rsOk; infer_instance

/-- The applier's state (the `run` goroutine's): the store's map, every key's value (a key it
lacks has the value `[]`, as for Go's lookup), and the applied-encodings table (each with its
answer, `AppliedOk`), at the committed log `ap` it applied. -/
def runOwn (γr : RKVNames) (r : Loc) (ap : List LogEntry) : IProp GF :=
  iprop(∃ (mK : Loc) (K : GMap (List w8) (List w8)) (mA : Loc) (A : GMap (List w8) (List w8))
      (ods : List (Option (List w8))),
    "HmK" ∷ r.[RKV, go!"kv"] ↦ mK ∗
    "HK" ∷ mK ↦$ K ∗
    "HmA" ∷ r.[RKV, go!"applied"] ↦ mA ∗
    "HA" ∷ mA ↦$ A ∗
    "#Hap" ∷ isCommittedLogLb γr.cluster ap ∗
    "%Hods" ∷ ⌜ods = ap.map odOf⌝ ∗
    "%Hval" ∷ ⌜∀ k, (K !! k).getD [] = kvFold (histOf ods) k⌝ ∗
    "%HA" ∷ ⌜AppliedOk A (histOf ods)⌝)

/-- **What the applier holds of its storage `st`** (persistent; 2026-10-30, stage F: until then
the storage's snapshot token at the application's view, its certificate registry and cap):
the storage's record, its `MemoryStorage`'s invariant at node `id`'s justifications (`kvJ`: what
`ApplySnapshot`, `CreateSnapshot` and `Compact` take), the stored snapshot open for writes
(`memSnapLb γs 0`, `memSnapNone_open`; the applier is the storage's only writer, so it needs no
token), and the cluster's voters (`Storage.voters`), the configuration of every snapshot it takes. -/
def runStor (γr : RKVNames) (id : w64) (st : Loc) : IProp GF :=
  iprop(∃ (ms : Loc) (γs : MemStorNames) (vsl : GoSlice),
    kvStorRec st ms γs ∗ memStorInvP ms γs (kvJ γr.cluster id) ∗ memSnapLb γs 0 ∗
    st.[RStorage, go!"voters"] ↦□ vsl ∗ vsl ↦*□ kvVoters)

instance runStor_persistent (γr : RKVNames) (id : w64) (st : Loc) :
    Persistent (runStor (GF := GF) γr id st) := by
  unfold runStor; infer_instance

/-- **The applier's view of its node** (kvreconf's, 2026-10-30), the committed log delivered `l`
applied up to `k` at the membership `m`: the node's configuration view at `m`, every conf entry
from the view's index to `k` rejected (`skippedIn`; the store's log has none). -/
def appNode (γr : RKVNames) (n : Loc) (l : List LogEntry) (k : Nat) (m : Membership) : IProp GF :=
  iprop(∃ v : ConfigView, nodeConfig n γr.cluster kvRaftN v ∗
      deliveredLogLb n γr.cluster kvRaftN l ∗ skippedIn γr.cluster l v.applied k ∗
      ⌜v.membership = m ∧ v.applied ≤ k⌝)

/-- **The applier's frozen delivered entries** above the known compaction point `c` (kvreconf's,
2026-10-30): every delivered entry of `D` past `c` is frozen in the storage, with the delivered
log's terms. `CreateSnapshot` takes the frozen entry at the applied index, `Compact` the one at
its target. -/
def frozenTo (γs : MemStorNames) (c : Nat) (D : List LogEntry) : IProp GF :=
  memLog γs (c + 1) DFrac.discard ((LogEntry.toEntries D 0).drop c)

instance frozenTo_persistent (γs : MemStorNames) (c : Nat) (D : List LogEntry) :
    Persistent (frozenTo (GF := GF) γs c D) := by
  unfold frozenTo; infer_instance

end ghost2

end EtcdGrove
end Perennial
