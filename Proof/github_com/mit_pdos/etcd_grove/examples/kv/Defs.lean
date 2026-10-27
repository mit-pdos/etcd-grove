/-
Lean-first (no Rocq counterpart).

# The key-value store's predicates (2026-10-10; 2026-10-14, stage R; the store, 2026-10-19)

## The client-facing state

A cluster of replicas shares raft's ghost state `γr.raft`. The store keeps the client's half
of raft's full committed log (`rLog γr.raft L`, `Protocol/GhostState.lean`) with its entries'
data `ods`; the store's history is their client data, first occurrences (`firstOcc ods`),
and the invariant keeps half of a ghost variable at the history (`rkvInv`); the store's state
is its fold (`kvFold`, `Base.lean`: every key's value). A client holds `rkvVal γr m`, the other
half, at a history whose fold is `m` (a ghost variable holds a countable value: the history,
not the map). `Put`/`Get`/`Append` hand their atomic update over `rkvVal` to `do`, which mints
the operation and keeps the update in the operation's slot (`opSlot`, with a later credit),
registers the operation's datum with raft once (`node_prop_register`), and gives every
`Node.Propose` of it -- a retry of a dropped proposal included -- a new atomic update over raft's
log that moves the store's log at a committed occurrence of the datum (`kv_propAu`,
`Lemmas.lean`; raft fires each at most once): at the first, it opens `rkvInv`, runs the client's
update from the slot and moves the history -- the linearization point; at a later one (a retry,
a redelivered proposal) only the log moves.
The result -- the key's value after the operation -- stays in the slot until the client
collects it with its ticket (`kv_collect`). The standing update for raft's own entries is the
store's too (`kv_noopAu`, given at allocation).

## Fresh data

`Node.Propose` wants a fresh token (`propFresh`) for an operation's first proposal. The
store mints one per operation, keyed by the operation's `(replica, seq)`
(`MintOk`): `rkvInv` holds the authority of raft's fresh-token map (`reFresh`), each
replica's last sequence number (`seq`, the replica's element under its lock), and the
persistent record of each minted operation (`mint`): every token is of a minted
operation, and every minted `(i, s)` has `s` at most replica `i`'s last sequence number.
So a new sequence number mints a token nobody had, and a datum with a token is the one
minted at its key. Every datum in the log was minted (only the store's updates move it),
so a new operation's datum is not in the history and its slot starts pending.

A read (2026-10-13, `Read`) mints its context the same way, from the same sequence numbers,
with a fresh token of raft's read registry (`reRdFresh`, 2026-10-14, stage R; `MintOk`'s third
clause): a deposited context with a minted key is the one minted there (`kv_read_minted`).

## Lower bounds on the history

`kvLb γr L` (persistent): the store's history has the prefix `L`: `L`
is the client data of a committed log (`firstOcc` of its entries' data). Every committed
log is a prefix of raft's, whose client data is the history, so `L` is a prefix of the
history; and conversely the history now is such an `L` (`kvLb_current`). `Read` takes
one at its call and returns its key's value after a longer one (`readP`).

## A replica

Its lock protects the next sequence number (a replica that has used up `2^64 - 1` of them
stops, in Go: `do` and `Read` loop forever at `maxSeq`; until 2026-10-19 operation credits,
`opCred`, which a caller had to pass in, bounded them), and the waiters: each a handoff
channel whose producer token the lock holds, for the operation minted at `(id, seq)`, on
which the replica's applier sends the key's value after the operation, with where the
operation's entry first is in a committed log (`waitP`); and (2026-10-13) the reads waiting
for their answer (`readsOwn`): each a handoff channel for the read context minted at `(id,
seq)`, on which the applier sends a read index of the context with its key's value after a
committed log at least that long (`readAns`; 2026-10-14, stage R: the read's record comes
with its deposit, inside `Node.ReadIndex`, after the waiter is made, and the reader turns the
answer into `readP`). The applier's own state -- the store's map, the applied-encodings
table, and the committed prefix it applied (`runOwn`) -- is the `run` goroutine's alone
(only `apply` and `answer` touch those fields, holding the lock for the waiters).

## Raft v3.7 (2026-10-16, stage R6b)

The entries of the logs are the model's records (`EntryM`, `Proof/go_etcd_io/raft/v3/PbModel.lean`:
what the getters of a `*pb.Entry` return), as raft's ghost state has them since the retarget; the
`Ready`'s messages are owned pointers (`sendSpec`); a `ReadState`'s context is its bytes (`rsOk`).

## The storage

`*kv.Storage` is a raft `Storage` (`KVStorageInstance.lean`): the instance of
`StorageModel` for the store (`kvStorageModel`), given a registry (`KVStor`: a
ghost map from a `Storage` struct to its `MemoryStorage` and that storage's ghost names,
whose authority is in `kvStorInv`) so that a storage's tokens are of its own names.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kv.Base

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

/-- The store's `Storage` struct (not raft's `Storage` interface). -/
abbrev RStorage [GooseExts] := github_com.mit_pdos.etcd_grove.examples.kv.Storage
/-- The store's replica struct, `KV`. -/
abbrev RKV [GooseExts] := github_com.mit_pdos.etcd_grove.examples.kv.KV

abbrev rStorageTy [GooseExts] [GoGlobalContext] : go.GoType :=
  github_com.mit_pdos.etcd_grove.examples.kv.Storage.ty
abbrev rKVTy [GooseExts] [GoGlobalContext] : go.GoType :=
  github_com.mit_pdos.etcd_grove.examples.kv.KV.ty

/-! ## The storage registry and the storage model -/

/-- The registry's ghost name: a class, so that the `StorageModel` instance below can be
an instance. -/
class KVStor (GF : BundledGFunctors) where
  kvStorName : GName

abbrev MemStorRec :=
  Loc × GName × GName × GName × GName × GName × GName × GName × GName × GName × GName × Int × GName

def memStorRec (ms : Loc) (γs : MemStorNames) : MemStorRec :=
  (ms, γs.hist, γs.done, γs.ep, γs.sn, γs.sw, γs.lk, γs.ok, γs.ak, γs.cb, γs.bd, γs.cap, γs.cert)

theorem memStorRec_inj (ms1 ms2 : Loc) (γs1 γs2 : MemStorNames) :
    memStorRec ms1 γs1 = memStorRec ms2 γs2 → ms1 = ms2 ∧ γs1 = γs2 := by
  intro h
  cases γs1; cases γs2
  simp only [memStorRec, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
  exact ⟨rfl, rfl⟩

def kvStorN : Namespace := nroot.@"kv_storage"

section stor
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kv.Assumptions]
variable [KVStor GF]

/-- The storage `s` is the `MemoryStorage` `ms` with the names `γs` (persistent). -/
def kvStorRec (s ms : Loc) (γs : MemStorNames) : IProp GF :=
  iprop(s.[RStorage, go!"MemoryStorage"] ↦□ ms ∗
    s ↪[KVStor.kvStorName (GF := GF)]□ memStorRec ms γs)

instance kvStorRec_persistent (s ms : Loc) (γs : MemStorNames) :
    Persistent (kvStorRec (GF := GF) s ms γs) := by
  unfold kvStorRec; infer_instance

theorem kvStorRec_agree (s ms1 ms2 : Loc) (γs1 γs2 : MemStorNames) :
    ⊢ kvStorRec (GF := GF) s ms1 γs1 -∗ kvStorRec s ms2 γs2 -∗ ⌜ms1 = ms2 ∧ γs1 = γs2⌝ := by
  unfold kvStorRec
  iintro ⟨-, #H1⟩ ⟨-, #H2⟩
  icases ghostMapElem_agree $$ H1 H2 with %H
  ipureintro; exact memStorRec_inj _ _ _ _ H

/-- The raft `Storage` interface value of the store's storage `s`. -/
def kvStorIface (s : Loc) : Storage :=
  interface.mkOk (go.GoType.PointerType rStorageTy) #s

def kvOwnStorage (st : Storage) (σ : StorState) : IProp GF :=
  iprop(∃ (s ms : Loc) (γs : MemStorNames), ⌜st = kvStorIface s⌝ ∗ kvStorRec s ms γs ∗
    ownMemoryStorage ms γs σ)

def kvAppendTok (st : Storage) (σ : StorState) (p : List EntryM) : IProp GF :=
  iprop(∃ (s ms : Loc) (γs : MemStorNames), ⌜st = kvStorIface s⌝ ∗ kvStorRec s ms γs ∗
    memAppendTok ms γs σ p)

def kvAppendedTok (st : Storage) (σ : StorState) (p : List EntryM) : IProp GF :=
  iprop(∃ (s ms : Loc) (γs : MemStorNames), ⌜st = kvStorIface s⌝ ∗ kvStorRec s ms γs ∗
    memAppendedTok ms γs σ p)

/-- (D19i part 1) The storage's boundary has reached `n`: its `MemoryStorage`'s. -/
def kvStorCut (st : Storage) (n : Int) : IProp GF :=
  iprop(∃ (s ms : Loc) (γs : MemStorNames), ⌜st = kvStorIface s⌝ ∗ kvStorRec s ms γs ∗
    memStorCut γs n)

/-- (D19i part 1) The floor's witness: its `MemoryStorage`'s; (D22 S-r) below `2^61`, as the
storage's extent is (what a snapshot taken at the floor needs, `SnapListsOk`). -/
def kvStorFloor (st : Storage) (x : w64) : IProp GF :=
  iprop(∃ (s ms : Loc) (γs : MemStorNames), ⌜st = kvStorIface s⌝ ∗ kvStorRec s ms γs ∗
    memFloorTok ms γs x ∗ ⌜uint.Z x < 2 ^ 61⌝)

/-- (D22 S-b′2) The snapshot `k` is certified in the storage's registry: its `MemoryStorage`'s. -/
def kvStorCert (st : Storage) (k : SnapTrip) : IProp GF :=
  iprop(∃ (s ms : Loc) (γs : MemStorNames), ⌜st = kvStorIface s⌝ ∗ kvStorRec s ms γs ∗
    memStorCert γs k)

/-- The store's storage model: every `Storage` is a registered store storage. -/
instance kvStorageModel : StorageModel GF where
  ownStorage := kvOwnStorage
  appendTok := kvAppendTok
  appendedTok := kvAppendedTok
  storCut := kvStorCut
  storCut_persistent := fun st n => by unfold kvStorCut; infer_instance
  storFloor := kvStorFloor
  storFloor_persistent := fun st x => by unfold kvStorFloor; infer_instance
  -- (2026-10-19, D21 M3) the store states no cap
  storCap := fun _ _ => iprop(False)
  storCap_persistent := fun _ _ => by infer_instance
  storCut_cap := fun _ _ _ => by iintro ⟨-, %H⟩; exact H.elim
  storCert := kvStorCert
  storCert_persistent := fun st k => by unfold kvStorCert; infer_instance

/-- The registry: each registered storage keeps half of its `MemoryStorage` field here
(so that a storage is registered once: a new one has the whole field). -/
def kvStorInvBody : IProp GF :=
  iprop(∃ M : GMap Loc MemStorRec, ghostMapAuth (KVStor.kvStorName (GF := GF)) 1 M ∗
    [∗map] s ↦ x ∈ M, s.[RStorage, go!"MemoryStorage"] ↦{DFrac.own (1 : Qp).half} x.1)

def kvStorInv : IProp GF := inv kvStorN kvStorInvBody

instance kvStorInv_persistent : Persistent (kvStorInv (GF := GF)) := by
  unfold kvStorInv; infer_instance

instance kvStorInvBody_timeless : Timeless (kvStorInvBody (GF := GF)) := by
  unfold kvStorInvBody; infer_instance

end stor

/-! ## The store's ghost state -/

/-- The ghost names of a store's cluster. -/
structure RKVNames where
  /-- raft's cluster (`Draft.Cluster`), in the store's namespace `kvRaftN` -/
  cluster : Draft.Cluster
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
client's, `Draft.ownCommittedOps`) -- the history is their data's (`logHist`) --, half of the
history's ghost variable, the read contexts used (`Draft.ownReadCtxs`), the sequence numbers, the
mint and the slots' registry. -/
def kvCore (γr : RKVNames) (ops : List Draft.LogEntry) (S : GMap w64 w64)
    (Mi : GMap (w64 × w64) (List w8)) (O : GMap (List w8) (GName × GName)) (U : GSet (List w8)) :
    IProp GF :=
  iprop(Draft.ownCommittedOps γr.cluster ops ∗ ghostVar γr.val (1 : Qp).half (logHist ops) ∗
    Draft.ownReadCtxs γr.cluster U ∗
    ghostMapAuth γr.seq 1 S ∗ ghostMapAuth γr.mint 1 Mi ∗ ghostMapAuth γr.ops 1 O ∗
    ⌜MintOk S Mi O U⌝ ∗
    -- every datum committed was minted (only the store's updates move `ops`)
    ⌜∀ d, some d ∈ ops.map odOf → Minted Mi d⌝)

instance kvCore_timeless (γr : RKVNames) (ops : List Draft.LogEntry) (S : GMap w64 w64)
    (Mi : GMap (w64 × w64) (List w8)) (O : GMap (List w8) (GName × GName)) (U : GSet (List w8)) :
    Timeless (kvCore (GF := GF) γr ops S Mi O U) := by
  unfold kvCore; infer_instance

def rkvInvBody (γr : RKVNames) : IProp GF :=
  iprop(∃ (ops : List Draft.LogEntry) (S : GMap w64 w64) (Mi : GMap (w64 × w64) (List w8))
      (O : GMap (List w8) (GName × GName)) (U : GSet (List w8)),
    kvCore γr ops S Mi O U ∗ [∗map] d ↦ γp ∈ O, opSlot γr d γp (logHist ops))

/-- See the file header. -/
def rkvInv (γr : RKVNames) : IProp GF := inv rkvN (rkvInvBody γr)

instance rkvInv_persistent (γr : RKVNames) : Persistent (rkvInv (GF := GF) γr) := by
  unfold rkvInv; infer_instance

/-- What a waiter learns with the value `v`: the operation's datum `d` first occurs at
`m` in a committed log, and `v` is its key's value after it. -/
def waitP (γr : RKVNames) (d : List w8) (v : List w8) : IProp GF :=
  iprop(∃ (l : List Draft.LogEntry) (ods : List (Option (List w8))) (m : Nat),
    Draft.isCommittedLogLb γr.cluster l ∗ ⌜ods = l.map odOf⌝ ∗
    ⌜ods[m]? = some (some d) ∧ d ∉ histOf (ods.take m) ∧
      v = kvFold (histOf (ods.take m) ++ [d]) (dkey d)⌝)

/-- A lower bound on the store's history (see the file header; persistent). -/
def kvLb (γr : RKVNames) (L : List (List w8)) : IProp GF :=
  iprop(∃ (l : List Draft.LogEntry), Draft.isCommittedLogLb γr.cluster l ∗ ⌜L = logHist l⌝)

instance kvLb_persistent (γr : RKVNames) (L : List (List w8)) :
    Persistent (kvLb (GF := GF) γr L) := by
  unfold kvLb; infer_instance

/-- What the applier answers a read of the context `c` with: a read state of `c` at index `i`
(`Draft.readStateOk`), and the value `v` of `c`'s key after a committed log `ap` at least `i`
long. The reader, which committed `c` to its predicate (`Draft.isReadCtx`), turns it into a value
after its lower bound. -/
def readAns (γr : RKVNames) (c : List w8) (v : List w8) : IProp GF :=
  iprop(∃ (i : w64) (ap : List Draft.LogEntry),
    Draft.readStateOk γr.cluster kvRaftN c i ∗ Draft.isCommittedLogLb γr.cluster ap ∗
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

/-- The voters of the store's cluster. -/
abbrev kvVoters : List w64 := [W64 1, W64 2, W64 3]

/-- Replica `id` at `r`, on node `n` of the store's static cluster (`Draft.isStaticCluster`, of
the voters `kvVoters`, admitting snapshots of the store's data, `kvSnapOk`; leader transfer on),
with the storage `st` (persistent). -/
def isReplica (γr : RKVNames) (γp : RepNames) (r : Loc) (id : w64) (n st : Loc) : IProp GF :=
  iprop(
    "#Hpkg" ∷ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kv ∗
    "#Hid" ∷ r.[RKV, go!"id"] ↦□ id ∗
    "#Hnode" ∷ r.[RKV, go!"node"] ↦□ interface.mkOk (go.GoType.PointerType node.ty) #n ∗
    "#Hst" ∷ r.[RKV, go!"storage"] ↦□ st ∗
    "#Hsrec" ∷ (∃ (ms : Loc) (γs : MemStorNames), kvStorRec st ms γs) ∗
    "#HisNode" ∷ Draft.isNode n γr.cluster kvRaftN id ∗
    "#Hstatic" ∷ Draft.isStaticCluster γr.cluster kvRaftN kvVoters kvSnapOk ∗
    "#Hxfer" ∷ Draft.leaderTransferOn γr.cluster kvRaftN ∗
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
(`Draft.sentMsg`), with its credits (`Draft.msgCredits`). Delivering them to the peers'
`Node.Step` is the transport's. -/
def sendSpec (f : GoFunc) (γ : Draft.Cluster) : IProp GF :=
  iprop(□ ∀ (msl : GoSlice) (ms : List QMsg),
    {{ msl ↦* ms.map QMsg.loc ∗
        [∗list] q ∈ ms, msgOwn q.loc (readyDq q.st) q.st ∗ Draft.sentMsg γ kvRaftN q.st ∗
          Draft.msgCredits γ kvRaftN q.st }}
      (App (Val #f) (Val #msl))
    {{ RET #(); True }})

instance sendSpec_persistent (f : GoFunc) (γ : Draft.Cluster) :
    Persistent (sendSpec (GF := GF) f γ) := by
  unfold sendSpec; infer_instance

/-- A `ReadState` Go value as `Ready` hands it out: its `RequestCtx` slice holds the bytes `c`
read-only, and the read state of `c` at its index (`Draft.readStateOk`). Persistent. -/
def rsOk (γ : Draft.Cluster) (v : ReadState) : IProp GF :=
  iprop(∃ c : List w8, v.RequestCtx' ↦*□ c ∗ Draft.readStateOk γ kvRaftN c v.Index')

instance rsOk_persistent (γ : Draft.Cluster) (v : ReadState) : Persistent (rsOk (GF := GF) γ v) := by
  unfold rsOk; infer_instance

/-- The applier's state (the `run` goroutine's): the store's map, every key's value (a key it
lacks has the value `[]`, as for Go's lookup), and the applied-encodings table (each with its
answer, `AppliedOk`), at the committed log `ap` it applied. -/
def runOwn (γr : RKVNames) (r : Loc) (ap : List Draft.LogEntry) : IProp GF :=
  iprop(∃ (mK : Loc) (K : GMap (List w8) (List w8)) (mA : Loc) (A : GMap (List w8) (List w8))
      (ods : List (Option (List w8))),
    "HmK" ∷ r.[RKV, go!"kv"] ↦ mK ∗
    "HK" ∷ mK ↦$ K ∗
    "HmA" ∷ r.[RKV, go!"applied"] ↦ mA ∗
    "HA" ∷ mA ↦$ A ∗
    "#Hap" ∷ Draft.isCommittedLogLb γr.cluster ap ∗
    "%Hods" ∷ ⌜ods = ap.map odOf⌝ ∗
    "%Hval" ∷ ⌜∀ k, (K !! k).getD [] = kvFold (histOf ods) k⌝ ∗
    "%HA" ∷ ⌜AppliedOk A (histOf ods)⌝)

/-- **What the applier holds of its storage `st`**, at the application's view `σt` of the
`MemoryStorage`'s snapshot and boundary: the storage's snapshot token (`memSnapTok`: the right to
install a snapshot, take one and compact), the certificate registry tied to the cluster (to
register the snapshots it takes, `Draft.storageCertInv`), the storage's cap (`NewStorage`'s,
`2^64`), and the cluster's voters (`Storage.voters`), the configuration of every snapshot it
takes. The application's snapshot is at its boundary or past it. -/
def runStor (γr : RKVNames) (st : Loc) (σt : StorState) : IProp GF :=
  iprop(∃ (ms : Loc) (γs : MemStorNames) (vsl : GoSlice),
    kvStorRec st ms γs ∗ memSnapTok ms γs σt ∗ Draft.storageCertInv γr.cluster kvRaftN γs ∗
    st.[RStorage, go!"voters"] ↦□ vsl ∗ vsl ↦*□ kvVoters ∗
    ⌜γs.cap = 2 ^ 64 ∧ uint.Z σt.prev.index' ≤ uint.Z σt.ss.index'⌝)

end ghost

section ccfg
variable [GooseExts]

/-- The change `RemoveMember(id)` proposes: `pb.ConfChange{Type: ConfChangeRemoveNode, NodeID:
id}` (type `1`; no context, no id). -/
def rmCC (id : w64) : ConfChangeM := { type := W32 1, nodeId := id, context := [], id := W64 0 }

end ccfg

end EtcdGrove
end Perennial
