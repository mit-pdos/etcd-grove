/-
Lean-first (no Rocq counterpart).

# The register's predicates (2026-10-10; 2026-10-14, stage R)

## The client-facing state

A cluster of replicas shares raft's ghost state `γr.raft`. The register keeps the client's half
of raft's full committed log (`rLog γr.raft L`, `Protocol/GhostState.lean`) with its entries'
data `ods`; the register's history is their client data, first occurrences (`firstOcc ods`),
and the invariant keeps the authoritative register value at `regFold (firstOcc ods)`
(`regInv`). A client holds `regVal γr x`, the other half of the value. `Put`/`Get` hand their
atomic update over `regVal` to `do`, which mints the operation and keeps the update in the
operation's slot (`opSlot`, with a later credit), and gives `Node.Propose` the persistent
atomic update over raft's log that moves the register's log at every committed occurrence of
the operation's datum (`reg_propAu`, `Lemmas.lean`): at the first, it opens `regInv`, runs the
client's update from the slot and moves the value -- the linearization point; at a later one
(a retry, a redelivered proposal) only the log moves. The result stays in the slot until the
client collects it with its ticket (`reg_collect`). The standing update for raft's own entries
is the register's too (`reg_noopAu`, given at allocation).

## Fresh data

`Node.Propose` wants a fresh token (`propFresh`) for an operation's first proposal. The
register mints one per operation, keyed by the operation's `(replica, seq)`
(`MintOk`): `regInv` holds the authority of raft's fresh-token map (`reFresh`), each
replica's last sequence number (`seq`, the replica's element under its lock), and the
persistent record of each minted operation (`mint`): every token is of a minted
operation, and every minted `(i, s)` has `s` at most replica `i`'s last sequence number.
So a new sequence number mints a token nobody had, and a datum with a token is the one
minted at its key. Every datum in the log was minted (only the register's updates move it),
so a new operation's datum is not in the history and its slot starts pending.

A read (2026-10-13, `Read`) mints its context the same way, from the same sequence numbers,
with a fresh token of raft's read registry (`reRdFresh`, 2026-10-14, stage R; `MintOk`'s third
clause): a deposited context with a minted key is the one minted there (`reg_read_minted`).

## Lower bounds on the history

`regLb γr L` (persistent): the register's history has the prefix `L`: `L`
is the client data of a committed log (`firstOcc` of its entries' data). Every committed
log is a prefix of raft's, whose client data is the history, so `L` is a prefix of the
history; and conversely the history now is such an `L` (`regLb_current`). `Read` takes
one at its call and returns the value after a longer one (`readP`).

## A replica

Its lock protects the next sequence number, with the credits for it (`opCred`: a
replica has `2^64 - 1` operations), and the waiters: each a handoff channel whose
producer token the lock holds, for the operation minted at `(id, seq)`, on which the
replica's applier sends the value after the operation, with where the operation's entry
first is in a committed log (`waitP`); and (2026-10-13) the reads waiting for their
answer (`readsOwn`): each a handoff channel for the read context minted at `(id, seq)`, on
which the applier sends a read index of the context with the value after a committed log at
least that long (`readAns`; 2026-10-14, stage R: the read's record comes with its deposit,
inside `Node.ReadIndex`, after the waiter is made, and the reader turns the answer into
`readP`). The applier's own state -- the value, the
applied-encodings table, and the committed prefix it applied (`runOwn`) -- is the `run`
goroutine's alone (only `apply` touches those fields, holding the lock for the waiters).

## Raft v3.7 (2026-10-16, stage R6b)

The entries of the logs are the model's records (`EntryM`, `Proof/go_etcd_io/raft/v3/PbModel.lean`:
what the getters of a `*pb.Entry` return), as raft's ghost state has them since the retarget; the
`Ready`'s messages are owned pointers (`sendSpec`); a `ReadState`'s context is its bytes (`rsOk`).

## The storage

`*register.Storage` is a raft `Storage` (`RegStorageInstance.lean`): the instance of
`StorageModel` for the register (`regStorageModel`), given a registry (`RegStor`: a
ghost map from a `Storage` struct to its `MemoryStorage` and that storage's ghost names,
whose authority is in `regStorInv`) so that a storage's tokens are of its own names.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.register.Base

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

/-- The register's `Storage` struct (not raft's `Storage` interface). -/
abbrev RStorage [FfiSyntax] := github_com.mit_pdos.etcd_grove.examples.register.Storage
/-- The register's `Register` struct. -/
abbrev RRegister [FfiSyntax] := github_com.mit_pdos.etcd_grove.examples.register.Register

abbrev rStorageTy [FfiSyntax] [GoGlobalContext] : go.GoType :=
  github_com.mit_pdos.etcd_grove.examples.register.Storage.ty
abbrev rRegisterTy [FfiSyntax] [GoGlobalContext] : go.GoType :=
  github_com.mit_pdos.etcd_grove.examples.register.Register.ty

/-! ## The storage registry and the storage model -/

/-- The registry's ghost name: a class, so that the `StorageModel` instance below can be
an instance. -/
class RegStor (GF : BundledGFunctors) where
  regStorName : GName

abbrev MemStorRec := Loc × GName × GName × GName

def memStorRec (ms : Loc) (γs : MemStorNames) : MemStorRec := (ms, γs.hist, γs.done, γs.ep)

theorem memStorRec_inj (ms1 ms2 : Loc) (γs1 γs2 : MemStorNames) :
    memStorRec ms1 γs1 = memStorRec ms2 γs2 → ms1 = ms2 ∧ γs1 = γs2 := by
  intro h
  cases γs1; cases γs2
  simp only [memStorRec, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl, rfl⟩ := h
  exact ⟨rfl, rfl⟩

def regStorN : Namespace := nroot.@"register_storage"

section stor
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.register.Assumptions]
variable [RegStor GF]

/-- The storage `s` is the `MemoryStorage` `ms` with the names `γs` (persistent). -/
def regStorRec (s ms : Loc) (γs : MemStorNames) : IProp GF :=
  iprop(s.[RStorage, go!"MemoryStorage"] ↦□ ms ∗
    s ↪[RegStor.regStorName (GF := GF)]□ memStorRec ms γs)

instance regStorRec_persistent (s ms : Loc) (γs : MemStorNames) :
    Persistent (regStorRec (GF := GF) s ms γs) := by
  unfold regStorRec; infer_instance

theorem regStorRec_agree (s ms1 ms2 : Loc) (γs1 γs2 : MemStorNames) :
    ⊢ regStorRec (GF := GF) s ms1 γs1 -∗ regStorRec s ms2 γs2 -∗ ⌜ms1 = ms2 ∧ γs1 = γs2⌝ := by
  unfold regStorRec
  iintro ⟨-, #H1⟩ ⟨-, #H2⟩
  icases ghostMapElem_agree $$ H1 H2 with %H
  ipureintro; exact memStorRec_inj _ _ _ _ H

/-- The raft `Storage` interface value of the register storage `s`. -/
def regStorIface (s : Loc) : Storage :=
  interface.mkOk (go.GoType.PointerType rStorageTy) #s

def regOwnStorage (st : Storage) (σ : StorState) : IProp GF :=
  iprop(∃ (s ms : Loc) (γs : MemStorNames), ⌜st = regStorIface s⌝ ∗ regStorRec s ms γs ∗
    ownMemoryStorage ms γs σ)

def regAppendTok (st : Storage) (σ : StorState) (p : List EntryM) : IProp GF :=
  iprop(∃ (s ms : Loc) (γs : MemStorNames), ⌜st = regStorIface s⌝ ∗ regStorRec s ms γs ∗
    memAppendTok ms γs σ p)

def regAppendedTok (st : Storage) (σ : StorState) (p : List EntryM) : IProp GF :=
  iprop(∃ (s ms : Loc) (γs : MemStorNames), ⌜st = regStorIface s⌝ ∗ regStorRec s ms γs ∗
    memAppendedTok ms γs σ p)

/-- The register's storage model: every `Storage` is a registered register storage. -/
instance regStorageModel : StorageModel GF where
  ownStorage := regOwnStorage
  appendTok := regAppendTok
  appendedTok := regAppendedTok

/-- The registry: each registered storage keeps half of its `MemoryStorage` field here
(so that a storage is registered once: a new one has the whole field). -/
def regStorInvBody : IProp GF :=
  iprop(∃ M : GMap Loc MemStorRec, ghostMapAuth (RegStor.regStorName (GF := GF)) 1 M ∗
    [∗map] s ↦ x ∈ M, s.[RStorage, go!"MemoryStorage"] ↦{DFrac.own (1 : Qp).half} x.1)

def regStorInv : IProp GF := inv regStorN regStorInvBody

instance regStorInv_persistent : Persistent (regStorInv (GF := GF)) := by
  unfold regStorInv; infer_instance

instance regStorInvBody_timeless : Timeless (regStorInvBody (GF := GF)) := by
  unfold regStorInvBody; infer_instance

end stor

/-! ## The register's ghost state -/

/-- The ghost names of a register cluster. -/
structure RegNames where
  raft : RaftNames
  /-- the register's value (`ghostVar`, halves: `regInv`'s and the client's) -/
  val : GName
  /-- each replica's last sequence number (a ghost map, its authority in `regInv`) -/
  seq : GName
  /-- the minted operations, `(replica, seq) ↦ data` (persistent elements) -/
  mint : GName
  /-- (2026-10-14, stage R) the operations' slots, `data ↦ (γq, γk)` (persistent elements,
  authority in `regInv`): each holds the client's atomic update until the datum's first
  committed occurrence, then its result or the client's ticket `γk` (`opSlot`) -/
  ops : GName

def regN : Namespace := nroot.@"register"

/-- What `Put`/`Get`'s atomic update may open: everything but raft's commit invariant
and the register's. -/
def regMask : CoPset := (⊤ \ ↑raftN) \ ↑regN

theorem regN_raftN : (↑regN : CoPset) ⊆ ⊤ \ ↑raftN :=
  mask_ndot_ne' nroot "register" "raft_commit" (by decide)

theorem raftN_regN : (↑raftN : CoPset) ⊆ ⊤ \ ↑regN :=
  mask_ndot_ne' nroot "raft_commit" "register" (by decide)

/-- The minting discipline (see the file header): the fresh-data tokens `M`, (2026-10-14,
stage R) the fresh read-context tokens `F` and the operations' slots `O` are minted. -/
def MintOk [FfiSyntax] (M : GMap (List w8) Unit) (F : GMap (List w8) Unit)
    (S : GMap w64 w64) (Mi : GMap (w64 × w64) (List w8)) (O : GMap (List w8) (GName × GName)) :
    Prop :=
  (∀ d, M !! d = some () → ∃ k, opKey d = some k ∧ Mi !! k = some d) ∧
  (∀ i s d, Mi !! (i, s) = some d → ∃ n, S !! i = some n ∧ uint.Z s ≤ uint.Z n) ∧
  (∀ c, F !! c = some () → ∃ k, opKey c = some k ∧ Mi !! k = some c) ∧
  (∀ d γp, O !! d = some γp → M !! d = some ())

/-- The ticket of a replica's operation credits (`Auth Nat`). -/
structure RepNames [FfiSyntax] where
  node : NodeNames
  cred : GName

section ghost
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.register.Assumptions]
variable [RegStor GF]

/-- The client's half of the register's value. -/
def regVal (γr : RegNames) (x : List w8) : IProp GF :=
  ghostVar γr.val (1 : Qp).half x

/-- An operation's atomic update over the register's value, the value moving by `f`
(`Put`/`Get` give `opNext kind val`; a slot keeps it as `regApply · d`). -/
def opAu (γr : RegNames) (f : List w8 → List w8) (Φ : List w8 → IProp GF) : IProp GF :=
  iprop(AU <{ ∃∃ (x : List w8), regVal γr x }> @ regMask, ∅
    <{ regVal γr (f x), COMM Φ (f x) }>)

/-- An operation's slot (2026-10-14, stage R; until then raft's proposal slot did this), for the
register's history `H`: the result predicate (tied to `γp.1`), and either the client's update
with a later credit, while `d` is not in the history, or -- once `d` first occurred, after
the history `H0` -- the update's result at the value after `H0 ++ [d]` or the client's
ticket `γp.2`. -/
def opSlot (γr : RegNames) (d : List w8) (γp : GName × GName) (H : List (List w8)) : IProp GF :=
  iprop(∃ Φ : List w8 → IProp GF, savedPredOwn γp.1 DFrac.discard Φ ∗
    ( (⌜d ∉ H⌝ ∗ £ 1 ∗ opAu γr (fun x => regApply x d) Φ)
    ∨ (∃ H0, ⌜H0 ++ [d] <+: H ∧ d ∉ H0⌝ ∗ (Φ (regFold (H0 ++ [d])) ∨ token γp.2)) ))

/-- The timeless part of the register's invariant: raft's full committed log (the client's
half, `rLog`, 2026-10-14, stage R) with its entries' data `ods` -- the history is their client
data, first occurrences (`firstOcc ods`) --, the value after the history, the authorities of
raft's fresh tokens (data and read contexts), the sequence numbers, the mint and the slots'
registry. -/
def regCore (γr : RegNames) (L : List EntryM) (ods : List (Option (List w8)))
    (M : GMap (List w8) Unit) (F : GMap (List w8) Unit) (S : GMap w64 w64)
    (Mi : GMap (w64 × w64) (List w8)) (O : GMap (List w8) (GName × GName)) : IProp GF :=
  iprop(rLog γr.raft L ∗ ([∗list] e;o ∈ L;ods, entDataIs γr.raft e o) ∗
    ghostVar γr.val (1 : Qp).half (regFold (firstOcc ods)) ∗
    ghostMapAuth γr.raft.reFresh 1 M ∗ ghostMapAuth γr.raft.reRdFresh 1 F ∗
    ghostMapAuth γr.seq 1 S ∗ ghostMapAuth γr.mint 1 Mi ∗ ghostMapAuth γr.ops 1 O ∗
    ⌜MintOk M F S Mi O⌝ ∗
    -- every datum in the log was minted (only the register's updates move `rLog`)
    ⌜∀ d, some d ∈ ods → M !! d = some ()⌝)

instance regCore_timeless (γr : RegNames) (L : List EntryM) (ods : List (Option (List w8)))
    (M : GMap (List w8) Unit) (F : GMap (List w8) Unit) (S : GMap w64 w64)
    (Mi : GMap (w64 × w64) (List w8)) (O : GMap (List w8) (GName × GName)) :
    Timeless (regCore (GF := GF) γr L ods M F S Mi O) := by
  unfold regCore; infer_instance

def regInvBody (γr : RegNames) : IProp GF :=
  iprop(∃ (L : List EntryM) (ods : List (Option (List w8))) (M : GMap (List w8) Unit)
      (F : GMap (List w8) Unit) (S : GMap w64 w64) (Mi : GMap (w64 × w64) (List w8))
      (O : GMap (List w8) (GName × GName)),
    regCore γr L ods M F S Mi O ∗ [∗map] d ↦ γp ∈ O, opSlot γr d γp (firstOcc ods))

/-- See the file header. -/
def regInv (γr : RegNames) : IProp GF := inv regN (regInvBody γr)

instance regInv_persistent (γr : RegNames) : Persistent (regInv (GF := GF) γr) := by
  unfold regInv; infer_instance

/-- What a waiter learns with the value `v`: the operation's datum `d` first occurs at
`m` in a committed log, and `v` is the register's value after it. -/
def waitP (γr : RegNames) (d : List w8) (v : List w8) : IProp GF :=
  iprop(∃ (l : List EntryM) (ods : List (Option (List w8))) (m : Nat),
    isCommitted γr.raft l ∗ ([∗list] e;o ∈ l;ods, entDataIs γr.raft e o) ∗
    ⌜ods[m]? = some (some d) ∧ d ∉ firstOcc (ods.take m) ∧
      v = regFold (firstOcc (ods.take m) ++ [d])⌝)

instance waitP_persistent (γr : RegNames) (d v : List w8) :
    Persistent (waitP (GF := GF) γr d v) := by
  unfold waitP; infer_instance

/-- A lower bound on the register's history (see the file header; persistent). -/
def regLb (γr : RegNames) (L : List (List w8)) : IProp GF :=
  iprop(∃ (l : List EntryM) (ods : List (Option (List w8))),
    isCommitted γr.raft l ∗ ([∗list] e;o ∈ l;ods, entDataIs γr.raft e o) ∗ ⌜L = firstOcc ods⌝)

instance regLb_persistent (γr : RegNames) (L : List (List w8)) :
    Persistent (regLb (GF := GF) γr L) := by
  unfold regLb; infer_instance

/-- What a read waiting with the lower bound `L0` learns with the value `v`: `v` is the
register's value after a history extending `L0`. -/
def readP (γr : RegNames) (L0 : List (List w8)) (v : List w8) : IProp GF :=
  iprop(∃ L, regLb γr L ∗ ⌜L0 <+: L ∧ v = regFold L⌝)

instance readP_persistent (γr : RegNames) (L0 : List (List w8)) (v : List w8) :
    Persistent (readP (GF := GF) γr L0 v) := by
  unfold readP; infer_instance

/-- What the applier answers a read of the context `c` with (2026-10-14, stage R): a read
index `i` of `c` (`readOk`), and the value `v` after a committed log `ap` at least `i` long.
The reader, which knows the log its deposit was made at (`readReq`, from `Node.ReadIndex`),
turns it into `readP`. -/
def readAns (γr : RegNames) (c : List w8) (v : List w8) : IProp GF :=
  iprop(∃ (i : w64) (ap : List EntryM) (ods : List (Option (List w8))),
    readOk γr.raft c i ∗ isCommitted γr.raft ap ∗
    ([∗list] e;o ∈ ap;ods, entDataIs γr.raft e o) ∗
    ⌜uint.Z i ≤ (ap.length : Int) ∧ v = regFold (firstOcc ods)⌝)

instance readAns_persistent (γr : RegNames) (c v : List w8) :
    Persistent (readAns (GF := GF) γr c v) := by
  unfold readAns; infer_instance

/-- A read's entry in the lock's invariant: the context `c` minted at `(id, s)`, and the
producer of its handoff channel (2026-10-14, stage R: the read's record comes with its
deposit, inside `Node.ReadIndex`, after the entry is made, so the answer carries `readAns`). -/
def readWaiterOk (γr : RegNames) (id s : w64) (ch : Loc) : IProp GF :=
  iprop(∃ (c : List w8) (γh : HandoffNames),
    (id, s) ↪[γr.mint]□ c ∗
    isHandoff γh ch (readAns γr c) iprop(True) iprop(False) ∗
    handoffProducer γh false)

/-- A replica's waiting reads (the lock's), each of a sequence number at most `ns`. -/
def readsOwn (γr : RegNames) (id : w64) (r : Loc) (ns : w64) : IProp GF :=
  iprop(∃ (mR : Loc) (Rd : GMap w64 Loc),
    "HmR" ∷ r.[RRegister, go!"reads"] ↦ mR ∗
    "HRd" ∷ mR ↦$ Rd ∗
    "%HRdom" ∷ ⌜∀ s ch, Rd !! s = some ch → uint.Z s ≤ uint.Z ns⌝ ∗
    "Hreads" ∷ [∗map] s ↦ ch ∈ Rd, readWaiterOk γr id s ch)

theorem readsOwn_mono (γr : RegNames) (id : w64) (r : Loc) (ns ns' : w64)
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

/-- A replica's operation credits. -/
def opCred (γp : RepNames) (n : Nat) : IProp GF := own γp.cred (◯ n : Auth Nat)

/-- A waiter's entry in the lock's invariant: the operation minted at `(id, s)`, and the
producer of its handoff channel. -/
def waiterOk (γr : RegNames) (id s : w64) (ch : Loc) : IProp GF :=
  iprop(∃ (d : List w8) (γh : HandoffNames), (id, s) ↪[γr.mint]□ d ∗
    isHandoff γh ch (waitP γr d) iprop(True) iprop(False) ∗ handoffProducer γh false)

/-- A replica's lock invariant (see the file header). -/
def lockInv (γr : RegNames) (γp : RepNames) (id : w64) (r : Loc) : IProp GF :=
  iprop(∃ (ns : w64) (mW : Loc) (W : GMap w64 Loc) (c : Nat),
    "Hns" ∷ r.[RRegister, go!"nextSeq"] ↦ ns ∗
    "HmW" ∷ r.[RRegister, go!"waiters"] ↦ mW ∗
    "HW" ∷ mW ↦$ W ∗
    "Hseq" ∷ id ↪[γr.seq] ns ∗
    "Hcred" ∷ own γp.cred (● c : Auth Nat) ∗
    "%Hc" ∷ ⌜uint.Z ns + (c : Int) < 2 ^ 64⌝ ∗
    "%HWdom" ∷ ⌜∀ s ch, W !! s = some ch → uint.Z s ≤ uint.Z ns⌝ ∗
    "Hwaiters" ∷ ([∗map] s ↦ ch ∈ W, waiterOk γr id s ch) ∗
    "Hrds" ∷ readsOwn γr id r ns)

/-- Replica `id` at `r`, on node `n`, with the storage `st` (persistent). -/
def isReplica (γr : RegNames) (γp : RepNames) (r : Loc) (id : w64) (n st : Loc) : IProp GF :=
  iprop(
    "#Hpkg" ∷ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.register ∗
    "#Hid" ∷ r.[RRegister, go!"id"] ↦□ id ∗
    "#Hnode" ∷ r.[RRegister, go!"node"] ↦□ interface.mkOk (go.GoType.PointerType node.ty) #n ∗
    "#Hst" ∷ r.[RRegister, go!"storage"] ↦□ st ∗
    "#Hsrec" ∷ (∃ (ms : Loc) (γs : MemStorNames), regStorRec st ms γs) ∗
    "#HisNode" ∷ isNode γp.node id n ∗
    "%Hraft" ∷ ⌜γp.node.raft = γr.raft⌝ ∗
    "%Hstor" ∷ ⌜γp.node.stor = regStorIface st⌝ ∗
    "#Hmu" ∷ sync.isMutex (r.[RRegister, go!"mu"]) (lockInv γr γp id r) ∗
    "#Hinv" ∷ regInv γr)

set_option synthInstance.maxHeartbeats 400000 in
set_option synthInstance.maxSize 4096 in
instance isReplica_persistent (γr : RegNames) (γp : RepNames) (r : Loc) (id : w64) (n st : Loc) :
    Persistent (isReplica (GF := GF) γr γp r id n st) := by
  unfold isReplica; infer_instance

/-- A replica (persistent; what `Put` and `Get` take). -/
def isRegister (γr : RegNames) (γp : RepNames) (r : Loc) : IProp GF :=
  iprop(∃ (id : w64) (n st : Loc), isReplica γr γp r id n st)

instance isRegister_persistent (γr : RegNames) (γp : RepNames) (r : Loc) :
    Persistent (isRegister (GF := GF) γr γp r) := by
  unfold isRegister; infer_instance

/-- The `send` callback (`func([]*pb.Message)`): it takes the messages of a `Ready` as `Ready`
hands them out (raft v3.7, 2026-10-16, stage R6b, D8: `readyData`): the slice of their pointers,
owned, each message owned at `readyDq` (whole, but a response, `MsgAppResp`/`MsgVoteResp`, at half:
raft's `acceptReady` still reads its `To`), with what the node's `Ready` says of it (persistent:
legitimately sent, `isRaftMsg`, of a term within the budget, `termLB`) and (2026-10-13) its read
credit (one for a `MsgReadIndex`). Delivering them to the peers' `Node.Step` (copying a
message's entries slice, which `Step` takes owned; passing a message's credit on) is the
transport's. -/
def sendSpec (f : GoFunc) (γn : NodeNames) : IProp GF :=
  iprop(□ ∀ (msl : GoSlice) (ms : List QMsg),
    {{ msl ↦* ms.map QMsg.loc ∗
        ([∗list] q ∈ ms, msgOwn q.loc (readyDq q.st) q.st ∗ isRaftMsg γn.raft q.st ∗
          termLB γn.bud q.st.msg.Term') ∗
        [∗list] q ∈ ms, rdCred γn.raft (if q.st.msg.Type' = MsgReadIndex then 1 else 0) }}
      (App (Val #f) (Val #msl))
    {{ RET #(); True }})

instance sendSpec_persistent (f : GoFunc) (γn : NodeNames) :
    Persistent (sendSpec (GF := GF) f γn) := by
  unfold sendSpec; infer_instance

/-- A `ReadState` Go value as `Ready` hands it out (raft v3.7, stage R6b): its `RequestCtx` slice
holds the bytes `c` read-only, and `readStateOk` of the record `⟨Index, c⟩` (D6: a read context is
its bytes). What `run` collects from `readStatesPts` (`readStatesPts_rsOk`, `Lemmas.lean`) and
`answer` takes per read state. Persistent. -/
def rsOk (γ : RaftNames) (v : ReadState) : IProp GF :=
  iprop(∃ c : List w8, v.RequestCtx' ↦*□ c ∗ readStateOk γ ⟨v.Index', c⟩)

instance rsOk_persistent (γ : RaftNames) (v : ReadState) : Persistent (rsOk (GF := GF) γ v) := by
  unfold rsOk; infer_instance

/-- The applier's state (the `run` goroutine's): the value and the applied-encodings
table, at the committed prefix `ap` it applied. -/
def runOwn (γr : RegNames) (r : Loc) (ap : List EntryM) : IProp GF :=
  iprop(∃ (v : List w8) (mA : Loc) (A : GMap (List w8) Bool)
      (ods : List (Option (List w8))),
    "Hv" ∷ r.[RRegister, go!"value"] ↦ v ∗
    "HmA" ∷ r.[RRegister, go!"applied"] ↦ mA ∗
    "HA" ∷ mA ↦$ A ∗
    "#Hap" ∷ isCommitted γr.raft ap ∗
    "#Hods" ∷ ([∗list] e;o ∈ ap;ods, entDataIs γr.raft e o) ∗
    "%Hval" ∷ ⌜v = regFold (firstOcc ods)⌝ ∗
    "%HA" ∷ ⌜AppliedOk A (firstOcc ods)⌝)

end ghost

/-! ## The cluster's configuration changes (2026-10-15, stage N)

The replicas' nodes are in raft's dynamic mode: the voters change by the conf-change entries
their `run`s apply (`node.ApplyConfChange`, before the `Advance` that acknowledges them). A pure
decoder (`CCDec`) cannot read an entry's bytes, so the cluster's conf changes are fixed in
advance: every conf-change entry carries the change `op` (raft's `reCCOk`, at allocation), and
the decoder answers `op` (`ccDecOf`). `op` applies at the initial configuration `c0`, giving
`c1`, and again at `c1`, giving `c1` (a removal of a voter: removing it again is nothing); so
the configuration a replica's node is at is `c0` or `c1` (`RunCfg`). -/

section ccfg
variable [FfiSyntax]

/-- The decoder of a cluster whose conf-change entries all carry the change `op`. -/
def ccDecOf (op : CCOp) : CCDec := fun _ _ => some op

/-- A replica's node in the dynamic mode of a cluster whose conf changes are all `op` (see
the section header). -/
def RegCC (γn : NodeNames) (op : CCOp) (c0 c1 : CCState) : Prop :=
  (∃ h0 h1, γn.mode = .dyn (ccDecOf op) c0 h0 h1) ∧
  (∀ ty bs, γn.raft.reCCOk ty bs →
    ty = W32 1 ∧ ∃ m, ccDecodeV1 bs = some m ∧ ccV2Of (.v1 m) = op) ∧
  ccStepB op c0 = some c1 ∧ ccStepB op c1 = some c1 ∧ c1.cfg.autoLeave = false

/-- The change `RemoveMember(id)` proposes: `pb.ConfChange{Type: ConfChangeRemoveNode, NodeID:
id}` (type `1`; no context, no id). -/
def rmCC (id : w64) : CCV1M := { type := W32 1, nodeId := id, context := [], id := W64 0 }

/-- What `run` knows of its node's configuration, at the committed log `D` applied up to
position `len`: the configuration index `ca` of the last conf change applied, past which `D`
has no conf entry before `len`, and the configuration, `c0` or `c1`. -/
def RunCfg (D : List EntryM) (len ca : Nat) (cfg c0 c1 : CCState) : Prop :=
  ca ≤ len ∧ NoConfIn D ca len ∧ (cfg = c0 ∨ cfg = c1)

end ccfg

end EtcdGrove
end Perennial
