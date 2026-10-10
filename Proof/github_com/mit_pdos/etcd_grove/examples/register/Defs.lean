/-
Lean-first (no Rocq counterpart).

# The register's predicates (2026-10-10)

## The client-facing state

A cluster of replicas shares raft's ghost state `γr.raft`; its client log
(`cLog γr.raft L`, `Protocol/GhostState.lean`: the data of the committed proposals, first
occurrences) is the register's, kept in one invariant with the authoritative register
value at `regFold L` (`regInv`). A client holds `regVal γr x`, the other half of the
value. `Put`/`Get` hand their atomic update over `regVal` to `do`, which wraps it in the
atomic update over `cLog` that `Node.Propose` deposits (`reg_propAu`, `Lemmas.lean`):
when raft commits the operation's first entry, the wrapper opens `regInv`, runs the
client's update and moves both to the new client log -- the linearization point.

## Fresh data

`Node.Propose` wants a fresh token (`propFresh`) for an operation's first proposal. The
register mints one per operation, keyed by the operation's `(replica, seq)`
(`MintOk`): `regInv` holds the authority of raft's fresh-token map (`reFresh`), each
replica's last sequence number (`seq`, the replica's element under its lock), and the
persistent record of each minted operation (`mint`): every token is of a minted
operation, and every minted `(i, s)` has `s` at most replica `i`'s last sequence number.
So a new sequence number mints a token nobody had, and a datum with a token is the one
minted at its key.

## A replica

Its lock protects the next sequence number, with the credits for it (`opCred`: a
replica has `2^64 - 1` operations), and the waiters: each a handoff channel whose
producer token the lock holds, for the operation minted at `(id, seq)`, on which the
replica's applier sends the value after the operation, with where the operation's entry
first is in a committed log (`waitP`). The applier's own state -- the value, the
applied-encodings table, and the committed prefix it applied (`runOwn`) -- is the `run`
goroutine's alone (only `apply` touches those fields, holding the lock for the waiters).

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
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
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

def regAppendTok (st : Storage) (σ : StorState) (p : List raftpb.Entry) : IProp GF :=
  iprop(∃ (s ms : Loc) (γs : MemStorNames), ⌜st = regStorIface s⌝ ∗ regStorRec s ms γs ∗
    memAppendTok ms γs σ p)

def regAppendedTok (st : Storage) (σ : StorState) (p : List raftpb.Entry) : IProp GF :=
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

def regN : Namespace := nroot.@"register"

/-- What `Put`/`Get`'s atomic update may open: everything but raft's commit invariant
and the register's. -/
def regMask : CoPset := (⊤ \ ↑raftN) \ ↑regN

/-- The minting discipline (see the file header). -/
def MintOk (M : GMap (List w8) Unit) (S : GMap w64 w64) (Mi : GMap (w64 × w64) (List w8)) :
    Prop :=
  (∀ d, M !! d = some () → ∃ k, opKey d = some k ∧ Mi !! k = some d) ∧
  (∀ i s d, Mi !! (i, s) = some d → ∃ n, S !! i = some n ∧ uint.Z s ≤ uint.Z n)

/-- The ticket of a replica's operation credits (`Auth Nat`). -/
structure RepNames [FfiSyntax] where
  node : NodeNames
  cred : GName

section ghost
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.register.Assumptions]
variable [RegStor GF]

/-- The client's half of the register's value. -/
def regVal (γr : RegNames) (x : List w8) : IProp GF :=
  ghostVar γr.val (1 : Qp).half x

def regInvBody (γr : RegNames) : IProp GF :=
  iprop(∃ (L : List (List w8)) (M : GMap (List w8) Unit) (S : GMap w64 w64)
      (Mi : GMap (w64 × w64) (List w8)),
    cLog γr.raft L ∗ ghostVar γr.val (1 : Qp).half (regFold L) ∗
    ghostMapAuth γr.raft.reFresh 1 M ∗ ghostMapAuth γr.seq 1 S ∗ ghostMapAuth γr.mint 1 Mi ∗
    ⌜MintOk M S Mi⌝)

/-- See the file header. -/
def regInv (γr : RegNames) : IProp GF := inv regN (regInvBody γr)

instance regInv_persistent (γr : RegNames) : Persistent (regInv (GF := GF) γr) := by
  unfold regInv; infer_instance

instance regInvBody_timeless (γr : RegNames) : Timeless (regInvBody (GF := GF) γr) := by
  unfold regInvBody; infer_instance

/-- What a waiter learns with the value `v`: the operation's datum `d` first occurs at
`m` in a committed log, and `v` is the register's value after it. -/
def waitP (γr : RegNames) (d : List w8) (v : List w8) : IProp GF :=
  iprop(∃ (l : List raftpb.Entry) (ods : List (Option (List w8))) (m : Nat),
    isCommitted γr.raft l ∗ ([∗list] e;o ∈ l;ods, entDataIs γr.raft e o) ∗
    ⌜ods[m]? = some (some d) ∧ d ∉ firstOcc (ods.take m) ∧
      v = regFold (firstOcc (ods.take m) ++ [d])⌝)

instance waitP_persistent (γr : RegNames) (d v : List w8) :
    Persistent (waitP (GF := GF) γr d v) := by
  unfold waitP; infer_instance

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
    "Hwaiters" ∷ [∗map] s ↦ ch ∈ W, waiterOk γr id s ch)

/-- Replica `id` at `r`, on node `n`, with the storage `st` (persistent). -/
def isReplica (γr : RegNames) (γp : RepNames) (r : Loc) (id : w64) (n st : Loc) : IProp GF :=
  iprop(
    "#Hpkg" ∷ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.register ∗
    "#Hid" ∷ r.[RRegister, go!"id"] ↦□ id ∗
    "#Hnode" ∷ r.[RRegister, go!"node"] ↦□ interface.mkOk (go.GoType.PointerType node.ty) #n ∗
    "#Hst" ∷ r.[RRegister, go!"storage"] ↦□ st ∗
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

/-- The `send` callback (`func([]pb.Message)`): it takes the messages of a `Ready`, with
what the node's `Ready` says of them (persistent). Delivering them to the peers'
`Node.Step` (copying a proposal's entries, which `Step` takes owned) is the transport's. -/
def sendSpec (f : GoFunc) (γn : NodeNames) : IProp GF :=
  iprop(□ ∀ (msl : GoSlice) (ms : List raftpb.Message),
    {{ msl ↦* ms ∗ [∗list] m ∈ ms, isRaftMsg γn.raft m ∗ termLB γn.bud m.Term' }}
      (App (Val #f) (Val #msl))
    {{ RET #(); True }})

instance sendSpec_persistent (f : GoFunc) (γn : NodeNames) :
    Persistent (sendSpec (GF := GF) f γn) := by
  unfold sendSpec; infer_instance

/-- The applier's state (the `run` goroutine's): the value and the applied-encodings
table, at the committed prefix `ap` it applied. -/
def runOwn (γr : RegNames) (r : Loc) (ap : List raftpb.Entry) : IProp GF :=
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

end EtcdGrove
end Perennial
