/-
**The raft wrapper's construction** (stage R8b-C of the raft v3.7 retarget, 2026-10-16; D12:
`notes/decisions.md`, "The new cluster's start"): what `newRaftNode` (`raft.go`) and the new
cluster's `bootstrappedRaft.newRaftNode` (`bootstrap.go`) are specified over, beside
`InvRaftNode.lean`'s predicates of the running wrapper. Lean-first (no Rocq counterpart).

* **The contracts** on the names-only callees and on what Perennial does not model, persistent
  triples the specs take in their preconditions (as `isServerBuilt` takes the names-only parts'
  contracts, `clusterVersionOk`): `NewRaftLoggerZap` (`zap_raft.go`, names-only: some logger
  interface, `rnLoggerZapOk`); raft's `SetLogger` (translated with its body, but its globals
  `raftLogger`/`raftLoggerMu` are allocated by raft's package initializer and their ownership
  dropped, `Init.lean`, so the write is not provable: `rnSetLoggerOk`); `contention.NewTimeoutDetector`
  (names-only: `isRNTimeoutDetector`, `rnTimeoutDetectorOk`); `time.NewTicker` (Perennial models no
  ticker: `isRNTicker`, the tick credits with the ticks, D10; `rnTickerOk`); the server's package
  globals `raftStatus` (a function value) and `raftStatusMu` (the mutex protecting it; not in the
  package facts `srvRaftInit`, which hold the metrics only: `rnRaftStatusOk`, the mutex's
  invariant owning the function); `serverstorage.NewStorage` (names-only: the WAL, `isRNWal`,
  `rnNewStorageOk`); `membership.RaftCluster.IsIDRemoved` (names-only: some boolean,
  `rnClusterOk`, from which the `isIDRemoved` closure meets `isRNIDRemoved`).
* **`rnBuilt E γ r cv`**: the wrapper as `newRaftNode(cv)` leaves it, before `NewServer` copies
  it into `EtcdServer.r` (`r: *b.raft.newRaftNode(...)`, by value), sets its `transport` and
  `start` runs it: the struct value owned whole at `r`, with the components `newRaftNode` alone
  provides (`rnParts`, persistent, on the value: the detector, the ticker, `stopped`'s bag,
  `done`'s broadcast channel, `msgSnapC`'s bag, `applyc`'s SPSC channel, `readStateC`'s bag of
  answered read states), `tickMu` a fresh `RWMutex` (its guard over `latestTickTs` is made where
  the struct finally lives: `isRaftNode_of_rnParts`, `NodeStart.lean`, which adds what the node
  and the server provide, `rnEnvOk`, the node's contract, the storage's, the transport's),
  `cfg`'s fields as the caller gave them, both halves of `applyc` with `cum` at `[[]]`, and the
  right to close `done`. The names `γ` are the wrapper's (`RNNames`): `newRaftNode` allocates
  `ap`, `cum` and `done`, the rest are the caller's.
* `srvIdxOk_boot`: the bootstrap log (`BootLogOk`) passes the server's `srvIdxOk` at the applied
  index `0` (its entries are v1 conf changes whose bytes decode: `isConfChangeEncoding`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRaftNode
public import Proof.go_etcd_io.raft.v3.Protocol.Facts
public import Proof.Lib.Iris

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

/-! ## The bootstrap log passes `srvIdxOk` -/

section pure
variable [FfiSyntax]

/-- **The bootstrap log at the applied index `0`** (D12): `BootLogOk`'s entries have the
consecutive indices `1..n`, are v1 conf changes whose bytes decode (raft's `ccDecodeV1`, the
server's `isConfChangeEncoding` since stage R8b), and `n < 2^61`. -/
theorem srvIdxOk_boot (ccOk : w32 → List w8 → Prop) (ps : List w64) (bootLog : List EntryM)
    (h : BootLogOk ccOk ps bootLog) : srvIdxOk (W64 0) (bootLog.map EntryModel.ofM) := by
  obtain ⟨hlen, hbound, hk⟩ := h
  refine ⟨?_, ?_⟩
  · simp only [List.length_map]
    rw [show uint.Z (W64 0) = 0 by word]
    omega
  · intro n m hm
    rw [List.getElem?_map] at hm
    obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.mp hm
    obtain ⟨-, hidx, hty, ⟨cm, hdec, -, -⟩, -⟩ := hk n e he
    refine ⟨?_, Or.inr ⟨?_, ?_⟩⟩
    · simp only [EntryModel.ofM]
      rw [show uint.Z (W64 0) = 0 by word]
      omega
    · simp only [EntryModel.ofM]; exact hty
    · simp only [EntryModel.ofM]; exact isConfChangeEncoding_of_decode hdec

end pure

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-! ## The contracts (see the file header) -/

/-- **`NewRaftLoggerZap(lg)`** (names-only): some logger interface value, for a non-nil zap
logger. -/
def rnLoggerZapOk : IProp GF :=
  iprop(□ ∀ lg : Loc, {{ ⌜lg ≠ null⌝ }} (App (Val (@! NewRaftLoggerZap)) (Val #lg))
    {{ (l : GoInterface), RET #l; True }})

instance rnLoggerZapOk_persistent : Persistent (rnLoggerZapOk (GF := GF)) := by
  unfold rnLoggerZapOk; infer_instance

/-- **raft's `SetLogger(l)`** (a contract: the ownership of its globals is not kept by raft's
package initializer). -/
def rnSetLoggerOk : IProp GF :=
  iprop(□ ∀ l : GoInterface, {{ True }} (App (Val (@! go_etcd_io.raft.v3.SetLogger)) (Val #l))
    {{ RET #(); True }})

instance rnSetLoggerOk_persistent : Persistent (rnSetLoggerOk (GF := GF)) := by
  unfold rnSetLoggerOk; infer_instance

/-- **`contention.NewTimeoutDetector(d)`** (names-only): a detector meeting `isRNTimeoutDetector`. -/
def rnTimeoutDetectorOk : IProp GF :=
  iprop(□ ∀ d : time.Duration, {{ True }}
    (App (Val (@! go_etcd_io.etcd.pkg.v3.contention.NewTimeoutDetector)) (Val #d))
    {{ (td : Loc), RET #td; isRNTimeoutDetector td }})

instance rnTimeoutDetectorOk_persistent : Persistent (rnTimeoutDetectorOk (GF := GF)) := by
  unfold rnTimeoutDetectorOk; infer_instance

/-- **`time.NewTicker(d)`** (Perennial models no ticker): for a non-zero `d`, a ticker meeting
`isRNTicker E` (its ticks carry `E.T`: until D19b, 2026-10-18, raft's tick credit, minted by the
ticker; now `True` for the server, `raftNode.tick` taking the credit, a time receipt, itself). -/
def rnTickerOk (E : RNEnv GF) : IProp GF :=
  iprop(□ ∀ d : time.Duration, {{ ⌜d ≠ W64 0⌝ }} (App (Val (@! time.NewTicker)) (Val #d))
    {{ (tk : Loc), RET #tk; isRNTicker E tk }})

instance rnTickerOk_persistent (E : RNEnv GF) : Persistent (rnTickerOk E) := by
  unfold rnTickerOk; infer_instance

/-- **The package globals `raftStatus` and `raftStatusMu`** (`raft.go`): the mutex owns the
function value (`raftStatus` is read by the `expvar` closure registered at init, under the
mutex; `bootstrappedRaft.newRaftNode` writes it once, under the mutex). -/
def rnRaftStatusOk : IProp GF :=
  sync.isMutex (globalAddr raftStatusMu) iprop(∃ f : GoFunc, globalAddr raftStatus ↦ f)

instance rnRaftStatusOk_persistent : Persistent (rnRaftStatusOk (GF := GF)) := by
  unfold rnRaftStatusOk; infer_instance

/-- **`serverstorage.NewStorage(lg, w, ss)`** (names-only): the WAL as the raft loop uses it
(`isRNWal`). -/
def rnNewStorageOk : IProp GF :=
  iprop(□ ∀ (lg w ss : Loc), {{ True }}
    (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.NewStorage)) (Val #lg)) (Val #w))
      (Val #ss))
    {{ (st : GoInterface), RET #st; isRNWal st }})

instance rnNewStorageOk_persistent : Persistent (rnNewStorageOk (GF := GF)) := by
  unfold rnNewStorageOk; infer_instance

/-- **`cl.IsIDRemoved(id)`** of the cluster `cl` (`membership.RaftCluster`, names-only): some
boolean. -/
def rnClusterOk (cl : Loc) : IProp GF :=
  iprop(□ ∀ id : w64, {{ True }}
    (App (Val (cl @!! go.GoType.PointerType api.membership.RaftCluster.ty @!! go!"IsIDRemoved"))
      (Val #id))
    {{ (b : Bool), RET #b; True }})

instance rnClusterOk_persistent (cl : Loc) : Persistent (rnClusterOk (GF := GF) cl) := by
  unfold rnClusterOk; infer_instance

/-- `tickMu`'s resource is fractional (for `sync.init_RWMutex`). -/
instance rnTickInv_fractional (r : Loc) : Fractional (rnTickInv (GF := GF) r) := by
  unfold rnTickInv
  exact fractional_exists_agree (fun (t : time.Time) q => iprop(rnLatestTickTsAddr r ↦{DFrac.own q} t))
    (fun t => fractional_of_dfractional (fun dq => typedPointsto (rnLatestTickTsAddr r) t dq))
    (fun x y q1 q2 => by
      iintro ⟨H1, H2⟩
      icombine H1 H2 gives %H
      ipureintro; exact H)

/-! ## The wrapper as built -/

/-- **The wrapper's components** (persistent): the predicates on the struct *value* `rv`'s
components, independent of where the struct lives (`NewServer` copies `*newRaftNode(...)` into
`EtcdServer.r` by value): the logger non-nil, `msgSnapC`'s bag, `applyc`'s SPSC channel,
`readStateC`'s bag of answered read states, the ticker, the detector, `stopped`'s bag and `done`'s
broadcast channel (its `Unknown` view). -/
def rnParts (E : RNEnv GF) (γ : RNNames) (rv : raftNode) : IProp GF :=
  iprop("%Hlgnn" ∷ ⌜rv.lg' ≠ null⌝ ∗
    "#Hmsci" ∷ isRNMsgSnapC E rv.msgSnapC' ∗
    "#Hapci" ∷ isRNApplyc E γ rv.applyc' ∗
    "#Hrsci" ∷ isRNReadStateC E rv.readStateC' ∗
    "#Htki" ∷ isRNTicker E rv.ticker' ∗
    "#Htdi" ∷ isRNTimeoutDetector rv.td' ∗
    "#Hstci" ∷ isUnitBag rv.stopped' ∗
    "#Hdnci" ∷ ownBroadcastChan rv.done' γ.done iprop(True) .Unknown)

instance rnParts_persistent (E : RNEnv GF) (γ : RNNames) (rv : raftNode) :
    Persistent (rnParts E γ rv) := by
  unfold rnParts; infer_instance

/-- **The raft wrapper `r` as `newRaftNode(cv)` leaves it** (see the file header): the struct
value `rv`, owned whole at `r` (to be copied), with `cfg`'s fields as the caller gave them
(`raftNodeConfig' = cv`, so `transport` is `cv`'s, nil), its `tickMu` a fresh `RWMutex` (the
guard over `latestTickTs` is made where the struct finally lives, `isRaftNode_of_rnParts`), the
components' predicates (`rnParts`), `applyc`'s two halves with `cum` at `[[]]` (the loop's and
the apply side's ghost state, `rnLoopTok`/`rnApplyTok`), and the right to close `done`. -/
def rnBuilt (E : RNEnv GF) (γ : RNNames) (r : Loc) (cv : raftNodeConfig) : IProp GF :=
  iprop(∃ rv : raftNode,
    "Hr" ∷ r ↦ rv ∗
    "%Hrv" ∷ ⌜rv.lg' = cv.lg' ∧ rv.raftNodeConfig' = cv⌝ ∗
    "Hmu" ∷ rv.tickMu' ↦ (zero_val sync.RWMutex) ∗
    "#Hparts" ∷ rnParts E γ rv ∗
    "Hprod" ∷ spscProducer γ.ap ([] : List toApply) ∗
    "Hcons" ∷ spscConsumer γ.ap ([] : List toApply) ∗
    "Hcum" ∷ monoListAuthOwn γ.cum 1 [([] : List EntryModel)] ∗
    "Hcum0" ∷ monoListIdxOwn γ.cum 0 ([] : List EntryModel) ∗
    "Hdtok" ∷ ownBroadcastChan rv.done' γ.done iprop(True) .Pending)

end defs

end EtcdGrove
end Perennial
