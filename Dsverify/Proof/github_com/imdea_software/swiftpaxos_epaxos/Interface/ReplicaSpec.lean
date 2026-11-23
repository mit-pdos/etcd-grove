/-
The replica framework's function specs (`replica/replica.go`), grouped here as
`def replica.<Func>.spec : Prop` / `def replica.Replica.<Method>.spec : Prop`, over the predicates
of `Epaxos/Interface/Replica.lean`. Life cycle of a replica's framework:

1. `replica.New` (inside `epaxos.New`): from the replica's start resources (its peer/client
   address token, `repFwStart γ id`, the final list `L` and the shared invariants), `fwFresh`.
2. `epaxos.New` registers its nine kinds (`rpc.Table.Register`, channels with `deliverChanP`),
   writes `Beacon`/`Durable` (false) and its stats counters, then freezes (`fwFreeze`).
3. `ConnectToPeers` (in `run`): listens on `L[id]`, dials the lower ids (each connection
   registered as `peer id` with the dial token), accepts the higher ones (`serveConn`'s P1
   classification; their readers handed back through `done`), starts a reader goroutine per
   connected peer (`replicaListener`: reads messages, mints delivery tokens, sends `deliverable`
   objects on the kinds' channels, answers beacons); returns `isReplicaFw` (the lock allocated with
   `fwLockInv … Rext`, `Rext` the protocol layer's), the listener, and `PreferredPeerOrder`.
   Peers that could not be connected stay unconnected (`SendMsg` then sends nothing).
4. `ComputeClosestPeers` (beacons, then `PreferredPeerOrder` read-only: `prefOrder`).
5. `WaitForClientConnections` (its own goroutine, never returns): accepts clients
   (`clientListener`: one `PROPOSE` per connection, the writer registered, a `proposal` on
   `ProposeChan`).
6. The protocol layer's calls: `SendMsg`, `ReplyProposeTS`, `FastQuorumSize`, `SlowQuorumSize`,
   and its own `alive(q)` (`fwCore_alive`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Interface.Replica

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net github_com.imdea_software.swiftpaxos_epaxos.kvs model

attribute [local instance] GooseGlobalGS.gooseInvGS

section fwMethod
variable [GooseExts] [GoLocalContext] [GoGlobalContext] [go.Semantics]

/-- A method of the `*replica.Replica` `r`. -/
abbrev fwMethod (r : Loc) (m : GoString) : val :=
  r @!! go.GoType.PointerType replica.Replica.ty @!! m

end fwMethod

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]
variable [epaxos.Assumptions] [HasExt netExt] [π : NetProtoGS]

/-- The replica package's initialization. -/
abbrev pkgInit_replica : IProp GF :=
  isPkgInit (PROP := IProp GF) pkg_id.github_com.imdea_software.swiftpaxos_epaxos.replica


/-- `replica.New(alias, id, 2, addrs, true, true, false, cfg, logger)` as `epaxos.New` calls it
(failures 2, thrifty, exec, no local reads) for replica `id` of the final list `L` (node `k`'s
address at `id`), from the replica's start resources. -/
def replica.New.spec [state.Assumptions] [github_com.emirpasic.gods.maps.treemap.Assumptions] [StateTreemap GF] : Prop :=
  ∀ (γ : EpNames) (k id : Nat) (L : List GoString) (sl : GoSlice) (als : GoString)
    (cfg logger proxy : Loc) (c : config.Config),
  {{ pkgInit_replica (GF := GF) ∗ ⌜k ∈ replicaNodes ∧ L[id]? = some (peerAddrOf k)⌝ ∗ listFinal γ L ∗
      sl ↦*□ L ∗ clientInvs γ ∗ repFwStart γ id ∗
      cfg ↦□ c ∗ ⌜c.Proxy' = proxy⌝ ∗ proxy ↦□ (zeroValDef : config.ProxyInfo) ∗
      logger ↦□ (zeroValDef : dlog.Logger) }}
    (App (App (App (App (App (App (App (App (App (Val (@! replica.New)) (Val #als))
      (Val #(W64 id))) (Val #(W64 2))) (Val #sl)) (Val #true)) (Val #true)) (Val #false))
      (Val #cfg)) (Val #logger))
  {{ (r : Loc), RET #r; ∃ p : FwPtrs,
      ⌜p.logger = logger ∧ p.aliasStr = als ∧ p.addrs = sl ∧ p.cfg = cfg ∧ p.proxy = proxy⌝ ∗
      fwFresh γ r id L p }}

/-- `r.ConnectToPeers()`: see the file header (step 3). `Rext` is what the protocol layer puts in
`r.M`'s invariant. -/
def replica.Replica.ConnectToPeers.spec : Prop :=
  ∀ (γ : EpNames) (r : Loc) (id : Nat) (L : List GoString) (p : FwPtrs) (Rext : IProp GF),
  {{ pkgInit_replica (GF := GF) ∗ fwRO γ r id L p ∗ fwFrozen γ r id p ∗ fwStart γ r id L p ∗ Rext }}
    (App (Val (fwMethod r go!"ConnectToPeers")) (Val #()))
  {{ RET #(); isReplicaFw γ r id L p Rext ∗ fwListening γ r id L ∗ fwPrefOwn r id }}

/-- `r.WaitForClientConnections()`: accepts and serves clients forever (never returns). -/
def replica.Replica.WaitForClientConnections.spec : Prop :=
  ∀ (γ : EpNames) (r : Loc) (id : Nat) (L : List GoString) (p : FwPtrs) (Rext : IProp GF),
  {{ pkgInit_replica (GF := GF) ∗ isReplicaFw γ r id L p Rext ∗ fwListening γ r id L }}
    (App (Val (fwMethod r go!"WaitForClientConnections")) (Val #()))
  {{ RET #(); False }}

/-- `r.SendMsg(t, code, msg)`: the protocol message `m` (held by `msg`, read) to peer `t`.
The caller supplies the send update `sendUpd γ id t m Ψ` (`Epaxos/Interface/Net.lean`) or (`∧`,
the framework picks) `Ψnil`: if `t`'s writer is set, `SendMsg` runs the update under `r.M` on its
half of the list of messages to `t` (so `m` gets `msgSent` at the next position) and writes `code`
and `m`'s body (all of it, or a prefix and the writer breaks); the caller gets `Ψ`. If `t` is not
connected (writer `nil`), nothing is sent, the update does not run (no position is taken: a writer
installed later starts an empty stream, whose messages must be at positions `0, 1, ...`) and the
caller gets `Ψnil` (e.g. `sendUpd γ id t m Ψ` back, or the protocol layer's `ep_sendLost`).
`t ≠ id` is a documented scope premise (not needed by the code: its own slot's writer is always
`nil`, which is the `Ψnil` path; every caller establishes it). The message is read: its struct at
`dq`, its slices at their own fractions `dq1`, `dq2` (`msgObj`; e.g. a `PreAcceptReply` whose
`Deps` are a read-only instance's and whose `CommittedDeps` are the replica's own array). -/
def replica.Replica.SendMsg.spec : Prop :=
  ∀ (γ : EpNames) (r : Loc) (id : Nat) (L : List GoString) (p : FwPtrs) (Rext : IProp GF)
    (t : Nat) (msg : GoInterface) (m : Msg) (dq dq1 dq2 : DFrac) (Ψ Ψnil : IProp GF),
  {{ pkgInit_replica (GF := GF) ∗ ⌜t < L.length ∧ t ≠ id ∧ m.isProto = true ∧ m.wf⌝ ∗
      isReplicaFw γ r id L p Rext ∗ msgObj msg m dq dq1 dq2 ∗
      (sendUpd γ id t m Ψ ∧ Ψnil) }}
    (App (App (App (Val (fwMethod r go!"SendMsg")) (Val #(W32 t))) (Val #m.code)) (Val #msg))
  {{ RET #(); msgObj msg m dq dq1 dq2 ∗ (Ψ ∨ Ψnil) }}

/-- `r.ReplyProposeTS(reply, w, mu)`: the one reply to client connection `cid` (its writer `w`,
its reply token), `OK = TRUE`, `CommandId = 0`, a value `v` that the op's fired output `o` allows
(`replyValOk`), any timestamp. -/
def replica.Replica.ReplyProposeTS.spec : Prop :=
  ∀ (γ : EpNames) (r : Loc) (id : Nat) (L : List GoString) (p : FwPtrs) (Rext : IProp GF)
    (reply w mu : Loc) (cid : Nat) (o : KvO) (v : List w8) (vsl : GoSlice) (ts : w64)
    (dq dq' : DFrac),
  {{ pkgInit_replica (GF := GF) ∗ ⌜replyValOk o v ∧ v.length < 2 ^ 16⌝ ∗ isReplicaFw γ r id L p Rext ∗
      reply ↦{dq} replica.defs.ProposeReplyTS.mk okTRUE (W32 0) vsl ts ∗ vsl ↦*{dq'} v ∗
      clientWriter γ id w cid ∗ replyTok γ id w ∗ fired γ cid o }}
    (App (App (App (Val (fwMethod r go!"ReplyProposeTS")) (Val #reply)) (Val #w)) (Val #mu))
  {{ RET #(); reply ↦{dq} replica.defs.ProposeReplyTS.mk okTRUE (W32 0) vsl ts ∗
      vsl ↦*{dq'} v }}

/-- `r.SendBeacon(t)`: a beacon to peer `t` (if connected); not a protocol message. -/
def replica.Replica.SendBeacon.spec : Prop :=
  ∀ (γ : EpNames) (r : Loc) (id : Nat) (L : List GoString) (p : FwPtrs) (Rext : IProp GF)
    (t : Nat),
  {{ pkgInit_replica (GF := GF) ∗ ⌜t < L.length ∧ t ≠ id⌝ ∗ isReplicaFw γ r id L p Rext }}
    (App (Val (fwMethod r go!"SendBeacon")) (Val #(W32 t)))
  {{ RET #(); True }}

/-- `r.ReplyBeacon(b)`: a beacon reply to peer `b.Rid` (if connected). -/
def replica.Replica.ReplyBeacon.spec : Prop :=
  ∀ (γ : EpNames) (r : Loc) (id : Nat) (L : List GoString) (p : FwPtrs) (Rext : IProp GF)
    (b : Loc) (dq : DFrac) (t : Nat) (ts : w64),
  {{ pkgInit_replica (GF := GF) ∗ ⌜t < L.length ∧ t ≠ id⌝ ∗ isReplicaFw γ r id L p Rext ∗
      b ↦{dq} replica.defs.GBeacon.mk (W32 t) ts }}
    (App (Val (fwMethod r go!"ReplyBeacon")) (Val #b))
  {{ RET #(); b ↦{dq} replica.defs.GBeacon.mk (W32 t) ts }}

/-- `r.ComputeClosestPeers()` (no latency table): beacons to the live peers, then
`PreferredPeerOrder` is a permutation of the ids with `id` last, read-only from then on. -/
def replica.Replica.ComputeClosestPeers.spec : Prop :=
  ∀ (γ : EpNames) (r : Loc) (id : Nat) (L : List GoString) (p : FwPtrs) (Rext : IProp GF),
  {{ pkgInit_replica (GF := GF) ∗ isReplicaFw γ r id L p Rext ∗ fwPrefOwn r id }}
    (App (Val (fwMethod r go!"ComputeClosestPeers")) (Val #()))
  {{ (sl : GoSlice), RET #sl; ∃ ord : List w32, prefOrder r id L ord }}

/-- `r.FastQuorumSize()`: `F + (F + 1) / 2` with `F = 2`. -/
def replica.Replica.FastQuorumSize.spec : Prop :=
  ∀ (γ : EpNames) (r : Loc) (id : Nat) (L : List GoString) (p : FwPtrs),
  {{ pkgInit_replica (GF := GF) ∗ fwRO γ r id L p }}
    (App (Val (fwMethod r go!"FastQuorumSize")) (Val #()))
  {{ RET #(W64 3); True }}

/-- `r.SlowQuorumSize()`: `(N + 1) / 2` with `N = 5`. -/
def replica.Replica.SlowQuorumSize.spec : Prop :=
  ∀ (γ : EpNames) (r : Loc) (id : Nat) (L : List GoString) (p : FwPtrs),
  {{ pkgInit_replica (GF := GF) ∗ fwRO γ r id L p }}
    (App (Val (fwMethod r go!"SlowQuorumSize")) (Val #()))
  {{ RET #(W64 3); True }}

end heap

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
