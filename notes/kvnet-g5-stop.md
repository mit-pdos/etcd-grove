# kvnet G5: a replica's clean stop and restart in its process (2026-11-24)

Why: `raft_kvnet_robust` should subsume kvreconf/kvdurable(+noax), which call raft's `node.Stop`
(`~/coordinator-notes`' raft-subsumption plan, gap G5). Before this change a kvnet incarnation ended only
when its process was killed. Now a client's `ReqDisrupt` of kind 3 (kvcheck's disruptor, one time in
eight) makes the process stop its incarnation cleanly and start the next one from its file.

## The Go change (`examples/raft/kvnet`, branch `kvnet-single/2026-11-24`)

- `replica.go`: kvdurable's stop plumbing is back. `Replica` has `stopc`, `runDone`, `tickDone` and
  `snapDone`. `run`, `ticker` and `snapshotter` select on `stopc` and send their done value, and `run`
  also does so on its `!fits` exit. `Replica.stop` is kvdurable's: close `stopc`, receive the three done
  values, `node.Stop()`, then `dmu.Lock()` **never unlocked** (nothing uses `dmu` afterwards; kvdurable's
  `crash` did lock+unlock over a disjunctive `kdDmuInv`, which kvnet's does not have).
- `transport.go`: `peerTransport` is an interface `{start(raft.Node); Send([]*pb.Message); stop()}`,
  made per incarnation by a `newPeerTransport` constructor. TCP's is `newTCPTransport`, which is
  `newTransport`. `Transport` has `stopc`. `Transport.stop` closes it, and `runPeer` selects on it, closes
  its connection and returns. The queues stay never closed (`isChanBag`). `Transport.servePeer` is gone.
- `node.go`: `Node{cfg, stats, newT, mu, r, t}`, where `mu` guards `r` and `t` and is held for the whole
  restart. The functions:
  - `current() *Replica`;
  - `stepPeer(m)`, which counts and steps `m` on `current().node` with `stepTimeout`. Both TCP's
    `Node.servePeer` and UDP's receiver call it;
  - `restart()`: lock, `stopIncarnation(n.r, n.t)`, count, `n.r, n.t = start(n.cfg, n.stats, n.newT)`,
    unlock;
  - `stopIncarnation(r, t)`: `r.stop()` then `t.stop()`;
  - `start(cfg, stats, newT) (*Replica, peerTransport)`: the old body of `StartNode`;
  - `startNode(cfg, newT)` and `StartNode(cfg) = startNode(cfg, newTCPTransport)`;
  - `accept(l)`: the accept loop. `Run = listen; StartNode(cfg).accept(l)`.

  `handle` and `status` read `current()` once. `handle`'s `ReqDisrupt` with `what == 3` calls
  `n.restart()`.
- `stats.go`: `StRestartsInProcess` (at the end). `kvcheck.go`: `disrupt` picks 3 one time in eight.
- Tests: `restart_test.go` `TestRestartInProcess` (20 restarts; every acknowledged write is read back
  after each one; race-clean); `driver` `TestRestartsInProcess` (4 random rounds: porcupine `Ok`,
  restarts in process 127/37/26/25 alongside 297/72/73/58 kills).

## The proof design (frozen; specs first)

### Replica layer (helper R)
Port of kvdurablenoax's stop (`RaftNoAx/{Spec,Proof}/.../kvdurablenoax/`: `Replica__stop`, `Replica__crash`,
`Replica__run`'s `stopc` branch, `Replica__ticker`, `Replica__snapshotter`, `newReplica`).
- `Defs.lean`: **done**. `KdRepNames` has `stopc sc rdc rd tdc td sdc sd`. `isReplicaR` has kvdurable's
  `#Hstopc #Hrdc #Htdc #Hsdc #HstopB #HrdH #HtdH #HsdH`. `repStopper` is kvdurable's. `runStart` has
  `handoffProducer ρ.rd false`.
- Specs: **done**.
  - `Replica__ticker`: `+ handoffProducer ρ.td false`.
  - `Replica__snapshotter`: `+ handoffProducer ρ.sd false`.
  - `newReplica`: post `+ repStopper γ vs dir id r`.
  - New `Replica__stop`: `{repStopper γ vs dir id r} r.stop() {∃ fl qc, kvStart γ vs dir id fl qc}`.
    This is the generation's start resource (`BootLemmas.lean`) at the same file invariant.
  - `Replica__run`'s statement is unchanged; `runStart` carries the producer.
- How `stop` gets `kvStart`:
  - From `runDone`: `run`'s half of `nodeRunning` and its claim `ghostVar ρ.ph.ph ½ v`. From
    `snapDone`: the other half.
  - `node.Stop` (`isNode`, `nodeRunning 1`) gives `nodeVacantA γ id x ∗ nodeArm n γ x`.
    `nodeArm_agree` with `#Harm` gives `x = ph.fl.x`.
  - `dmu.Lock()` gives `kdDmuInv`. Take `Hdh`, `Hcpm` and `Hlive`'s `kdWriter ph.fl S o`. `run`'s claim
    `v` against `kdPhaseInv`'s half settles the phase, and `run` returns only with its claim at
    `(none, S)`, so the phase is `idle`.
  - `kvStart`'s `ghostVar fl.wr ½ (S, ⟨cur, none⟩, none)` is `kdWriter fl S o` with
    `cur = kdFileVal o`. `fileHolds γ S cur` comes from opening `kdFileInvK` (writer halves agree; the
    crashed side is refuted with `notCrashed`, as `persist`'s proof does).
  - Persistent parts (`kdCluster`, `osInv`, `durInv`, `kdFileInvK`, `Hdf`, `Hidr`) come from
    `isReplica`.

### Transport and node layer (helper T)
- `TransportDefs.lean`:
  - Add the transport's stop channel to `isTransportCore`: `t.stopc ↦□ sc ∗ ownBroadcastChan sc γsc True
    .Unknown`. The `.Pending` closer comes from `newTransport`'s post.
  - **The peer-transport contract**, which UDP's transport proves too (send it to the UDP lead when
    stated). It is over an interface value `tv` and the methods resolved at `peerTransport.ty`:
    - `ptFresh F γ N id tv` (exclusive): `∀ n, isNode n γ N id -∗ WP tv.start(mkOk n) {ptRunning F γ N id
      tv}`.
    - `ptRunning F γ N id tv := ptSend F id tv ∗ ptStop tv`, where `ptSend` (persistent) is `□` the triple
      `{pkg ∗ msl ↦*{dq} ms ∗ [∗list] sendElem F m} tv.Send(msl) {msl ↦*{dq} ms}` (what `kv_sendSpec`
      turns into `sendSpec` for the method value), and `ptStop tv` (exclusive) is `WP tv.stop() {True}`.
    - `ptCtor F γ N id f` (persistent) is `□ ∀ am M sts`, the triple `{pkg ∗ am ↦$□ M ∗ (kvPeerAddrs-like:
      every other address's protocols) ∗ isStats sts} f(id, am, sts) {tv, ptFresh F γ N id tv}`.
    - TCP: `newTCPTransport.spec` is `ptCtor` at the function, from `newTransport`, `Transport.start`
      (which no longer needs `stepLaw`: receiving moved to the node), `Transport.Send` and the new
      `Transport.stop` (`{isTransportCore ∗ the .Pending closer} t.stop() {True}`). `runPeer`: `select`
      with `stopc`, `Close` on stop.
- `NodeDefs.lean`: `isNodeS` loses its node handle `n` and gains the incarnation stopper `stp`:
  - `nodeLockInv F rep stp nd cfg M γ N id := ∃ r tv n, nd.r ↦ r ∗ nd.t ↦ tv ∗ r.node ↦□ mkOk n ∗ □ rep
    r id ∗ isNode n γ N id ∗ stp cfg M r tv`.
  - `isNodeS F rep stp nd γ N id := ∃ cfg M sp f, nd.cfg ↦□ cfg ∗ ⌜cfg.ID' = id⌝ ∗ cfg.Addrs' ↦$□ M ∗
    nd.stats ↦□ sp ∗ isStats sp ∗ nd.newT ↦□ f ∗ ptCtor F γ N id f ∗ stepLaw F γ N id ∗ isMutex nd.mu
    (nodeLockInv …)` (persistent).
- New specs, generic in `rep`, `stp` and `S` like `StartNode`'s, proved at the concrete instantiation
  (`kvRep`, `kvNodeStart`, `stp := repStopper γ vs dir id r ∗ ptStop tv ∗ the persistent rest of
  kvNodeStart`):
  - `start.spec F rep stp S γ N`: `{pkg ∗ cfg.Addrs' ↦$□ M ∗ S id dir opts M ∗ isStats sts ∗ ptCtor F γ N
    id f ∗ stepLaw…} start(cfg, sts, f) {r tv, ∃ n, r.node ↦□ mkOk n ∗ □ rep r id ∗ isNode n γ N id ∗ stp
    cfg M r tv}`. This is the old `StartNode` proof.
  - `stopIncarnation.spec stp S`: `{pkg ∗ stp cfg M r tv} stopIncarnation(r, tv) {S cfg.ID' cfg.Dir'
    cfg.Opts' M}`. Concretely: `Replica.stop` gives `kvStart`, then `ptStop`, then reassemble
    `kvNodeStart`.
  - `Node.restart`, generic (callees `start`, `stopIncarnation`, `Stats.add`).
  - `Node.current`, `Node.stepPeer` (the old `servePeer`'s step part, with `stepLaw`), `Node.servePeer`
    (moved from `Transport`), `Node.accept`, `startNode`.
  - `StartNode.spec` keeps its statement, but `isNodeS` gains `stp`. `Run`/`RunNode` keep theirs.
- Changed users of `isNodeS`: `Node.serve`, `handle`, `serveClient`, `status` (read `current()`), and
  `Link.lean` (`etc/gen-link.py`) with the top-level modules (`TopStart`, `TopLevelRobustness`), whose
  statements must not change.

### Trust
No trusted file changes: no axiom, no premise, no semantics. The top-level statement
`raft_kvnet_robust` is unchanged (its program `RunNode` changed: it now restarts on request).
