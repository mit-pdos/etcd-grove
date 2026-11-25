/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/Names.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

The run's ghost names (`DriverDistSpec.Γs`): one record per subsystem, each sealed in its own
module (`HUBS.md`'s slot convention): a change inside a subsystem changes its record, not the hub.

Port: imports `Net/`'s net/rpc vocabulary (`Net.Proof.net.rpc.Proto`, `RpcWorld`) in place of the
lab's `Harness.Proof.net.rpc.Results` and nothing of the hub `Slots`, so that the protocol's pure
layers, which import the names, reach no unproved library spec.
-/
module

public import Net.Proof.net.rpc.Proto

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial.gryff

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

/-- The deployment's names (master registry). `registry`: the master's registrations, a
mono-list of `"addr:port"` strings in registration order (its prefix order is the replica ids). -/
structure DeployNames where
  registry : GName

/-- Stage 2's names (D9, `GryffProof/Proto2/InvDefs.lean`; `notes/stage2-interface-I.md`):
* `pred`: each replica id's predicted words (`Nat ↦ Option (List w64)`, a ghost map: `none` until
  the master registers the node that becomes that replica id (D13), then a persistent element,
  `predIdIs`; the unset elements wait in the registry's invariant, `predSlot`);
* `nodePred`: each replica node's predicted words (`Nat ↦ Option (List w64)`, keyed by the
  registry's node index `k`, node `k + 2`; `none` until the node's boot records its package
  prophecy, `pred_set`, then a persistent element, `predIs`; D13);
* `claim`: each replica node's claim of its replica id's start resources from the registry
  (`Nat ↦ Unit`, exclusive elements, `slotClaimTok`; D13);
* `budget`: the clients' operation budget units (`Nat ↦ Unit`, exclusive elements, `budget`;
  24 units, keys `0 .. 23`, 4 to each client node (stage 3); D14);
* `trace k`: replica id `k`'s real trace of model events (a mono-list; half in the invariant, half
  in the replica's lock invariant, `traceHalf`);
* `hist`: the real history of labels `(replica id, event)` in real order (a mono-list, the
  invariant's);
* `rxCur`: per directed pair `(k, q)` the number of messages of `k`'s stream to `q` handed out as
  receive tokens (a ghost map, the receiving side's exclusive element);
* `rx`: the receive tokens not yet consumed, `(k, q, n) ↦ m` (a ghost map, exclusive elements);
* `reqs`: the client requests' tokens not yet consumed, `(cid, rid) ↦ (replica id, input)`;
* `connRep`: each client connection's replica id (persistent elements). -/
structure Proto2Names where
  pred : GName
  nodePred : GName
  claim : GName
  budget : GName
  trace : Fin 3 → GName
  hist : GName
  rxCur : GName
  rx : GName
  reqs : GName
  connRep : GName
deriving Inhabited

/-- The register protocol's names (Gryff's invariant, `GryffProof/Proto/Inv.lean`):
* `reg`: the abstract register (a ghost variable; the client's `own_state` is the other half);
* `lin`: the linearized operations with their outputs, in order (a mono-list);
* `tagVal`: the value of every tag ever stored (a ghost map, append-only, persistent elements);
* `stores`: each replica node's register (value, tag) (a ghost map; node `k`'s lock invariant
  owns its element);
* `storeLbs`: lower bounds of the stores' tags (a ghost map of persistent elements);
* `ops`: the client operations, by (client id, request id): input and the client's names, fixed
  at registration (a ghost map of persistent elements, H-U4-7);
* `places`: the operations' places, by operation id, fixed once (a ghost map of persistent
  elements, H-U4-7);
* `insts`: the EPaxos instances' committed attributes (a ghost map, persistent elements);
* `execSeq`: the agreed chain of executed RMWs (a mono-list);
* `preds`: each replica node's predicted execution sequence (D2: its prophecy; a ghost map);
* `turns`: each Gryff client id's next request id and whether its last request is pending
  (exclusive turn tokens, H-U4-4);
* `nodeIds`: each replica node's registration id (a ghost map, persistent elements);
* `conns`: each Gryff client id's connection, once bound (`none` while unused; exclusive
  elements while unused, persistent once bound; H-U4-8);
* `placers`: each accepted connection's placing counter (the last request id it placed; a ghost
  map, the acceptor's exclusive element; H-U4-8). -/
structure ProtoNames where
  reg : GName
  lin : GName
  tagVal : GName
  stores : GName
  storeLbs : GName
  ops : GName
  insts : GName
  execSeq : GName
  preds : GName
  turns : GName
  nodeIds : GName
  places : GName
  conns : GName
  placers : GName
  /-- the accepted connections whose requests are placed (a ghost map `Nat ↦ Unit` of
  persistent elements, `connPlaced`; the placers' invariant's: port, in place of the lab's
  read-only fresh-end tokens, which `Net/`'s `connFresh` has no persistent form of) -/
  placed : GName
  /-- stage 2's names (the invariant `gryffInv2`; `reg`, `lin`, `ops`, `turns`, `conns`,
  `placers` above are shared with it) -/
  s2 : Proto2Names

/-- The run's ghost names. -/
structure GryffNames [GooseExts] (GF : BundledGFunctors) where
  deploy : DeployNames
  proto : ProtoNames
  /-- the rpc world of the master's and the replicas' rpc addresses -/
  rpc : net.rpc.RpcWorld GF

end Perennial.gryff
