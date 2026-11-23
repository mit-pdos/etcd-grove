/-
The run's ghost names (`EpNames`): one record, chosen once at the start, that every node's share and every cross-package predicate is
indexed by.

Each subsystem has its own small structure of names (defined here, with a docstring saying
what it will hold), so that adding a name later changes only that structure. The client side's
names are fields of `EpNames` itself (they are needed now): the abstract key-value state's ghost
variable (`kv`), the escrow's map of fired outputs (`fired`), the connection-role registry
(`roles`) and the escrows' names (`escrows`).
-/
module

public import Perennial.Ghost.GhostMap

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris

/-- The master's ghost names (server 1 (node 11), `master.Master`; `Epaxos/Interface/Registry.lean`): the
write-once final node list (`listFinal`, `listUnset`) and the node tokens of the registration
exchange (`nodeTok k`, traded for replica-id tokens, `notes/stage1-plan.md`, "Registration and
replica ids"). -/
structure MasterNames where
  /-- the final node list: a ghost map over the one key `()`, its authority (empty) the
  master's right to fix the list, its persistent element the list -/
  list : GName
  /-- the node tokens: a ghost map from a replica node `k` (2..6) to `()`, each element whole -/
  nodes : GName

/-- The replicas' framework ghost names (`replica.Replica`): the replica-id tokens `idTok i`
(`Epaxos/Interface/Registry.lean`), and the peer streams' and client writers' ghost state
(`Epaxos/Interface/Net.lean`, `Epaxos/Interface/Replica.lean`). Per-direction / per-replica names
are functions (the start allocates the 25 / 5 it needs). -/
structure RepNames where
  /-- the replica-id tokens: a ghost map from a replica id `i` (0..4) to `()`, each element
  whole -/
  ids : GName
  /-- the protocol messages sent from replica `f` to replica `t`, in order: an append-only list
  (`sent f t`), its authority in two halves (`sentHalf`: the sender's framework, under `r.M`,
  and the protocol layer), its persistent index facts `msgSent` -/
  sent : Nat → Nat → GName
  /-- the delivery tokens of the stream from `f` to `t` at `t` (`deliv t f`): a ghost map from a
  position to `()` (`delivTok`, whole elements), its authority the minting right (`delivFrom`) -/
  deliv : Nat → Nat → GName
  /-- the dial right of replica `d` to replica `i`'s address (`dials d i`): a discardable ghost
  variable, `none` while unused (`dialTok`), then the connection's id, persistent (`peerConn`) -/
  dials : Nat → Nat → GName
  /-- replica `i`'s registered client writers (`cwriters i`): a ghost map from the
  `*bufio.Writer` to its connection's id (`clientWriter`, persistent elements) -/
  cwriters : Nat → GName
  /-- replica `i`'s reply tokens (`replies i`): a ghost map from a client writer to `()`
  (`replyTok`, whole elements): one reply per client connection -/
  replies : Nat → GName

/-- The EPaxos protocol's ghost names (`epaxos`, the invariant `epInv`; the bodies are the epaxos
package's, `Epaxos/Proof/epaxos/GhostDefs.lean`): per replica `i` (`i < 5`), the history of its
protocol states (`rep i`: a fractional mono-list of `RState`s, a quarter in `sysAuth`, three
quarters in `repFrag γ i σ`; its last element is the state, its elements give `crtLb`), its
outboxes (`outbox i to`), its pending broadcast (`pend i`), its executor's progress (`cur i`)
(ghost variables, a half in `sysAuth`, a half in the fragment), and its re-proposal tokens
(`chan i`: a ghost map from a fresh key to the proposal, its authority in `sysAuth`). -/
structure ProtoNames where
  rep : Nat → GName
  outbox : Nat → Nat → GName
  pend : Nat → GName
  cur : Nat → GName
  chan : Nat → GName

/-- The run's ghost names (`RemoteDistSpec.Γs`). -/
structure EpNames where
  /-- the abstract key-value state: a ghost variable over a finite map (`kvHalf`,
  `Epaxos/Interface/Client.lean`), one half the client's `own_state`, the other the replicas' -/
  kv : GName
  /-- the escrow's fired outputs: a ghost map from a client connection's id to the output its op
  linearized with (`fired`, `firedAuth`); the authority is the replicas' -/
  fired : GName
  /-- the connection-role registry: a ghost map from a connection id (to a replica's
  peer/client address) to its role (`ConnRole`), registered by the dialer with its `connFresh`
  token (`roleInv`) -/
  roles : GName
  /-- the escrows' names: a ghost map from a client connection's id to the names of its op's
  escrow (`escrowNames`: the claim token, and the one-shot fire state, a discardable ghost
  variable `none` while pending, then the output, persistent), registered with the role
  (`roleInv`), persistent elements -/
  escrows : GName
  /-- the master's names -/
  master : MasterNames
  /-- the replica framework's names -/
  rep : RepNames
  /-- the protocol invariant's names -/
  proto : ProtoNames

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
