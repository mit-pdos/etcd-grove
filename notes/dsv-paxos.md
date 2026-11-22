# dsv-paxos: dsverify-lab's paxos kit on the net extension (phase 6, first kit)

Branch `dsv-paxos` (2026-11-22). Plan: `notes/dsverify-net-port-plan.md`, phase 6. Source:
dsverify-lab `master` `7a84fb35`, `examples/paxos/` (run `paxos-net-3`, proof at tag `final`,
bumped there to Perennial `3afd77e35`; read only, nothing in the lab changed).

## What is where

| | here |
|---|---|
| Go | `examples/dsverify/paxos/` (module `github.com/xiang90/paxos`, the lab's fork path): the fork's `paxos` package and the kit `examples/paxosnet` with its ten commands `cmd/{orch,client0..3,server1..5}`; `kit_test.go` runs the ten machines in one process |
| translation | `etc/goose.py` project `dsv-paxos` into the part `Dsverify/` (lean_lib `Dsverify`; remote and `net` the part `Net/`'s, lintest and porcupine the main tree's, marshal Perennial's) |
| initializers | `etc/gen-init.py` `dsv_inits` (from `Net/`'s inventory with the part's added): `Dsverify/Proof/**/{Init,PkgTable}.lean`; marshal, which `Net/`'s `ExternalInit` does not list, through `Dsverify/Proof/runtime/PkgInitDsv.lean` (the same lemma, unguarded) |
| the protocol's proof | `Dsverify/Proof/github_com/xiang90/paxos/`: the lab's files, ported by editing (`Inv`, `Agents`, `MsgMethods`, `Acceptor/Learner/ProposerProof`, `Net` + `NetProof` the transport, `Deploy` + `DeployProof`, `Link`) |
| the kit | `.../paxos/examples/paxosnet/`: `Kit.lean` (the register as remote's store `woR`, its model's sets, the specs), `KitProof.lean`, `Mains.lean`, `Linked.lean` |
| the statement | `Dsverify/Spec/.../paxosnet/TopLevelRobustness.lean`: `paxos_remote_robust.spec`, `DistDeploy paxosKitAddrs (system σ) g → Robust [] (system σ) g threads (2^63)`; definitions in `Proof/.../TopLevelDefs.lean`; proof `Proof/.../TopLevelRobustness.lean` |
| trust base | `etc/tcb-collections/dsv-paxos.txt` |

## What changed against the lab

- **The deployment is remote's** (the plan's phase 6: kits ported onto `examples/lib/remote`, the
  verified porcupine in place of the lab's porcupine axiom and driver). The lab ran the four clients
  on one client node with its own driver, recorder and write-once checker; here an orchestrator
  machine runs `remote.Check` against the **write-once register with pending proposals** (a
  porcupine model, `kit.go`'s `Model`; linkv's pending-writes store `woB`), and each client is a
  machine of its own (`remote.ServeClient`), so ten machines. `netcluster.go`'s layout changed
  accordingly: the address list is acceptors, learners, then client `c`'s own address, and
  `NewNetCluster(addrs, me, ...)` hosts client `me`'s two agents only. The clients' staggering is
  in the operation (client `c` waits `(c/2)·StaggerMs` before proposing). Addresses are
  `127.0.0.1:74xx` (counter's choice; valid for `DistDeploy`).
- `Client` makes its paxos node **before** `ServeClient` and its `newClient` returns it: remote's
  `ServeClient.spec` takes `newClient` as a persistent triple with precondition `True`, which cannot
  consume client `c`'s one-shot tokens, and a second node of client `c` would reuse its proposer's
  proposal numbers (a real safety requirement of the protocol, not only of the proof). Design
  finding for remote: a `newClient` that needs exclusive resources (or must run once) cannot use
  `ServeClient` as specified; the kit sidesteps it in Go.
- **The client's update is remote's linearization point** (`Inv.lean`, `opAU`): a one-shot fancy
  update `|={⊤∖paxosEop, ∅}=> ∃ σ, own_state Γ σ ∗ (own_state Γ (woStep v σ).1 ={∅,⊤∖paxosEop}=∗ Φ …)`
  in place of the lab's atomic update at `clientN`; it is `remote.lin (woR Γ)` (`lin_opAU`) and is
  fired by `opAU_commit` (from the acceptor's helping step or the client's return). The register's
  state is the paxos invariant's other half, kept by remote's pending library.
- **The transport** (`NetProof.lean`) is over `Net/Spec/net/*` (taken as hypotheses, linked) and
  `Proto.lean`'s laws: `Write` + `writeP`/`write_acc` (the writer token grows by a prefix of the
  frame), `Read` + `read_au` (reads give `recvTokL`; a frame's protocol fact costs a later credit),
  `Listen` + `listen_au`, `Accept` + `accept_au` (the listener owned by `acceptLoop`), `DialTimeout`
  + `dial_au`, `Close`/deadlines + `close_au`/`deadline_au`. The specs of `tcpnet.go` keep the lab's
  shape (`is_node`, `own_net`, `wireProto Φ`/`noProto`); `serve` no longer threads an address token.
  `readFull`'s proof is remote's, with paxos's early return on any error.
- `Propose.spec`'s answer also gives the value's bound (`len < 2^48`, from the report's `msgWf`).
- Tactic drift from Perennial `3afd77e35` to `74471ecd8`: range loops over slices (`slice.forRange`),
  `forMapPostcondition`'s fifth case, `decide` on goals with instance variables, bag lemmas need
  `ncfupd_of_fupd`, `time.After`'s clock bound (`time.After.spec_pkgInit`), slice literals.

## State

Compiles: the translation, the whole paxos package's proof and Link, the kit's proofs, mains and
links, and `paxos_remote_robust` (`#print axioms`: `propext`, `sorryAx`, `Classical.choice`,
`Quot.sound`). The `sorry`s (all in `Dsverify/Proof/.../paxosnet/KitProof.lean`):

- `Model.wp_proof`: `Model()` meets `woS` (`isModel`): `step`, `push`, `has`, `erase`, `equal` on
  the Go `State{Known, Val, Pend []string}`, and `woSet`'s laws (the configurations a state stands
  for, closed under late effects, and the four kinds of step). The counter's `ModelDefs.lean` is the
  template (its state is two integers; here a read-only slice).
- `Codec.wp_proof`: `Codec()` meets `codecOk (woR Γ)` (string/byte conversions, `append`).

No axiom of this repository is added. Not done: the per-function spec/proof file layout (the
lab's hub files are kept, as for its Link); `etc/gen-link.py` does not generate these Links
(hand-written, like the lab's); the TCB collection's baseline (needs a full build).
