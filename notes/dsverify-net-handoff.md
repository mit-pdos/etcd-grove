# Handoff: dsverify-lab onto the net extension, shared library models (2026-11-21)

For whoever continues this work. The plan is `notes/dsverify-net-port-plan.md` (its Section 2 lists
every decision; each phase records its state); this note is the snapshot: what is done, what is open,
where it lives, the user's decisions, and the traps. `origin/lean` at writing: `3e3862765b`.

## The goal (the user's, 2026-11-17)

Port dsverify-lab's network kits onto etcd-grove's network semantics, and have **one network semantics
and one set of library models (net/http, gRPC, net/rpc, protobuf, JSON) shared by etcd and the dsverify
examples**. Copy from dsverify-lab what is needed. dsverify-lab's runs must never see etcd-grove (the lab
consumes an export, phase 3).

## The user's decisions (all recorded in `notes/decisions.md`)

- **"The net extension"**, never "the TCP extension": names say `net` (`GooseLang/Ext/Net`, `netExt`,
  part `Net/`). It **stays in etcd-grove** until further notice.
- **We never launch dsverify-lab runs**; kit proofs are ported by editing them.
- **One canonical spec per Go function**: dsverify's Hoare triples for `net` are not added as second
  specs; its vocabulary is a library of laws over our specs (`GooseLang/Ext/Net/Proto.lean`).
- **The kits' statement is `Robust`** (`Robustness/Statement.lean`): `DistDeploy … → Robust [] nodes g
  bound`, every kit machine stable (no restart), proved through the bridge `Net/Statement/DistBridge.lean`
  from Perennial's no-crash `goose_dist_adequacy`.
- **Models are first-class Go packages in `models/`** (not patches of the real packages): the model of
  grpc-go is `models/grpc`, of net/http `models/net/http`, ...; the difference from upstream is a
  computed artifact (`models/diff.py`). Each model's trusted claim: every behavior of the real library
  that the program observes is a behavior of the model (more is fine, fewer is unsound).
- **Trusted generated code: the generator is the trusted artifact** (`models/protobuf/pbgen_core.py`):
  inputs derived from the real schema/types, hard refusals outside the subset, a small documented core,
  generator-level differential tests over random schemas, a `--check` gate.
- **D25** (Go's write lock): a waiting `Write` step may only stutter (the user: "stuttering is ok for
  Write because it's sound to do so"). **F1** (Go panics past 2^20 waiters on one socket): a known
  limitation, not modeled.
- **kvnet's net changes** (2026-11-21, the user's task text in `notes/net-tcp.md`, v3.4): no plan, no
  hosts; `addrOk` addresses; a listening token; specs; the net+fs bundle.

## Done (on `origin/lean`)

| What | Where | Notes |
|---|---|---|
| plan, reference copies of dsverify's harness at `348a866` | `notes/dsverify-net-port-plan.md`, `old/dsverify/` | not built |
| the rename tcp → net | `GooseLang/Ext/Net/`, part `Net/` (lean_lib `Net`), goose project `net`, `lake exe net-replay` | |
| net semantics v3.3 | `Impl.lean` D23 `"tcp4"`, D24 socket options, D25 write lock | review `notes/axiom-review/tcp-semantics.md` v3.3 |
| net semantics v3.4 (for kvnet) | `Impl.lean`: no plan/hosts, `addrOk`/`listenOk`/`lisAccepts`, `NetLocal.init`, `NetGlobal.init`, `crash_init`; `netLisTok` (atomic update at `Listen`, lives in an invariant, survives crashes); `GooseLang/Ext/NetFs/Adequacy.lean` (`kvnetExts = [netExt, fsExt]`, `kvnet_dist_crash_adequacy`) | review v3.4; `notes/net-tcp.md` |
| the kits' net library | `GooseLang/Ext/Net/Proto.lean` (+ `Stream.lean`) | the coverage table lab-name → our spec + law is in the plan, phase 4 |
| the kits' statement | `Net/Statement/{DistDeploy,DistBridge}.lean`; echo's instance `…/examples/net/echo/RobustLinked.lean` (`echo_dist_robust`) | `DistDeploy` since v3.4: distinct valid addresses, no connections, no listeners |
| codecs | `models/protobuf/` (`pbgen_core.py`, `pbdesc`, `pbgenrand`), `models/pbcodec`, `models/json/jsongen.py` (old form), `models/jsoncodec`; Go module `models.lab`; Lean `Net/*/models_lab/` | `models/README.md`; review `notes/axiom-review/pbgen.md` |
| gate fix | `etc/gates.sh`: the k8s race control runs with `-count=1` | a cached pass had made every landing fail |

## Open work, in order

**Landed (2026-11-21): `lean` `ed897615f5`** (the land queue, claim #24): items 1-3's work below, the
branches and their worktrees deleted. Items 1-3's remaining Lean work and phase 7 now follow
`notes/phase7-plan.md`; coordination is on GitHub issues (#8), this work's claim is #24.

**Update (2026-11-21, second session; superseded by the line above).** Items 1-3's Go halves are ready to land as one stack:
`models-rpc-http-lean` (`50e9626bd2`: merged with `origin/lean`; item 1's `ErrShutdown` checked: the
model produces it too, about one run in 20 in both builds, a race in Go's `Client` code, which the
model keeps, so the test now allows it) ← `models-grpc-land` (`models-grpc` merged, `models/diff.py`
the fuller script with grpc's entry and dropped-package report; `TestAtMostOnce` fixed: grpc-go's own
spurious clean end of a server stream after a transparent retry, `nonissues/grpc-transparent-retry-spurious-eof.md`)
← `models-json-land` (`models-json` merged: gates.sh, README, goroot.py, the plan resolved). All on
origin. Checked on `models-json-land`: the gates' whole `models` section (`go vet`/`go test` of
`models` at go1.27.3, jsongen `--check` of both inputs, `rpcdifftest/run.sh`, `grpcdifftest/run.sh`,
`jsonstreamtest/run.sh`, `examples/models`), `etc/goose.py --check --project models` and
`--project models-net`. **Not done: the full `lake build`** (stopped at 12499/19030 jobs by the
machine's memory pressure while another session built; `Net/Code/models_lab/jsoncodec.lean` changed,
so `Net`'s jsoncodec proofs are rebuilt), hence no `etc/land.sh`. Next: from the worktree holding the
`.lake` (`agent-a6df7e3fe86988fc1`, now on `models-json-land`), `lake build`, then `etc/land.sh` (it
lands all three), push `lean`, delete the merged branches (`models-rpc-http`, `models-rpc-http-lean`,
`models-grpc`, `models-grpc-land`, `models-json`, `models-json-land`) and their worktrees.

1. **net/rpc Lean half: land it.** Branch `models-rpc-http-lean` (origin, `a83b1c5a49`; on
   `models-rpc-http`'s Go half, merged with lean): translations compile; proved (no axiom): the frame
   codec, `readFull`/`readFrame`, the codec registry, `clientCodec.ReadResponseHeader`; collection
   `etc/tcb-collections/models-net.txt`. Its landing failed in the `models` gate: the fault test
   (stream cut at every byte) saw `ErrShutdown` **from real net/rpc**, outside the expected set.
   **Do not just widen the test**: check the model can produce `ErrShutdown` in that situation; if it
   cannot, the model under-approximates real net/rpc (unsound) and must be fixed. Then fix the plan
   note's and STATUS's premature "landed" wording on that branch, merge lean, `etc/land.sh`, push.
   Remaining Lean work (none of it stated yet): the other codec methods, the protocol vocabulary
   (`RpcWorld`), `Client.Call` (keep dsverify's at-most-once handler run), the server, package init
   (needs net/http's initializers translated first), `DialHTTPPath`, the net/http server proofs (Go's
   real server: the largest item). `go/token.IsExported` is modeled (exact on ASCII, arbitrary
   otherwise) in `Net/TrustedCode/go/token.lean`.
2. **gRPC model, Lean half.** Go half on branch `models-grpc` (origin `cb1a05cfca`): grpc-go v1.84.0's
   source with the transport/connection management replaced (one stream per connection, the real
   HTTP/2 preface), 32 differential tests (`models/internal/grpcdifftest/run.sh`), 13 etcd examples
   pass over it. Known gap: no keepalive, so `examples/etcd/partition`'s failover tests fail over the
   model in Go runs (sound, but not faithful in timing). Its report's list of functions needing specs
   and goose risks is in the plan, phase 5.4. When landing with `models-rpc-http`: both touch
   `models/diff.py`; keep the fuller one and add grpc's entry.
3. **JSON model.** Branch `models-json` (origin `f6ab1827fd`): `jsongen` reworked to the trusted-generator
   standard, `models/encoding/json` (Go 1.27.3's default `encoding/json` is v1-over-v2: model and tests
   target that), stream transcript tests. Lean half not started. vsr's fork must name its unnamed
   decoding struct (goose).
4. **Phase 6, the kits.** The proofs are in dsverify-lab `master` `examples/<system>/` (`9cbb866` or
   later): paxos, craq, vr, rabia, epaxos, quepaxa, gryff, swiftpaxos, each with `goal/`, `proof/`,
   `fork/`, `harness/`, `src/`, `SOURCE.md` (Perennial `4c8617a9e`, each with its own harness copy).
   Port into a part `Dsverify/`, merging the harness copies into one; order: paxos (raw TCP: needs
   nothing more), vr (JSON model), rabia (bufio law: blocked on Perennial, below), epaxos/gryff (bufio,
   net/rpc), craq (net/rpc over http), swiftpaxos (net/rpc, gob, sha256), quepaxa (gRPC). Each goal
   becomes `DistDeploy … → Robust [] …`. `DistDeploy` changed in v3.4: re-check the plan's phase 6 text.
5. **Phase 3, the export** to dsverify-lab: a standalone Lake package of the net extension, `Net/`,
   `Robustness/Statement.lean`, `models/`, with a leak check (no etcd/raft names). Known leak: the
   proved stream library's remaining files under `Net/Proof/github_com/mit_pdos/etcd_grove/examples/net/
   wire/`. Changing dsverify-lab itself needs the user's go-ahead (nothing there has been touched;
   its local clone was only fetched).
6. **Phase 7, etcd onto the models**: its own stage (`notes/specs-only/tcp-extension-design.md`
   §5-7 for the old design; now with first-class models).

## Perennial changes needed (`notes/perennial-changes.md`)

- **`init`/`globalInit` on `ExtSemantics`** (the user's item 2 for kvnet; `Robust` will require it):
  landed in Perennial by the kvnet session as `ExtSemantics.initLocal`/`initGlobal` with `_init`
  adequacy wrappers (`c0ec40070`), and `goose_dist_mixed_crash_adequacy` (some machines crash, others
  never: `19fd486f6`), per STATUS's kvnet entry of 2026-11-21; **etcd-grove's pin is not bumped yet**.
  At the bump: plug net's `NetLocal.init`/`NetGlobal.init` (standalone in `Impl.lean`, with
  `crash_init`) into the net extension's `ExtSemantics` instance, give fs its own, and revisit
  `DistBridge` (the mixed adequacy also lets a kit's servers crash while its client does not).
- **A stronger listening token** (held while the listener is open, returned by a crash) needs per-node
  ghost state that can refer to global ghost state. The invariant-based token suffices for kvnet.
- `wp_slice_copy`'s count as `sint.Z` (blocks the bufio-over-connection law, hence rabia, epaxos, gryff).
- goose taking `-overlay` (today the std models need a GOROOT farm, `models/goroot.py`), goose's
  module name for vendored packages, `type Delim rune`.

## Traps

- **Never `rm`** (it prompts the user and stalls the session): `git worktree remove [-f -f]`, `lake
  clean`, `go clean -cache`.
- **One Lean build environment fits on the disk** (a `.lake` is 25-45 GB). Move it between worktrees
  with `mv`, never copy. The built one is in `.claude/worktrees/agent-a6df7e3fe86988fc1` since 2026-11-21 (moved from `agent-a9a5dda109e09fcc9`, built there at
  `b5b7ee6f58`).
- **A notes-only landing must be notes-only against LOCAL `lean`** (`git diff --name-only lean HEAD`),
  or `etc/land.sh` runs the full gates and builds a 30 GB `.lake`. Local `lean` and `origin/lean`
  drift apart; other sessions push often.
- **Never push an unbuilt merge** to `origin/lean`; build and gate, then push (fast-forward only).
- The gates' Go tests run with the test cache on: a "must fail" control needs `-count=1`.
- `PATH` in agent shells lacks `/usr/local/go/bin` (goose and the gates need it).
- dsverify-lab's `examples/` must never be visible to a lab run (its README); copying into etcd-grove is
  fine.

## Worktrees of this session (clean up when their branches land)

`.claude/worktrees/`: `agent-a6df7e3fe86988fc1` (`models-rpc-http-lean`), `agent-a97fc578e8756c45c`
(`models-rpc-http`), `agent-a638714fbba963503` (`models-grpc`), `agent-a9a5dda109e09fcc9` (merged
`net-noplan`; holds the built `.lake`), `agent-ac80d2f2ef6b1e568` (merged), `dsverify-net-plan`
(this note's).
