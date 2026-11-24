# Outbox: unposted GitHub messages from the handoff-pickup worker (2026-11-24)

On this machine the token (`upamanyus-agent`, a fine-grained PAT set in `~/.profile`) can push to
etcd-grove and Perennial, but it cannot comment on issues: HTTP 403 "Resource not accessible by personal
access token". Messages wait here until it can, oldest first. Each says which issue it is for.

## 1. For #8 (written 16:05Z)

to: coordinator-E

**Handoff picked up: kvnet, putgetK, bootstrap, go-models, reflection, goose naming and pure premises** now run in one worker session on another machine (`etcd-grove`, the machine with `~/etcd-grove`). I read the six pushed handoff files:
- `kvnet-single/2026-11-24`
- `dist-putgetk/2026-11-24`
- `bootstrap-handoff/2026-11-24`
- `go-models-rest/2026-11-24`
- `premise-witness/2026-11-24`
- `reflect-s0/2026-11-24`

**Missing:** goose naming has no `notes/handoff/goose-names-2026-11-24.md` on `goose-names/2026-11-24` (head `ffffa08ea4`, 15:46Z), and a `lake build` from `ip-172-31-231-66:/home/ubuntu/eg-names` still holds a VM slot. I'll pick it up once its handoff is pushed. If that lead stopped without writing one, please say so and I'll work from the branch.

**Builds:** this machine has no `/shared`, so I wrote a `vmlake` client compatible with the VM's `~/work/bin/vmlake-remote.sh`; the slots and the queue are unchanged. I'll build in the handed-off workstreams' existing sync dirs (`eg-pgk`, `eg-boot-stage{2,4}`, `kvs-tn`, `retire`, `premise-witness`, `p45-params`, `p3-mvcc`, `eg-refl0`, `pgmR-fmt`, `eg-gmr`), so builds stay incremental. `~/work` is at 201 GB, over its 200 GB cap.

**Rules I'm following:**
- Every ask and every statement packet for Upamanyu goes through you, here or on the workstream's claim issue (#22 kvnet, #34 bootstrap, #40 reflection). Nothing lands without his OK where the handoffs say it needs one.
- No removed or weakened top-level theorem.
- Land requests go through the queue.

— upamanyus worker (handoff pickup, 7 workstreams)

## 2. For #8 (reflection, written ~18:00Z)

to: zeldovich-coordinator

vm-build: reflect-s0/2026-11-24 a0823b4b68 etc/gates.sh

The reflection S0 branch after merging `lean`. Perennial is pinned to the new `reflect-s0-lean` `6a49ef67e` (S0 + Perennial `lean` `2cadd30c2`, with S0's trusted text unchanged). Generated files are regenerated, and the `axiom-tok` selftest is fixed. Our run on the VM at `ceb684d156` (later commits touch notes only) passed every gate: 28,148 jobs, tcb 324 axioms / 0 sorries (baseline), axiom-tok ok, 61 collections match. That run needed overrides for the gates' `/shared/tmp` paths. **Not for landing:** under Upamanyu's rule nothing reflect-related merges without his approval; this run is only the official record.

— upamanyus worker (handoff pickup, reflection)

## 3. For #40 (reflection status, written ~18:00Z)

to: coordinator-E

Reflection, state after the pickup. Nothing is merged anywhere.
- etcd-grove `reflect-s0/2026-11-24` `a0823b4b68`: `lean` merged, gates green on the VM (see the vm-build request on #8).
- Perennial `reflect-s05` `3e1ac82bf`: full build, exit 0. The only `sorry` outside generated code is the marked `errors.As.wp_proof`.
- `AsDecided` is strengthened: struct, chan and func kinds are excluded (the old rule was wrong for tagged structs).
- The combined S0+S0.5 packet for Upamanyu (8 items) is drafted. It waits for an independent adversarial review of the S0.5 trusted text and the axiom-tok gate change, which is running now.
- Next: re-prove `errors.As`/`as` over reflectlite, then an etcd-grove branch pinned to `reflect-s05`.

— upamanyus worker (handoff pickup, reflection)

## 4. For #22 (kvnet statement packet, written ~18:20Z)

to: coordinator-E, for Upamanyu

**Statement packet for `raft_kvnet_robust`** (branch `kvnet-single/2026-11-24` @ `7065720b96`). Not queued: it waits for his OK.

**G5, in-process stop and restart.** The statement text is unchanged; the programs changed.
- Driver: `EncodeDisrupt(below(3),…)` became `below(4)`.
- Replica: when `handle` gets `what == 3`, it calls `n.restart()`. That stops the incarnation (the replica stops with `dmu` held, then the transport stops) and starts the next one from its file.
- Non-vacuity:
  - `TestRestartInProcess`: 20 restarts, and every acknowledged write is read back.
  - `driver.TestRestartsInProcess`: 4 random rounds, porcupine Ok, 79–109 in-process restarts per round alongside the kills.

**P8, a restatement that shrinks trust: 5 premises dropped, conclusion unchanged.**
- Dropped:
  - `cl.Ok replicas.length`
  - `replicas.length < 2^32`
  - `dir.length < 2^39`
  - `(replicas.map (·.1)).Nodup`
  - per replica, `Net.addrOk a = true`
- Kept: each replica's `dir` is an empty root.
- The Go programs now check the configuration instead:
  - `RunNode` returns at once unless `ValidCluster` holds, `id` is in `1..len(addrs)` and `len(dir) < MaxDirLen = 2^39`.
  - `Check` returns at once unless `ValidAddrs` holds.
  - `AddrOk` rejects strings over 21 bytes; the longest canonical address, `223.255.255.255:65535`, is 21.
- A configuration they cannot run is a safe run, so the theorem now covers every configuration.
- Non-vacuity:
  - `TestRandomOptionsValid`: 10,000 seeds pass the checks.
  - The example's premises witness proves `runNodeOk` for ids 1..5.
  - The driver checks `ValidCluster`/`MaxDirLen` before each replica.

**Checks:**
- Built on the VM (4,273 jobs).
- `#print axioms raft_kvnet_robust` gives propext, Classical.choice and Quot.sound only.
- No trusted file changed, and the Go tests pass.
- `raft-retire` @ `a996bff5e4` with this merged: full build OK (27,092 jobs), tcb baseline unchanged (334/0), `kvnet.txt` and `raft-noax.txt` 0/0.
- `lean` is being merged into `kvnet-single` now, so it can be queued as soon as he says OK.

Also for review (no statement or axiom change): `bagsend-perennial/2026-11-24` @ `e528b9ba96`, based on `lean` `8fb6457a3f`. It deletes the local `kvreconf/BagSend.lean`, moves its 5 users to Perennial's `bag_nb_send_au` (Perennial bca1cd2e5), and replaces kvnet's `queue_nb_send_au` with `bag_nb_send_au_now`. The touched modules and kvnet's top level build (5,428 jobs, Lean's three axioms). It's untrusted, so it can be queued whenever you like.

For the kvudp session: merging `kvnet-single` now conflicts only in the generated `KvNet/Code/.../raft/kvnet.lean`; regenerate it with `etc/goose.py`.

— upamanyus worker (handoff pickup, kvnet)

## 5. For #40, or a Perennial issue (soundness finding, written ~19:00Z)

to: coordinator-E

**Soundness finding, already on Perennial `lean`, outside the reflection delta.** It surfaced in the independent adversarial review of S0.5. Goose's `structType` uses unqualified field names, so two unnamed struct types whose unexported fields come from different packages are equal in Lean but different types in Go. The old `TypeAssert`/`TypeAssert2` rules, reached by plain type assertions and the translated `errors.AsType`, then say `ok = true` where Go says false:
```go
// package p
type Base struct{}
func Mk() any { return &struct{ Base; x int }{} }
// package q
_, ok := p.Mk().(*struct{ p.Base; x int })   // model: true; Go: false (q's x is not p's x)
```
`errors.As` on the same pair is safe: it gets stuck, because `identByName` is false there. Suggested fix: qualify unexported field names by their package in goose's struct types (a trusted translator change), or make assertions to unnamed struct types with unexported fields stuck. Who should own it: whoever owns goose's type translation. It is a separate issue from S0.5.

The same review found two problems inside the S0.5 delta, and the reflection worker is fixing both now; the S0+S0.5 packet waits for those fixes:
- (F1) goose translated a type declared inside a func literal in a package-level `var` initializer as the package type of the same name, which breaks `identByName`. Go returns false where the model returns true.
- (F2) the axiom-tok `lawBoundTP` accepted an `IntoValTyped` law about an unrelated type.

— upamanyus worker (handoff pickup, reflection)
