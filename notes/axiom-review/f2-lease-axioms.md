# Review: the four interim lessor axioms of F2 (`etcd-safe-f2` @ `5ccca72e58`)

Read-only review (`etcd_dist.view`, `Proof/.../examples/etcd/dist/Lease*Dist.lean`): no Go test run and no
Lean proof written, so the program below is the shape of a counterexample, not a checked one.

## Verdicts

| axiom | verdict |
|---|---|
| `Lease_LeasesGranted_dist` | **UNSOUND today** (with `Lease_Grant_dist`), program below; sound once P-L1 lands |
| `Lease_Grant_dist` | **NEEDS-FIX** (the group's fix): sound alone, but its post is what the attack uses |
| `Lease_GrantLive_dist` | **NEEDS-FIX** (same fix); no attack without a `lessorSlot` nobody provides yet |
| `Lease_LeasesLive_dist` | **NEEDS-FIX** (same fix); same condition |

None is linked (only hypotheses of `client/leaseGrant.lean`, `leaseList.lean`, the Run* specs): no exported
result is affected today. The docstrings' "no linked result before P-L1" rule is checked by nothing.

## The flaw: every member has the same lessor name today

The statements quantify over every `Γ`. The only `Γ` a client can get an `etcdAddrAt` fact for is the start's
`ClusterNames.view = DistView.ofKV γk`, and that view has `ls := fun _ => 0`. So `Γ.ls A = Γ.ls B` holds by
`rfl` for any two members. `leaseGrantedAt (Γ.ls A) i id`, which the Grant post gives about member A, is
then also the premise that `Lease_LeasesGranted_dist` at member B asks for. But `LeaseLeases` is a local read:
`s.lessor.Leases()` with no read index and no leader check (`v3_server.go:739`; the v3rpc interceptor checks
the leader only under `WithRequireLeader`). A member that is lagging, or cut off from the leader, still
answers it. In Go, a grant at A is not listed at B until B applies it.

**Program** (a variant of `RunLeaseCatchup`, `examples/etcd/dist/client/lease.go:121`, with the grant moved
to the other member and no polling):
```go
cA := newClient([]string{eps[0]}); cB := newClient([]string{eps[1]})
g, err := leaseGrant(cA, maxLeaseTTL); if err != nil { return }
ls, err := leaseList(cB);              if err != nil { return }
if !listed(ls, g.ID) { panic("lease granted at A not listed at B") }
```
**Run:** a 3-member cluster in which member 1 is cut off from the others (or only slow to apply). The grant
commits through members 0 and 2 and is applied at member 0 before the reply. Member 1 then lists from a
lessor without the lease, and the program panics. This is the failure that `leaseCatchup` polls to avoid.
**Proof** (the triple, at `Γ := ofKV γk` with `γk.lm = .mono`, from the start's `etcdAddrAt` facts):
`Lease_Grant_dist` at member 0 gives `leaseGrantedAt 0 i id`. `Lease_LeasesGranted_dist` at member 1 with
`G = [id]` (since `Γ.ls 1 = 0`) gives `id ∈ ids`, so the `panic` branch is dead. No other axiom is needed
beyond the start's address facts (`etcdSvc`).

The revocable pair has the same defect, but the attack also needs `lessorSlot 0` (from `leaseMember`):
`GrantLive` at A gives `leaseLiveFrom 0 i id`, hence `lessorLb 0 i'`; `LeasesLive` at a lagging B gives
`id ∉ ids₁` at `j ≥ i'`; `LeasesLive` at A with `lessorLb 0 j` gives `ids₂` at `j₂ ≥ j`, and the absent-stays law
gives `id ∉ ids₂`. Go lists it at A: `if !inB && inA2 { panic }` is dead in the proof, fires in a run. No start provides `lessorSlot 0` yet (it needs `ghostMapAuth 0 ½ ∅` or `lessorHistOk 0`).

## The fix

P-L1 as `notes/etcd-dist-n9b.md` §11 item 2 plans it, with one requirement made explicit:
- the start allocates a **distinct** fresh `Γ.ls mid` per member (`ClusterNames.ls`);
- `NewServer` makes the member's lessor at exactly that name.

Then the cross-member premise cannot be met. Until then: add `lease.lessorSlot (Γ.ls mid)` to each premise
(as `memberCli` does), or `⌜∀ a b, Γ.ls a = Γ.ls b → a = b⌝` to the two `Leases` premises (`ofKV` fails it).
Also make the "no link before P-L1" rule a check in `etc/`.

## Attacks tried that failed (post-P-L1 reading, names distinct)
- **Lost grant reply:** clientv3 retries a mutable RPC only when it was never sent. A lost reply is the
  error arm, which claims nothing. A retried grant grants a fresh lease; the post names the id in the reply.
- **Grant reply before the member applies it:** `LeaseGrant` -> `raftRequest` waits on `s.w`, which only this
  member's apply triggers, after its `lessor.Grant`. An apply by snapshot never triggers it (timeout, error).
  ID 0 is refused by the loop at `v3_server.go:437`. A collision, including across members whose 16-bit
  prefixes differ only in bit 15 (masked by `&(1<<63-1)`), gives `ErrLeaseExists`, which is the error arm.
- **`Leases` listing a lease that has since expired (revocable):** the post is a snapshot at some `j ≥ n`.
  It claims nothing about the lease at reply time. The listing is taken under `le.mu`.
- **Mono and expiry (TTL, clock):** a short TTL would break `LeasesGranted`, but a member served at a mono
  view runs `lease.runCfg _ .mono` (`kvCongr` includes `lm`), which needs `lease.leasesNoExpiry`: such runs are
  outside every closed theorem. Say so in the docstrings (the premise comes through the member's start).
- **Lessor restart without a crash** (`applySnapshot` -> `lessor.Recover`): same object, same name. The
  backend is at a later index and holds every applied grant, with no revoke in mono mode. It is an
  in-process history step, and `histOnce` is proved there.
- **`lessorLb` passed between clients:** it exists only after the member reached `n`; later calls see `j ≥ n`.
- **`levelTok 0`, credits:** lent and returned as in `KV_*_dist`; no `£` involved (the law spends the caller's).
- **Ownership:** `sl ↦*` is clientv3's fresh slice, `↦□` a fresh struct's; `Nodup`: map keys.
- **With `Client_LeaseLeases_dist`/`Client_LeaseTimeToLive_dist`:** no history facts; nothing to combine.

Not tried: grpc size limits (`grpcRepliesFit`), learners (refuse `LeaseGrant`: error arm).
