# Review of the combined F7+F2 proposal (`etcd-safe-f7` @ `5b15e37521`, `AuthServeProposed.lean`)

Read-only (`axiom` skill); no Go test or Lean proof, so attacks are shapes. Go: `.lake/go-src/etcd/server/etcdserver/server.go`.

## Verdicts

| target | verdict |
|---|---|
| `NewServer.specG_dist_proposed` (+ `authNamesFreshD`) | **SOUND** |
| `Serve_dist_proposed.spec` (+ `memberUpOnL`, `memberUpL`) | **SOUND**, provided it *replaces* `Serve_dist` (see 3) |
| usability (start → NewServer → boot → Serve) | **USABLE**: no statement change needed; five proof links are missing (see 2) |

## 1. NewServer against Go: sound

Each difference from `NewServerDist.lean` is justified:
- **The binders `γa`, `γl`.** The Go construction does not depend on ghost names.
- **`Hγa`, `authNamesFreshD γa`** (auth on only).
  - Go calls `auth.NewAuthStore` unconditionally (`server.go:370`).
  - The 12 authorities are exactly what the in-process proof allocates today: `authHist_alloc` (`auth/Model.lean:625`, which gives hist ¾+¼, cur ½+½, pub, fen, fca, cap, bk, succ, rdt), `ghostMapAuth fresh ∅` (`authFreshInit`), `tokAlloc` (`tok`) and the `rdy` mono-nat.
  - Nothing is missing or extra. No name is counted twice inside it: `tokAuth` owns `γa.tok`, and `authFreshInit` owns `γa.fresh`.
- **`Hlslot`**, i.e. `ghostMapAuth γl ½ ∅ ∗ lessorSlot γl`.
  - Go calls `lease.NewLessor` exactly once, unconditionally, before `mvcc.New` (`server.go:345`).
  - `lease.NewLessor.specAt` (proved from `newLessor.specAt`, via `newLessor_alloc_at`; no `Link` uses it yet) consumes exactly this premise.
  - A snapshot restores the same lessor object (`s.lessor.Recover`, `:1087`), so its name is stable.
- **Post `mvccLeases E.γ = γl`: true.** `mvcc.New(..., srv.lessor, ...)` (`server.go:367`) gets `NewLessor`'s lessor, and `mvcc.New`'s spec carries its name into the store (`γ.st.leases = γl`, `Spec/.../mvcc/New.lean:96`; `mvccLeases γ` is `γ.leases`).
- **Post `E.authMode = .on γa` replaces `∃ γa`.** It is the same store, at the caller's name.
- **No double counting.** `γa` and `γl` are disjoint families of names. No other premise holds an auth or lessor
  name (`newServerStoreFreshA`: st/cr/slog/nlog; `srvReadNamesFreshNK`: cursor/applied/committed/notifier/logs/
  pend/hi), and the post returns no authority at `γa` or `γl`. Before the call the caller can keep only true lower
  bounds at the boot values; it cannot pin `γl` (needs both halves; a second slot is blocked by the mask).
- **The error arm.** If `NewServer` fails before `NewLessor`, the slot stays open forever with half of the authority lost. This is harmless: a `lessorAt γl` fact exists only on a lease axiom's success arm, which needs a member served at `γl`.

Retirement obligations (in the docstring): the in-process `specG` restated at the caller's `γl` (via
`NewLessor.specAt`), `auth_store_boot_on` taking the caller's names, `srvTpInv_alloc` taking a given `γa.rdy`.

## 2. Usability: the chain, and the missing links

1. **Start (`ClusterStart`/`clusterAllocN`).** Per member, allocate `γl` (`ghostMapAuth γl 1 ∅`, split, `inv_alloc lessorSlotN` with one half) and, with auth on, `γa` (`authNamesFreshD γa`). Then define `Γ.ls`, `Γ.au` injective over all `w64`: the members' names, plus padding for non-members with names above every allocated one. After that, `etcdAddr_set` at `Γ`.
2. **Hand-over.** `memberSliceOf`/`memberShareD` carry the other half, the slot and `authNamesFreshD` to the member's machine.
3. **Member (`MainLogger.wp_proof`).** It calls `NewServer.specG_dist_proposed` at `γa := Γ.au mid`, `γl := Γ.ls mid`, and gets from the post `mvccLeases E.γ = γl`, `E.authMode = .on γa`, and `lease.srvInv on srv E m`, which gives `srvLeaseRd srv E m` (`srvLeaseRd_of_srvInv`) with `m = ρ.rd.kv.lm = Γ.kv.lm` (`lease.bootCfg`, `kvCongr`).
4. **The serving resources.** Build them as today:
   - auth off: `memberUpL`, the `memberUp` conjuncts at `MainLogger.lean:308-407`, at `m` in place of `.none`, plus the equation;
   - auth on: `memberUpOnL`, by `memberUpOn_intro`'s parts as authkv's `startServer` does, plus the equation.
5. **Serve.** `Serve_dist_proposed` at `c.view`; the guarded premise holds by step 1's injectivity.

Missing links (proof work only; every statement involved is satisfiable):
- **L1.** There is no `authNamesFreshD_alloc`. It is easy: `authHist_alloc` with `authHist_full`, `ghost_map_alloc_empty`, `tokAlloc` and a mono-nat alloc.
- **L2.** There is no `lessorSlot_alloc`.
- **L3.** `ClusterNames` has no `ls`/`au` fields, and `ClusterNames.view` is still `DistView.ofKV` (constants, which fail the injectivity premises).
- **L4.** `memberShareD`/`memberSliceOf` do not carry the new resources.
- **L5.** With auth on, the deployment has no path: `AdequacyMember`'s `Hauth : d.cfg.auth = false` and
  `memberCfg_off` need an auth-on counterpart meeting NewServer's auth-on config premises (`AuthToken "simple"`,
  TTL bound), `kvInvM true` at the start, and `□ (srvTLSId s -∗ False)` (from `ClientCertAuthEnabled ↦□ false`).

## 3. Condition C and the lease ties: holds, conditionally

- **Proposed Serve is the only server of `etcdSvc`.** `etcdSvc` is an opaque axiom with no law, and `grpcServeTok` needs `grpcServes Svc …` (`InvGrpcRun.lean:173`), which no proof can give for `etcdSvc Γ mid`. So the in-process `etcdstart.Serve.spec`, whose view shift lets the caller choose `Svc`, and a raw `grpc.Server.Serve` cannot serve it.
  With the proposal, `Serve_dist_proposed` is the only server. Both of its branches tie `Γ.ls mid`, and the auth-on branch also ties `Γ.au mid`.
- **Mode mismatches are blocked.** `.on γa` contradicts `E.authOn = false`, and the reverse likewise. A revocable
  `Γ` needs `lease.srvInv … .revocable`; `srvLeaseRd`'s restart disjunct is `.none` only.
- **Two servers for one `(Γ, mid)` are impossible**: they need two halves of `γl`'s authority or two `authNamesFreshD`.
- **Caveat (an ordering constraint, no hole in the proposal).** Six unlinked lease axioms already on the branch
  (`Lease_Grant_dist`, `_GrantLive_`, `_LeasesGranted_`, `_LeasesLive_`, `Client_LeaseTimeToLive_dist`,
  `Client_LeaseLeases_dist`) read `Γ.ls mid` and are unsound beside the *current* `Serve_dist` (any auth-off `Γ`,
  no `Γ.ls` tie: a start-owned `Γ.ls mid` plus a real Grant gives `leaseLiveFrom` about a fake history).
  - **So the current `Serve_dist` must be deleted in the same step that the proposal lands, never kept beside it, and no result may link these axioms before then.** Their docstrings say "until P-L1 is in, no linked result may use this axiom"; I would also add an `etc/tcb-collections` or gate check for it.

## 4. New holes from the merge: none found

Tried: the slot double-opened (mask); a caller-made pin at `γl` (needs the whole authority, leaving nothing for
`Hlslot`); `γl` colliding with a `γa` field (both premises; the post returns nothing); the error arm after
`NewLessor` (Go has closed the slot); `m = .none` (`NewLessor` still runs); `γa` unused with auth off; the same
member at two addresses (its stocks, `γl` and `nodeVacant` are exclusive).
The restart limit (no-crash only) is in the docstring. I found no issue in the verified Go code.
