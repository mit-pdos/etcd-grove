# Re-review F7 group C after fixes (`etcd-safe-f7` @ `6d9d9fd662`)

Read-only (axiom skill): no Go test run, no Lean proof written. The attacks below are shapes, not checked
counterexamples. Diff vs `d946f6cbda`: `S2Interim.lean` (`DistView.au`), `AuthViewDist.lean`,
`AuthServeProposed.lean`, and `MemberLessor.lean` (new, identical to `etcd-safe-f2` @ `54fa3c9780`).

## Verdicts

| draft | verdict |
|---|---|
| `Lease_GrantOn_dist` | **SOUND**, given the proposed Serve and the merged NewServer (N1) |
| `Lease_RevokeOn_dist` | **SOUND**. It reads no `Γ.ls` |
| `Lease_TimeToLiveKeysOn_dist` | **SOUND**, given the proposed Serve. F1 and F2 are closed and `Γ.kv.lm = .revocable` is present |
| `Lease_LeasesOn_dist` | **SOUND**, given the proposed Serve |
| `NewServer.specG_dist_proposed` + `authNamesFreshD` | SOUND as a statement, but **NEEDS-FIX (N1)**: without F2's `γl`, no start can meet the new Serve |
| `Serve_dist_proposed.spec` | **SOUND**. Usability nit N2 (the `Γ.au` injectivity premise also binds auth-off views) |
| `etcdstart.memberUpOnL` / `memberUpL` | SOUND definitions. `memberUpOnL` is `memberUpOn` verbatim plus `m` and `mvccLeases E.γ = γl` (checked against `etcdstart/Defs.lean:607`); `memberUpL` is the same over `memberUp` (`:466`) |

## 1. Are both holes closed? Yes.

- **Minting is still unrestricted.** `etcdAddr_set` (`S2Interim.lean:121`) still mints `etcdAddrAt a Γ mid` for any `Γ`, but it spends `addrUnset a`, so each address gets one view.
- **A view nobody serves is harmless.** The only server of `etcdSvc` is `Serve_dist`. `etcdSvc` has no law, so a raw grpc `Server.Serve` serves only an empty method set. If no member serves `Γ`, Go fails the call, and that is the error arm.
- **`Γ.au` is closed (F1).** To serve `(Γ, mid)` with auth on, the start must give `memberUpOnL … (Γ.au mid)`. That needs a server `E` with `E.authMode = .on (Γ.au mid)`. The only way to get one is `NewServer.specG_dist_proposed` at `γa := Γ.au mid`, which takes `authNamesFreshD γa`: all 12 authorities, whole. The start keeps only lower bounds that agree with the boot values, so it cannot own a history that refutes the verdicts.
- **`Γ.ls` is closed (F2).** `memberUpL`/`memberUpOnL` require `mvccLeases E.γ = Γ.ls mid` and `srvLeaseRd s E Γ.kv.lm`, which is the real lessor's `lease.srvInv` at that name. Every lease fact goes through `lessorAt γl i σ = ∃ γr, lessorPinR γl γr ∗ (mono list at γr)`, and the pin is a discarded ghost-map element at `γl`.
  - Under the merged NewServer, both halves of `γl`'s map authority go away: one into `lessorSlot γl`, one to `NewLessor.specAt`. The start cannot insert its own pin, and two pins at `γl` agree on `γr`.
  - Under today's NewServer, `E.γ` is fresh inside NewServer, so a `Γ.ls mid` the start owns cannot equal it.
- **`ofKV` cannot be served.** Its placeholders (`ls = 0`, `au` constant) fail the drafts' distinctness premises and Serve's `Γ.au` injectivity, and `mvccLeases E.γ = 0` cannot be arranged. So no proposed axiom is usable at `ofKV`, and it gives no hole.
- **Modes agree.** `kvCongr` includes `lm` (`InvRequest.lean:965`), and `lease.bootCfg` forces `lm = m` (`LeaseApi.lean:69`). So Serve's `Γ.kv.lm` is the mode NewServer gave `srvInv`.

## 2. Can a real start meet Serve's new premises? Not with F7's NewServer text alone (N1)

- **N1 (NEEDS-FIX).** F7's `NewServer.specG_dist_proposed` has no lessor binder.
  - Its post gives `∃ E` with `envAgree E E₀`, and `envAgree` (`InvBuild.lean:67`: `γs, Nx, γrev, cmp`) does not fix `E.γ`. So `mvccLeases E.γ` is a name chosen inside NewServer.
  - The view is fixed before any machine runs, and nothing is published to clients (O1 option B). So no start can make `Γ.ls mid` equal that name.
  - Both `memberUpL` and `memberUpOnL` are therefore unprovable, and the proposed Serve is useless with this text, for auth off as well as on.
  - F2's `NewServer.specG_dist_proposed` (`etcd-safe-f2:Spec/.../dist/NewServerDist.lean:308`) supplies the missing parts: the binder `γl`, the premise `"Hlslot"` (`ghostMapAuth γl ½ ∅ ∗ lease.lessorSlot γl`), and `mvccLeases E.γ = γl` in the post.
  - **Fix:** write one merged text, F7's `γa`/`Hγa` plus F2's `γl`/`Hlslot`/post equation. Have the start allocate a fresh `γl` and `γa` per member, and set `Γ.ls mid := γl` and `Γ.au mid := γa`.
  - With that text, `memberUpOnL` follows from the post: `E.authMode = .on γa` from `on = true →`, `mvccLeases E.γ = γl`, `srvLeaseRd` from `lease.srvInv on srv E m` (`srvLeaseRd_of_srvInv`), and the rest as `memberUpOn` is met today.
  - The two proposals touch disjoint parts of the statement, so the merge is mechanical. Review the merged text once more before it replaces the axiom.
- **N2 (nit, Serve).** `∀ a b, Γ.au a = Γ.au b → a = b` is required even when `Γ.auth = false`, where `au` is never read. An auth-off start must pad `au` injectively (possible, but pointless).
  - **Fix:** guard the premise with `Γ.auth = true →`, or drop it. It is redundant given the tie, and the drafts keep their own copy.
- **Limit (not a hole).** `lessorSlot γl` closes once, at the first `NewLessor`. A crash-restarted incarnation cannot remake its lessor at `Γ.ls mid`, and `srvLeaseRd`'s restart branch is mode `.none` only. So revocable auth-on serving after a crash is unsupported. That is outside the no-crash line; state it in the docstring.

## 3. Leases across members, auth on (Go: `.lake/go-src/etcd/server/etcdserver/v3_server.go`)

- **Grant at A.** `LeaseGrant` (`:435`) → `requireAuthInfo` → `raftRequest`, which waits on A's own apply. So `leaseLiveFrom (Γ.ls A)` holds. Every fact it gives is at A's names.
- **Revoke at B, B lagging.** The revoke goes through raft (`:471`), after the grant in the log.
  - `writeCheckedD` is cluster-level; `leaseCheckD` is at B's `Γ.au B` from B's own `requireAuthInfo`.
  - A lease already gone gives `ErrLeaseNotFound`, the error arm. The post names no lessor state.
- **TTL at B, B lagging.** `checkLeaseTimeToLive` (`:608`) runs on B's own store and lessor.
  - If B has not enabled auth: `enabledVerdictFrom … false` at B. If B lacks the lease (`Lookup` nil): `leaseAbsentFrom (Γ.ls B) j`, which is K's first disjunct.
  - Then the leader answers. The post claims only the echoed `ID`, and the trailing `ErrAuthOldRevision` is the error arm.
  - The premises `authPubLbM (Γ.au B) n₀` and `lessorLb (Γ.ls B) m₀` come only from B's facts: names are distinct, and a lower bound of A's says nothing about B's.
- **Leases at B.** `LeaseLeases` (`:738`) is local, with no leader check.
  - A lagging B omits A's lease. The post's `leaseIdsAt (Γ.ls B) j ids` cannot be combined with A's `leaseLiveFrom (Γ.ls A)`, which is F2's earlier hole, now closed.
  - The per-lease `leaseKeysVerdictFrom` is a disjunction (absent, or every key readable), which Go's loop over `l.Keys()` meets at some `j ≥ m₀`.
- **Token at B issued by A.** Simple tokens are per member. B answers `ErrInvalidAuthToken`, and the client has one endpoint: error arm or retry.

## 4. New holes: none found

Tried:
- the same server served twice, at two `mid`s: `memberUpOnL`'s stocks are exclusive, and so is the distinctness premise;
- an auth-off member at an auth-on `Γ`, or the reverse: `E.authMode = .on _` against `E.authOn = false`;
- `Γ.au mid` aliasing another member: the authorities are exclusive;
- two tables equal for different `Γ`: `etcdSvc` is opaque and has no law;
- the drafts' distinctness over all `w64`: satisfiable by padding non-members.

No issue in the verified Go code.
