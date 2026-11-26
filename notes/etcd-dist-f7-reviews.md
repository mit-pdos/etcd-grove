# F7: review list for the auth-on dist drafts (S1, 2026-11-26; drafts compiled at `5cb43bae2f`; reviewed, fixes applied 2026-11-26)

One `axiom`-skill review per row, fresh (given the code and the draft, not `notes/etcd-dist-f7.md`'s
reasoning), in one batch with the re-reviews of `Serve_dist` and `NewServer_dist`. The drafts are `.spec`
definitions in `Proof/github_com/mit_pdos/etcd_grove/examples/etcd/dist/AuthViewDist.lean` (below: `AVD`)
and `.../dist/AuthServeProposed.lean` (`ASP`); nothing imports either, no axiom. Go sources: etcd's client
`client/v3/` and server `server/` at the fork's pin (`.lake/go-src/etcd`, `upamanyus/etcd` `goose-lean`);
the single-process specs they mirror are in `Proof/go_etcd_io/etcd/client/v3/ResultsOn.lean` and
`Spec/go_etcd_io/etcd/client/v3/`.

## The lead's condition, and what every review checks

(#50, 2026-11-26T01:29:52Z.) Each success arm says member `mid`'s check passed for the call's user at the
current auth history (`servedBy eps Γ mid` and one of `writeCheckedD`, `readCheckedD`/`txnReadCheckedD`,
`leaseCheckD`, `adminRepliedD`, `New`'s `passwordChecked`); each error arm (`err ≠ nil ∧ resp = null`) admits
every token failure. For every row, also try:

- **A token from member A presented to member B.** clientv3's balancer sends each RPC to any endpoint, with
  the one token the client holds. The simple token's prefix is drawn at the receiving member and goes through
  raft (`EtcdServer.Authenticate`, `server/etcdserver/v3_server.go:838`, `SimpleToken: st` at :875); every
  member's apply assigns `<prefix>.<index>` to the same user (`tokenSimple.assign`,
  `server/auth/simple_token.go:215`). So B accepts A's token as the same user once B has applied that
  entry, and before that (or after B's own TTL keeper expired it) answers `ErrInvalidAuthToken`, which the
  retry interceptor turns into a refresh and a resend (`client/v3/retry_interceptor.go:89`,
  `shouldRefreshToken` :157). Break the success arm by finding a run where B binds the request to a user
  other than `principalOf cfg` (or `""`): two members issuing the same token string to different users (the
  prefix is 16 random letters per call, the index the raft index: distinct entries give distinct indices),
  a token reassigned after expiry, `cfg.Token` preset (excluded: `cfg.Token' = []`), the client's
  `Username`/`Password` fields written after `New` (they are public fields of `*Client`; `getToken` reads
  them at every refresh: is anything in `isNewClient` pinning them?).
- **Expired tokens.** Each member's `simpleTokenKeeper` deletes a token after `TokenTTL` (300 s in
  `dist/server/server.go`) independently; a refresh may land at another member. Check nothing in a post
  assumes the token was valid anywhere.
- **Resends.** A write is resent after `ErrInvalidAuthToken`/`ErrAuthOldRevision` (mutable RPCs included);
  `writeAuD` is persistent and fires at most once. Can two attempts both apply (one entry each)? The
  single-process argument is `srvPropAu1` (one entry per attempt, each told its own grant; a refused
  attempt's entry applies no step).
- **`userOk`'s empty user.** With auth on an empty user is refused by every check (`ErrUserEmpty`); the
  arm still admits it, so it claims less. Check no draft's caller could need more.

## Rows

| # | Draft | Where | Go function (source) | Mirrors | What to try to break | Fixed per review (2026-11-26, `notes/axiom-review/f7-{a,b,c}.md`) |
|---|---|---|---|---|---|---|
| 1 | `New_user_dist` | `AVD:249` | `clientv3.New(cfg)` → `getToken` (`client/v3/client.go:86`, :285, :473) | `clientv3.New.spec` (`clientAuthPre`) | `getToken` treats `ErrAuthNotEnabled` as success with no token: the arm's `enabledVerdict (.on (A mid)) false` disjunct. Does `passwordChecked` at `A mid` hold when the `Authenticate` RPC went to member B but `CheckPassword` ran at B (it does: `mid` is existential over `eps`)? A member whose auth store lags the history (user not yet added there). | A: UNSOUND (free `A`) → fixed: `Γ.au mid`, tied by Serve |
| 2 | `KV_PutOn_dist` (also F2's `KV_PutLease_dist` row, at `leaseID ≠ 0`) | `AVD:276` | `(*kv).Put` (`client/v3/kv.go:159`) | `client_put_on` (`ResultsOn.lean:58`) | The token from A at B; a resend after `ErrAuthOldRevision` whose first attempt's entry is committed but refused; `WithLease(id)` with `id` revoked meanwhile (`ErrLeaseNotFound`: no step, the update must not fire; `checkLeasePuts` refused at apply). `writeCheckedD`'s `grantedAt` at `L` before the entry. | A: SOUND |
| 3 | `KV_DeleteOn_dist` | `AVD:301` | `(*kv).Delete` (`client/v3/kv.go:192`) | `client_delete_on` (`ResultsOn.lean:263`) | As row 2; a range delete whose permission covers part of the range (`isDeleteRangePermitted` over `[key, end)`), `prevKV` with read permission missing (etcd checks read on `prevKV`). | A: SOUND |
| 4 | `Txn_CommitOn_dist` | `AVD:335` | `(*txn).Commit` (`client/v3/txn.go:138`) | `client_txn_on` (`ResultsOn.lean:371`) | Nested transactions' checks (`irrTxn`'s grant, `txnClassFrom`'s); a read-only txn resent at another endpoint (`□ AU`); a writing txn whose compare reads keys the user may not read (`checkTxnReqsPermission` checks compares as reads). | A: UNSOUND, read-only branch (free `A`) → fixed: `Γ.au mid` |
| 5 | `KV_GetOn_dist` (with the barrier floor `authFloorD`) | `AVD:384` | `(*kv).Get` (`client/v3/kv.go:164`) | `client_range_on` (`ResultsOn.lean:188`) | The floor: member `mid`'s published index `m` with its state at `i ≤ m` the history's after `L ⊒ L₀`. Index alignment: `authStateAt γa i` is the member's auth history's `i`-th state, `srvReqLogLb` has no raft fillers (`authFloorAt` uses the raft log and `ai0`). A member that answers after its read index but whose auth store is behind its apply. `readAuthedD` (cluster-level) vs the member-local verdict. | A: UNSOUND (free `A`) → fixed: `Γ.au mid`; floor alignment to re-review Re-review A's N1 applied (2026-11-26): `readCheckedD` gives `srvReqLogLb γR L` for `readAuthedD`'s `L` (now a parameter), so the read's log is committed. |
| 6 | `Auth_UserAdd_dist` | `AVD:419` | `(*authClient).UserAdd` (`client/v3/auth.go:156`) | `authClient.UserAdd.spec`, `etcdUserAddSpecW` | Sent before `AuthEnable` by an anonymous client (`P = none`); a resend (admin RPCs are mutable: resent only after a refusal) applying twice (`ErrUserAlreadyExist` on the second: the error arm). `adminRepliedD`'s `mid`. | B: NEEDS-FIX → fixed: `name.length ≤ maxKeySize`, `□ (∀ um, ⌜…⌝ → …)` |
| 7 | `Auth_UserGrantRole_dist` | `AVD:446` | `(*authClient).UserGrantRole` (`client/v3/auth.go:176`) | `authClient.UserGrantRole.spec`, `etcdUserGrantRoleSpecW` | Name bound `user.length ≤ maxKeySize` (server-side premise moved to the client); role absent (`ErrRoleNotFound`); grant to `root`. | B: SOUND |
| 8 | `Auth_RoleAdd_dist` | `AVD:467` | `(*authClient).RoleAdd` (`client/v3/auth.go:196`) | `authClient.RoleAdd.spec`, `etcdRoleAddSpecW` | Empty role name (`ErrRoleEmpty`); `root` role. | B: SOUND |
| 9 | `Auth_RoleGrantPermission_dist` | `AVD:489` | `(*authClient).RoleGrantPermission` (`client/v3/auth.go:201`) | `authClient.RoleGrantPermission.spec`, `etcdRoleGrantPermissionSpecW` | `permType` outside READ/WRITE/READWRITE; `rangeEnd = "\x00"` (from-key); the client's key bound `key.length < 2^63 - 1`. | B: SOUND |
| 10 | `Auth_AuthEnable_dist` | `AVD:512` | `(*authClient).AuthEnable` (`client/v3/auth.go:141`) | `authClient.AuthEnable.spec` | No `root` user (`ErrRootUserNotExist`), root without the root role (`ErrRootRoleNotExist`); a lagging member answering. | B: SOUND |
| 11 | `Lease_GrantOn_dist` | `AVD:536` | `(*lessor).Grant` (`client/v3/lease.go:222`) | `client_lease_grant_on` (`ResultsOn.lean:484`), F2's `Lease_GrantLive_dist` | One endpoint: `leaseLiveFrom (Γ.ls mid)` — the reply waits on the member's apply? The id drawn at the receiving member; `□ ∀ id` update; resend after a token refresh drawing a second id (two leases granted, one returned). | C: NEEDS-FIX (F1, F2) → fixed: `Γ.au mid`; `Γ.ls mid` tied by Serve |
| 12 | `Lease_RevokeOn_dist` | `AVD:566` | `(*lessor).Revoke` (`client/v3/lease.go:237`), server `LeaseRevoke` (`server/etcdserver/v3_server.go:471`: `requireAuthInfo` then raft) | `client_lease_revoke_on` (`ResultsOn.lean:549`) | The apply-time check (`checkLeasePuts`: write on every attached key, or admin) vs `writeCheckedD`'s `grantedAt`; a lease already expired/revoked (`ErrLeaseNotFound`); a resend. | C: NEEDS-FIX (F1) → fixed: `Γ.au mid` |
| 13 | `Lease_TimeToLiveKeysOn_dist` | `AVD:596` | `(*lessor).TimeToLive` with `WithAttachedKeys()` (`client/v3/lease.go:246`), server `LeaseTimeToLive` / `checkLeaseTimeToLive` (`v3_server.go:699`, :608) | `lessor.TimeToLive.spec` at `etcdLeaseTTLSpecMdW` (`LeaseSpecs.lean:58`), F2's view-free `Client_LeaseTimeToLive_dist` | The keys check is member-local (`s.lessor.Lookup` at `mid`, `IsRangePermitted` at `mid`) but the answer is the leader's (`leaseTimeToLive` forwards): the post claims only the echoed ID and `mid`'s verdict. `ErrAuthOldRevision` when the auth revision moved during the call. `leaseKeysFold gs false = true` with more options. | C: UNSOUND (F1, F2) → fixed: `Γ.au mid`, Serve tie, `Γ.kv.lm = .revocable` added |
| 14 | `Lease_LeasesOn_dist` | `AVD:622` | `(*lessor).Leases` (`client/v3/lease.go:262`), server `LeaseLeases` / `checkLeaseLeases` (`v3_server.go:738`, :752) | `lessor.Leases.spec` at `etcdLeaseLeasesSpecMdW` (`LeaseSpecs.lean:101`), F2's `Lease_LeasesLive_dist` | The listing and the check read `mid`'s lessor at one index `j`? (`ls := s.lessor.Leases()` before `checkLeaseLeases`, which reads each lease's keys again.) Revocable mode only. | C: UNSOUND (F1, F2) → fixed: `Γ.au mid`, Serve tie |
| 15 | `NewServer.specG_dist_proposed` (P-A1) | `ASP:104` | `etcdserver.NewServer` (`server/etcdserver/server.go`) | the current `NewServer.specG_dist` (`Spec/.../dist/NewServerDist.lean`) | `authNamesFreshD` (`ASP:64`): every `auth.AuthNames` field's fresh authority at the boot values (`authHist_alloc`, `tokAlloc`, `srvTpInv_alloc`): is one missing, or at a value `NewServer`'s boot does not produce? `γa` shared between two members (the start must allocate per member); auth off (`on = false`) ignores `γa`. | C: SOUND Merged (2026-11-26) with F2's P-L1 text (`etcd-safe-f2`'s `NewServerDist.lean:308`, deleted): see row 20. |
| 16 | `Serve_dist_proposed.spec` | `ASP:283` | `etcdstart.Serve` (`examples/lib/etcdstart`) | the current `Serve_dist.spec` (`Spec/.../dist/ServeDist.lean`) | The disjunction `Γ.auth = false ∨ ρ.rd.kv.hist = Γ.kv.hist`: a member serving `Γ` with auth on but its own history names; `etcdSvc`'s entries now the `etcd*SpecOn` handlers at `T := False`: a deployment with `ClientCertAuthEnabled`. | C: NEEDS-FIX (F1, F2) → fixed: `Γ.au`, `memberUpOnL`/`memberUpL` at `Γ.ls mid`, `Γ.kv.lm` Merged (2026-11-26) with F2's `Serve_dist.spec_proposed` (`etcd-safe-f2`'s `ServeDist.lean:60`, deleted; its auth-off half is this text's `memberUpL` branch); re-review C's N2 applied (the distinct-`Γ.au` premise guarded by `Γ.auth = true →`); docstring states condition C and the restart limit: see row 20. |
| 17 | `DistView.au` (new field), `DistView.ofKV`'s placeholder | `S2Interim.lean:56` | none (a view) | the approved design's P-A1 | Nothing reads `au` but the drafts; `ofKV`'s constant fails the distinct-names premises (so no draft applies to an `ofKV` view). M1's statement unchanged. | new (review A's fix) |
| 18 | `etcdstart.memberUpOnL` | `ASP:222` | `etcdstart.Serve`'s member | `memberUpOn`'s body verbatim plus `mvccLeases E.γ = γl` (F2's `memberUpL` with auth on) | Does any part of `memberUpOn` differ? Can `E.authMode = .on (Γ.au mid)` and `mvccLeases E.γ = Γ.ls mid` both hold for a start that owns `Γ.au mid`'s or `Γ.ls mid`'s authorities? | new (review C's F2) |
| 19 | `etcdstart.memberUpL` (`MemberLessor.lean`, F2's file, verbatim) | `MemberLessor.lean:38` | as 18, auth off | F2's P-L1 | Reviewed with `Serve_dist_proposed.spec` (row 16, F2's text merged into it) | one copy after the merge of `etcd-safe-f2` (2026-11-26); C: SOUND |
| 20 | **The combined proposal** (F2 + F7, merged 2026-11-26): `NewServer.specG_dist_proposed` (P-A1 + P-L1) and `Serve_dist_proposed.spec` | `ASP:104`, `ASP:283` | `etcdserver.NewServer`; `etcdstart.Serve` | the current `NewServer.specG_dist`, `Serve_dist.spec` | One re-review of the merged text before it replaces either axiom (review C asked for it). NewServer: F7's `γa`/`"Hγa"` (`authNamesFreshD γa` with auth on)/`E.authMode = .on γa` and F2's `γl`/`"Hlslot"`/`mvccLeases E.γ = γl` together: can a start meet both per member, and does any conjunct of one interfere with the other? Serve: condition C (no other route serves an auth-on `Γ` without `memberUpOn(L) … (Γ.au mid)`); the guarded distinct-`Γ.au` premise at an auth-off view; the restart limit (slot closes once, `authNamesFreshD` needs a fresh history). | not yet reviewed |

## Distinct names (every row reading `Γ.au mid` or `Γ.ls mid`: 1, 4, 5, 11-14, 16)

These drafts take `∀ a b : w64, Γ.au a = Γ.au b → a = b` (and, where they read `Γ.ls`, `∀ a b : w64, Γ.ls a =
Γ.ls b → a = b`): the form the lease review proposed (`ofKV`'s constants fail it). Until 2026-11-26 the auth
names were a free binder `A`, which reviews A and C showed unsound: injectivity alone is met by a caller
sharing one `hist` name it owns. Now `Serve_dist_proposed`'s exclusive member resources tie `Γ.au mid` and
`Γ.ls mid` to the real member, which makes these premises redundant (kept, harmless).
is the same form. Check: can a fact about member A's names still be used at member B?

## Left from the 2026-11-26 reviews

- Review A: once `Γ.au` is tied, re-review `authFloorD`'s alignment (`authStateAt (Γ.au mid) i` vs
  `srvAuthAtLog Γ.kv srvAuthSt0 L`).
- Review C: P-A1 must pass `γa`'s `tok`, `fresh` and `rdy` names into the token provider and `srvTpInv`
  proofs (`AuthSrvLinked.lean:131`): S2, with P-L1.

## Findings while drafting (S1)

- The design note says tokens are per member. They are not: the simple token is assigned cluster-wide
  through raft (above). The drafts are unaffected (they state the user, not the token), but the note's
  "a client that rotates endpoints re-authenticates" is only the lagging/expired case.
- `principalOf` ignores `cfg.Token`: a preset token binds the calls to its user. `clientCfgOk` already asks
  `cfg.Token' = []` of `New`; the client facts (`userClientAt`, `authClientAt`, `leaseUserAt`) now carry it.
- `getToken` returns success on `ErrAuthNotEnabled`: `New_user_dist`'s success arm admits it.
