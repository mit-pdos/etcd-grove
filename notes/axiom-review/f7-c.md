# Review F7 group C: auth-on lease drafts and the proposed NewServer/Serve (`etcd-safe-f7` @ `d946f6cbda`)

Read-only (axiom skill): no Go test run, no Lean proof; the attacks are shapes, not checked counterexamples. Go: `.lake/go-src/etcd`.

## Verdicts

| draft | verdict |
|---|---|
| `Lease_GrantOn_dist` | NEEDS-FIX (F1, F2). Sound once both are fixed |
| `Lease_RevokeOn_dist` | NEEDS-FIX (F1 only, since it reads no `Γ.ls`). Sound otherwise |
| `Lease_TimeToLiveKeysOn_dist` | **UNSOUND as written** (F1, F2: program below). Sound once both are fixed |
| `Lease_LeasesOn_dist` | **UNSOUND as written**, same shape as TTL (F1, F2). Sound once both are fixed |
| `NewServer.specG_dist_proposed` + `authNamesFreshD` | **SOUND** |
| `Serve_dist_proposed.spec` | NEEDS-FIX (F1: bind `Γ.au`; F2: P-L1's lessor binding). The disjunction itself is sound |

## F1: `A` is a free binder, tied to nothing

Each lease draft quantifies `A : w64 → auth.AuthNames` with only `∀ a b, A a = A b → a = b`. The caller
supplies `auth.authPubLbM (.on (A mid)) n₀`, and `monoNatLbOwn_0` gives that at `n₀ = 0` for any name. The post
then states verdicts at `A mid`: `enabledVerdictFrom`, `adminVerdictFrom`, and `permVerdictFrom` inside
`leaseKeysVerdictFrom`. The caller can choose an injective `A` whose `A mid` has a history authority it
allocated and keeps (`[st]` with `st.enabled`, no admin, no read permission). All three verdicts are then
refutable. `Serve_dist_proposed.spec A` takes its own `A` too, and nothing equates the two.
- In Grant and Revoke, `leaseCheckD … (fun _ => True)` holds for any `info` with `Username = ""`, so the claim is
  empty and there is no attack (it is weak, matching `requireAuthInfo`). F1 is still needed before they can say anything.
- **Fix:** replace `A` by `Γ.au` everywhere, and in Serve require `memberUpOn … (Γ.au mid)`. Address facts are
  minted for any `Γ` (`etcdAddr_set`, `S2Interim.lean:121`), so the only sound tie is Serve's premise on the member.

## F2: `Γ.ls mid` is not tied to the serving member's lessor (needs P-L1, not only distinct names)

The distinct-names premise blocks F2's shared-name attack. It does not stop a start from publishing a `Γ` whose
`ls` are names it allocated and owns. `etcdAddr_set` takes any `Γ`. The proposed Serve's `memberUpOn` uses lease
mode `.none` (`srvLeaseRd s E .none`), whose lessor is `mvccLeases E.γ`, and states nothing about `Γ.ls`. The
TTL draft has no `Γ.kv.lm` premise, so it applies to every view Serve can serve.
- **Program** (TTL, after F2's or P-L1's Serve lets a revocable member serve): the start owns `Γ.ls mid` and `A mid`
  as in F1. A root client runs `g := Grant(ttl)`, `Put(k, WithLease(g.ID))`, then
  `_, err := TimeToLive(g.ID, WithAttachedKeys())`, and `if err == nil { panic("cx") }`.
  - Go: the call succeeds (admin) and the program panics.
  - Proof: the success arm needs one of three disjuncts, and each is refuted:
    - `enabledVerdictFrom … false` and the admin disjunct, by the owned history (F1);
    - the K disjunct `leaseAbsentFrom (Γ.ls mid)`, by an owned lessor authority that records the lease with key `k`.
  - Once `Γ.ls` is bound but `A` is still free, the attack needs a proof that the real lease is not absent. The
    auth-on revocable boot premise `leasesNoExpiry` (`lease.bootCfg`, `LeaseApi.lean:69`) and no revoke make this plausible.
- `Leases` falls the same way, through `[∗list] id ∈ ids, leaseKeysVerdictFrom …` with a listed leased key.
- **Fix:** in Serve (P-L1), require that the member's lessor name is `Γ.ls mid` and its lease mode is `Γ.kv.lm`. With
  F1 and F2 bound through Serve's exclusive resources, two members cannot share names, so both distinct-names
  premises become redundant. They are still harmless.

## Attacks tried that fail (with F1 and F2 fixed)

- **Distinct names over all `w64`.** Not vacuous (pad the members' fresh names injectively); non-members have no `etcdAddrAt`.
- **Grant at A; revoke, list or TTL at a lagging B.**
  - Grant's reply waits on A's own apply (`raftRequest` → `s.w`), so `leaseLiveFrom (Γ.ls A)` holds; B's posts are at `Γ.ls B` only.
  - Lagging-B TTL: `Lookup` returns nil (absent: K holds), and the leader answers. The post claims only the echoed ID.
  - Lagging-B Revoke goes through raft (global order). If the lease is already gone, `ErrLeaseNotFound` gives the error arm.
  - B's token not yet applied: `ErrInvalidAuthToken`, then a refresh at B (one endpoint), which is the error arm or a retry.
- **Resends after a token refresh.** `requireAuthInfo` fails before the proposal, so there is no entry. A second
  grant draws a fresh id: two leases, one returned. `□ ∀ id, writeAuD` admits both fires, and the post names only the reply's id.
- **TTL and expiry with auth on.** A member booted with `on ∧ revocable` needs `lease.leasesNoExpiry`. The TTL post
  claims nothing about the remaining TTL. Leases: the listing at `j` comes before `checkLeaseLeases`, whose reads are
  later. The `From j` forms and `n ≥ n₀` cover that order. The trailing revision checks are not relied on.
- **`authNamesFreshD`.**
  - All 12 `AuthNames` fields are covered, each exclusive and at `authHist_alloc`/`authBoot_alloc`'s values
    (`Model.lean:625`, `Boot.lean:58`).
  - `tokAuth` owns only `γt`, so `fresh` is not given twice. Two same-type full authorities at one name (for example
    `hist = cap`) are invalid: the premise is then unsatisfiable, which is no attack.
  - A caller keeps only lower bounds that agree with the boot values; `γa` cannot be shared (exclusive authorities).
  - `on = false` ignores `γa`. `envAgree` excludes `authMode`, so a chosen `E₀` cannot force `γa = γ'`.
  - Diff vs the current text: only the binder, `Hγa`, and `∃ γa` → `γa`.
- **Serve's disjunction.**
  - An auth-off member at an auth-on `Γ` needs `memberUpOn`'s `E.authMode = .on _`. `NewServer` at `on = false`
    gives `authOn = false`, so it cannot.
  - The reverse case (an auth-on member at an auth-off `Γ`) needs `memberUp`'s `E.authOn = false`, which it cannot give.
  - A different history: `hist` must match when `Γ.auth`, and `γa` starts at `bootState` (no crash in scope).
- **The principal.** `Client.Username`/`Password` are `↦□` (`InvClientAuth.lean:137`): not rewritable after `New`.

## Notes

- P-A1 must thread `γa.tok`/`fresh`/`rdy` into the provider and `srvTpInv` proofs (`AuthSrvLinked.lean:131`). Revocable
  drafts are unusable under the proposed Serve (`m = .none`, `lm = m`) until P-L1. No issue in the verified Go code.
