# Repairs, fourth round: the lease view (repair4-lease)

2026-11-09. The findings F1, F2 and F3 of `verify/F-client-api.md`. Go checked against
`.lake/src/server`: `etcdserver/v3_server.go:636-737` and `lease/leasehttp/http.go`.

## Per finding

### F3 (3c, soundness): `ltlView` accepted views obtained after the answer. Fixed, as the reviewer suggested

- **The defect.** `Leasehttp.ltlView` quantified `□ ∀ γ ep i` over the view bound inside a
  persistent wand. A view obtained after the handler answered could therefore be fed to it, for
  example a grant after a `404`. Then `TimeToLiveHTTP.spec` derived `False`.
- **`lease/leasehttp/Api.lean`:**
  - **New `leaseLbOpt γ ep vi`** (transparent): the caller's optional view bound. It is
    `leaseViewLb γ ep i` for `some i`, and nothing for `none`.
  - **`ltlView γ ep vi url id found`** is now
    `match vi with | some i => □ (leaseURLOf γ ep url -∗ ∃ j σ₀ t, ⌜i ≤ j ∧ …⌝ ∗ etcdLb γ σ₀ ∗ leaseViewLb γ ep j) | none => True`.
  - `leaseURLOf` stays inside the wand. It is a run-wide fact about `url`: the URL set is used
    once, and the host's `addrFree` is spent once, so `url` had no other handler before. The
    header says so.
  - **New law `leaseURLOf_peerURL`**: `leaseURLOf γ ep url ⊢ ⌜leasePeerURL url⌝`. It is the
    realization's own conjunct. It lets a caller that holds the gate of F1 meet
    `TimeToLiveHTTP`'s deployment premise.
- **`TimeToLiveHTTP.spec`:**
  - new binders `γ ep vi`;
  - new conjunct `leaseLbOpt γ ep vi` in the pre;
  - the `200` and `ErrLeaseNotFound` outcomes give `ltlView γ ep vi url id found`;
  - there is a Changes line.
- **Why it is true of the handler** (`http.go:109-160`). The call starts while the caller holds
  view `i`. The handler then waits for `h.waitch()` and calls `Lookup`, which reads the lessor's
  current table. The lessor only moves forward, so that table is at or past `i`.
- **One definition.** 2c's `srvLeaseLbOpt` (`ApiReq.lean`) is now an `abbrev` for
  `Leasehttp.leaseLbOpt`.
- **The only user** is 2c's assumed contract `EtcdServer.leaseTimeToLive`. Its forwarding sketch
  passes its own `srvLeaseLbOpt γ ep vi` to every attempt (it is persistent and held from the
  call's start). The Changes block says so. No snippet calls `TimeToLiveHTTP`.

### F2 (1c / 2a): no source for `leaseViewLb γ ep 0`. Fixed with the law, premise-free

- **W0 `api/v3/State.lean`.** New `leaseViewLb_zero.spec : ∀ γ ep, ⊢ leaseViewLb γ ep 0`.
- **The realization is restated** in `leaseViewLb`'s docstring: `i = 0`, or
  `∃ id, srvEp γ ep id ∗` member `id`'s lessor view of `i`.
- **Why it is realizable with no premise.** Every consumer's claim at `i = 0` holds of every state:
  - an answer read at a table `≥ 0`;
  - `leaseViewLb_le`'s `0 < leaseTables.length`, which holds because `State.leaseTables` is
    `leaseHist ++ [leases]`, so it is never empty.
- **I chose differently from the suggestion.** The brief suggested a premise such as `srvEp` or
  `servesAt`. It would be an unneeded premise, so I left it out. A client could still supply it:
  it has `servesAt` through `clientPre`.
- **1c `ApiClient.lean`.** `viaPre`'s `⌜i = 0⌝ ∨` alternative is dropped, so the `some (ep, i)`
  case is now `V ep ∗ leaseViewLb γ ep i`. That is consistent with 2a's `etcdUnary`, which gives
  `leaseFact` only with `srvLeaseLbOpt γ ep vi`. The pre-existing half of F2 is closed.
- **`lessor.Grant`.** It calls at `via = some (ep, 0)`. Its sketch now cites `leaseViewLb_zero`.
- **Text updated:** `lessor__TimeToLive`, `ApiLease` (header, `LeaseRead.Triple`'s doc).
- **The snippet `ReqTTLGoneNotListedSole` now closes.** The steps:
  1. `TimeToLive` at `via = some (ep, 0)`, the view from `leaseViewLb_zero`.
  2. Under `soleMember γ ∗ peerLeaseServed γ`, the row gives the not-found answer at table
     `j ≥ 0` with `leaseViewLb γ ep j`. A found lease has `GrantedTTL > 0`, so `GrantedTTL == 0`
     is the not-found answer.
  3. `Leases` at `via = some (ep, j)` is answered at a table `j' ≥ j`.
  4. The lease is absent at `j` and not granted again, so it is absent at `j'`.
- **The snippet's text.** Its Assumes and Specs lines are rewritten. `ReqGoneNotListed`'s stale
  Users rationale is fixed (RR-client S1).

### F1 (2c → 1c, 2a): the `soleMember` row was false under `etcdstart`. Fixed: the row is gated on a deployment fact

- **New in W0 `State.lean`:** `peerLeaseServed γ`, opaque and persistent, with
  `peerLeaseServed_persistent` and `peerLeaseServed_gen`.
  - It means: every member of `γ` serves its own lessor's lease handler at
    `u ++ "/leases/internal"` for each of its peer URLs `u`.
  - Intended realization: `□ ∀ σ m u ep, etcdLb γ σ -∗ ⌜m ∈ σ.members ∧ u ∈ m.peerURLs⌝ -∗ srvEp γ ep m.id -∗ leaseURLOf γ ep (u ++ "/leases/internal")`.
  - It is W0's, not 4b's `leaseURLOf`, because the client's `viaFact` cannot name server
    vocabulary.
- **New in 2e `ApiBoot.lean`:**
  - **`peerLeaseServed_intro`:** `soleMember γ ∗ memberBoot γ [m] m ⊢ memberBoot γ [m] m ∗ peerLeaseServed γ`,
    under `∀ u ∈ m.peerURLs, leasePeerURL (u ++ "/leases/internal")`.
    - Why it is true: under `soleMember` every reached state's members are `[m]` with `m`'s peer
      URLs. Neither `MemberAdd` nor `MemberUpdate` can happen without a `urlsRight`. So the
      realization reduces to `leaseURLOf_intro`.
  - **`peerLeaseServed_url`:** the elimination into `leaseURLOf`.
  - Both are in the header's law list.
- **The gate.** `soleMember γ -∗` became `soleMember γ ∗ peerLeaseServed γ -∗` in:
  - the assumed contract `EtcdServer__leaseTimeToLive.lean`;
  - 2c's `srvLeaseFact` (`ApiReq.lean`), and therefore 2a's `leaseFact`, which is an `abbrev` for it;
  - 1c's `viaFact` (`ApiClient.lean`).
- **The contract is now true for every starter.** Under `etcdstart` the gate cannot be met,
  because `leasePeerURL` is false of its peer URLs. The base outcome stays true there:
  `leaseStep`'s not-found is admissible at table 0.
- **The forwarding sketch now goes through the gate:**
  1. `peerLeaseServed_url` at the leader's record (with `srvAt`'s `srvEp`) gives `leaseURLOf`;
  2. `leaseURLOf_peerURL` gives the `leasePeerURL` that `TimeToLiveHTTP` needs;
  3. `ltlView` gives the row.
- **`examples/lib/etcdstart` is not changed.**
- **Changes lines (`verify-round F1`)** are in:
  - `EtcdServer__leaseTimeToLive.lean`, `EtcdServer__LeaseTimeToLive.lean`;
  - `lessor__TimeToLive.lean`;
  - `LeaseServer__LeaseTimeToLive.lean` (also flags its stale "no per-member view yet" remark,
    RR-client S1);
  - the doc texts of `v3rpc/Api.lean`'s `leaseFact`, `ApiLease.lean` and `leasehttp/Api.lean`'s
    `leaseURLOf`.
- **leaseexpiry's Users text.** `lessor__TimeToLive.lean`, `ApiLease.lean` and the snippet's
  Users line say: `examples/etcd/leaseexpiry`'s "gone by `TimeToLive`, so not listed" check is
  proved only with a starter that serves `s.LeaseHandler()` on the peer address. etcd's
  `newPeerHandler` does; `etcdstart` does not, so under it the check is unproved.

## Requests

### To the coordinator

- **`open-questions.md` A4 / C24 / 3.2.** Record the gate and the decision below. Also record that
  the single-member alternative exists as `soleMember γ ∗ peerLeaseServed γ`; A4 still says the
  clause is dropped (RR-client S2).
- **`top.md`.** Nothing.

## New decisions

1. **The `TimeToLive` row needs a starter that serves the lease handler on the peer address (F1).**
   - The row is gated on W0's `peerLeaseServed γ`, a deployment fact. It is introduced, for a
     one-member cluster only, under 4b's trusted premise `leasePeerURL` of the member's peer URLs.
   - So the proof of `examples/etcd/leaseexpiry` needs one of two harness changes:
     - `examples/lib/etcdstart` serves a mux with `s.RaftHandler()` and `s.LeaseHandler()` at
       `/leases` and `/leases/internal`, as `etcdhttp.newPeerHandler` does, with a spec of
       `LeaseHandler` that makes `leasePeerURL` derivable;
     - or leaseexpiry uses a starter that does.
   - Until then its final check is unproved.
   - **The user should decide** whether to change the shared harness (not done here; its header
     says it calls only what has specs).
   - **The alternative** was to keep the row under `soleMember` alone and record the gap. That
     leaves a trusted contract that is false as stated, so I rejected it.
2. **`leaseViewLb γ ep 0` is free (F2).** The law has no premise: the trivial view means nothing
   known. That replaces `viaPre`'s explicit `i = 0` alternative, and keeps one form of the
   per-member premise across 1c and 2a.
3. **`TimeToLiveHTTP` takes the caller's view in its pre (F3).** A caller with no view passes
   `vi = none` and gets nothing. A member caller now has `leaseViewLb_zero` for `some 0` anyway.

## Build

- **Changed modules first:** `etc/specs-build.sh` on `State`, `leasehttp.{Api,TimeToLiveHTTP}`,
  `ApiBoot`, `ApiReq`, `ApiClient` and `EtcdServer__leaseTimeToLive`: **OK (7 modules)**.
- **Then the importers:** the `SpecPlan.Spec.*` leaves of `etc/importers.py --leaves api/v3/State.lean`
  (1092 modules; `State` is imported by every other changed module): **OK (1092 modules)**, `Build completed successfully (3597 jobs)`, no errors.
- **Snippets:** `go vet ./specreq/clientv3lease/` passes and `gofmt -l` prints nothing.
