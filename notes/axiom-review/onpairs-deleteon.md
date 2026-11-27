# Auth-on dist axioms paired with their auth-on contracts; `KV_DeleteOn_dist` gains `reqShape` (2026-11-27)

(Superseded in part: `txnshape-narrowing.md` restates the premise as `kvShapeAll` of the wire request.)

Branch `etcd-safe-onpairs/2026-11-27` (from lean `c123838fbc`). This branch continues
`onrevlb-weakening.md`'s "Not done". It weakens one landed interim axiom by adding a premise. That shrinks trust,
so the coordinator pre-approved it.

## The finding: `KV_DeleteOn_dist` did not require the request shape the auth-on contract needs

The finding came from pairing `KV_DeleteOn_dist` with its auth-on contract `client.client_delete_on`
(`Proof/go_etcd_io/etcd/client/v3/ResultsOn.lean:263`) instead of the auth-off `kv.Delete.spec`.

The auth-on service spec requires the caller to send a request of the shape the permission cache decides:
- `etcdDeleteSpecOnW` (`KVServiceOn.lean:106`) and `etcdDeleteSpecMW` (`:527`, at `on = true`) both require
  `⌜auth.reqShape o.key o.base.rangeEnd⌝`.
- `auth.reqShape` (`server/v3/auth/Model.lean:180`) is `key ≠ [] ∧ (rangeEnd = [] ∨ isOpenEnded rangeEnd ∨ key < rangeEnd)`.
- The handler's proof destructs it (`Results.lean:1372`, `%Hsh`) and passes it on (`:1405`).
- `client_delete_on` discharges it from its `hk : key ≠ []` at `opts = []`.

The auth-off spec needs no shape, so the old pairing showed no difference. The F7 reviews (`f7-a.md`,
`f7-rerev-a.md`) do not discuss it. Without the premise, the axiom claimed a success post for requests no
proof covers: `deleteReplied`'s facts, and `writeCheckedD`'s `grantedAt`, which `auth.granted` makes vacuous
outside `reqShape` for a non-root user.

| axiom | Today | With this change |
|---|---|---|
| `KV_DeleteOn_dist` (`Spec/.../dist/KVDeleteOnDist.lean`) | the pre's pure facts: `¬ opDeletePanics key opts ∧ (opDeleteModel key opts).t = W64 3 ∧ rangeEnd ≠ [W8 0]` | the same, `∧ auth.reqShape key (deleteWireOf (opDeleteModel key opts)).base.rangeEnd` |

**What callers lose.** Nothing real:
- etcd refuses an empty key before the auth check (`ErrGRPCEmptyKey`).
- An inverted range (`key ≥ rangeEnd`, not open-ended) deletes nothing.
- The only dist caller is `work_deleteD` (`auth/WorkCallsDist.lean`), at `opts = []`. It now takes
  `hk : k ≠ []` and proves the conjunct by `deleteWire_nil` and `⟨hk, Or.inl rfl⟩`, as `client_delete_on` does.
- Its two uses in `auth/WorkDist.lean` pass the `hkd`/`hkc` (`keyOfK_ne_nil`) they already had.

**Still not backed: any `opts`.** `client_delete_on` fixes the options to `[]`, and the axiom takes any
`opts`. The service spec takes any request `o`, so this is a proof gap, not a false claim. The gate lists it
as a `dev` line that names this follow-up.

**Follow-up (untrusted, not done here):** generalize `client_delete_on` to any `opts`, as `client_put_on`
and `client_range_on` already are. This overlaps dsverify-net's approved widening Q2.

## The gate: four more auth-on pairs

`etc/dist-axiom-diff-allow.txt` now pairs four more axioms with their auth-on theorems in `ResultsOn.lean`.
Each pair has its `dev` lines.

| axiom | paired with | differences | over-claims |
|---|---|---|---|
| `KV_DeleteOn_dist` | `client_delete_on` | 54 | `reqShape`: fixed above. Any `opts`: the follow-up above. |
| `KV_GetOn_dist` | `client_range_on` | 53 | none |
| `Lease_GrantOn_dist` | `client_lease_grant_on` | 42 | none |
| `Lease_RevokeOn_dist` | `client_lease_revoke_on` | 37 | none |

**`KV_GetOn_dist`.**
- `rangeReplyOk` is replaced by `rangeAns_st`'s `rangeStOk` facts, which are mode-agnostic. `m.count` is
  dropped.
- `rangeAuthed` becomes `readCheckedD`, as F7 S5/N1 reviewed it.
- The theorem's `committedAtLeast`, floor and `authPubLbM` are the member's. At `c = 0`, `n = 0` they are free.
- `serializable = false` becomes an unconditional premise.
- `kvReadAu` is unfolded, so it is the same AU.

**The lease pairs.**
- The posts drop the header and `etcdReached`.
- `leaseGrantResT`/`leaseRevokeResT` (at `authOn = true`) give the `Q` conjunct.
- Revoke's `writeCheckedD` is `leaseRevokeResT`'s `grantedAt`/`hdrBoundT`/`pubAfterM` at the cluster. These
  are `writeGrantOn`'s three, the same replacement as `KV_PutOn_dist`'s.
- `leaseCheckFrom` becomes `leaseCheckD` (F7/F9).

## Not paired with an auth-on contract: `Lease_TimeToLiveOn_dist`, `Lease_LeasesOn_dist`, `WatchOn_dist`

I took route (ii): left as they are. A gate extension that pairs with a `def` instantiated at `on = true`
would not help:
- `etcdLeaseTTLSpecMdW`/`etcdLeaseLeasesSpecMdW` (`LeaseSpecs.lean:58/101`) are service specs
  (`fun md req Φ Ψe => iprop(…)`), not client triples.
- So a token diff against the dist triple would be the whole text, and it would surface nothing.

These axioms are still paired with the generic client specs `lessor.TimeToLive.spec`/`lessor.Leases.spec` at
a parameter `Spec`, and `watcher.Watch.spec`. Their posts' content is compared by hand. I read them against
the service specs:
- **`Lease_LeasesOn_dist`.** No over-claim: `leaseIdsAt` at `j ≥ m₀` and `leaseCheckD` over
  `leaseKeysVerdictFrom` are `etcdLeaseLeasesSpecMdW`'s, and `Nodup` is not claimed.
- **`Lease_TimeToLiveOn_dist`.** The echoed `ID` and the keys verdict are `etcdLeaseTTLSpecMdW`'s. Its
  reply-keys conjunct (`ks ↦*□ kbs`, each key `permVerdictFrom … .read`) is more than the service spec and
  the client spec give. It is the known, reviewed F7-fork claim, backed by `EtcdServer.LeaseTimeToLive.spec`'s
  keys conjunct on fork `d26dd5da6` (`f7fork-ttl-dist-keys.md`, SOUND), and its `dev` line says so. It is not
  a new finding.
- **`WatchOn_dist`.** No auth-on contract exists. `onrevlb-weakening.md`'s argument (the server never
  compacts at auth on) backs its revision facts. Its other conjuncts were not re-read here.

**What each needs, so that a gate catches a later drift:**
- `client_lease_ttl_on` and `client_lease_leases_on`: auth-on theorems in `ResultsOn.lean`, shaped like
  `client_lease_grant_on`. Each is `lessor.TimeToLive.spec`/`lessor.Leases.spec` instantiated at
  `etcdLeaseTTLSpecMd`/`etcdLeaseLeasesSpecMd` with auth on, with `attemptPre` discharged and the post
  unfolded. Each is a small proof, untrusted, and then a `pair` like the four above. The TTL pair's keys
  conjunct would stay a `dev` line citing the fork review, unless the theorem also goes through
  `EtcdServer.LeaseTimeToLive.spec`.
- `WatchOn_dist`: an auth-on in-process watch contract, `watcher.Watch.spec` at the auth-on server's
  `watchSpec`. That is larger. Until then, its pair stays against the auth-off `watcher.Watch.spec`.
