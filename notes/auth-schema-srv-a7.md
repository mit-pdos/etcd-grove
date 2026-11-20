# auth-schema-srv A7: the link (HARD STOP for the user, 2026-11-19)

A6 is done: the realization proves D22's two trusted texts. A7 links it, which removes the named hypothesis
`hD22` from three closed theorems. Nothing is linked yet; this note is what the user decides on.

## 1. What is proved (A6, branch `auth-schema-srv`)

`Proof/go_etcd_io/etcd/server/v3/etcdserver/AuthRealSrv.lean`:

- `real_srv (47 callee specs) (hRB : receiptBound GF ≤ 2 ^ 48) :
  isPkgInit backend ∗ isPkgInit schema ⊢ authSchemaSrv`
- `real_snap (...) (γa γt γv) : isPkgInit backend ∗ isPkgInit schema ∗ ownTokAuthDfrac γt DFrac.discard ticketN ∗
  vaultInv γa γv ⊢ authSchemaSnap γa (ownToks γt 1)` (used by `real_srv` for the post's snapshot clause).

The 47 callee specs are the backend's and schema's (`batchTxBuffered.*`, `readTx.*`, `backend.{BatchTx,ReadTx,
ForceCommit}`, `schema.authBatchTx.*`, `schema.authReadTx.*`, `schema.authBackend.*`, `schema.bucket.*`). Each has a
`wp_proof` theorem with no `axiom` or `sorry` in its own file (their proofs rest on the bbolt and proto axioms
already in the baseline). `AuthReal*.lean` contain no `axiom` or `sorry`. The realization is in
`AuthReal{Inv,Pool,Rd,Rsv,Life,Wr,New,Srv}.lean`.

`authSchemaSrv`'s text has no package-initialization premise, so the theorem takes the two `isPkgInit`s. `hRB` comes
from `ReceiptBoundLe` at the link.

## 2. The closed statements: old → new

These three closed theorems lose one hypothesis. Nothing else in their statements changes:

- `etcd_auth_safe` (`Proof/github_com/mit_pdos/etcd_grove/examples/etcd/auth/Results.lean:189`)
- `etcd_auth3_safe` (`.../etcd/auth3/Results.lean:86`)
- `etcd_authN_safe` (`.../etcd/authN/Results.lean:81`)

The removed lines:

```
    -- (D22) the auth store's backend with auth on: trusted text, a named hypothesis
    (hD22 : ∀ hG : HeapGS .hasLC putgetGF, ⊢ authSchemaSrv (GF := putgetGF) (hG := heapAt hG lctx))
```

The same hypothesis goes from each theorem along their chains:

- auth: `etcd_auth_adequate` (`Adequacy.lean:85`) and `authkv_startServer` (`Results.lean:76`).
- auth3: `etcd_auth3_adequate` (`Adequacy.lean:79`), `etcd_auth3.wp_startMember` and `etcd_auth3.wp_Main`
  (`MainLinked.lean`).
- authN: `etcd_authN_adequate` (`Adequacy.lean:73`), `etcd_authN.wp_StartMemberAuth`, `etcd_authN.wp_StartMembersAuth`
  and `etcd_authN.wp_Main` (`MainLinked.lean`).
- server: `server_new_auth_on` (`etcdserver/Results.lean:2140`), `srv_auth_tp_on` (`Results.lean:2096`),
  `authStoreKit_on` (`AuthSrv.lean:433`, which opens it at `:496`) and `authSrvTP_on` (`AuthSrv.lean:675`).

**The link (plan, ~150-300 lines):**

- `authStoreKit_on` opens `authSchemaSrv` at `AuthSrv.lean:496`. It would use `real_srv` instead, instantiated with the
  server `Link`'s `wp_` theorems and `ReceiptBoundLe`. The package inits would come from the `isPkgInit` already in
  that context (`#Hpkg`, through the package-dependency lemmas).
- If they cannot be derived there, the fallback is to add `isPkgInit backend ∗ isPkgInit schema` to
  `authSchemaSrv`'s `∀` premises. That is harmless: the text is no longer trusted once it is proved.
- After the link, regenerate the server `Link`, the collections (`etc/tcb-report.py --collection ... --check
  --update` for the auth, auth3 and authN collections and the server's), and the baseline if it changes.

## 3. Trusted text this branch changed (the A7 list)

What the user approved, item by item, with where each text stays trusted after the link. "Leaves the TCB" means the
text is only in `authSchemaSrv`/`authSchemaSnap`, which A7 proves, so it is no longer a hypothesis. To confirm on the
TCB report after the link.

| item | old → new | after A7 |
|---|---|---|
| fix (A) | boot write contract at `authWTok γc`, `Post` gives back `plHook nil` → at `authWTok γc ∗ plHook d.γB func.nil` (questions.md "A6 STOP decided") | leaves the TCB (`authSchemaSrv`) |
| L-rev | `authBkLend` takes `⌜1 ≤ st.revision⌝` (weaker; "A6 STOP 2 decided") | leaves the TCB |
| P2 | `authSchemaSnap` takes `⌜auth.permKeysOk st⌝` (weaker; "A6 STOP 2 decided") | leaves the TCB |
| P1' | `auth.authLockQ γa hs := monoListAuthOwn γa.hist ¼ hs ∗ ⌜∀ st ∈ hs, permKeysOk st⌝` ("A6 STOP 3 decided") | in `authSchemaSrv`/`Snap` (through `authLockI`): leaves; auth's internals: proved |
| R-c | `auth.rolesOut`/`roleListOut` list only `rolesListed` names, all of them when fewer than `2^63 - 1` ("A6 R-c ... decided") | in the write and read contracts of `authSchemaSrv`: leaves; `RoleList`'s proved spec |
| O-a | `schema.authBucketsAre`'s roles clause up to permutation ("A6 O-a and STOP 6 decided") | in `authBucketsAt` (`authSchemaSnap`, `authBkLend`): leaves |
| K-c | sealed `rbPartRF` holds ⅛ of `γ.rbk` per claimed bucket, `rbClaimC` ⅝ (was ¾) (soundness §7) | **stays**: bodies under `isBackend`, so `backend.backend.Snapshot.wp_proof` (axiom) and `newPostK` |
| `rbPartF`'s fraction | ½ → ¼ (A6.2, soundness §6) | **stays** (under `isBackend`) |
| `newPostK`'s tokens | `newPostK` holds `rbClaimToks γ P ⊤` (A6.2 C1-C5) | **stays** wherever `newPostK` is in a trusted text |
| `authRdSlots`' tokens | `authRdSlots d := rdAuth ∗ rbClaimToks d.γB d.P authBkts` (A6.2) | leaves (`authSchemaSrv`/`Snap`) |
| ticket count | `authSchemaSrv`'s tickets `authRdN` → `authRdN - 1` ("A6.1b decided") | leaves |

There is no new trusted text beyond these: V-pub and the realization's invariants are internal.

## 4. Trust-base delta

- **Removed** from the three closed theorems: the hypothesis `hD22`, and with it the texts of `authSchemaSrv` and
  `authSchemaSnap` (and `authBkLend`, `authWAtHook`, `authRdSlots`, `authOpenQ` inside them).
- **Added** to their collections: the axioms the realization reaches through the backend's and schema's proofs.
  This branch's additions to the baseline are already recorded:
  - `bbolt.Bucket.ForEach_kvr.wp_proof` and `bbolt.Bucket.ForEach_kvw.wp_proof` (A2 Freeze);
  - `proto.MarshalRole.wp_proof` and `proto.MarshalUser.wp_proof` (A3 Freeze).

  The exact per-collection delta comes from `etc/tcb-report.py --collection` after the link. No `sorry` or axiom is
  added by A6.
