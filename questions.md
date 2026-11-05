# Questions (hub plan step 7, the program-start boundary; branch `hub-step7`)

Session etcd-grove-83, worktree `/shared/etcd-grove-hub7`, off `lean` fd99415136. Scope only so far:
no Lean edits. The design is in `notes/spec-first-plan.md`, "Step 7 Scope (2026-11-05)"; the full
statement list, old → new, is there too (and in `/shared/tmp/hub7-scope-statements.md`).

## Scope summary

**Scope: for the user via etcd-grove-82** (a hard stop: Main.spec changes).

- **Bundles** (sealed, `@[no_expose]`, in a new `etcdstart` API module
  `Proof/github_com/mit_pdos/etcd_grove/examples/lib/etcdstart/StartRes.lean`, owned by `etcdstart`):
  - `memberStartRes name a`: what a `Main` takes per member (program start): `walDirFresh (wd name)`,
    and for `a.peer = some p` `netAddrFree p ∗ httpProtoFree p`, for `a.client = some c` `netAddrFree c`;
  - `memberFreshRes name a γn`: what a first-start starter takes (after the cluster's network
    allocation): the same with `http.httpProtoOwn p (raftProto (netRh γn))` for the peer;
  - `memberRestartRes name a γn γ ρ id`: what a restart starter takes: `srvDiskImage γ ρ id
    (name ++ ".etcd")` (which holds `walFiles`) and the peer's `netAddrFree p ∗ httpProtoOwn p …`,
    as `restart/stop.spec` returns them.
  - `a : MemberAddrs := { peer client : Option GoString }`: the addresses the program listens on for
    that member. Optional because the closed theorems fix `As`: the one-member examples' `HAs` lists
    only the client address, putget3's only member 1's client (D3).
- **Laws:** `memberStartRes_intro` (adequacy, from `startRights`' lists, by `List.Perm`, D2) as
  `etcd_adequate_members`; `alloc3` restated (start bundles in, fresh bundles out);
  `memberStartRes_fresh` (no peer: any `γn`); `_client` (on start and fresh bundles: the client's
  `netAddrFree` out, the rest back at `client := none`); `memberFreshRes_peer`/`memberRestartRes_peer`
  (the peer's listen and protocol rights out); `memberFreshRes_boot` (`wal.bootRes cfg`, at
  `cfg`'s data directory `name ++ ".etcd"` and WAL directory `""`); `memberRestartRes_boot`
  (`srvDiskImage …`, the restart contract's input; the restart owner's to refine).
- **Statements that change:** 16 Main statements, all top-level (14 on `lean`, K6's `MainPartition`,
  lease-expiry's `leaseexpiry` Main) and restart's draft `runRes`; 11 `etcdstart` starter statements
  (10 changed, `newServer.specCompact` deleted); 6 example-local starters (`partition`/`cluster3`,
  `restart` ×3, `auth.startServer`); `alloc3`. `Serve` and the other consumers unchanged. The closed
  theorems (`*_safe`, `*_adequate`) and `startRights`/`goose_adequacy_start` are unchanged.
- **Success measure:** spec files naming a start resource: 34 on `lean` → 5 (the consumers).
- **Build budget:** the step rebuilds about 132 modules (20.6k lines; 28 `--leaves` targets) if the
  bundle module is imported by the edited specs directly, 193 (28.3k lines) if through `Defs`. A later
  start resource then changes a sealed body: the module and its `import all` users (about 4).
- **Order:** after K6 (`k8s3m`) and `lease-expiry` land; before the restart threads `walFiles` through
  the examples; `r2b3` and `auth-comp5` in either order.

## Q1. The examples' Main.spec changes (hard stop)

**Scope: for the user via etcd-grove-82.**

Same meaning: each bundle unfolds to the tokens the Main takes today. But the Mains are the
statements the closed theorems consume, so a change to their text is a hard stop. The full list,
old → new, is in the plan section (A: 16 TOP statements; C/D: the starters).

- (a) Approve the list as written: the one-member Mains take `memberStartRes name ⟨none, some client⟩`;
  putget3 three bundles; partition, `MainWatch`, `MainPartition` the cluster bundle (D1).
- (b) Approve the bundles for the starters only. The Mains keep their tokens, and each adequacy
  proof converts. This leaves the Mains threading every new start resource, which is what the step
  is meant to stop.
- (c) Defer the step.

**Recommendation: (a).** The closed theorems stay as they are, word for word: `HAs`/`HDs` are
unchanged, and the intro takes the lists in any order (D2). No trust-base change.
**Depends on it:** the whole Draft; the restart's `walFiles` round (which this step absorbs).

## Q2. The mode twins of hub 4: in this step or next?

**Scope: for the user via etcd-grove-82.**

The twins are `BuildServer.spec`/`specStop`/`specRestart`, `newServer.spec`/`specCompact`, and
`restart.startMember.spec`/`specRestart`. `Start{,Compacting,Periodic}Server` are three Go
functions, not twins (Q3 covers them).

- (a) Merge every twin family in this step.
- (b) Merge only where the bundle forces an edit of both twins' preconditions, and where the merge
  is small.
- (c) Defer all of them.

**Recommendation: (b), which here means only `newServer`.** `newServer.specCompact` is proved but
used by no proof and is not in `Link.lean`. K6 gives `newServer.spec` the compaction mode `cmp`, and
the compactor-on callers use `newServerMode.spec`. So delete `specCompact` (and its `wp_proof`)
rather than merge it.
Leave `BuildServer`'s three and restart's `startMember` pair to the restart owner, recorded:
- `spec` and `specStop` differ only in the post;
- `specRestart` is the fresh/restart split, whose merge is the restart contract's design (L3,
  `bootPremise` vs `bootPremiseR`, `memberBuilt` vs `memberBuiltR`);
- they are r2b3's drafts.

With the bundles, a merged starter later takes `memberFreshRes` or `memberRestartRes` by its start
kind: the bundles are the mode's precondition, ready for that merge.
**Depends on it:** the size of Draft; r2b3's conflicts (none under (b)).

## Q3. The repeated pure premise lists (`etcdstart.memberCfgOk …`)

**Scope: for the user via etcd-grove-82.**

About 15 `→` premises are copied across 11 starter statements and 6 example-local ones:
- the bounds;
- the raft names (`γ.vs`, `γ.rule`, `γ.boot`);
- `γn.N`/`γn.dir`/`netDirOk`/`rafthttp.bootCfg`;
- `Uok`, the UTF-8 keys, `lg ≠ null`;
- the effect premises.

The bounds are also written two ways: `threadBound GF ≤ 2 ^ 28 →` in most, `[ThreadBoundLe GF (2 ^ 28)]`
in `BuildServer` and restart's starters.

- (a) A premise bundle in this step.
- (b) A follow-up step (7b) right after step 7 lands.
- (c) Never: let each subsystem's slot absorb its own premises (`raftNode.bootCfg`, `rafthttp.bootCfg`,
  ...) as the slot convention does.

**Recommendation: (b), done as (c) where a slot exists.** Step 7 moves separating resources only, so
its review stays narrow. Mixing in pure premises would put every subsystem's boot premises in one
review, and would conflict with K6 (`cmp`) and lease-expiry (`lm`) on the same lines.
In 7b:
- a sealed `etcdstart.memberCfgOk` for the starter's own premises (the URLs, UTF-8, logger);
- the subsystems' existing slots for the rest;
- the bounds normalized to the `ThreadBoundLe`/`ReceiptBoundLe` classes (the bounds plan's form).

**Depends on it:** nothing in step 7.

## Q4. Where the API module lives; an importable list for `etcdstart` now?

**Scope: for the user via etcd-grove-82.**

- (a) `StartRes.lean` in `Proof/.../examples/lib/etcdstart/` (as `WalApi.lean` sits in the server's
  `Proof/` directory), sealed by `@[no_expose]`, with `etc/import-all.txt` lines. Also an
  `etc/api/etcdstart.txt` now, as raft's started:
  - the API group: `StartRes`, the starter specs, `Adequacy`, `Alloc`, `Alloc3`;
  - a debt group: the about 30 other `etcdstart` modules that examples import today (`Defs`, `Base`,
    `OneMember`, `Served`, ...);
  - `etc/gen-interface.py` output committed under `interface/`.
- (b) The module now, the importable list in a follow-up.
- (c) The bundles in `Defs.lean`, no new module.

**Recommendation: (a).** The interface is where a reviewer sees the bundles' laws instead of their
bodies (the slot convention's "sealing moves the review"). The list's check is what stops an example
from unfolding the bundle (`import all`).
Importantly, the starter specs and the Mains import `StartRes` directly, not through `Defs`:
- 132 modules rebuilt by the step instead of 193;
- a later body change rebuilds only `StartRes` and its `import all` users (`newServerMode`,
  `NewMember`, `Alloc3`, the laws).

(c) would put the bundle under `Defs`' 166 importers.
**Depends on it:** Draft's file layout; CI's interface check (one more list).

## Decided by the agent, pending the user (2026-11-05, Scope)

- **D1. The cluster's start bundle, `cluster3.startRes cfg`** (after K6 lands). It holds the three
  members' `memberStartRes (cfg.Nameᵢ') ⟨some cfg.Peerᵢ', some cfg.Clientᵢ'⟩` and the three bridges'
  `netAddrFree cfg.Bridgeᵢ'`. It is sealed in `cluster3`'s API, and its laws go to the members'
  bundles and the bridges' tokens. The bridges are no member's resource, so without it the partition
  Mains and `MainPartition` keep naming `netAddrFree bridgeAddrᵢ`: 4 files that would fail the
  success measure.
  - Options: (a) this bundle; (b) the bridges stay inline in those Mains.
  - Recommendation: (a). `cluster3` is the starter of a three-member cluster, and K6 already passes
    its `Config` record.
- **D2. The intro takes the lists up to order.** `memberStartRes_intro (ms : List (GoString ×
  MemberAddrs)) (Bs As Ds) (hA : (ms.flatMap addrsOf ++ Bs).Perm As) (hD : (ms.map (wd ∘ fst)).Perm
  Ds)` turns `startRights`' three lists into `[∗ list] m ∈ ms, memberStartRes m.1 m.2` and `[∗ list]
  b ∈ Bs, netAddrFree b`.
  - Why: the closed theorems' lists are not in member order (putget3's `As = [peer₁, peer₂, peer₃,
    client₁]`), and `addrsUnclaimed` is axiomatized, with no permutation lemma. So the intro adapts
    to the theorem's list, not the reverse. The client addresses' `httpProtoFree` is dropped, as
    today.
  - Distinctness: `As.Nodup`/`Ds.Nodup`, the premises `goose_adequacy_start` already takes, so no
    new premise for the examples.
  - Packaged as `etcd_adequate_members`, beside `etcd_adequate`: each `Adequacy.lean` calls it once.
- **D3. Optional addresses (`MemberAddrs`).** A bundle with a mandatory peer address would force
  the one-member examples' closed theorems to take their unused peer address in `HAs`. That is a
  stronger hypothesis, so a weaker theorem, and a top-level change. Options:
  - (a) `Option` fields;
  - (b) two bundle families (one-member, cluster member);
  - (c) mandatory fields.

  Recommendation: (a), by "modes generalize, no twins".
- **D4. `leaseTTLRowR` into the lease slot (lease-expiry's H-a, "moves with step 7")**. Make it a
  first-start part of the lease slot, under a defaulted flag:
  - `memberBuilt … (fresh := true)` and `memberUp … (fresh := true)`, passing it to `srvLeaseRd`;
    `lease.srvInv`'s first-start part is `leaseTTLRowR`;
  - `memberBuiltR` and restart's `memberUp` pass `false`;
  - no example passes a new argument;
  - the conjunct leaves the posts of `newServer`, `newServerMode`, `BuildServer` and `StartServer`.

  Options: (a) in step 7, as its own commit after lease-expiry lands, its sealed body agreed with
  the lease owner; (b) later, by the lease owner. Recommendation: (a). Step 7 already edits those
  four starters, and the flag is the start kind the bundles make explicit.
- **D5. `netHttpOk γn id` stays outside the bundles**: it is the cluster allocation's output, not a
  program-start resource.

## Hub requests

None from this step. It is itself the hub plan's step 7, owned by the coordinator. The coordinator
tells K6, lease-expiry, r2b3 and auth-comp5 that when they land, their conflicts with step 7 are in
the starter and Main preconditions, and resolve toward the bundle.
