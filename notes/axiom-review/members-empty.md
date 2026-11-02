# Axiom review: `membership.membersOfBk_empty` (a draft, not yet in any tree)

- **Axiom** (requested by session etcd-grove-56, to go right after `membership.membersOfBk` in
  `Proof/go_etcd_io/etcd/server/v3/etcdserver/InvRest.lean` on branch `snap-sorries`,
  `29532cab89`):
  ```lean
  axiom membership.membersOfBk_empty [GooseExts] (bk : GMap GoString backend.BktData)
      (hm : bk.lookup go!"members" = some ∅) (hr : bk.lookup go!"members_removed" = some ∅) :
      membership.membersOfBk bk = (∅, ∅)
  ```
  `membersOfBk` is opaque (`GMap GoString BktData → GMap w64 (List GoString) × GMap w64 Bool`); its
  only meaning comes from the names-only contract axiom
  `schema.membershipBackend.MustReadMembersFromBackend.wp_proof`
  (`Spec/go_etcd_io/etcd/server/v3/storage/schema/membershipBackend__MustReadMembersFromBackend.lean`):
  with the reader's token and the writer's half of the tracked buckets `rbOwn d.γB bk`, the call
  returns `mp, rp` with `membersRead mp (membersOfBk bk).1 ∗ rp ↦$ (membersOfBk bk).2`.
- **Use**: the first boot entry's `AddNode` validates on the fresh backend
  (`ccValidOn restBootBk m = true`: `ccValidM ∅ ∅ m` holds for an `AddNode`), so `ep.confState`
  becomes the voters' (S5 of #11).
- **Revision**: the etcd fork `249d76bea7` (`.lake/go-src/etcd`, the pin of `etc/goose.py` on both
  `lean` and `snap-sorries`); go1.27.3.
- **Verdict: survives** (2026-10-31). No counterexample; none built (no panicking program exists:
  below).

## The claim in Go

`MustReadMembersFromBackend` (`server/storage/schema/membership.go:83-89`) panics only if
`readMembersFromBackend` (`:91-123`) returns an error, and that function makes both maps with `make`
(non-nil, empty), then runs `tx.UnsafeForEach(Members, …)` and `tx.UnsafeForEach(MembersRemoved, …)`.
The only errors and panics are inside the visitors (`mustParseMemberIDFromBytes`'s `lg.Panic`,
`json.Unmarshal`'s error), and the only writes to the maps are there too. So: no key visited in
either bucket ⇒ no panic, and the result is `(empty map, empty map)`, which is what
`membersRead mp ∅ ∗ rp ↦$ ∅` describes (`membersRead mp ∅` forces the `ml` of `mp ↦$ ml` to be
empty: `(ml !! k).isSome = false` for every `k`).

## Attacks tried

1. **Other buckets.** `readMembersFromBackend` reads only `Members` (id 10, `"members"`) and
   `MembersRemoved` (id 11, `"members_removed"`) (`schema/bucket.go:32-33,49-50`). The bolt read
   is by name (`unsafeForEach`, `backend/batch_tx.go:254-259`), the read buffer by bucket id
   (`txReadBuffer.ForEach`, `backend/tx_buffer.go:131-136`), and the ids are unique among the
   schema's buckets (`bucket.go:43-55`: 1-5, 10, 11, 20-22, 100). No key of another bucket (e.g. a
   `"members"` key in `Key`) can reach the visitors; the Go test below puts one in `Key` and one in
   `cluster` and the result stays empty. So the Go answer is a function of those two buckets only;
   the opaque being over all of `bk` is weaker than Go, not stronger, and the axiom's premises name
   exactly those two buckets.
2. **Absent vs. empty.** The premises say `some ∅`: the buckets exist with no keys (what
   `MustCreateBackendBuckets`, `membership.go:171-178`, leaves, and what `restBootBk` has; `∅ :
   BktData` is the bucket with no keys, `bktOf`'s default). Go gives the same answer for an absent
   bucket (`unsafeForEach` and `txReadBuffer.ForEach` both return `nil` on a missing bucket), so
   the axiom could be stated with `(bk.lookup n).getD ∅ = ∅` and still be true; as drafted it is
   strictly weaker. No panic on a missing bucket (`UnsafeForEach` does not require it).
3. **Can the reads fail or panic on empty buckets?** `baseReadTx.UnsafeForEach`
   (`backend/read_tx.go:54-76`) runs the buffer's `ForEach` (`bucketBuffer.ForEach`, a loop over
   `used` entries: none), bolt's `Bucket.ForEach` (no keys: no visit, `nil`), and the buffer again;
   none returns an error without a visit. `lg.Panic` is not reached.
4. **A stale buffer entry that the model's `∅` misses.** Can bolt+buffer show a key while the
   tracked view `bk` says the bucket is empty? A put is buffered and written back on `Unlock`
   (the model's view includes it); a delete is not buffered but forces a commit on `Unlock`
   (`batchTxBuffered.Unlock`, `batch_tx.go:328-360`, `pendingDeleteOperations`), which resets the
   read buffer. Driven in Go (below): a member saved (buffered, batch interval 1h), deleted, its
   `members_removed` key deleted: the read is `(0, 0)`. Whether `rbOwn d.γB bk` faithfully reflects
   the read view in general is the existing read contract's claim (and the backend proof's), not
   this axiom's; this axiom only makes that claim load-bearing at the empty view, where it holds.
5. **Inconsistency in Lean (`⊢ False`).** `membersOfBk` is opaque and, on `snap-sorries`, appears in
   no other axiom or law: its only other occurrence in a trusted statement is the read contract,
   a Hoare triple of a names-only Go function (`Code/.../storage/schema.lean` has its signature, no
   body), so no operational fact constrains it. The other opaques in the neighbourhood
   (`memBucketsOk`, used by `clusterImageOk_restModel`'s axiom; `ccMemberOf`) are not related to
   `membersOfBk` by any statement. Replacing `membersOfBk` by `fun _ => (∅, ∅)` satisfies the axiom
   and leaves every other statement as it was, so the axiom adds no inconsistency. Note also that
   `clusterImageOk_restModel`'s own docstring already argues the boot entries validate because
   "`ValidateConfigurationChange` finds no member with its id or peer URLs yet": the new axiom is
   that argument's first step made explicit, and agrees with it.
6. **The `GMap` side.** `bk.lookup n = some ∅` is a plain lookup in the tracked-bucket map; nothing
   else in the model ties `restBootBk`'s `members` to a different value (`restBootBk_of_fresh`, a
   theorem, proves the fresh backend's tracked buckets equal `restBootBk`, whose `members` and
   `members_removed` are `∅`). No map fact conflicts.
7. **The use.** With the axiom, `ccValidOn restBootBk m` is `ccValidM ∅ ∅ m`: `(∅ !! id).getD false
   = false`, and for `m.type = 0`, `∅ !! id = none` and no URL is taken in `∅`. That is Go's verdict
   too: on the fresh backend `ValidateConfigurationChange` with `shouldApplyV3` finds no removed id,
   no member with the id, no member with the peer URLs (nothing writes `members` before the boot
   entries are applied: `MustSaveMemberToBackend` is called only from `RaftCluster`'s
   `AddMember`/`UpdateAttributes`/`PromoteMember`/`UpdateRaftAttributes`, `cluster.go:403,474,510,558`,
   none at bootstrap).

## Go check

A test added through `go test -overlay` (no file written in the shared `.lake/go-src/etcd`), in
package `schema` at the pin, go1.27.3: three backends (`betesting.NewTmpBackend`, batch interval
1h, limit 10000):

- `created-empty`: `MustCreateBackendBuckets`, then the read;
- `absent`: no buckets created, then the read;
- `emptied-again`: a member saved (and read back: 1 member), deleted
  (`MustDeleteMemberFromBackend`), its `members_removed` key deleted, puts pending in `cluster` and
  in `Key` under the key `"members"`, then the read.

```
=== RUN   TestMembersEmptyAxiom
    members_empty_axiom_test.go:17: created-empty: members=0 removed=0 (members nil=false removed nil=false)
    members_empty_axiom_test.go:17: absent: members=0 removed=0 (members nil=false removed nil=false)
    members_empty_axiom_test.go:17: emptied-again: members=0 removed=0 (members nil=false removed nil=false)
--- PASS: TestMembersEmptyAxiom (0.00s)
```

## Not tried

- A Lean counterexample: there is no Go panic to prove away, and the consistency argument (attack 5)
  is a model of the opaque, not a proof term; `membersOfBk` and `restBootBk` are not on `lean`.
- The read contract itself (`MustReadMembersFromBackend.wp_proof`) beyond the empty case: whether
  `rbOwn` with the writer's half pins the read view in all cases (attack 4 only at the empty view).

## Suggestions (not applied)

- The axiom could be avoided: define `membersOfBk bk` from the two buckets with an opaque per-key
  decode (`memberIdOf : GoString → w64`, the URL decode of a value, as `ccMemberOf` is opaque), e.g.
  a fold over `(bk.lookup go!"members").getD ∅` and `(bk.lookup go!"members_removed").getD ∅`; the
  empty case is then a theorem, and "a function of these two buckets only" (attack 1) is
  definitional instead of a docstring claim. The read contract's statement is unchanged.
- If it stays an axiom, the absent-bucket case is also true (attack 2), though the use does not need it.
