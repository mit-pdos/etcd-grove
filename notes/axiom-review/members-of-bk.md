# Axiom review: `membership.membersOf` and `membership.membersOfBk_empty`, over the two membership buckets

- **Statements** (`Proof/go_etcd_io/etcd/server/v3/etcdserver/InvRest.lean`, branch `lease-grant`,
  `ad1a206a26`, the user's (A) of `notes/lease-grant-plan.md`, "Plumbing"):
  ```lean
  opaque membership.membersOf [GooseExts] :
      Option backend.BktData → Option backend.BktData → GMap w64 (List GoString) × GMap w64 Bool
  def membership.membersOfBk [GooseExts] (bk : GMap GoString backend.BktData) :=
    membership.membersOf (bk.lookup go!"members") (bk.lookup go!"members_removed")
  axiom membership.membersOfBk_empty [GooseExts] (bm br : Option backend.BktData)
      (hm : bm.getD ∅ = ∅) (hr : br.getD ∅ = ∅) : membership.membersOf bm br = (∅, ∅)
  ```
  Before: `membersOfBk` opaque over the whole tracked-bucket map, and the axiom over a whole `bk`
  with the same two premises on its `members` and `members_removed` lookups.
- **New trusted claim.** `membersOfBk` is meant by the read contract
  `schema.membershipBackend.MustReadMembersFromBackend.spec`
  (`Spec/go_etcd_io/etcd/server/v3/storage/schema/membershipBackend__MustReadMembersFromBackend.lean`):
  the call returns `membersOfBk bk`. Making it a definition through `membersOf` claims that this answer
  depends only on the `members` and `members_removed` entries of `bk`, `none` and `some _` kept apart.
  The axiom now says that `none` and `some ∅`, in either position, decode to no members. The use:
  `RestLeased.lean`'s `ccValidOn_restGrantT` and friends (a lease record put in `lease` leaves
  `ccValidOn` as it was) now follow by unfolding, with no premise; `ccValidOn_boot` uses the axiom.
- **Revision**: the etcd fork `ab3c28d9a` (the pin of `etc/goose.py`; `membership.go`, `read_tx.go`,
  `batch_tx.go` and `bucket.go` are the same at `09669450f`, the head of `/shared/etcd-goose-lean-wk`);
  go1.27.3.
- **Earlier review**: `notes/axiom-review/members-empty.md` (2026-10-31, the old axiom: survives). It
  established that Go reads only these two buckets, and that an absent bucket reads like an empty one,
  and it suggested this narrowing. This review builds on it.
- **Verdict: survives** (2026-11-03). No counterexample exists: there is no Go program in which another
  bucket changes the answer, and no mismatch in the empty case. No Lean counterexample was built,
  because there is no panic to prove away.

## The claim in Go

`MustReadMembersFromBackend` (`server/storage/schema/membership.go:83-89`) calls
`readMembersFromBackend` (`:91-122`). That function makes two empty maps, opens `be.ReadTx()`, and runs
`tx.UnsafeForEach(Members, …)` and `tx.UnsafeForEach(MembersRemoved, …)`. The visitors call only
`mustParseMemberIDFromBytes` (pure: `types.IDFromString` of the key, `:180-188`) and `json.Unmarshal`
of the value into a `*Member`. Neither reads the backend. `UnsafeForEach`
(`backend/read_tx.go:54-76`) reads the read buffer by bucket **id** (`txReadBuffer.ForEach`,
`tx_buffer.go:131-136`: `txr.buckets[bucket.ID()]`) and bbolt by bucket **name** (`unsafeForEach`,
`batch_tx.go:254-259`: `tx.Bucket(bucket.Name())`).

## Attacks tried

1. **Another bucket under the same id or name.** The read reaches another bucket's contents only if
   that bucket shares id 10 or 11 (buffer) or the name `members` or `members_removed` (bbolt).
   `backend.Bucket` has a single implementation outside tests, `schema.bucket`
   (`git grep 'ID() .*BucketID'` at the pin: `schema/bucket.go:75`), and its only values are the
   schema's (`bucket.go:43-56`): ids 1-5, 10, 11, 20-22 and 100, with distinct names. No collision.
   In the model, the names `go!"lease"`, `go!"cluster"` and so on differ from `go!"members"` and
   `go!"members_removed"` as strings. That difference is all `RestLeased` uses.
2. **A lease record** (the case that motivated (A)). `MustUnsafePutLease` writes `Lease` (id 3, name
   `lease`), keyed by the 8-byte big-endian lease id. The batch's write-back to the read buffer
   (`txWriteBuffer.writeback`) merges bucket by bucket, by id, and touches no other bucket. Driven in Go
   (below): a lease record, pending and then committed, leaves the read as it was.
3. **Member-shaped data in other buckets.** In every other bucket (`key`, `meta`, `lease`, `alarm`,
   `cluster`, `auth`, `authUsers`, `authRoles`, `test`) the Go test puts a member's key
   (`BackendMemberKey(0x1234)`) with its JSON value, a key `"members"`, and a key `"members_removed"`.
   None of them is read.
4. **`cluster`: the cluster version and downgrade info.** These are read by
   `ClusterVersionFromBackend` and `DowngradeInfoFromBackend` (`membership.go:190-230`), which
   `UnsafeLoad` (`cluster.go:256-260`) calls separately from `MustReadMembersFromBackend`.
   `ValidateConfigurationChange` (`cluster.go:304-…`, the verdict `ccValidOn` models) calls only
   `MustReadMembersFromBackend`, plus the configuration's `c.maxLearners`, which is not in the backend.
   The Go test saves a cluster version, downgrade info and an alarm. The read is unchanged.
5. **A missing bucket vs. an empty one (the `Option`).** In Go both give `nil` from both readers (no
   visit), hence `(empty, empty)`. That is what the axiom says for `none` and `some ∅` in either
   position. In the model, a `none` at a member bucket in the read contract's `rbOwnIn d.γB memberBkts
   bk` (`backend/InvBackend.lean:344,364`) means one of two things. Either the bucket is absent from
   the writer's contents (`rbElem … (none, _)`), or it is not among the ghost map's tracked names `γ.rbD`.
   `γ.rbD` holds every tracked bucket of the table, so a session cannot have created it (`rbDomOf`,
   `NewAlloc.lean:140-143`; `KBReal.P`'s `RB` holds both member buckets, `InvStore.lean:109-115`). In
   both cases the bucket does not exist in Go, so `none` never stands for "unknown contents" that the
   axiom would wrongly declare empty. Whether the read view equals the writer's contents is the read
   contract's claim, reviewed with the backend-auth split (`TestBksReadInsidePendingBatch`), not this
   axiom's.
6. **Is the narrowing a new claim at all?** It is not, beyond what the read contract already said.
   Since 2026-11-01 the contract takes only `rbOwnIn d.γB membership.memberBkts bk` and
   `membersDecode bk`, both of which constrain `bk` only at `members` and `members_removed`. So a caller
   could already pick any other entries of `bk`, and the contract promised the same Go result as
   `membersOfBk bk` for every such choice. The old opaque was therefore sound only if it ignored those
   entries. (A program that reads twice and checks that the two answers agree needs exactly this
   congruence.) The new definition states it.
7. **The empty case.** This is unchanged from `members-empty.md`, attacks 2-3. Over empty or absent
   buckets, no visitor runs, there is no `lg.Panic`, and both maps are `make`'s non-nil empty maps.
   `membersRead mp ∅ ∗ rp ↦$ ∅` describes them.
8. **Consistency (`⊢ False`).** `membersOf` occurs in no other trusted statement, only in
   `membersOfBk`'s body. `fun _ _ => (∅, ∅)` satisfies the axiom, so the axiom adds no inconsistency.
9. **A nested bucket inside `members`.** bbolt's `ForEach` visits a sub-bucket with `v = nil`, and
   `json.Unmarshal(nil, …)` fails, so `lg.Panic` is reached. No etcd code creates a nested bucket, and
   the model's `BktData` has keys only. This concerns the contents of `members`, which is the read
   contract's `membersDecode` premise, not this axiom.

## Go check

The test was written in a scratch copy of the pin (`git archive ab3c28d9a`), package `schema`,
go1.27.3, `betesting.NewTmpBackend` (batch interval 1h, limit 10000). It covers six cases: the member
buckets absent, created empty, or holding one member (`MustSaveMemberToBackend`); then every other
bucket filled as in attacks 2-4, either left pending or force-committed. The read is compared before
and after the filling.

```
=== RUN   TestMembersOfBkAxiom
    members_of_bk_axiom_test.go:70: absent+others-buffered: before members=0 removed=0; after filling others members=0 removed=0
    members_of_bk_axiom_test.go:70: absent+others-committed: before members=0 removed=0; after filling others members=0 removed=0
    members_of_bk_axiom_test.go:70: empty+others-buffered: before members=0 removed=0; after filling others members=0 removed=0
    members_of_bk_axiom_test.go:70: empty+others-committed: before members=0 removed=0; after filling others members=0 removed=0
    members_of_bk_axiom_test.go:70: onemember+others-buffered: before members=1 removed=0; after filling others members=1 removed=0
    members_of_bk_axiom_test.go:70: onemember+others-committed: before members=1 removed=0; after filling others members=1 removed=0
--- PASS: TestMembersOfBkAxiom (0.01s)
```

## Not tried

- The read contract beyond what attacks 5-6 need: whether `rbOwnIn` pins the read view, and whether
  `membersDecode` is enough for a panic-free decode.
- Whether the backend model keeps `P.BT` injective on ids. This matters for the backend's own buffer
  model: the real table is (attack 1), but `KBReal.BT` is a parameter.

## Suggestions (not applied)

- The axiom can still be avoided, as `members-empty.md` suggested. Define `membersOf` as a fold of
  opaque per-key decoders over `bm.getD ∅` and `br.getD ∅`. The `none`/`some ∅` identification is then
  definitional, and the empty case becomes a theorem.
