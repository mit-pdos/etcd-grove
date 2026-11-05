# Axiom review: `membership.membersOf_decode` (a draft on branch `r2b3`, 2026-11-04)

- **Axiom** (the restart plan's R2b-3d gap 3, approved by the user as a trust-boundary axiom on the
  opaque `membersOf`, `Proof/go_etcd_io/etcd/server/v3/etcdserver/InvRest.lean`). If the `members`
  bucket's entries are exactly `memberKey mm.id ↦ memberEnc mm` for members `ms` with distinct ids,
  and the `members_removed` keys are exactly `memberKey id` for `id ∈ rs`, then `membersOf` gives
  each member's peer URLs by id, and `rs` as removed. Reviewed with `membersOf`,
  `membersOfBk_empty` and the read contract
  `schema.membershipBackend.MustReadMembersFromBackend`.
- **Revision**: the etcd fork `673da07c8fab` (the pin of `etc/goose.py`); go1.27.3.
- **Verdict: refuted as drafted; restated.** The draft had no UTF-8 premise and is false of Go. A
  Go program shows the panic, but no Lean counterexample proof was built: it would need a program
  that writes the bucket through specced code (a backend, its buckets and `MustSaveMemberToBackend`),
  so it is not worth it for an axiom not yet landed, restated in the same change. The restatement
  adds `hu : ∀ mm ∈ ms, ∀ u ∈ mm.peerURLs, utf8Valid u` and survives the attacks below.

## The refutation

`readMembersFromBackend` (`server/storage/schema/membership.go:91-123`) `json.Unmarshal`s each value
into a `*Member`, and `MustSaveMemberToBackend` stores `json.Marshal(m)`. `json.Marshal` coerces a
string's invalid UTF-8 bytes to U+FFFD (`encoding/json`: "String values encode as JSON strings
coerced to valid UTF-8"), so a member whose peer URL is not valid UTF-8 reads back with a different
peer URL. The draft claimed the original. The Go test (`examples/axiomcx/membersdecode`, not kept:
it needs testify, which `examples/go.mod` does not carry; source below) at the pin:

```
membersdecode_test.go:27: saved "http://\xff:2380", read "http://�:2380"
panic: membersOf_decode: the peer URL read back differs from the one saved
```

```go
func TestPeerURLRoundTrip(t *testing.T) {
	be, _ := betesting.NewDefaultTmpBackend(t)
	defer be.Close()
	schema.CreateMetaBucket(be.BatchTx())
	mb := schema.NewMembershipBackend(zap.NewNop(), be)
	mb.MustCreateBackendBuckets()
	url := "http://\xff:2380"
	m := &membership.Member{ID: types.ID(7), RaftAttributes: membership.RaftAttributes{PeerURLs: []string{url}}}
	mb.MustSaveMemberToBackend(m)
	be.ForceCommit()
	members, _ := mb.MustReadMembersFromBackend()
	got := members[types.ID(7)].PeerURLs[0]
	if got != url {
		panic("membersOf_decode: the peer URL read back differs from the one saved")
	}
}
```

## Attacks on the restatement (survives)

1. **The key.** `mustParseMemberIDFromBytes` is `types.IDFromString`, which is `strconv.ParseUint(s,
   16, 64)`. `BackendMemberKey(id)` is `id.String()`, `strconv.FormatUint(id, 16)`. Hex round trips,
   and no other key shape is admitted (`hm`). Two members with one key would need equal ids, which
   `hnd` excludes.
2. **The value.** `m := &Member{ID: memberID}; json.Unmarshal(v, &m)`: the JSON object decodes into
   the preset member. `Member`'s fields marshal and unmarshal symmetrically: `id` a number,
   `peerURLs` (nil marshals as `null`, unmarshals to nil, the empty list either way),
   `isLearner,omitempty`, `name,omitempty`, `clientURLs,omitempty`. HTML escaping (`<`, ...)
   and ` ` decode back. With valid UTF-8, the only string transformation is gone. Only peer
   URLs are in the conclusion, so the other fields' strings do not matter.
3. **The value `null`.** `memberEnc` is `json.Marshal` of a non-nil `*Member` (its docstring), never
   `null`, so `m` is never reset to nil.
4. **Removed.** Every key visited gives `removed[id] = true`, whatever the value. `hr` names exactly
   the keys, so the conclusion matches.
5. **Absent buckets.** `getD ∅`: Go's `UnsafeForEach` on a missing bucket visits nothing, the same as
   `membersOfBk_empty` (reviewed in `members-empty.md`).
6. **Consistency with the other statements.** `membersOf` is opaque. Its other law
   (`membersOfBk_empty`) is the instance `ms = rs = []`, where both conclusions agree (empty maps).
   The read contract only passes `membersOfBk` through. `membersOf` defined as the fold Go performs
   (UTF-8 coercion included) satisfies both laws, so the pair is consistent.

## `apply.memberEnc_id_learner` (2026-11-04, the same change)

`memberEnc a = memberEnc b → a.id = b.id ∧ a.isLearner = b.isLearner`, in
`Proof/go_etcd_io/etcd/server/v3/etcdserver/apply/RestModel.lean`. **Survives.**

- **The id.** `Member.ID` is `types.ID`, a `uint64` with no `MarshalJSON` or `UnmarshalJSON`
  (`client/pkg/types/id.go`), so it is written as `"id":<decimal>`, which is injective. No other field
  is named `id`: `RaftAttributes` and `Attributes` are embedded, with fields `peerURLs`,
  `isLearner`, `name` and `clientURLs`.
- **The learner flag.** `IsLearner bool json:"isLearner,omitempty"`: `"isLearner":true` appears iff it
  is true. A string field cannot imitate it, because json escapes the quotes inside strings.
- **Coercion.** Only strings are coerced (invalid UTF-8 to U+FFFD), and neither field is a string.
- **Consistency.** `memberEnc` is opaque. Its other statements (`membersDecode`, `membersOf_decode`)
  constrain it only through `memberKey` and the decode, and both hold of the real `json.Marshal`.

## `apply.memberKey_inj` (2026-11-04, the same change)

`memberKey a = memberKey b → a = b`. **Survives.** `schema.BackendMemberKey(id)` is
`[]byte(id.String())` (`server/storage/schema/bucket.go:106-108`). `types.ID.String()` is
`strconv.FormatUint(uint64(i), 16)` (`client/pkg/types/id.go:27-29`): lowercase hex, no leading
zeros, `"0"` for 0, so injective on `uint64`. `memberKey` is opaque, and its other statements
(`membersDecode`, `membersOf_decode`) are true of this function, so the axioms are consistent.
