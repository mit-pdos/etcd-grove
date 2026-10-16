---
upstream: known
checked: 2026-10-16
links:
  - etcd-io/etcd#18437 issue closed: the symptom (a fresh simple token rejected by another member); closed with a documentation note, the cause given as the API-layer check not being linearizable, without the off-by-one
  - etcd-io/website#883 pr merged: the "known issue" note on simple tokens
  - etcd-io/etcd@66c7aab4d: introduced it (3.5.3, the txPostLockHook fix of #13766: the stored consistent index lags during apply)
---

# auth: a simple token names the index before the entry that issued it, so other members do not wait for it

- **Status**: bug (a fresh simple token is spuriously rejected with `ErrInvalidAuthToken` by a
  member that has not yet applied the issuing entry; a regression in 3.5.3). JWT tokens are not
  affected.
- **Where**: at the pinned revision (`etc/goose.py`, etcd `107edf7e4`; identical on upstream
  `main`):
  - `server/etcdserver/apply/backend.go:157-163`, `applierV3backend.Authenticate`: the token's
    index is `a.options.ConsistentIndex.ConsistentIndex()`;
  - `server/etcdserver/server.go:1904-1909`, `applyEntries`: before the entry is applied only
    the *applying* index is set (`SetConsistentApplyingIndex(e.Index)`). The stored index moves
    in the post-lock hook (`:2448-2455`) or after the entry (`:1945-1948`), and `Authenticate`
    takes no batch lock first, so `ConsistentIndex()` is the previous entry's index;
  - `server/auth/simple_token.go:215-245`: `assign` writes the index into the token
    (`"<prefix>.<index>"`), and `isValidSimpleToken` waits on `indexWaiter(index)`
    (`applyWait.Wait`, `server.go:355-358`) before `info` looks the token up.
- **What happens**: the Authenticate entry at index `e` issues `"<prefix>.<e-1>"`. A member that
  has applied `e-1` but not `e` (its `applyWait` triggered for `e-1`, `server.go:984`) passes the
  wait at once and does not find the token, so `AuthInfoFromCtx` returns `ErrInvalidAuthToken`.
  With the correct index it would wait until it has applied `e` and then accept the token. The
  issue's log shows it: entry 19146857, consistent index 19146856, token `….19146856`.
  Reproduction (in `server/etcdserver/apply`, at the pin; passes, that is, shows the bug):

  ```go
  // member builds an auth applier (as defaultAuthApplierV3, with its own cindex) whose token
  // provider's waiter reports index i applied iff i <= *applied; auth enabled
  // (mustCreateRolesAndEnableAuth) and a user "alice" with password "pw".
  func TestSimpleTokenNamesPreviousIndex(t *testing.T) {
  	var appliedA, appliedB uint64
  	a, ciA, _ := member(t, &appliedA)
  	_, _, asB := member(t, &appliedB)
  	ciA.SetConsistentIndex(9, 1)         // entries up to 9 applied
  	ciA.SetConsistentApplyingIndex(10, 1) // applying the Authenticate entry at 10
  	resp, err := a.Authenticate(&pb.InternalAuthenticateRequest{Name: "alice", SimpleToken: "prefix"})
  	require.NoError(t, err)
  	require.True(t, strings.HasSuffix(resp.Token, ".9")) // "prefix.9", not "prefix.10"
  	appliedB = 9 // member B has applied 9, not yet 10
  	md := metadata.New(map[string]string{rpctypes.TokenFieldNameGRPC: resp.Token})
  	ctx, cancel := context.WithTimeout(metadata.NewIncomingContext(context.Background(), md), 2*time.Second)
  	defer cancel()
  	_, err = asB.AuthInfoFromCtx(ctx)
  	require.ErrorIs(t, err, auth.ErrInvalidAuthToken) // at once (28µs), no wait
  }
  ```

  The full test file (with `member`):
  `issues/etcd-simple-token-index-off-by-one/authenticate_index_test.go`.
- **Expected**: the token names the index of the entry that issued it, so `isValidSimpleToken`
  on any member waits until that member has applied it (the purpose of the `indexWaiter`, and
  the 3.4/3.5.0–3.5.2 behavior, when `applyEntryNormal` stored `e.Index` before applying).
- **How the proof handles it**: the specs admit it. `applierV3backend.Authenticate.spec`
  (`Spec/go_etcd_io/etcd/server/v3/etcdserver/apply/applierV3backend__Authenticate.lean`) does
  not state the context it passes. The store's `Authenticate` is a contract of `isAuthStore`
  (`Proof/go_etcd_io/etcd/server/v3/etcdserver/apply/Contracts.lean:183-187`). The token
  provider is the contract `tokenProviderOk` (`Proof/go_etcd_io/etcd/server/v3/auth/InvAuth.lean`:
  `info` returns any auth info and boolean). `authStore.AuthInfoFromCtx.spec` admits
  `ErrInvalidAuthToken` for any token. `simple_token.go` is not translated. The cindex specs do
  distinguish the stored index (`ConsistentIndex`) from the applying one, so a spec naming the
  token's index would fail at `backend.go:158` (`notes/bug-triage/etcd-18437.md`, proposal
  `simple-token-index`).
- **Possible fixes**: in `applierV3backend.Authenticate`, take the index from
  `ConsistentApplyingIndex()` (the entry being applied). Or have the caller pass the entry's
  index in the request wrapper.
- **Found**: 2026-10-16, bug triage of etcd-io/etcd#18437 against the specs (reproduced at the
  pin).
