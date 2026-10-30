# The auth store's history tied to the log; the read law (2026-10-30)

authkv's `Main` must conclude that once `SetUp` froze the auth history at `hs`, the auth store's
state at every later index is `last hs`. The store records its states in its own ghost history
(`authStateAt γa i st`); the server's model records them along the log (`admStates`). Nothing tied
the two. H5 of the auth-mode merge; the user approved candidate 3; the critiques are the spec
reviewer's (three rounds) and authkv's session's.

## The first version (candidate 1)

A cap on the store's history the server raises, with the store's admin operations needing the
cap's permission through an unguarded premise at every history:

```lean
apply.adminExtra E γa rq Pre   -- no history
  ⊇ □ ∀ hs, ⌜adminPassL (.on γa) hs rq⌝ → capNextM (.on γa) hs R
authStateAt_setup : … authStateAt γa m st ∗ ⌜setupFrozenOk hs⌝ ={E'}=∗ ⌜st = last hs⌝  -- at a fixed E'
```

## The critiques, and what each changed

1. **A premise must be provable by whoever supplies it** (round 1 and 2). The server's cap covers
   only the store's actual history, so it cannot prove the permission at every `hs` the check
   would pass. Changed: `adminExtra` takes the history `hs` (the binder `adminSpecL` and
   `dispatch.adminSpec` already have), and the permission is at that `hs`.
2. **Guard by what the code has checked, where it has checked it** (round 2). The verdict of the
   admission check was only in `applierAdmL`'s post, after the dispatch callback runs. Changed:
   the callbacks' preconditions gain `⌜adminPassL …⌝` (the Go checks before `applyFunc`), and above
   the dispatch the permission is guarded by it (`adminExtraG`).
3. **Use only what the client's spec exports** (round 2): `setupFrozenOk` is not in `SetUp`'s post.
   Changed: the history along the log has no state twice (`admStates_nodup`, by an order that
   every recorded step raises), so `last hs` is at one index; `SetUp.spec` does not change.
4. **Take the client's own index** (round 1): the read law takes `SetUp`'s `k` as `SetUp` returns
   it (`authStateAt γa k (hs.getLastD srvAuthSt0)`).
5. **State masks as subset premises** (authkv): so the law holds at `⊤` and at the read results'
   masks.

## The approved spec (candidate 3), as implemented

```lean
def authHistTie (E : apply.AEnv GF) (γr : ReadNames) (st₀ : auth.AuthState) : IProp GF :=
  match E.authMode with
  | .on γa => iprop((∃ stl R, auth.authInv stl R (.on γa)) ∗
      inv authTieN iprop(∃ A, srvRLogLb γr.raft A ∗
        auth.capAuth γa (auth.bootState :: admStates γr.kv st₀ A)))
  | _ => iprop(True)

theorem authStateAt_setup … (hγa : E.authMode = .on γa) (hE0 : ↑srvRaftN ⊆ E') (hE1 : ↑kvN ⊆ E')
    (hE2 : ↑authHistN ⊆ E') (hE3 : ↑authTieN ⊆ E') (hE4 : ↑(nroot.@"authRev") ⊆ E') :
    srvRaftLogInv ρ.raft ∗ kvInvOn ρ.raft ρ.kv srvAuthSt0 ∗ authHistTie E ρ srvAuthSt0 ∗
      authHistFrozen ρ.kv γz hs ∗ auth.authStateAt γa k (hs.getLastD srvAuthSt0) ∗ ⌜k ≤ m⌝ ∗
      auth.authStateAt γa m st ={E'}=∗ ⌜st = hs.getLastD srvAuthSt0⌝
```

The implementation derived the pin `hs = srvHist A` at the admin entry (`authHistTie_raise`) rather
than threading it through `kvAppliedOn` as the design sketched: a fact the proof can derive where
it is used need not be carried in an invariant.
