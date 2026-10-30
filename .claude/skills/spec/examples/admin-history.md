# The admin requests over a client's view of the auth history; authkv's `SetUp` (2026-10-29)

etcd's admin requests (`UserAdd`, `RoleAdd`, `UserGrantRole`, `RoleGrantPermission`,
`AuthEnable`) change the auth state. The server's admin specs must let a client (authkv's
`SetUp`) conclude what the auth state is after its calls, and that nothing changes it afterwards.
The auth-mode merge's 5b; the user approved candidate 4 of the server design and the `SetUp`
statement; the critiques below are the spec reviewer's (three rounds) and authkv's session's.

## The first version (candidate 1)

The admin request's permission was an abstract persistent `Q` the client chose per call, and
`SetUp.spec` took the Auth service as a premise in the client's terms:

```lean
def setupAuthOk (ep : GoString) (Su : GrpcSpec …) … (Se : GrpcSpec …) (Q : Fin 8 → IProp GF) :=
  isGrpcRpc ep "/etcdserverpb.Auth/UserAdd" Su ∗ … ∗
  □ ▷ Su ⟨"root", "root-pw"⟩ (fun _ => Q 0) ∗ … ∗ □ ▷ Se () (fun _ => Q 7)

SetUp.spec: {{ … ∗ setupAuthOk ep Su Sg Sr Sp Se Q }} SetUp(cl) {{ rev ok; if ok then Q 0 ∗ … ∗ Q 7 }}
```

Nothing tied `Q` to the auth state, and nothing stopped another client (or a stale delivery of one
of `SetUp`'s own retried calls) from changing the state afterwards: `Main` could not conclude that
the state stays `setupSt`.

## The critiques, and what each changed

1. **The state is shared; say who may change it** (round 1). The candidate 1 history was a log of
   the client's calls, but the server applies every delivery, retries included. Changed: a
   mono-list auth history along the requested log, a pure function of it (`admStates γk st₀ L`),
   half in `kvInvOn`, half the client's `authHistView`; the admin request's permission is an atomic
   update over the view (`histAu`), so only the view's holder can change the state.
2. **Record only what changes the store** (round 2, G5). An entry refused, or one whose step errs or
   keeps the state, records nothing, exactly when the store's own history does not grow
   (`auth/Steps.lean`). Changed: `admEntry` needs `adminOk` and `adminNext rq st ≠ st`.
3. **No disjunct in the atomic precondition** (round 2, G1). Candidate 2's precondition was the view
   *or* a frozen history with a proof that the caller is not admitted. Changed: the precondition is
   the view alone; the post carries the admission (`adminOk` at the last state), so a frozen
   caller refutes the commit itself.
4. **Freezing must hold timeless contents** (G2): a freezable cell (`authHistCell`) allocated up
   front, an invariant an atomic update's precondition can open; `authHistFrozen = cell ∗ mark`.
5. **The commit gives the logs** (authkv, G3): `L`, `L ++ [e]` and the history after, so the
   frozen log `Lset` is tied to the view's states.
6. **The reply tells what was recorded** (G4): `□ Q hs` at the commit; the reply carries `□ Q` if
   the entry was recorded at the reply's log, else that it was not.
7. **`SetUp`'s premise in etcd's terms** (the user's approval of the set-up draft): the specs are
   etcd's, served at `ep` (`setupAuthServed`), not abstract `Su … Se`.
8. **Found in the proof** (not critiques; reported): the reply's not-recorded case needs a lower
   bound of the history at its log (`adminRecRes` gains `authHistLb`); the published state after
   `AuthEnable`'s entry needs `e.data ≠ []` (`pubAfterM`) and the entry above the start's
   consistent index (`SetUp` takes `c0 ≤ ai0`); the context's outgoing metadata needed a
   trust-boundary spec (the user chose an axiom over a premise).

## The approved spec

```lean
def histAu (γ : ServerRaftNames) (γk : KVNames) (st₀ : auth.AuthState)
    (Gb : apply.HeaderModel → IProp GF) (rq₀ : apply.IRRModel)
    (Q : List auth.AuthState → IProp GF) : IProp GF :=
  □ AU <{ ∃∃ hs, authHistView γk hs }> @ (⊤ \ ↑srvRaftN) \ ↑kvN, ∅
    <{ ∃ hm L e, Gb hm ∗ srvReqLogLb γ L ∗ srvReqLogLb γ (L ++ [e]) ∗
         ⌜irrDecode e.data = some (withHeader rq₀ hm) ∧ admStates γk st₀ L = hs ∧
          adminOk (hs.getLastD st₀) (principal of hm) ∧ authDet … ∧
          admStates γk st₀ (L ++ [e]) = hs ++ [adminNext (withHeader rq₀ hm) (hs.getLastD st₀)]⌝ ∗
         authHistView γk (hs ++ [adminNext …]),
       COMM □ Q hs }>

abbrev SetUp.spec : Prop :=
  ∀ … (cl ep V s E ρ cid mid γa), E.authMode = .on γa → uint.Z ρ.kv.c0 ≤ uint.Z ρ.raft.ai0 → …
  {{ isPkgInit authkv ∗ isNewClient cl [ep] V ∗ clientTokAt cl [ep] (fun _ => False) ∗
      isGrpcRpcMd ep "/etcdserverpb.KV/Put" (etcdPutSpecOn s E ρ cid mid) ∗ (□ ∀ k ∈ setupKeys, …) ∗
      setupAuthServed ep s E ρ ∗ □ (srvTLSId s -∗ False) ∗ authHistView ρ.kv [srvAuthSt0] }}
    SetUp(cl)
  {{ rev ok; if ok then ∃ γz hs Lset k r, authHistFrozen ρ.kv γz hs ∗ srvReqLogLb ρ.raft Lset ∗
       ⌜admStates ρ.kv srvAuthSt0 Lset = hs ∧ srvAuthAtLog ρ.kv srvAuthSt0 Lset = setupSt r⌝ ∗
       authPubLb γa k ∗ authStateAt γa k (setupSt r)
     else True }}
```

The principles it shows: a shared state's spec says who may change it (an exclusive view, the
update a resource); an atomic precondition is the resource alone, the admission in the post; the
client's post is the abstract state (`setupSt`, frozen, published), not the calls' replies.
