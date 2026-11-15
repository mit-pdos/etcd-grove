/-
# The auth store's internal vocabulary (batch 3d)

What the package's own helpers' specs are stated over (`lockedReadTx`, `isOpPermitted`, the cache,
the revision's helpers, `selectPassword`, the providers' constructors). Package-internal: no other
package's statement mentions these; clients see `Api.lean`. Their intended realization is the
store's invariant of `Api.lean`'s header.

* `txAt tx a` (exclusive): a locked auth transaction `tx` (an `UnsafeAuthReader`: the backend's read
  transaction, or its batch transaction, also an `UnsafeAuthWriter`) whose buckets hold `a` (4b's
  contract, `authBackendAt`'s realization).
* `rdTx γa tx j a` (exclusive): `lockedReadTx`'s answer: `txAt tx a` at the store's `j`-th state
  (the backend view), holding the reader slots of `beMu` and of the backend's read lock, lent by a
  `threadTok`; `RUnlock()` gives it back (`rdTx_RUnlock`).
* `wrStep γa i a a'` (exclusive): the writer inside an admin step from its `i`-th state `a` towards
  `a'`, not yet recorded (between `BatchTx().Lock()` and `commitRevision`); `wrRec γa i a'`: the step
  recorded (`a'` is the `(i+1)`-th state, `commitRevision` or `setRevision` done), the views moving.
  The admin methods' proofs open `authCur` into `wrStep` and close `wrRec` back into `authCur` after
  the batch transaction's `Unlock`. Both carry, with the batch session, the lock's turn
  `Backend.beTurn γb` (4a's verify-round repair: every `Lock*` returns it, `Unlock`'s second atomic
  update takes it back; 4b's `SchemaTx.lean` `btLockIn`/`btLockOut`/`btUnlock` under `authBatchTx`),
  so no auth method's statement changes: each takes the turn at its lock and gives it back at its
  `Unlock` inside the call.
* `cacheEntry p a u` (persistent): `p` is a `*unifiedRangePermissions` holding `u`'s merged read and
  write permissions at `a` (3f's interval trees over bytes-affine keys).
* `cacheOwn st a` (exclusive): the right to replace the store's cache map, now of `a` (the writer's,
  inside `wrRec`; `NewAuthStore`'s before the invariants exist).
* `optsMapAt m opts` (exclusive): the fresh `map[string]string` at `m` holds the `key=value` pairs
  of `opts` after its first comma (`decomposeOpts`'s), what the JWT provider parses.
* `userRolesAt p roles` (persistent): `p` is a `*authpb.User` whose `Roles` slice holds `roles`,
  read-only.
* `tpOpen tp γ R` (persistent): the provider's contract opened (`tokenProviderAt` given to a store),
  its `info` gated on `R` (verify round, A9 3d F7).
* **The `TokenProvider` bundle** (review round 1, S7): `tpOpen tp γ R` with `tpFrom tp n` (exclusive:
  no token of an `Authenticate` index above `n` assigned; the store's `tokFrom γa n` is its
  provider's), `tpRoot tp` (persistent: root tokens without a collision; `rootTokOk`'s); `assign`
  takes the API's transparent `authnCtx` (verify round: `tpAuthn`, `simpleAuthn` gone, opaques with
  no introduction). Its laws are the
  interface methods' triples (`tp_info`, `tp_assign`, `tp_assignRoot`, `tp_enable`, `tp_disable`,
  `tp_invalidateUser`, `tp_genTokenPrefix`) and its opening (`tokenProviderAt_open`), proved per
  provider from the concrete methods' specs (`tokenSimple__*`, `tokenNop__*`; JWT: assumed in
  `newTokenProviderJWT.spec`); the instances `simple_provider`, `nop_provider`.
* The simple provider: `simpleAt t γ R` (persistent; its waiter gated on `R`: its lock `simpleTokensMu` and invariant: the map
  `simpleTokens`, each token `tok ↦ u` with `tokenUser γ tok u`, its index part at most the bound
  of `simpleFrom`; the keeper field, `nil`, or a running
  keeper with its stop right; verify-round: no reserved `threadTok`, the keeper goroutine runs on
  its fork's own), `simpleFrom t n` (exclusive), `simpleFresh t tok` (exclusive: `tok`
  is not in the map and no one else may add it).
* The TTL keeper: `keeperAt tm t` (persistent: `tm`'s channels and ticker resolution, its `mu` is
  `&t.simpleTokensMu`, its delete function `t`'s), `keeperTokens tm S` (exclusive, held under that
  lock: the `tokens` map's keys are `S`), `keeperRun tm` (exclusive: the goroutine's right; `donec`'s
  close carries no token, verify-round), `keeperStop tm` (exclusive: the
  right to stop it once).
* `permKeysAt ps ks` (persistent): the `*authpb.Permission`s `ps` have the keys `ks`, read-only.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.auth.Api
public import SpecPlan.Spec.context.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Auth

open Iris Iris.BI EtcdModel

section res
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

opaque txAt [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (tx : GoInterface) (a : AuthState) : IProp GF := iprop(True)
opaque rdTx [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (γa : AuthNames) (tx : GoInterface) (j : Nat) (a : AuthState) : IProp GF := iprop(True)
opaque wrStep [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (γa : AuthNames) (i : Nat) (a a' : AuthState) : IProp GF := iprop(True)
opaque wrRec [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (γa : AuthNames) (i : Nat) (a' : AuthState) : IProp GF := iprop(True)
opaque cacheEntry [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (p : Loc) (a : AuthState) (u : GoString) : IProp GF := iprop(True)
opaque cacheOwn [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (st : Loc) (a : AuthState) : IProp GF := iprop(True)
opaque optsMapAt [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (m : Loc) (opts : GoString) : IProp GF := iprop(True)
opaque userRolesAt [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (p : Loc) (roles : List GoString) : IProp GF := iprop(True)
opaque tpOpen [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (tp : GoInterface) (γ : Cluster) (R : IProp GF) : IProp GF := iprop(True)
opaque tpFrom [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (tp : GoInterface) (n : Nat) : IProp GF := iprop(True)
opaque tpRoot [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (tp : GoInterface) : IProp GF := iprop(True)
opaque simpleAt [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (t : Loc) (γ : Cluster) (R : IProp GF) : IProp GF := iprop(True)
opaque simpleFrom [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (t : Loc) (n : Nat) : IProp GF := iprop(True)
opaque simpleFresh [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (t : Loc) (tok : GoString) : IProp GF := iprop(True)
opaque keeperAt [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (tm t : Loc) : IProp GF := iprop(True)
opaque keeperTokens [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (tm : Loc) (S : GoString → Prop) : IProp GF := iprop(True)
opaque keeperRun [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (tm : Loc) : IProp GF := iprop(True)
opaque keeperStop [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (tm : Loc) : IProp GF := iprop(True)
opaque permKeysAt [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (ps : List Loc) (ks : List Bytes) : IProp GF := iprop(True)

def tpRoot_persistent.spec : Prop := ∀ tp, Persistent (tpRoot (GF := GF) tp)
def simpleAt_persistent.spec : Prop := ∀ t γ R, Persistent (simpleAt (GF := GF) t γ R)
def keeperAt_persistent.spec : Prop := ∀ tm t, Persistent (keeperAt (GF := GF) tm t)
def permKeysAt_persistent.spec : Prop := ∀ ps ks, Persistent (permKeysAt (GF := GF) ps ks)

/-- The simple provider's once-only right splits off a fresh token for a later index. -/
def simpleFrom_fresh.spec : Prop := ∀ (t : Loc) (n idx : Nat) (p : GoString),
  n < idx → (46#8) ∉ p →
  simpleFrom (GF := GF) t n ⊢ simpleFrom t idx ∗
    simpleFresh t (simpleTok p idx)

def cacheEntry_persistent.spec : Prop := ∀ p a u, Persistent (cacheEntry (GF := GF) p a u)
def userRolesAt_persistent.spec : Prop := ∀ p roles, Persistent (userRolesAt (GF := GF) p roles)
def tpOpen_persistent.spec : Prop := ∀ tp γ R, Persistent (tpOpen (GF := GF) tp γ R)

/-- The read transaction's state is its `txAt`. -/
def rdTx_txAt.spec : Prop := ∀ γa tx j a,
  rdTx (GF := GF) γa tx j a ⊢ txAt tx a ∗ (txAt tx a -∗ rdTx γa tx j a)

/-- `tx.RUnlock()` (4b's `AuthReadTx`): the reader's slots back, as its `threadTok`. -/
def rdTx_RUnlock.spec : Prop := ∀ γa tx j a,
  {{ rdTx (GF := GF) γa tx j a }}
    (App (Val (tx @!! go_etcd_io.etcd.server.v3.auth.AuthReadTx.ty @!! go!"RUnlock")) (Val #()))
  {{ RET #(); threadTok }}

/-! ### The `TokenProvider` bundle (S7) -/

/-- A provider given to a store is opened: its contract, its index right from `0`, and root tokens
if `rt`. -/
def tokenProviderAt_open.spec : Prop := ∀ tp γ R rt,
  tokenProviderAt (GF := GF) tp γ R rt ⊢
    tpOpen tp γ R ∗ tpFrom tp 0 ∗ (if rt then tpRoot tp else iprop(True))

def tpOpen_tpFrom_excl.spec : Prop := ∀ tp n n',
  tpFrom (GF := GF) tp n ∗ tpFrom tp n' ⊢ iprop(False)

/-- `info(ctx, tok, rev)`, once the gate `R` holds: refused, or an `AuthInfo` naming the user the
cluster issued `tok` to. -/
def tp_info.spec : Prop := ∀ (tp ctx : GoInterface) (γ : Cluster) (R : IProp GF) (tok : GoString)
    (rev : w64),
  {{ tpOpen (GF := GF) tp γ R ∗ □ R ∗ Context.ctxOk ctx }}
    (App (App (App (Val (tp @!! go_etcd_io.etcd.server.v3.auth.TokenProvider.ty @!! go!"info"))
      (Val #ctx)) (Val #tok)) (Val #rev))
  {{ (ai : Loc) (ok : Bool), RET (PairV #ai #ok);
      ⌜ok = false⌝ ∨ (⌜ok = true⌝ ∗ ∃ (u : GoString) (rev' : w64), tokenUser γ tok u ∗
        authInfoAt ai DFrac.discard u rev') }}

/-- `assign(ctx, name, rev)` from an `Authenticate` context at a fresh index: a token the cluster
issued to `name`, or an error. -/
def tp_assign.spec : Prop := ∀ (tp ctx : GoInterface) (γ : Cluster) (R : IProp GF) (name : GoString)
    (rev : w64) (n idx : Nat),
  {{ tpOpen (GF := GF) tp γ R ∗ Context.ctxOk ctx ∗ authnCtx γ ctx name idx ∗ tpFrom tp n ∗
      ⌜n < idx⌝ }}
    (App (App (App (Val (tp @!! go_etcd_io.etcd.server.v3.auth.TokenProvider.ty @!! go!"assign"))
      (Val #ctx)) (Val #name)) (Val #rev))
  {{ (tok : GoString) (err : GoInterface), RET (PairV #tok #err); tpFrom tp idx ∗
      (⌜err ≠ GoInterface.nil⌝ ∨ (⌜err = GoInterface.nil⌝ ∗ tokenUser γ tok name)) }}

/-- `assign(ctx, "root", rev)` (`WithRoot`'s) of a provider whose root tokens do not collide. -/
def tp_assignRoot.spec : Prop := ∀ (tp ctx : GoInterface) (γ : Cluster) (R : IProp GF) (rev : w64),
  {{ tpOpen (GF := GF) tp γ R ∗ tpRoot tp ∗ Context.ctxOk ctx }}
    (App (App (App (Val (tp @!! go_etcd_io.etcd.server.v3.auth.TokenProvider.ty @!! go!"assign"))
      (Val #ctx)) (Val #rootUser)) (Val #rev))
  {{ (tok : GoString) (err : GoInterface), RET (PairV #tok #err);
      ⌜err ≠ GoInterface.nil⌝ ∨ (⌜err = GoInterface.nil⌝ ∗ tokenUser γ tok rootUser) }}

def tp_enable.spec : Prop := ∀ (tp : GoInterface) (γ : Cluster) (R : IProp GF),
  {{ tpOpen (GF := GF) tp γ R }}
    (App (Val (tp @!! go_etcd_io.etcd.server.v3.auth.TokenProvider.ty @!! go!"enable")) (Val #()))
  {{ RET #(); True }}

def tp_disable.spec : Prop := ∀ (tp : GoInterface) (γ : Cluster) (R : IProp GF),
  {{ tpOpen (GF := GF) tp γ R }}
    (App (Val (tp @!! go_etcd_io.etcd.server.v3.auth.TokenProvider.ty @!! go!"disable")) (Val #()))
  {{ RET #(); True }}

def tp_invalidateUser.spec : Prop := ∀ (tp : GoInterface) (γ : Cluster) (R : IProp GF) (u : GoString),
  {{ tpOpen (GF := GF) tp γ R }}
    (App (Val (tp @!! go_etcd_io.etcd.server.v3.auth.TokenProvider.ty @!! go!"invalidateUser")) (Val #u))
  {{ RET #(); True }}

def tp_genTokenPrefix.spec : Prop := ∀ (tp : GoInterface) (γ : Cluster) (R : IProp GF),
  {{ tpOpen (GF := GF) tp γ R }}
    (App (Val (tp @!! go_etcd_io.etcd.server.v3.auth.TokenProvider.ty @!! go!"genTokenPrefix")) (Val #()))
  {{ (s : GoString) (err : GoInterface), RET (PairV #s #err); True }}

/-- The simple provider is a provider (no root tokens). -/
def simple_provider.spec : Prop := ∀ (t : Loc) (γ : Cluster) (R : IProp GF),
  simpleAt (GF := GF) t γ R ∗ simpleFrom t 0 ⊢
    tokenProviderAt (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.auth.tokenSimple.ty) #t) γ R false

/-- The no-op provider is a provider of any cluster's tokens (it accepts and assigns none), at any
gate (it has no waiter). -/
def nop_provider.spec : Prop := ∀ (p : Loc) (γ : Cluster) (R : IProp GF),
  ⊢ tokenProviderAt (GF := GF) (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.auth.tokenNop.ty) #p) γ R true

end res

end Auth
end EtcdGrove
end Perennial
