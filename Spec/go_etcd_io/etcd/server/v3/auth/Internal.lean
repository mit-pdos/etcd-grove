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
  the batch transaction's `Unlock`.
* `cacheEntry p a u` (persistent): `p` is a `*unifiedRangePermissions` holding `u`'s merged read and
  write permissions at `a` (3f's interval trees over bytes-affine keys).
* `cacheOwn st` (exclusive): the right to replace the store's cache map (the writer's, inside
  `wrRec`; `NewAuthStore`'s before the invariants exist).
* `userRolesAt p roles` (persistent): `p` is a `*authpb.User` whose `Roles` slice holds `roles`,
  read-only.
* `tpOpen tp γ` (persistent): the provider's contract opened (`tokenProviderAt` given to a store).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.auth.Api

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

opaque txAt (tx : GoInterface) (a : AuthState) : IProp GF := iprop(True)
opaque rdTx (γa : AuthNames) (tx : GoInterface) (j : Nat) (a : AuthState) : IProp GF := iprop(True)
opaque wrStep (γa : AuthNames) (i : Nat) (a a' : AuthState) : IProp GF := iprop(True)
opaque wrRec (γa : AuthNames) (i : Nat) (a' : AuthState) : IProp GF := iprop(True)
opaque cacheEntry (p : Loc) (a : AuthState) (u : GoString) : IProp GF := iprop(True)
opaque cacheOwn (st : Loc) : IProp GF := iprop(True)
opaque userRolesAt (p : Loc) (roles : List GoString) : IProp GF := iprop(True)
opaque tpOpen (tp : GoInterface) (γ : Cluster) : IProp GF := iprop(True)

def cacheEntry_persistent.spec : Prop := ∀ p a u, Persistent (cacheEntry (GF := GF) p a u)
def userRolesAt_persistent.spec : Prop := ∀ p roles, Persistent (userRolesAt (GF := GF) p roles)
def tpOpen_persistent.spec : Prop := ∀ tp γ, Persistent (tpOpen (GF := GF) tp γ)

/-- The read transaction's state is its `txAt`. -/
def rdTx_txAt.spec : Prop := ∀ γa tx j a,
  rdTx (GF := GF) γa tx j a ⊢ txAt tx a ∗ (txAt tx a -∗ rdTx γa tx j a)

/-- `tx.RUnlock()` (4b's `AuthReadTx`): the reader's slots back, as its `threadTok`. -/
def rdTx_RUnlock.spec : Prop := ∀ γa tx j a,
  {{ rdTx (GF := GF) γa tx j a }}
    (App (Val (tx @!! go_etcd_io.etcd.server.v3.auth.AuthReadTx.ty @!! go!"RUnlock")) (Val #()))
  {{ RET #(); threadTok }}

end res

end Auth
end EtcdGrove
end Perennial
