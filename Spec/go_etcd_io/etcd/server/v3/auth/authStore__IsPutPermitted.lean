/-
## `(*authStore).IsPutPermitted(authInfo, key)`

**Users.** `checkPutAuth` (`apply/auth.go:74`) and `checkLeasePutsKeys` (`apply/auth.go:215`), the writer at apply time (3a); the lease checks `checkLeaseRenew` (`v3_server.go:595`, 2c), a reader. Snippets: `examples/specreq/auth/check.go` (`ReqCheckPass`, `ReqWriterCheck`).

**Proof sketch.** `isOpPermitted(authInfo.Username, authInfo.Revision, key, nil, WRITE)` (its spec): the
`AuthInfo`'s two fields read (fraction `dq`), then the flag (`IsAuthEnabled`, at `jf`), the revision
(`Revision`), the user under `lockedReadTx` (the backend view, at `jx`), its root role
(`hasRootRole`), the cache (`isRangeOpPermitted`, at `jc`); each view at or after the caller's
`authLb γa i0`.

**Changes.** The old spec (`permVerdict M info k e`: one recorded state in mode `on`, nothing in
mode `off`) restated over W0's state, one statement for every mode: the three views' states are
named, so a **pass** is `State.permits` at one recorded state (the flag's `enabled = false`, the
backend's root role, or the cache's cover: `checkOk`), and so a reached one (`authAt_reached`): what
2b's watch create and 2c's reads need. A **denial** names the three views (`checkDenied`): at one
state when they coincide (the writer's check: `authCur_at`, `authAt_le`), not in general (the
header of `Api.lean`). The key-length premise is the old one (`adt.NewBytesAffine*`'s `make` of
`len + 1`).

**Margin.** An inverted range may be refused although the model's `covers` holds of it vacuously
(`rngInverted`); `ErrAuthOldRevision`'s state (the revision read) is not named; the order of the
views (the backend and the cache are at or after the flag: the flag moves last in `AuthEnable`,
`AuthDisable` and `Recover`, the cache before the backend's publication) is not stated, as no
caller uses it.
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

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

/-- **`as.IsPutPermitted(ai, key)`**: a write of the key `key` by `ai`'s user, checked
(`checkPost`): `nil` only at a recorded state that permits it. -/
def authStore.IsPutPermitted.spec : Prop :=
  ∀ (st ai : Loc) (γ : Cluster) (γa : AuthNames) (i0 : Nat) (dq : DFrac) (u : GoString)
    (rev : w64) (key : GoSlice) (dk : DFrac) (k : List w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ authStoreAt st γ γa ∗ authLb γa i0 ∗ threadTok ∗ authInfoAt ai dq u rev ∗ key ↦*{dk} k ∗
      ⌜sint.Z key.len < 2 ^ 63 - 1⌝ }}
    (App (App (Val (st @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.auth.authStore.ty @!! go!"IsPutPermitted")) (Val #ai)) (Val #key))
  {{ (err : GoInterface), RET #err; threadTok ∗ authInfoAt ai dq u rev ∗ key ↦*{dk} k ∗
      checkPost γa i0 u rev .write { key := k, rangeEnd := [] } err }}

end spec
end Auth
end EtcdGrove
end Perennial
