/-
# etcd's backend for the auth store (batch 4a, second pass; lease-auth's request)

As `LeaseBackend.lean` for the lessor: the laws that produce the auth store's backend vocabulary
(`auth/Api.lean`: `Auth.authBackendAt be a`, `Auth.authBeHook be Pre Q`) from 4a's predicates and
4b's `NewAuthBackend` wrapper. Only the server's proofs (2e's `NewServer`, 2d's `applySnapshot`
through `authStore.Recover`) import this module. 4b declined to own the vocabulary; these are
introduction and elimination laws only.

* `authFp`: the auth store's part of the image, the `auth`, `authUsers` and `authRoles` buckets
  (existence, entries, buffer flags). Tracked (the store reads it through read transactions:
  4b's `rdSect` of the shared read transaction).
* `authImg C a` (opaque `Prop`): **the three auth buckets of `C` decode to the auth state `a`**: the
  `auth` bucket's flag and revision (4b's `Schema.authEnabledOf`, `authRevOf`), the users' and
  roles' records (`Schema.recsWf`, 3d's record decodings: users' passwords `a`'s credentials, roles'
  and permissions' lists up to order, users' roles sorted). Opaque until 3d states the record
  decodings (as `StateImage.lean`'s `smRest`, which it is part of: `smRest_auth`).
* `authShare`: the auth store's fixed share of the backend's open token (so that the server gets it
  back whole at a close: `authBackendAt_elim`).

Intended realization of `Auth.authBackendAt (iface abe) a` (3d's, restated here as the laws'
reason): `abe ↦□ authBackend.mk (beIface b) lg`, `isBackend γ b p Pk`, `bktsAre γ`,
`beOpen γ authShare`, `beCur γ authFp C ∗ beVis γ authFp V` agreeing, `authImg C a`, and the schema's
transaction contracts over them (`SchemaTx.lean`'s `beRet`, `btLockIn`/`btUnlock`, `rtSect`, `btRd`,
`btWr`, `rtRd`). Reader slots are not part of it: each read section takes one from the store's own
reader stock (`NewAuthStore`'s premise).

## Laws

`authBackendAt_intro`, `authBackendAt_elim`, `authBeHook_intro`, `smRest_auth`.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.storage.backend.SchemaTx
public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.storage.backend.StateImage
public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.auth.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Backend

open Iris Iris.BI

/-- **The auth store's share of a backend's open token** (named: fixed, so that the server gets it
back whole). -/
def authShare : Qp := (1 : Qp).half.half

section model
variable [GooseExts] [GoGlobalContext]

/-- **The auth store's part of the image**: the `auth`, `authUsers`, `authRoles` buckets. -/
def authFp : Fp :=
  Fp.union (Fp.bucket (Schema.Bkt.name .auth))
    (Fp.union (Fp.bucket (Schema.Bkt.name .authUsers)) (Fp.bucket (Schema.Bkt.name .authRoles)))

/-- **The auth buckets of `C` decode to `a`** (see the header; opaque until 3d states the record
decodings). -/
opaque authImg (C : Image) (a : EtcdModel.AuthState) : Prop

end model

/-- **An image of the state machine's state holds its auth state** (`smRest`'s auth part). -/
def smRest_auth.spec [GooseExts] [GoGlobalContext] : Prop :=
  ∀ (I : Image) (σ : EtcdModel.State), smRest I σ → authImg I σ.auth

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

/-- `abe` as the `AuthBackend` value `NewAuthBackend` returns. -/
def authBeIface (abe : Loc) : GoInterface :=
  interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.authBackend.ty) #abe

/-- **The auth store's backend** (2e's `NewServer`: `schema.NewAuthBackend(lg, be)`, then
`auth.NewAuthStore`; 2d's `applySnapshot`: the new backend's, for `Recover`): from the wrapper,
the backend's buckets (`bktsAre`), the auth share of the open token and the opener's parts of the
three auth buckets, agreeing and holding `a`. -/
def authBackendAt_intro.spec : Prop :=
  ∀ (γ : BeNames) (b : Loc) (p : GoString) (Pk : IProp GF) (abe lg : Loc) (C V : Image)
    (a : EtcdModel.AuthState),
  (abe ↦□ (go_etcd_io.etcd.server.v3.storage.schema.authBackend.mk (beIface b) lg) : IProp GF) ∗
    isBackend γ b p Pk ∗ bktsAre γ ∗ beOpen γ authShare ∗
    beCur γ authFp C ∗ beVis γ authFp V ∗ ⌜Image.agree authFp C V ∧ authImg C a⌝ ⊢
  |={⊤}=> Auth.authBackendAt (authBeIface abe) a

/-- **The auth store's backend given back** (the backend's close; the old backend after
`Recover`): the share and the parts, at the state the store last wrote. -/
def authBackendAt_elim.spec : Prop :=
  ∀ (γ : BeNames) (b : Loc) (p : GoString) (Pk : IProp GF) (abe lg : Loc)
    (a : EtcdModel.AuthState),
  (abe ↦□ (go_etcd_io.etcd.server.v3.storage.schema.authBackend.mk (beIface b) lg) : IProp GF) ∗
    isBackend γ b p Pk ∗ Auth.authBackendAt (authBeIface abe) a ⊢
  |={⊤}=> beOpen γ authShare ∗ ∃ C V : Image,
    beCur γ authFp C ∗ beVis γ authFp V ∗ ⌜Image.agree authFp C V ∧ authImg C a⌝

/-- **The backend's post-lock hook run, for the auth store** (as `leaseHookRun_intro`): a hook run
proved over 4a's contract at every share, with the hook fixed (`beHook` discarded). -/
def authBeHook_intro.spec : Prop :=
  ∀ (γ : BeNames) (b : Loc) (p : GoString) (Pk : IProp GF) (abe lg : Loc) (f : GoFunc)
    (Pre Q : IProp GF),
  (abe ↦□ (go_etcd_io.etcd.server.v3.storage.schema.authBackend.mk (beIface b) lg) : IProp GF) ∗
    isBackend γ b p Pk ∗ beHook γ DFrac.discard f ∗ (∀ q, hookRun γ q Pk f Pre Q) ⊢
  Auth.authBeHook (authBeIface abe) Pre Q

end laws

end Backend
end EtcdGrove
end Perennial
