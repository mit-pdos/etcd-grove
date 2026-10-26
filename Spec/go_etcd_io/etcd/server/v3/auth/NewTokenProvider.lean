/-
`auth.NewTokenProvider(lg, opts, indexWaiter, ttl)` (`store.go`). Lean-first (no Rocq counterpart);
the server-construction unit, stage N0 (2026-10-16, D13: `notes/decisions.md`), for `NewServer`.
Settled at unit N1 (2026-10-17) as an axiom at the trust boundary; proved since the auth plan's E2g
(2026-10-25, `Proof/go_etcd_io/etcd/server/v3/auth/NewTokenProvider.lean`): `decomposeOpts`, the
simple and no-op providers' constructors proved, the JWT provider's an axiom
(`newTokenProviderJWT`), and the simple provider's facts added to the post.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvBoot
public import Proof.go_etcd_io.etcd.server.v3.auth.TokenSimpleAdmin

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `NewTokenProvider(lg, opts, iw, ttl)`: a token provider, or an error (an invalid `opts`): on
success the provider is not nil (`*tokenSimple`, `*tokenJWT`, `*tokenNop`: a typed pointer in the
interface). For the options `"simple"` and a positive TTL (2026-10-25, the auth plan's E2g) the
provider is the simple one, with `newTokenProviderSimple`'s facts: its index waiter `iw`
(read-only; the provider's `info` calls it, whose contract, `simpleWaitOk`, its caller states) and,
under fresh names, `simpleOk`, `simpleAdmin` and the rights' authority, from which
`tokenSimple_okA` gives the token provider's contract. No path panics (`decomposeOpts`'s
`strings.Split` has a first field; the JWT constructor returns: its axiom). -/
abbrev auth.NewTokenProvider.spec : Prop :=
  ∀ (lg : Loc) (opts : GoString) (iw : GoFunc) (ttl : time.Duration),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ ⌜lg ≠ null⌝ }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.auth.NewTokenProvider)) (Val #lg))
      (Val #opts)) (Val #iw)) (Val #ttl))
  {{ (tp err : GoInterface), RET (PairV #tp #err);
      ⌜err = GoInterface.nil → tp ≠ GoInterface.nil⌝ ∗
      (⌜opts ≠ go!"simple" ∨ sint.Z ttl ≤ 0⌝ ∨
        ∃ (p : Loc) (γt γf : GName), ⌜err = GoInterface.nil ∧
          tp = interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.auth.tokenSimple.ty) #p⌝ ∗
          auth.tsF go!"indexWaiter" p ↦□ iw ∗ auth.simpleOk p γt γf ∗ auth.simpleAdmin p ∗
          ghostMapAuth γf 1 (∅ : GMap GoString Unit)) }}

end spec

end EtcdGrove
end Perennial
