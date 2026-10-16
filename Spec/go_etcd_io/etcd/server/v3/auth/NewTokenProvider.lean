/-
`auth.NewTokenProvider(lg, opts, indexWaiter, ttl)` (`store.go`): names-only. Lean-first (no Rocq counterpart); the server-construction unit, stage N0 (2026-10-16, D13:
`notes/decisions.md`), for `NewServer`.
Pending (`?` in `etc/link-lean-first-server.txt`): a hypothesis of `NewServer`'s linked result
until unit N1 settles it (then an axiom at the trust boundary).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvBoot

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

/-- `NewTokenProvider(lg, opts, iw, ttl)`: a token provider, or an error (an invalid `opts`); the
index waiter `iw` is an opaque value (the provider calls it later, outside the model). -/
abbrev auth.NewTokenProvider.spec : Prop :=
  ∀ (lg : Loc) (opts : GoString) (iw : GoFunc) (ttl : time.Duration),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ ⌜lg ≠ null⌝ }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.auth.NewTokenProvider)) (Val #lg))
      (Val #opts)) (Val #iw)) (Val #ttl))
  {{ (tp err : GoInterface), RET (PairV #tp #err); True }}

end spec

end EtcdGrove
end Perennial
