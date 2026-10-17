/-
`auth.NewAuthStore(lg, be, tp, cost)` (`store.go`): names-only. Lean-first (no Rocq counterpart); the server-construction unit, stage N0 (2026-10-16, D13:
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

/-- `NewAuthStore(lg, be, tp, cost)` on a fresh backend: an auth store, disabled, with its reader
resource `RD`: the request path's contract (`isReqAuth`) and the apply contract with auth off
(`isAuthStore … false`) at any batch-lock invariant and hook. -/
abbrev auth.NewAuthStore.spec : Prop :=
  ∀ (lg : Loc) (ab tp : GoInterface) (cost : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗ ⌜lg ≠ null⌝ }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.auth.NewAuthStore)) (Val #lg))
      (Val #ab)) (Val #tp)) (Val #cost))
  {{ (st : GoInterface), RET #st; ∃ RD : IProp GF, RD ∗ isReqAuth st RD ∗
      □ (∀ (γ : mvcc.StoreNames) (P : IProp GF) (f : val), apply.isAuthStore st γ P f RD false) }}

end spec

end EtcdGrove
end Perennial
