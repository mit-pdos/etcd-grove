/-
`v3compactor.New(lg, mode, retention, rg, c)` (`compactor.go`): names-only. Lean-first (no Rocq counterpart); the server-construction unit, stage N0 (2026-10-16, D13:
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

/-- `New(lg, mode, retention, rg, c)`: a compactor (`compactorOk`, not nil, whose `Run` returns),
or an error (an unknown mode). -/
abbrev v3compactor.New.spec : Prop :=
  ∀ (lg : Loc) (mode : GoString) (ret : time.Duration) (rg c : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor }}
    (App (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.v3compactor.New))
      (Val #lg)) (Val #mode)) (Val #ret)) (Val #rg)) (Val #c))
  {{ (cp err : GoInterface), RET (PairV #cp #err);
      ⌜err ≠ GoInterface.nil⌝ ∨ ⌜err = GoInterface.nil ∧ cp ≠ GoInterface.nil⌝ ∗ compactorOk cp ∗
        compactorRunOk cp }}

end spec

end EtcdGrove
end Perennial
