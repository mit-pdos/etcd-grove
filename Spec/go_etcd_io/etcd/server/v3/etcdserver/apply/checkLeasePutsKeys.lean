/-
`apply.checkLeasePutsKeys` (auth.go). Lean-first (no Rocq counterpart); the vocabulary is
`Proof/go_etcd_io/etcd/server/v3/etcdserver/apply/Chain.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Chain

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.apply go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-- **`checkLeasePutsKeys(as, ai, l)`**: `nil` for an admin (`IsAdminPermitted`); else `IsPutPermitted` of each of the lease's keys (`l.Keys()`): the first error, or `nil`; the `AuthInfo` kept, nothing written. -/
abbrev apply.checkLeasePutsKeys.spec : Prop :=
  ∀ (st : GoInterface) (P : IProp GF) (f : val) (ai : Loc)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (dq : DFrac) (l : Loc) (id : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗ apply.isAuthStore st P f ∗ ai ↦{dq} info ∗ apply.leaseIs l id }}
    (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.apply.checkLeasePutsKeys))
      (Val #st)) (Val #ai)) (Val #l))
  {{ (err : GoInterface), RET #err; ai ↦{dq} info ∗ applyErrIs err }}

end spec

end EtcdGrove
end Perennial
