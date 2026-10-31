/-
`apply.checkLeasePuts` (auth.go). Lean-first (no Rocq counterpart); the vocabulary is
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-- **`checkLeasePuts(as, ai, lessor, id)`**: the lessor's `Lookup(id)`; for a lease, `checkLeasePutsKeys`: its error, or `nil`; the `AuthInfo` kept, nothing written. With the lease owner's view (`U = some (L, I)`, its resource lent and given back), a `nil` answer gives the class of `id`'s keys at `I` (`leaseKeysClass`; a lease the lessor does not have holds no key). -/
abbrev apply.checkLeasePuts.spec : Prop :=
  ∀ (st le : GoInterface) (γ : mvcc.StoreNames) (P : IProp GF) (f : val) (RD : IProp GF) (on : auth.AuthMode) (RW : IProp GF) (ai : Loc)
    (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (dq : DFrac) (id : w64) (U : apply.LeaseView),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗ apply.isAuthStore st γ P f RD on RW ∗ apply.isApplyLessorAny le γ P f RW ∗ ai ↦{dq} info ∗ RD ∗
      apply.lessorView γ.leases U }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.apply.checkLeasePuts))
      (Val #st)) (Val #ai)) (Val #le)) (Val #id))
  {{ (err : GoInterface), RET #err; ai ↦{dq} info ∗ RD ∗ apply.lessorView γ.leases U ∗
      authApplyErrIs err ∗ ⌜on.isOn = false → err = GoInterface.nil⌝ ∗
      (∀ _ : err = GoInterface.nil, apply.viewClass U (fun I => apply.leaseKeysClass on info I id)) }}

end spec

end EtcdGrove
end Perennial
