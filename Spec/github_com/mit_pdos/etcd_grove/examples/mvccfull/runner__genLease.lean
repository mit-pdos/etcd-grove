/- Lean-first (no Rocq counterpart).

`x.genLease(m)` (`examples/mvccfull/mvccfull.go`): no lease (`0`) half the time or when the
member has no live lease, else one of its live leases `L` (`m.leases`, read).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.Writer

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.mvccfull mvcc mvcc.api

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- See the file header. -/
abbrev runner.genLease.spec : Prop :=
  ∀ (x mp : Loc) (sl : GoSlice) (L : List w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.mvccfull ∗ mF go!"leases" mp ↦ sl ∗ sl ↦* L }}
    (App (x @!! go.GoType.PointerType runner.ty @!! go!"genLease") (Val #mp))
  {{ (l : w64), RET #l; mF go!"leases" mp ↦ sl ∗ sl ↦* L ∗ ⌜l = W64 0 ∨ l ∈ L⌝ }}

end spec

end mvccfull
end EtcdGrove
end Perennial
