/- Lean-first (no Rocq counterpart).

`x.checkHook(m, i)` (`examples/mvccfull/mvccfull.go`): returns when the member's hook saved the
index `i` (`m.saved`, the writer's counter: only the member's hook, under the batch lock of the
writer's own write, stores it).
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
abbrev runner.checkHook.spec : Prop :=
  ∀ (x mp : Loc) (i : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.mvccfull ∗ sync.atomic.ownInt64 (mF go!"saved" mp) (DFrac.own 1) i }}
    (App (App (x @!! go.GoType.PointerType runner.ty @!! go!"checkHook") (Val #mp)) (Val #i))
  {{ RET #(); sync.atomic.ownInt64 (mF go!"saved" mp) (DFrac.own 1) i }}

end spec

end mvccfull
end EtcdGrove
end Perennial
