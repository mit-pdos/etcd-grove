/- Lean-first (no Rocq counterpart).

`x.newVal()` (`examples/mvccfull/mvccfull.go`): a new value (`"v"`, the incremented count, a
padding of up to `MaxVal` bytes); the count incremented (below `2 ^ 63 - 1`: at most three values per
operation). The model takes the value as the op records it, so the spec says nothing of its text.
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
abbrev runner.newVal.spec : Prop :=
  ∀ (x : Loc) (cfg : Config) (n : w64),
  0 ≤ sint.Z n → sint.Z n + 1 < 2 ^ 63 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.mvccfull ∗ rF go!"cfg" x ↦□ cfg ∗ rF go!"vals" x ↦ n }}
    (App (x @!! go.GoType.PointerType runner.ty @!! go!"newVal") (Val #()))
  {{ (v : GoString), RET #v; rF go!"vals" x ↦ (n + W64 1) }}

end spec

end mvccfull
end EtcdGrove
end Perennial
