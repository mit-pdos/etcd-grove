/- Lean-first (no Rocq counterpart).

`x.genEnd()` (`examples/mvccfull/mvccfull.go`): a range end, owned by the caller: `nil` (one key),
an empty slice (from the key on), `"d"` (past every key) or one of the run's keys (`genKey`). The
spec does not say which of the first two is `nil` (whether Goose's empty composite literal is a
`nil` slice is the model's; every caller handles both through `decide (end = slice.nil)`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccfull.Readers

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccfull

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.mvccfull

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccfull.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- See the file header. -/
abbrev runner.genEnd.spec : Prop :=
  ∀ (x : Loc) (ks : List GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.mvccfull ∗
      runnerKeys x ks }}
    (App (x @!! go.GoType.PointerType runner.ty @!! go!"genEnd") (Val #()))
  {{ (s : GoSlice), RET #s; ∃ e : GoString, s ↦* e ∗ ⌜e = [] ∨ e = go!"d" ∨ e ∈ ks⌝ }}

end spec

end mvccfull
end EtcdGrove
end Perennial
