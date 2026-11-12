/- Lean-first (no Rocq counterpart).

`x.genKey()` (`examples/mvccfull/mvccfull.go`): a fresh byte slice of one of the run's keys
(`x.keys[choose(len(x.keys))]`, converted). The keys are not empty (`runnerKeys`), so the index is
in range. Used by the readers (`genRange`) and the writer (puts, deletes, txns).
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
abbrev runner.genKey.spec : Prop :=
  ∀ (x : Loc) (ks : List GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.mvccfull ∗
      runnerKeys x ks }}
    (App (x @!! go.GoType.PointerType runner.ty @!! go!"genKey") (Val #()))
  {{ (s : GoSlice), RET #s; ∃ k : GoString, s ↦* k ∗ ⌜k ∈ ks⌝ }}

end spec

end mvccfull
end EtcdGrove
end Perennial
