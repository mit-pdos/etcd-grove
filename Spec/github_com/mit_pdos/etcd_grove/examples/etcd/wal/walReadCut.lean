/- Lean-first (no Rocq counterpart).

`walReadCut(h, k)` (`examples/etcd/wal/ref.go`): the spec's relaxed reader (`tReadCut`): the whole
history (`k = 0`), or the read from the purged prefix `k ≤ |h|`; for a well-formed history.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.Rep

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_wal

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.etcd.wal

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.wal.Assumptions]

/-- See the file header. -/
abbrev walReadCut.spec : Prop :=
  ∀ (s : GoSlice) (h : List TOp) (k : w64),
  tHistWf h → uint.nat k ≤ h.length →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.wal ∗ opsRep s h }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.wal.walReadCut)) (Val #s)) (Val #k))
  {{ (v : contents) (ok : Bool), RET (PairV #v #ok); readRes (tReadCut h k) v ok }}

end spec

end etcd_wal
end EtcdGrove
end Perennial
