/- Lean-first (no Rocq counterpart).

`lastIdx(h)` (`examples/etcd/wal/ref.go`): the larger of the last entry record's index and the
highest snapshot record's index of `h` (`tLastIdx`; `walLastIdx`, `tLastIdx_abs`).
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
abbrev lastIdx.spec : Prop :=
  ∀ (s : GoSlice) (h : List TOp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.wal ∗ opsRep s h }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.wal.lastIdx)) (Val #s))
  {{ RET #(tLastIdx h); True }}

end spec

end etcd_wal
end EtcdGrove
end Perennial
