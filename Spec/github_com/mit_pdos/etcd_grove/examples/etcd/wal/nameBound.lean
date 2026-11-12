/- Lean-first (no Rocq counterpart).

`nameBound(h, a)` (`examples/etcd/wal/ref.go`): the last position at which a WAL file named at most
`a` can start (`tNameBound`; `walNameBound … false`, `tNameBound_eq`).
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
abbrev nameBound.spec : Prop :=
  ∀ (s : GoSlice) (h : List TOp) (a : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.wal ∗ opsRep s h }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.wal.nameBound)) (Val #s)) (Val #a))
  {{ RET #(tNameBound h a); True }}

end spec

end etcd_wal
end EtcdGrove
end Perennial
