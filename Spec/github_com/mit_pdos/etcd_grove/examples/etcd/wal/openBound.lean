/- Lean-first (no Rocq counterpart).

`openBound(imgs, a)` (`examples/etcd/wal/ref.go`): the largest `nameBound` at `a` of the images
`imgs` (`tOpenBound`).
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
abbrev openBound.spec : Prop :=
  ∀ (s : GoSlice) (imgs : List (List TOp)) (a : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.wal ∗ imgsRep s imgs }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.wal.openBound)) (Val #s)) (Val #a))
  {{ RET #(tOpenBound imgs a); True }}

end spec

end etcd_wal
end EtcdGrove
end Perennial
