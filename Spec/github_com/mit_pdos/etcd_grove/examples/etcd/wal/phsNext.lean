/- Lean-first (no Rocq counterpart).

`phsNext(p, h)` (`examples/etcd/wal/ref.go`): the hard state after a `Save` of `h` (`tPhsNext`: an
empty one leaves `p`).
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
abbrev phsNext.spec : Prop :=
  ∀ (p h : THs),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.wal }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.wal.phsNext)) (Val #p)) (Val #h))
  {{ RET #(tPhsNext p h); True }}

end spec

end etcd_wal
end EtcdGrove
end Perennial
