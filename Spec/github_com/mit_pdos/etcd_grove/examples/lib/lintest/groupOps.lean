/- Lean-first (no Rocq counterpart).

`groupOps(id, clients, ops, ops2)` (lintest.go; 2026-11-08, k8s 7f): the number of operations
`RunLin2`'s client `id` runs, `ops` in the first group (`id < clients`) and `ops2` in the second.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.lintest.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace lintest

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lib.lintest.Assumptions]

/-- See the file header. -/
abbrev groupOps.spec : Prop :=
  ∀ (id clients ops ops2 : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.lintest }}
    (App (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.lib.lintest.groupOps))
      (Val #id)) (Val #clients)) (Val #ops)) (Val #ops2))
  {{ RET #(if sint.Z id < sint.Z clients then ops else ops2); True }}

end spec

end lintest
end EtcdGrove
end Perennial
