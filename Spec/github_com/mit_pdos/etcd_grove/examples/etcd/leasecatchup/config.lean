/-
`config()` (`examples/etcd/leasecatchup/leasecatchup.go`; lease-mono3, 2026-11-06,
`notes/lease-mono3-plan.md`): the cluster's configuration. Lean-first (no Rocq counterpart).

**The triple:** from the package's `isPkgInit`, it returns `clusterCfg`
(`Proof/github_com/mit_pdos/etcd_grove/examples/etcd/leasecatchup/Defs.lean`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.leasecatchup.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_leasecatchup

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.leasecatchup.Assumptions]

/-- See the file header. -/
abbrev config.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.leasecatchup }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.leasecatchup.config)) (Val #()))
  {{ RET #clusterCfg; True }}

end spec

end etcd_leasecatchup
end EtcdGrove
end Perennial
