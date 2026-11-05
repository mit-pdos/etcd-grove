/-
`config()` (`examples/etcd/partition/linkv3p.go`, 2026-11-05): the cluster's configuration, a
`cluster3.Config` literal: linkv3p's token, member names, addresses and snapshot settings. Lean-first
(no Rocq counterpart).

**The triple:** from the package's `isPkgInit`, `config()` returns `clusterCfg` (`Defs.lean`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.partition.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_partition

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.partition.Assumptions]

/-- See the file header. -/
abbrev config.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.partition }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.partition.config)) (Val #()))
  {{ RET #clusterCfg; True }}

end spec

end etcd_partition
end EtcdGrove
end Perennial
