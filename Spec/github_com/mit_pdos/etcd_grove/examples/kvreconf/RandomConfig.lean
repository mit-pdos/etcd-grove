/- Lean-first (no Rocq counterpart).

`RandomConfig()` (check.go): `Main`'s test configuration: random options a cluster may run with
(`RandomOptions`, `OptsOk`), 4 clients of 100 operations each, and one to three proposers of
configuration changes (the pauses are not specified: nothing depends on them).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.DefsCluster

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvreconf

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvreconf.Assumptions]

/-- See the file header. -/
abbrev RandomConfig.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kvreconf }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.kvreconf.RandomConfig)) (Val #()))
  {{ (cfg : github_com.mit_pdos.etcd_grove.examples.kvreconf.Config), RET #cfg;
      ⌜OptsOk cfg.Options' ∧ cfg.Clients' = W64 4 ∧ cfg.Ops' = W64 100 ∧
        1 ≤ sint.Z cfg.Proposers' ∧ sint.Z cfg.Proposers' ≤ 3⌝ }}

end spec

end kvreconf
end EtcdGrove
end Perennial
