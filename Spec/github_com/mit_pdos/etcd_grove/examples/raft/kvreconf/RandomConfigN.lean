/- Lean-first (no Rocq counterpart).

`RandomConfigN(k)` (check.go; 2026-11-16, kvraftN): `RandomConfig()` on `k` voters, with up to `k + 4`
replicas (`RandomOptionsN`), for `1 ≤ k < 2^59`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvreconf.DefsCluster

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvreconf

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvreconf.Assumptions]

/-- See the file header. -/
abbrev RandomConfigN.spec : Prop :=
  ∀ (k : w64), 1 ≤ uint.Z k → uint.Z k < 2 ^ 59 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvreconf }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.kvreconf.RandomConfigN)) (Val #k))
  {{ (cfg : github_com.mit_pdos.etcd_grove.examples.raft.kvreconf.Config), RET #cfg;
      ⌜OptsOk cfg.Options' ∧ cfg.Options'.Voters' = k ∧ cfg.Clients' = W64 4 ∧ cfg.Ops' = W64 100 ∧
        1 ≤ sint.Z cfg.Proposers' ∧ sint.Z cfg.Proposers' ≤ 3⌝ }}

end spec

end raft_kvreconf
end EtcdGrove
end Perennial
