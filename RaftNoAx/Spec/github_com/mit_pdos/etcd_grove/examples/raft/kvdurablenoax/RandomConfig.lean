-- The copy for the part `RaftNoAx/` of `Spec/github_com/mit_pdos/etcd_grove/examples/raft/kvdurable/RandomConfig.lean` (etc/copy-part.py; rerun it, do not edit).
/- kvreconf's (the same Go text), ported. Lean-first (no Rocq counterpart).

`RandomConfig()` (check.go): `Main`'s test configuration: random options a cluster may run with
(`RandomOptions`, `kdOptsOk`), 4 clients of 100 operations each, and one to three proposers of
configuration changes (the pauses, the crashes' among them, are not specified: nothing depends on
them).
-/
module

public import RaftNoAx.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvdurablenoax.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvdurable

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvdurablenoax.Assumptions]

/-- See the file header. -/
abbrev RandomConfig.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvdurablenoax }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.kvdurablenoax.RandomConfig)) (Val #()))
  {{ (cfg : github_com.mit_pdos.etcd_grove.examples.raft.kvdurablenoax.Config), RET #cfg;
      ⌜kdOptsOk cfg.Options' ∧ cfg.Options'.MaxReplicas' = W64 9 ∧ cfg.Clients' = W64 4 ∧ cfg.Ops' = W64 100 ∧
        1 ≤ sint.Z cfg.Proposers' ∧ sint.Z cfg.Proposers' ≤ 3⌝ }}

end spec

end raft_kvdurable
end EtcdGrove
end Perennial
