/-
`NewClient(cfg, lg)` (`examples/lib/cluster3/cluster3.go`; until 2026-11-05 inline in package
`partition`'s `startCluster`, at linkv3p's bridges): a client of the cluster of configuration `cfg`
through every member's bridge (an attempt goes to one of them, failover, D27): the examples' client
constructor `etcdstart.NewClients` of the three bridge addresses. Lean-first (no Rocq counterpart).

**The triple:** from the package's `isPkgInit`, at a logger `lg` (not null) and a configuration
meeting `cfgOk` (its bridge addresses plain `host:port`s, `clientv3.New`'s premise), `NewClient(cfg,
lg)` returns either a client `clientv3.New`'s over the three bridges (`isNewClient`) at the watch
environment `V`, the caller's choice (a client of the started cluster takes `watchEnv cfg R₁ R₂ R₃
γr pfx` of the members' watch servers, `Defs.lean`; one that never watches needs none of its facts),
with its tokens, or a non-nil error and a null client. It needs nothing of the cluster: the client
dials lazily.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cluster3

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Assumptions]

/-- See the file header. -/
abbrev NewClient.spec : Prop :=
  ∀ (cfg : github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Config) (lg : Loc)
    (V : client.WEnv GF),
  cfgOk cfg → threadBound GF ≤ 2 ^ 31 → lg ≠ null →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.cluster3 }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.lib.cluster3.NewClient)) (Val #cfg))
      (Val #lg))
  {{ (cl : Loc) (err : GoInterface), RET (PairV #cl #err);
      (⌜err = GoInterface.nil⌝ ∗ isNewClient cl (bridges cfg) V ∗
        clientTokAt cl (bridges cfg) (fun _ => iprop(False))) ∨
      ⌜err ≠ GoInterface.nil ∧ cl = null⌝ }}

end spec

end cluster3
end EtcdGrove
end Perennial
