/- Lean-first (no Rocq counterpart).

`server.proxyEnvSet()` (`examples/etcd/dist/server`): whether one of the four proxy variables net/http reads
is nonempty; when it returns `false`, the process has none set (`noProxyEnv`, `S5Interim.lean`, from
`os.Getenv.specEnv`: the value read is the process's for the run).
-/
module

public import GeneratedProof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.server
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.S5Interim

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist
namespace server

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.server.Assumptions]

/-- See the file header. -/
abbrev proxyEnvSet.spec : Prop :=
  {{ (True : IProp GF) }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.dist.server.proxyEnvSet)) (Val #()))
  {{ (b : Bool), RET #b; if b then iprop(True) else noProxyEnv (hG := hG) }}

end spec

end server
end etcd_dist
end EtcdGrove
end Perennial

end
