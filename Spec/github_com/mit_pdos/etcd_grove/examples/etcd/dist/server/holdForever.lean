/- Lean-first (no Rocq counterpart).

`server.holdForever()` (`examples/etcd/dist/server`): it never returns (`for { time.Sleep(time.Hour) }`).
-/
module

public import GeneratedProof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.server

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
abbrev holdForever.spec : Prop :=
  {{ (True : IProp GF) }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.dist.server.holdForever)) (Val #()))
  {{ RET #(); False }}

end spec

end server
end etcd_dist
end EtcdGrove
end Perennial

end
