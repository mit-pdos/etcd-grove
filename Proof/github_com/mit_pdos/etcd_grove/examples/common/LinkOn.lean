/-
`common.Serve`'s auth-on spec (`Serve.specOn`), linked: `Link.lean` (generated) links each
function by its one `.spec`, and `Serve.specOn` is the second spec of `Serve` until the merge folds
it into `Serve.spec`. Its callees' results are `Link.lean`'s, as `wp_Serve`'s. authkv's `Link.lean`
takes it as a term (an `=` callee, `etc/gen-link.py`'s `EXTRA_IMPORTS`). Lean-first (no Rocq
counterpart).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.common.Link

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace common

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.common

section links
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.common.Assumptions]

/-- **`Serve` with auth on** (`Serve.wp_proofOn`), over `wp_Serve`'s callees. -/
theorem wp_ServeOn :
    EtcdGrove.common.Serve.specOn (GF := GF) (hG := hG) :=
  EtcdGrove.common.Serve.wp_proofOn grpc.wp_KeepaliveEnforcementPolicy v3rpc.wp_Server net.wp_Listen
    grpc.Server.wp_Serve

end links

end common
end EtcdGrove
end Perennial
