/-
`grpc.StaticMethod()` (grpc's `rpc_util.go`): the call option the generated stubs prepend
(`rpc_grpc.pb.go`), for unit C1 (the client's KV stub). It was the trust boundary (an axiom) while
grpc's function was names only; proved over the real body since 2026-11-20 (prove-grpcsmall),
`Proof/google_golang_org/grpc/StaticMethod.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvKVConn

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `grpc.StaticMethod()` returns a `StaticMethodCallOption{}` as a `CallOption` (`callOptOk`:
an option that holds no pointer). -/
abbrev grpc.StaticMethod.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.grpc }}
    (App (Val (@! google_golang_org.grpc.StaticMethod)) (Val #()))
  {{ (v : GoInterface), RET #v; callOptOk v ∗
      -- (2026-10-21, D29) a `StaticMethodCallOption`, a scalar option (no retry option)
      ⌜scalarOpts [v]⌝ }}

end spec

end EtcdGrove
end Perennial
