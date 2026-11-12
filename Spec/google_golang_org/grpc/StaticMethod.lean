/-
`grpc.StaticMethod()` (grpc, names only): the call option the generated stubs prepend
(`rpc_grpc.pb.go`). The trust boundary (an axiom, `Proof/google_golang_org/grpc/
StaticMethod.lean`), for unit C1 (the client's KV stub). Lean-first (no Rocq counterpart).
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
