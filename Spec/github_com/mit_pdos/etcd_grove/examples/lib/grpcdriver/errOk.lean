/- Lean-first (no Rocq counterpart).

`errOk(err)`: `true` of an error that is a gRPC status (it has grpc's `GRPCStatus`) or `io.EOF`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.PlainInvoke

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI EtcdGrove

namespace github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]
variable [pkg_wr : google_golang_org.protobuf.types.known.wrapperspb.Assumptions]

/-- See the file header. -/
abbrev errOk.spec : Prop :=
  ∀ (err : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver ∗
      go_etcd_io.etcd.cache.v3.statusErrOk err ∗
      (⌜go_etcd_io.etcd.cache.v3.hasGRPCStatus err⌝ ∨ eofIs err) }}
    (App (Val (@! errOk)) (Val #err))
  {{ RET #true; True }}

end spec

end github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver
end Perennial
