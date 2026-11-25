/- Lean-first (no Rocq counterpart).

`(*server).Fail(ctx, m)`: for a decoded request at `v` (`pbStringValueT`'s `recv`) and `Fail`'s spec
at it (`failSpec`: `Ψe v`, `Svc.lean`), it fails: a non-nil error whose description is `v`
(`errors.New(v)` for a `v` starting with `p`, `status.Error(codes.NotFound, v)` otherwise), with
`Ψe v` (`handlerErrOut`), one grpc's server takes (`srvErrOk`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver.ServerDefs

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

/-- See the file header. -/
abbrev server.Fail.spec : Prop :=
  ∀ (s : Loc) (ctx : GoInterfaceOk) (r : Loc) (v : GoString) (md : GrpcMd)
    (Φ : GoString → IProp GF) (Ψe : GoString → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver ∗
      (pbStringValueT (GF := GF)).toProtoMsg.recv r v ∗ failSpec md v Φ Ψe }}
    (App (App (Val (s @!! go.GoType.PointerType server.ty @!! go!"Fail"))
      (Val #(GoInterface.ok ctx))) (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      ⌜err ≠ GoInterface.nil⌝ ∗ handlerErrOut Ψe err ∗ go_etcd_io.etcd.cache.v3.srvErrOk err }}

end spec

end github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver
end Perennial
