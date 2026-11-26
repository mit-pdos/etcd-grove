/- Lean-first (no Rocq counterpart).

`(*server).ServerStream(m, st)`: for the first request `m` received at `v` (the receiver's token at
`[v]`), on the wrapped server end of a stream of `StringValue`s, for a response content `Dn` that
holds of each byte of the first request (`ssDn`): sends `v` one byte per message; returns an error
grpc's server takes (`srvErrOk`).
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
abbrev server.ServerStream.spec : Prop :=
  ∀ (s r : Loc) (v : GoString) (st : GoInterface) (γ : StreamNames) (Dn : Nat → GoString → IProp GF)
    (ci : GoInterfaceOk) (cd : _root_.Perennial.context.ContextDesc (IProp GF)) (md : GrpcMd),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver ∗
      stringValueSend r v ∗ srvStreamIs st γ strmMsg strmMsg ssUp Dn ci cd ∗
      (□ ∀ j m, ssDn md γ j m -∗ Dn j m) ∗
      srvRecvTok (Req := strmMsg (GF := GF)) γ [v] ∗ srvSendTok (Rep := strmMsg (GF := GF)) γ [] }}
    (App (App (Val (s @!! go.GoType.PointerType server.ty @!! go!"ServerStream")) (Val #r)) (Val #st))
  {{ (err : GoInterface), RET #err; go_etcd_io.etcd.cache.v3.srvErrOk err }}

end spec

end github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver
end Perennial
