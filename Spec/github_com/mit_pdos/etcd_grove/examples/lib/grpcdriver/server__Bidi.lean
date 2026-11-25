/- Lean-first (no Rocq counterpart).

`(*server).Bidi(st)`: on the wrapped server end of a stream of `StringValue`s with `Bidi`'s requests
(`biUp`), for a response content `Dn` that holds of each echoed request (`biDn`: the `j`th response
is the `j`th request), both tokens at `[]`: sends back each request it receives, in order; returns
an error grpc's server takes (`srvErrOk`).
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
abbrev server.Bidi.spec : Prop :=
  ∀ (s : Loc) (st : GoInterface) (γ : StreamNames) (Dn : Nat → GoString → IProp GF)
    (ci : GoInterfaceOk) (cd : _root_.Perennial.context.ContextDesc (IProp GF)) (md : GrpcMd),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver ∗
      srvStreamIs st γ strmMsg strmMsg biUp Dn ci cd ∗ (□ ∀ j m, biDn md γ j m -∗ Dn j m) ∗
      srvRecvTok (Req := strmMsg (GF := GF)) γ [] ∗ srvSendTok (Rep := strmMsg (GF := GF)) γ [] }}
    (App (Val (s @!! go.GoType.PointerType server.ty @!! go!"Bidi")) (Val #st))
  {{ (err : GoInterface), RET #err; go_etcd_io.etcd.cache.v3.srvErrOk err }}

end spec

end github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver
end Perennial
