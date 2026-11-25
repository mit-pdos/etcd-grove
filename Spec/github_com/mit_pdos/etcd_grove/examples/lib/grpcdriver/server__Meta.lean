/- Lean-first (no Rocq counterpart).

`(*server).Meta(ctx, m)`: for a context whose incoming metadata is `md` (`metadata.ctxInMD`) and
`Meta`'s spec at it (`metaSpec`, `Svc.lean`: the joined values below `stringValueMax`), it answers
the values `md` has at `mdKeyS`, joined by `","` (`""` with no metadata), with a `nil` error.
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
abbrev server.Meta.spec : Prop :=
  ∀ (s : Loc) (ctx : GoInterfaceOk) (r : Loc) (v : GoString) (md : GrpcMd)
    (Φ : GoString → IProp GF) (Ψe : GoString → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver ∗
      (pbStringValueT (GF := GF)).toProtoMsg.recv r v ∗ metadata.ctxInMD ctx md ∗
      metaSpec md v Φ Ψe }}
    (App (App (Val (s @!! go.GoType.PointerType server.ty @!! go!"Meta"))
      (Val #(GoInterface.ok ctx))) (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      ⌜err = GoInterface.nil⌝ ∗
      stringValueSend resp (go!",".intercalate (metadata.mdVals md mdKeyS)) ∗
      Φ (go!",".intercalate (metadata.mdVals md mdKeyS)) }}

end spec

end github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver
end Perennial
