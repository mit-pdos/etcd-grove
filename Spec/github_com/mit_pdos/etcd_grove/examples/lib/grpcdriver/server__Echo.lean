/- Lean-first (no Rocq counterpart).

`(*server).Echo(ctx, m)`: on the driver's server (`isDrvServer`, `ServerDefs.lean`), for a decoded
request at `v` (`pbStringValueT`'s `recv`) and `Echo`'s spec at it (`echoSpec`: `v` a fresh value
with its id's token, `Svc.lean`), it answers `v#1` (`v`'s first run) with a `nil` error: a sender's
`*StringValue` (`stringValueSend`) and `Φ (v ++ "#1")`.
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
abbrev server.Echo.spec : Prop :=
  ∀ (γid : GName) (s : Loc) (ctx : GoInterfaceOk) (r : Loc) (v : GoString) (md : GrpcMd)
    (Φ : GoString → IProp GF) (Ψe : GoString → IProp GF),
  {{ isDrvServer γid s ∗ (pbStringValueT (GF := GF)).toProtoMsg.recv r v ∗
      echoSpec γid md v Φ Ψe }}
    (App (App (Val (s @!! go.GoType.PointerType server.ty @!! go!"Echo"))
      (Val #(GoInterface.ok ctx))) (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      ⌜err = GoInterface.nil⌝ ∗ stringValueSend resp (v ++ go!"#1") ∗ Φ (v ++ go!"#1") }}

end spec

end github_com.mit_pdos.etcd_grove.examples.lib.grpcdriver
end Perennial
