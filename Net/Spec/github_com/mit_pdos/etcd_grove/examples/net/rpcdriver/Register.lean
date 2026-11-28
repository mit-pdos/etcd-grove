/- Lean-first (no Rocq counterpart).

The driver's `Register()` (`rpc_model_gen.go`): from net/rpc's initial codec state (no codec
registered, `codecUnset`), it registers the generated codec (`codecSet drvCodec`), over net/rpc's
`SetCodec`. Proved in `Net/Proof/.../rpcdriver/Register.lean`.
-/
module

public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.Codec

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Net

namespace github_com.mit_pdos.etcd_grove.examples.net.rpcdriver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [net.rpc.Assumptions] [π : NetProtoGS]
variable [rpcdriver.Assumptions]

/-- See the file header. -/
abbrev Register.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗
      sync.isMutex (globalAddr net.rpc.codecMu) (net.rpc.codecInv (GF := GF)) ∗
      net.rpc.codecUnset }}
    (App (Val (@! rpcdriver.Register)) (Val #()))
  {{ RET #(); net.rpc.codecSet drvCodec }}

end spec

end github_com.mit_pdos.etcd_grove.examples.net.rpcdriver
end Perennial
