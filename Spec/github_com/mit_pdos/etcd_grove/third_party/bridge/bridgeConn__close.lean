/-
`(*bridgeConn).close()` (`third_party/bridge/bridge.go`): closes the connection's two ends.
Lean-first (no Rocq counterpart).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.third_party.bridge.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bridgeP

open Iris Iris.BI github_com.mit_pdos.etcd_grove.third_party

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.third_party.bridge.Assumptions]

/-- **`c.close()`**, from any thread, any number of times: it returns. -/
abbrev bridgeConn.close.spec : Prop :=
  ∀ (c : Loc) (inc outc : GoInterfaceOk) (donec : GoChan),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.third_party.bridge ∗
      connFields c inc outc donec ∗ netConnOk inc ∗ netConnOk outc }}
    (App (Val (c @!! go.GoType.PointerType bridge.bridgeConn.ty @!! go!"close")) (Val #()))
  {{ RET #(); True }}

end spec

end bridgeP
end EtcdGrove
end Perennial
