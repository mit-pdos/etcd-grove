/-
`(*bridge).DropConnections()` (`third_party/bridge/bridge.go`): under the mutex, closes every
registered connection (waiting for its copy goroutines) and empties the map. Lean-first (no Rocq
counterpart).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.third_party.bridge.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bridge

open Iris Iris.BI github_com.mit_pdos.etcd_grove.third_party

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.third_party.bridge.Assumptions]

/-- **`b.DropConnections()`**, from any thread: it returns. -/
abbrev bridge.DropConnections.spec : Prop :=
  ∀ (b : Loc) (γ : BridgeNames) (addr : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.third_party.bridge ∗
      isBridge b γ addr }}
    (App (Val (b @!! go.GoType.PointerType bridge.bridge.ty @!! go!"DropConnections")) (Val #()))
  {{ RET #(); True }}

end spec

end bridge
end EtcdGrove
end Perennial
