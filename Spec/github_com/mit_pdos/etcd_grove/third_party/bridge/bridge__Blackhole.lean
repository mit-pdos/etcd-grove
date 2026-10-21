/-
`(*bridge).Blackhole()` (`third_party/bridge/bridge.go`): closes `blackholec` under the mutex, so
that every copy loop drops what it reads from then on. Lean-first (no Rocq counterpart).
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

/-- **`b.Blackhole()`** of a bridge that is not blackholed (the owner's flag `false`: a second
`Blackhole` would close a closed channel, `issues/etcd-bridge-blackhole-twice-panic.md`): it
returns, the bridge blackholed. -/
abbrev bridge.Blackhole.spec : Prop :=
  ∀ (b : Loc) (γ : BridgeNames) (addr : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.third_party.bridge ∗
      isBridge b γ addr ∗ bridgeHoled γ false }}
    (App (Val (b @!! go.GoType.PointerType bridge.bridge.ty @!! go!"Blackhole")) (Val #()))
  {{ RET #(); bridgeHoled γ true }}

end spec

end bridgeP
end EtcdGrove
end Perennial
