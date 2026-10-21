/-
`b.Unblackhole()` (`third_party/bridge/bridge.go`; `notes/client-cut-plan.md` K1): a trust-boundary spec, the
bridge's code is not verified (`Proof/github_com/mit_pdos/etcd_grove/third_party/bridge/Defs.lean`).
Lean-first (no Rocq counterpart).
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

/-- **`b.Unblackhole()`**, blackholed or not: it returns, the bridge not blackholed. -/
abbrev bridge.Unblackhole.spec : Prop :=
  ∀ (b : Loc) (addr : GoString) (h : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.third_party.bridge ∗
      bridgeAt b addr h }}
    (App (Val (b @!! go.GoType.PointerType bridge.bridge.ty @!! go!"Unblackhole")) (Val #()))
  {{ RET #(); bridgeAt b addr false }}

end spec

end bridge
end EtcdGrove
end Perennial
