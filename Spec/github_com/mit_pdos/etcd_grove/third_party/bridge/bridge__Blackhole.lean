/-
`b.Blackhole()` (`third_party/bridge/bridge.go`; `notes/client-cut-plan.md` K1): a trust-boundary spec, the
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

/-- **`b.Blackhole()`** of a bridge that is not blackholed (a second `Blackhole` closes a closed
channel, `issues/nonissues/etcd-bridge-blackhole-twice-panic.md`): it returns, the bridge blackholed. -/
abbrev bridge.Blackhole.spec : Prop :=
  ∀ (b : Loc) (addr : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.third_party.bridge ∗
      bridgeAt b addr false }}
    (App (Val (b @!! go.GoType.PointerType bridge.bridge.ty @!! go!"Blackhole")) (Val #()))
  {{ RET #(); bridgeAt b addr true }}

end spec

end bridge
end EtcdGrove
end Perennial
