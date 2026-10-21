/-
`(*bridge).ioCopy(dst, src)` (`third_party/bridge/bridge.go`): copies `src` to `dst` until a read
or write fails, or, once the bridge is blackholed, reads `src` to its end and drops it. Lean-first
(no Rocq counterpart).
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

/-- **`b.ioCopy(t, s)`**, on a relay's direction from `s` to `t` with everything read written,
with a share of `b.blackholec` (the channel `ch`): it returns, with the share. -/
abbrev bridge.ioCopy.spec : Prop :=
  ∀ (b : Loc) (q : Qp) (ch : GoChan) (γbh : ChanNames) (l s t : GoInterfaceOk) (rd : List w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.third_party.bridge ∗
      bF b go!"blackholec" ↦{DFrac.own q} ch ∗ ownBroadcastChan ch γbh iprop(True) .Unknown ∗
      relayDir l s t rd rd }}
    (App (App (Val (b @!! go.GoType.PointerType bridge.bridge.ty @!! go!"ioCopy"))
      (Val #(interface.ok t : GoInterface))) (Val #(interface.ok s : GoInterface)))
  {{ (err : GoInterface), RET #err; bF b go!"blackholec" ↦{DFrac.own q} ch }}

end spec

end bridge
end EtcdGrove
end Perennial
