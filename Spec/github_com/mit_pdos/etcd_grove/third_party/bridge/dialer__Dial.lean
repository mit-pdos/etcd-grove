/-
`dialer.Dial()` (`third_party/bridge/dialer.go`): `net.Dial(d.network, d.addr)`. Lean-first (no
Rocq counterpart).
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

/-- **`d.Dial()`**, `d` a TCP dialer to `addr`: as `net.Dial("tcp", addr)`. -/
abbrev dialer.Dial.spec : Prop :=
  ∀ (addr : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.third_party.bridge }}
    (App (Val ((bridge.dialer.mk go!"tcp" addr) @!! bridge.dialer.ty @!! go!"Dial")) (Val #()))
  {{ (c err : GoInterface), RET (PairV #c #err);
      (⌜err = GoInterface.nil⌝ ∗ ∃ co : GoInterfaceOk, ⌜c = interface.ok co⌝ ∗
        netConnOk (GF := GF) co ∗ netDialed co addr) ∨ ⌜err ≠ GoInterface.nil⌝ }}

end spec

end bridge
end EtcdGrove
end Perennial
