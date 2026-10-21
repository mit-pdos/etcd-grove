/-
`net.Dial(network, address)` (names only; `notes/client-cut-plan.md` K1): the connection the
bridge (`third_party/bridge`'s `dialer`) dials to the member's address. The vocabulary:
`Proof/net/InvRelay.lean`.
-/
module

public import Proof.net.InvRelay

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `net.Dial("tcp", addr)` returns a connection dialed to `addr` (`netConnOk`, and `netDialed`,
which a relay pairs with a connection it accepted) and `nil`, or a non-nil error. -/
abbrev net.Dial.spec : Prop :=
  ∀ (network addr : GoString),
  {{ ⌜network = go!"tcp"⌝ }}
    (App (App (Val (@! net.Dial)) (Val #network)) (Val #addr))
  {{ (c err : GoInterface), RET (PairV #c #err);
      (⌜err = GoInterface.nil⌝ ∗ ∃ co : GoInterfaceOk, ⌜c = interface.ok co⌝ ∗
        netConnOk (GF := GF) co ∗ netDialed co addr) ∨ ⌜err ≠ GoInterface.nil⌝ }}

end spec

end EtcdGrove
end Perennial
