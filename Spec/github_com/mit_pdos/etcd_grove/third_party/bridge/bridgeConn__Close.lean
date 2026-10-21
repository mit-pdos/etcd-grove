/-
`(*bridgeConn).Close()` (`third_party/bridge/bridge.go`): closes the connection's two ends and
waits for `donec`, which `serveConn` closes once its copy goroutines are done. Lean-first (no
Rocq counterpart).
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

/-- **`c.Close()`**, on a connection of the bridge `b`, from any thread: it returns once `donec`
is closed, with the deposit it was closed with (`doneQ`: the goroutines' share of
`b.blackholec`, for the holder of the claim token). -/
abbrev bridgeConn.Close.spec : Prop :=
  ∀ (b c : Loc) (q : Qp) (γt : GName),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.third_party.bridge ∗
      connOk b c q γt }}
    (App (Val (c @!! go.GoType.PointerType bridge.bridgeConn.ty @!! go!"Close")) (Val #()))
  {{ RET #(); doneQ b q γt }}

end spec

end bridgeP
end EtcdGrove
end Perennial
