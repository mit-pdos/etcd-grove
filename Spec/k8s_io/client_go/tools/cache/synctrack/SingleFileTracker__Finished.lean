/-
`(*SingleFileTracker).Finished()` (`synctrack.go:169`): the counter decremented (it panics if negative), and the tracker marked synced if it reaches zero after its upstream synced. Lean-first; phase 4 of `notes/k8s-daemonset-plan.md` (the shared informer's listeners).
-/
module

public import Proof.k8s_io.client_go.tools.cache.synctrack.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace synctrack

open Iris Iris.BI k8s_io.client_go.tools.cache.synctrack

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.synctrack.Assumptions]

/-- **`t.Finished()`** with a start token: returns (the counter was positive, so the panic is
unreachable). -/
abbrev SingleFileTracker.Finished.spec : Prop :=
  ∀ (t : Loc) (γ : GName),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache.synctrack ∗ isSFT t γ ∗
      sftTok γ }}
    (App (Val (t @!! go.GoType.PointerType SingleFileTracker.ty @!! go!"Finished")) (Val #()))
  {{ RET #(); True }}

end spec

end synctrack
end EtcdGrove
end Perennial
