/-
`(*SingleFileTracker).Start()` (`synctrack.go:160`): the counter incremented (`atomic.AddInt64`). Lean-first; phase 4 of `notes/k8s-daemonset-plan.md` (the shared informer's listeners).
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

/-- **`t.Start()`**: a start token (`sftTok`); in an execution of fewer than `2^63` Go steps
(`receiptBound GF ≤ 2^63`), so the counter does not wrap. -/
abbrev SingleFileTracker.Start.spec : Prop :=
  ∀ (t : Loc) (γ : GName), receiptBound GF ≤ 2 ^ 63 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.client_go.tools.cache.synctrack ∗ isSFT t γ }}
    (App (Val (t @!! go.GoType.PointerType SingleFileTracker.ty @!! go!"Start")) (Val #()))
  {{ RET #(); sftTok γ }}

end spec

end synctrack
end EtcdGrove
end Perennial
