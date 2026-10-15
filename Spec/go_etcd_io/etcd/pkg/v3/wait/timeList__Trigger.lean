/-
`tl.Trigger(deadline)` (`wait_time.go`). Lean-first (no Rocq counterpart); the request path's unit 4b (2026-10-13).
-/
module

public import Proof.go_etcd_io.etcd.pkg.v3.wait.TimeList

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.pkg.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `tl.Trigger(d)`, with `□ P d`: it records `d` as the last trigger's deadline (even below the
last: see `TimeList.lean`) and closes the channels of every deadline at most `d` with `P` of it. -/
abbrev wait.timeList.Trigger.spec : Prop :=
  ∀ (tl : Loc) (P : w64 → IProp GF) (d : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.wait ∗ isTimeList tl P ∗ □ P d }}
    (App (Val (tl @!! go.GoType.PointerType wait.timeList.ty @!! go!"Trigger")) (Val #d))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
