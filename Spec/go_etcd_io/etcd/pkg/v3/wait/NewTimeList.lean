/-
`wait.NewTimeList()` (`wait_time.go`): a new `*timeList` for a predicate `P` of deadlines. Lean-first (no Rocq counterpart); the request path's unit 4b (2026-10-13).
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

/-- `wait.NewTimeList()`, for a predicate `P` of deadlines monotone downward that holds of `0`
(the last trigger's deadline is `0`): a `WaitTime` interface value backed by a `*timeList` meeting
`isTimeList` (`closec` closed, `waitClosecInit`, from the package's fact since D19r (D),
2026-10-18; a premise until then). -/
abbrev wait.NewTimeList.spec : Prop :=
  ∀ (P : w64 → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.wait ∗ □ P (W64 0) ∗ waitMono P }}
    (App (Val (@! wait.NewTimeList)) (Val #()))
  {{ (tl : Loc), RET #(interface.mkOk (go.GoType.PointerType wait.timeList.ty) #tl); isTimeList tl P }}

end spec

end EtcdGrove
end Perennial
