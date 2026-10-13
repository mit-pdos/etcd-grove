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
(the last trigger's deadline is `0`), and `closec` closed (`waitClosecInit`, the package's
initialization): a `*timeList` meeting `isTimeList`. -/
abbrev wait.NewTimeList.spec : Prop :=
  ∀ (P : w64 → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.wait ∗ □ P (W64 0) ∗ waitMono P ∗
      waitClosecInit }}
    (App (Val (@! wait.NewTimeList)) (Val #()))
  {{ (tl : Loc), RET #tl; isTimeList tl P }}

end spec

end EtcdGrove
end Perennial
