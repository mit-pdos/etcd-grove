/-
`tl.Pending()` (`wait_time.go`, etcd PR #22495). Lean-first (no Rocq counterpart;
pr-verify/etcd-22495, 2026-10-17).
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

/-- `tl.Pending()`: a non-negative count (the map's size, `len(tl.m)`, under the lock: the number
of distinct deadlines not yet triggered at that moment; other threads change it, so the
postcondition says no more). -/
abbrev wait.timeList.Pending.spec : Prop :=
  ∀ (tl : Loc) (P : w64 → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.wait ∗ isTimeList tl P }}
    (App (Val (tl @!! go.GoType.PointerType wait.timeList.ty @!! go!"Pending")) (Val #()))
  {{ (n : w64), RET #n; ⌜0 ≤ sint.Z n⌝ }}

end spec

end EtcdGrove
end Perennial
