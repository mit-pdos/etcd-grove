/-
`tl.Wait(deadline)` (`wait_time.go`). Lean-first (no Rocq counterpart); the request path's unit 4b (2026-10-13).
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

/-- `tl.Wait(d)`: a channel closed, never sent on, whose close tells some `Q` giving `P d`: the
package's `closec` (closed in `init`, `Q = True`) if `d` was triggered (`P d` holds: the lock
invariant's `□ P last`, `d ≤ last`), else the channel of the deadline `d` (`Q = P d`). -/
abbrev wait.timeList.Wait.spec : Prop :=
  ∀ (tl : Loc) (P : w64 → IProp GF) (d : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.wait ∗ isTimeList tl P }}
    (App (Val (tl @!! go.GoType.PointerType wait.timeList.ty @!! go!"Wait")) (Val #d))
  {{ (ch : Loc), RET #ch; ∃ Q : IProp GF, waitBcast ch Q ∗ □ (Q -∗ P d) }}

end spec

end EtcdGrove
end Perennial
