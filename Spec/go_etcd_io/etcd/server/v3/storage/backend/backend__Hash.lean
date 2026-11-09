/-
## `(*backend).Hash(ignores)` (`backend.go:425-452`): trusted (names only)

**Users.** mvcc's `hash` (`kvstore.go:161`, `schema.DefaultIgnores`), the corruption checker
through it. **Why it is true.** `b.mu.RLock()`, bbolt's `View` (a read transaction: the reader
slot lent; on a closed database `View` returns `ErrDatabaseNotOpen`), a CRC over every bucket's
entries the filter keeps (the filter's contract), `h.Sum32()`. **Changes.** From `specs-ref`'s:
a reader slot. **Margin.** The hash's value is not stated (mvcc's specs need none).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Backend

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- **`b.Hash(ignores)`**: some hash and error; the reader slot back. -/
def backend.Hash.spec : Prop :=
  ∀ (γ : BeNames) (b : Loc) (p : GoString) (Pk : IProp GF) (ign : GoFunc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗ isBackend γ b p Pk ∗ beRdToks γ 1 ∗ ignOk ign }}
    (App (Val (b @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.backend.backend.ty @!! go!"Hash")) (Val #ign))
  {{ (h : w32) (err : GoInterface), RET (PairV #h #err); beRdToks γ 1 }}

end spec

end Backend
end EtcdGrove
end Perennial
