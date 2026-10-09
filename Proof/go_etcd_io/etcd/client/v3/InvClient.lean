/-
What a caller assumes of a `*clientv3.Client`'s own fields, beyond its embedded interfaces
(`isEtcdClient`, `InvNew.lean`; `isEtcdLeaseClient`, `InvEtcdTxn.lean`): its logger
(`Client.GetLogger`). Lean-first (no Rocq counterpart).

**The logger.** `Client.lg` is an `atomic.Pointer[zap.Logger]`, set by `newClient` and replaced
only by `WithLogger` (with a caller's logger); `isClientLogger cl` is an invariant holding it,
whatever it is, non-nil. `GetLogger()` (`c.lg.Load()`) returns some non-nil logger.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvOp
public import Perennial.Proof.sync.atomic

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section addrs
variable [FfiSyntax] [GoGlobalContext] [GoSemanticsFunctions]

/-- `&client.lg` (an `atomic.Pointer[zap.Logger]`). -/
abbrev clientLgAddr (cl : Loc) : Loc :=
  structFieldRef go_etcd_io.etcd.client.v3.Client go!"lg" cl

end addrs

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]

/-- The invariant's namespace. -/
def clientLgN : Namespace := nroot .@ "clientv3_lg"

/-- **The client's logger** (persistent): the client's `lg` holds, at every point, a non-nil
`*zap.Logger` (an invariant: `WithLogger` may replace it). -/
def isClientLogger (cl : Loc) : IProp GF :=
  inv clientLgN iprop(∃ lg : Loc,
    sync.atomic.ownPointer (hG := hG) (T' := go_uber_org.zap.Logger) (clientLgAddr cl)
      (DFrac.own 1) lg ∗
    ⌜lg ≠ null⌝)

instance isClientLogger_persistent (cl : Loc) : Persistent (isClientLogger (GF := GF) cl) := by
  unfold isClientLogger; infer_instance

end defs

end EtcdGrove
end Perennial
