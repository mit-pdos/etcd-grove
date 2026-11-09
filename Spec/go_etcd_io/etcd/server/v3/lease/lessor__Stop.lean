/-
## `(*lessor).Stop()` (`lessor.go:615`): names only (an assumed spec)

**Users.** The server's `Cleanup` (`server.go:947`, 2e), once, on `run`'s shutdown or embed's error
path. Snippet `lessor.go` (`ReqStop`).

**Why it is true.** `close(le.stopC)` (the close right: `lessorStop le`, once; a second `Stop` would
close it twice and panic); `<-le.doneC` (closed by the run loop when it returns: it may block
meanwhile in the checkpointer, partial correctness). The lessor's other methods keep working after
it (`specs-ref`'s axiom review, attack 11).

**The run loop's thread token** (verify round, A9 3c F2): the run loop deposits the `threadTok`
`NewLessor`'s caller lent it when it returns (before closing `doneC`), so `Stop` gives it back.

**Changes** (from `specs-ref`'s `lessor__Stop.lean`, `lessorStopTok`): renamed `lessorStop`; verify
round: the run loop's `threadTok` given back.
**Margin.** None: the writer's token (with the lease bucket, `lessorState_bkt`) is the caller's.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.lease.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Lease

open Iris Iris.BI EtcdModel

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

/-- **Stop the lessor's run loop** (once). -/
def lessor.Stop.spec : Prop :=
  ∀ (le : Loc) (γ : Names) (c : Cfg),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ∗ isLessor le γ c ∗
      lessorStop le }}
    (App (Val (le @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.lease.lessor.ty @!!
      go!"Stop")) (Val #()))
  {{ RET #(); threadTok }}

end spec
end Lease
end EtcdGrove
end Perennial
