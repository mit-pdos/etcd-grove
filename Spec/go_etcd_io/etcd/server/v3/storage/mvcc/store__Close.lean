/-
`(*store).Close()` (`kvstore.go:515`).

**Users**: `KV.Close` on the server's watchable store (which wraps it, 3f): `Cleanup`
(`server.go:950`), `NewServer`'s error path (`server.go:376`). Snippet `ReqClose`.

**Proof sketch**: `close(s.stopc)` (the open token's close right: no second close),
`fifoSched.Stop()` (the open token's `schedOpen` whole and `Pay`: pending jobs run, the job's
resources back); `mvccClosed γ` is the open token's remains with what `Stop` gave.

**Changes** from `specs-ref`'s `store__Close.lean`: the contract at `*store`; `mvccClosed` (with
`mvccClosed_rest`) in place of `True` (`examples/oneshot-close.md`).

**Margin**: none.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Mvcc

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- `KV.Close`'s contract at `*store`. -/
def store.Close.spec : Prop :=
  ∀ s : Loc, KV.Close.contract (GF := GF) (go.GoType.PointerType store.ty) #s

end spec
end Mvcc
end EtcdGrove
end Perennial
