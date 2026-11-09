/-
## `(*list).Register(id)`

**Users.** `processInternalRaftRequestOnce` (`v3_server.go:1107`: the request's fresh id, before
proposing), `EtcdServer.configure` (`server.go`: a conf change's id). Concurrent callers. Snippet:
`examples/specreq/wait/wait.go` (`ReqRegisterTrigger`).

**Proof sketch.** `make(chan any, 1)`; the shard `id % 64`'s `Lock`; the invariant's map has no
entry for `id` (the invariant holds `waitTok γw id` for each registered id: a second token is
excluded, so `log.Panicf` is unreachable); insert the channel with its registration (the token
moves in); `Unlock` (deferred). The receive half is the caller's.

**Changes.** The old spec took the id's wait slot of the generator's names and a per-registration
expectation `Ψ`; restated over `waitTok` and the registry's `P`.

**Margin.** None.
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.wait.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Wait

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.wait.Assumptions]

/-- **Registers `id`** (never registered before: its token): the caller becomes the receiver of
`id`'s one value. -/
def list.Register.spec : Prop :=
  ∀ (l : Loc) (γw : WaitNames) (P : w64 → GoInterface → IProp GF) (id : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.wait ∗ listAt l γw P ∗
      waitTok γw id }}
    (App (Val (l @!! go.GoType.PointerType go_etcd_io.etcd.pkg.v3.wait.list'.ty @!! go!"Register"))
      (Val #id))
  {{ (ch : Loc), RET #ch; waitRecv γw id ch }}

end spec
end Wait
end EtcdGrove
end Perennial
