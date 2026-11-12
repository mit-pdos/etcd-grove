/-
## `wait.New()`

**Users.** `EtcdServer.start` (`server.go:567`: `s.w = wait.New()`), the server's tests. Snippet:
`examples/specreq/wait/wait.go`.

**Proof sketch.** `make([]listElement, 64)`, each shard's map made in the loop; the registry's
invariants allocated (one `RWMutex` invariant per shard, empty maps), the ghost set authority
empty (`waitToks γw []`). `P` is the caller's choice, saved in the invariants.

**Changes.** The old spec (`specs-ref`'s `New.lean`) was over the id generator's names (`γi`, the
ids' wait slots) and a registration condition `R id Ψ` per registration, and handed out the
shards' reader slots `RD`. Restated: one answer predicate `P id x` per registry, the ids' freshness
the client's (`waitToks`), no reader slots (the caller's thread token covers `IsRegistered`'s
reader).

**Margin.** None.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.pkg.v3.wait.Api

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

/-- **A new registry** (a `*list` as a `Wait`) answering with `P`, nothing registered. -/
def New.spec : Prop :=
  ∀ (P : w64 → GoInterface → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.wait }}
    (App (Val (@! go_etcd_io.etcd.pkg.v3.wait.New)) (Val #()))
  {{ (w : GoInterface), RET #w; ∃ (l : Loc) (γw : WaitNames),
      ⌜w = interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.pkg.v3.wait.list'.ty) #l⌝ ∗
      listAt l γw P ∗ waitToks γw [] }}

end spec
end Wait
end EtcdGrove
end Perennial
