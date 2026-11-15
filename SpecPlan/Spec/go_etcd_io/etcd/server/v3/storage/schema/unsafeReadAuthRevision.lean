/-
## `schema.unsafeReadAuthRevision(...)` (internal)

**Users.** The `authBatchTx`/`authReadTx` methods of the same name (for the auth store's revision reads (`auth/store.go`)).
**Proof sketch.** `tx.UnsafeRange(Auth, authRevision, nil, 0)` (`txRd`), `BigEndian.Uint64` (`authRevWf`: eight bytes). **Changes.** From `specs-ref`'s `unsafeReadAuthRevision.lean` (where it had one: the read
transaction's state): over the contract.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.storage.schema.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Schema

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.schema.Assumptions]

/-- **The auth revision** (`0` if absent). -/
def unsafeReadAuthRevision.spec : Prop :=
  ∀ (tx : GoInterface) (S : Scope) (R : View → IProp GF) (V : View) (m : BData),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗ txRd tx S R ∗ R V ∗ ⌜S.has .auth authRevKey ∧ V .auth = some m ∧ authRevWf m⌝ }}
    (App (Val (@! go_etcd_io.etcd.server.v3.storage.schema.unsafeReadAuthRevision)) (Val #tx))
  {{ RET #(authRevOf m); R V }}

end spec
end Schema
end EtcdGrove
end Perennial
