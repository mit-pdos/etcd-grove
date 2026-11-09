/-
## `schema.unsafeGetUser(...)` (internal)

**Users.** The `authBatchTx`/`authReadTx` methods of the same name (for the auth store's checks and admin operations (`auth/store.go:433,...`)).
**Proof sketch.** `tx.UnsafeRange(AuthUsers, name, nil, 0)` (`txRd`), `proto.Unmarshal` into a fresh `authpb.User` (`recsWf`: no error, `lg.Panic` unreachable). **Changes.** From `specs-ref`'s `unsafeGetUser.lean` (where it had one: the read
transaction's state): over the contract.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.schema.Api

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

/-- **The user `name`**: `nil`, or a fresh message of its stored record. -/
def unsafeGetUser.spec : Prop :=
  ∀ (lg : Loc) (tx : GoInterface) (S : Scope) (R : View → IProp GF) (V : View) (m : BData) (name : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗ txRd tx S R ∗ R V ∗ ⌜S.has .authUsers name ∧ V .authUsers = some m ∧ recsWf go_etcd_io.etcd.api.v3.authpb.User.ty m⌝ }}
    (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.schema.unsafeGetUser)) (Val #lg)) (Val #tx)) (Val #name))
  {{ (p : Loc), RET #p; R V ∗ recRes go_etcd_io.etcd.api.v3.authpb.User.ty (m name) p }}

end spec
end Schema
end EtcdGrove
end Perennial
