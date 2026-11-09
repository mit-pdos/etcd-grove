/-
## `schema.unsafeGetAllUsers(...)` (internal)

**Users.** The `authBatchTx`/`authReadTx` methods of the same name (for `UserList`, `RoleDelete`'s user scan (`auth/store.go`)).
**Proof sketch.** `tx.UnsafeForEach(AuthUsers, f)` (`txRd`, `f` never fails; `I l` holds the slice `vs` of the value slices appended, keeping the lent bytes, `lentKVs l`), then a fresh `authpb.User` per value (`Proto.msgAt … zero`: a law 3h/Proto owe, see the integration report) and `proto.Unmarshal` of each value (`recsWf`), then `lentKVs l` given back for `R V`. **Changes.** From `specs-ref`'s `unsafeGetAllUsers.lean` (where it had one: the read
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

/-- **Every user**, each once, in some order (`nil` if none). -/
def unsafeGetAllUsers.spec : Prop :=
  ∀ (lg : Loc) (tx : GoInterface) (S : Scope) (R : View → IProp GF) (V : View) (m : BData),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗ txRd tx S R ∗ R V ∗ ⌜S.whole .authUsers ∧ V .authUsers = some m ∧ recsWf go_etcd_io.etcd.api.v3.authpb.User.ty m⌝ }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.schema.unsafeGetAllUsers)) (Val #lg)) (Val #tx))
  {{ (sl : GoSlice), RET #sl; R V ∗ ∃ l, ⌜entsAny m l⌝ ∗ recsRes go_etcd_io.etcd.api.v3.authpb.User.ty sl (l.map Prod.snd) }}

end spec
end Schema
end EtcdGrove
end Perennial
