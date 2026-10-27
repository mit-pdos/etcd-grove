/-
`s.UserAdd(ctx, r)` (`v3_server.go`): unless the request asks for no password, the password hashed
(`bcrypt.GenerateFromPassword` at the auth store's `BcryptCost()`), the hash put base64-encoded in
`r.HashedPassword` and `r.Password` cleared; then `raftRequest` on
`&pb.InternalRaftRequest{AuthUserAdd: r}`. Lean-first (no Rocq counterpart); the auth plan's E2x
(2026-10-26), vocabulary `AuthEntry.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthEntry
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AdminOn
public import Proof.encoding.base64.Base

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- The auth store `ast`'s `BcryptCost()` returns (some `int`; `authStore.BcryptCost` returns its
field `bcryptCost`, read-only after `NewAuthStore`). A definition so that `wp_start` does not try
to unfold the interface's method. -/
def bcryptCostOk (ast : GoInterfaceOk) : IProp GF :=
  iprop(□ ({{ True }} (App (Val #(methods ast.ty go!"BcryptCost" ast.v)) (Val #()))
    {{ (c : w64), RET #c; True }}))

instance bcryptCostOk_persistent (ast : GoInterfaceOk) : Persistent (bcryptCostOk (GF := GF) ast) := by
  unfold bcryptCostOk; infer_instance

/-- **`s.UserAdd(ctx, r)`** for the request `r` (not nil) with the name `name`, its passwords
owned (the handler writes them) and its options read-only (`auth.userOptsAt o b`), the server's
auth store `ast` (its `authStore` field, read-only) whose `BcryptCost()` returns: the request it
proposes has a password choice that cannot fail (`apply.UserAddModel.pwSure`: no password asked
for, or `Password` cleared and `HashedPassword` the standard base64 encoding of the hash), which
discharges the proposer's `pwSure` (the auth plan's E2t, E2u). The proposal is the contract
`authRaftOk` for the response type `*pb.AuthUserAddResponse`, for any such model of the request
(the persistent `Hraft`), as for the other Auth entry points (`EtcdServer.UserGrantRole.spec`);
the outcome: the hashing's error, before any proposal (`nil`, the error and `P` back), or
`authEntryOut`. -/
abbrev EtcdServer.UserAdd.spec : Prop :=
  ∀ (s : Loc) (ctx : GoInterfaceOk) (ast : GoInterfaceOk) (r : Loc) (name pw hpw : GoString)
    (o : Loc) (b : Bool) (P : IProp GF) (Q : Loc → GoInterface → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      structFieldRef EtcdServer go!"authStore" s ↦□ GoInterface.ok ast ∗
      bcryptCostOk ast ∗
      ⌜r ≠ null⌝ ∗ structFieldRef etcdserverpb.AuthUserAddRequest go!"Name" r ↦□ name ∗
      structFieldRef etcdserverpb.AuthUserAddRequest go!"Password" r ↦ pw ∗
      structFieldRef etcdserverpb.AuthUserAddRequest go!"HashedPassword" r ↦ hpw ∗
      structFieldRef etcdserverpb.AuthUserAddRequest go!"Options" r ↦□ o ∗ auth.userOptsAt o b ∗
      P ∗
      □ (∀ m : apply.UserAddModel, ⌜m.name = name ∧ m.noPassword = b ∧ m.pwSure⌝ →
          authRaftOk s ctx (irrUserAdd m) etcdserverpb.AuthUserAddResponse.ty P Q) }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"UserAdd"))
      (Val #(GoInterface.ok ctx))) (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      (⌜resp = null ∧ err ≠ GoInterface.nil⌝ ∗ P) ∨ (applyErrIs err ∗ authEntryOut Q resp err) }}

/-- **What a mode-`on` `UserAdd` of `name` answers** (`adminOutOn` for the request the handler
proposed, some model `m` of it with the name `name`, the password choice `b` and a password choice
that cannot fail). -/
def userAddOutOn (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (F : mvcc.Log) (name : GoString)
    (b : Bool) (l : Loc) (err : GoInterface) : IProp GF :=
  iprop(∃ m : apply.UserAddModel, ⌜m.name = name ∧ m.noPassword = b ∧ m.pwSure⌝ ∗
    adminOutOn s E ρ (irrUserAdd m) F (adminQh ρ.kv (irrUserAdd m))
      etcdserverpb.AuthUserAddResponse.ty l err)

/-- **`s.UserAdd(ctx, r)` with auth on** (the auth plan's E3w, 2026-10-27; `AdminOn.lean`): `spec`
with its contract `raftRequest.specM true`'s (`authRaftOk_on`), the request admitted (`adminPropOk`,
for a name of at most `maxKeySize` bytes, its password choice sure by `spec`); the outcome: the
hashing's error before any proposal (`adminPreOn` back), or `authEntryOut` of `userAddOutOn`: on
success, the request applied at the committed prefix `L` before its entry (`appliedOkM true`), the
auth state after it published (`pubAfterM true`) and its step determinate there (`adminQh`); else
the apply thread's error, or the request perhaps proposed. -/
abbrev EtcdServer.UserAdd.specOn : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (ast : GoInterfaceOk) (r : Loc) (name pw hpw : GoString)
    (o : Loc) (b : Bool) (F : mvcc.Log),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      structFieldRef EtcdServer go!"authStore" s ↦□ GoInterface.ok ast ∗
      bcryptCostOk ast ∗
      ⌜r ≠ null⌝ ∗ structFieldRef etcdserverpb.AuthUserAddRequest go!"Name" r ↦□ name ∗
      structFieldRef etcdserverpb.AuthUserAddRequest go!"Password" r ↦ pw ∗
      structFieldRef etcdserverpb.AuthUserAddRequest go!"HashedPassword" r ↦ hpw ∗
      structFieldRef etcdserverpb.AuthUserAddRequest go!"Options" r ↦□ o ∗ auth.userOptsAt o b ∗
      ⌜name.length ≤ backend.maxKeySize⌝ ∗ adminPreOn s E ρ ctx cd F }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"UserAdd"))
      (Val #(GoInterface.ok ctx))) (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      (⌜resp = null ∧ err ≠ GoInterface.nil⌝ ∗ adminPreOn s E ρ ctx cd F) ∨
      (applyErrIs err ∗ authEntryOut (userAddOutOn s E ρ F name b) resp err) }}

end spec

end EtcdGrove
end Perennial
