/-
**`SetUp`'s Auth premise from the served Auth service** (the auth plan's E3zb, 2026-10-28).
Lean-first (no Rocq counterpart).

`SetUp.spec` takes `setupAuthOk ep Su Sg Sr Sp Se Q`: the five admin methods registered at `ep`
with specs `Su`, ..., and each of the set-up's eight calls' precondition with its `Q`. At etcd's
specs of the Auth service (`v3rpc.etcdUserAddSpec`, ..., `AuthService.lean`), which a member with
auth on serves (`etcd_kv_auth_served_on`), each call's precondition is the name's length bound and
the caller's continuation from the reply's facts; so `Q` is what each reply carries
(`setupQ`: `userAddReplied` for the three `UserAdd`s, `adminReplied` of its request for the
others), and `setupAuthOk_of_served` gives the premise from the five registrations alone.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.authkv.SetUp
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthService

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace authkv

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **What `SetUp`'s eight admin calls' replies carry**, in the order of `setupAuthOk`'s `Q`. -/
def setupQ (E : apply.AEnv GF) (ρ : ReqNames) : Fin 8 → IProp GF
  | ⟨0, _⟩ => v3rpc.userAddReplied E ρ go!"root"
  | ⟨1, _⟩ => v3rpc.adminReplied E ρ (irrUserGrantRole go!"root" go!"root")
  | ⟨2, _⟩ => v3rpc.adminReplied E ρ (irrRoleAdd go!"r")
  | ⟨3, _⟩ => v3rpc.adminReplied E ρ
      (irrRoleGrantPermission go!"r" (some ⟨W32 2, go!"a", go!"b"⟩))
  | ⟨4, _⟩ => v3rpc.userAddReplied E ρ go!"u"
  | ⟨5, _⟩ => v3rpc.adminReplied E ρ (irrUserGrantRole go!"u" go!"r")
  | ⟨6, _⟩ => v3rpc.userAddReplied E ρ go!"v"
  | ⟨_ + 7, _⟩ => v3rpc.adminReplied E ρ irrAuthEnable

/-- **`SetUp`'s Auth premise from the five served Auth methods** (see the file header). -/
theorem setupAuthOk_of_served (ep : GoString) (E : apply.AEnv GF) (ρ : ReqNames) :
    isGrpcRpc ep go!"/etcdserverpb.Auth/UserAdd" (v3rpc.etcdUserAddSpec E ρ) ∗
      isGrpcRpc ep go!"/etcdserverpb.Auth/UserGrantRole" (v3rpc.etcdUserGrantRoleSpec E ρ) ∗
      isGrpcRpc ep go!"/etcdserverpb.Auth/RoleAdd" (v3rpc.etcdRoleAddSpec E ρ) ∗
      isGrpcRpc ep go!"/etcdserverpb.Auth/RoleGrantPermission"
        (v3rpc.etcdRoleGrantPermissionSpec E ρ) ∗
      isGrpcRpc ep go!"/etcdserverpb.Auth/AuthEnable" (v3rpc.etcdAuthEnableSpec E ρ) ⊢
    setupAuthOk ep (v3rpc.etcdUserAddSpec E ρ) (v3rpc.etcdUserGrantRoleSpec E ρ)
      (v3rpc.etcdRoleAddSpec E ρ) (v3rpc.etcdRoleGrantPermissionSpec E ρ)
      (v3rpc.etcdAuthEnableSpec E ρ) (setupQ E ρ) := by
  iintro ⟨#Hu, #Hg, #Hr, #Hp, #He⟩
  iunfold setupAuthOk
  iframe Hu Hg Hr Hp He
  unfold v3rpc.etcdUserAddSpec v3rpc.etcdUserGrantRoleSpec v3rpc.etcdRoleAddSpec
    v3rpc.etcdRoleGrantPermissionSpec v3rpc.etcdAuthEnableSpec
  isplitr
  · iintro !> !>
    isplitr; · ipureintro; decide
    iintro H; iExactEq H; rfl
  isplitr
  · iintro !> !>
    isplitr; · ipureintro; decide
    iintro H; iExactEq H; rfl
  isplitr
  · iintro !> !>
    isplitr; · ipureintro; decide
    iintro H; iExactEq H; rfl
  isplitr
  · iintro !> !>
    isplitr; · ipureintro; decide
    iintro H; iExactEq H; rfl
  isplitr
  · iintro !> !>
    isplitr; · ipureintro; decide
    iintro H; iExactEq H; rfl
  isplitr
  · iintro !> !>
    isplitr; · ipureintro; decide
    iintro H; iExactEq H; rfl
  isplitr
  · iintro !> !>
    isplitr; · ipureintro; decide
    iintro H; iExactEq H; rfl
  iintro !> !> H
  iExactEq H; rfl

end defs

end authkv
end EtcdGrove
end Perennial
