/-
**The apply thread's auth resource** (the auth plan's E2k, 2026-10-26, moved here by E2m so that
the apply thread's state `srvApplyKV`, `InvApplier.lean`, can hold it; `notes/decisions.md`, "E2m
of the auth plan"). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRequest
public import Proof.go_etcd_io.etcd.server.v3.auth.Fuel
public import Proof.go_etcd_io.etcd.server.v3.auth.InvAuth
public import Proof.go_etcd_io.etcd.server.v3.auth.TieRes

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The apply thread's auth resource** of the store `stl` in the mode `M` (the auth plan's E2k,
2026-10-26; `notes/decisions.md`, "E2l of the auth plan", the apply thread's auth resource): in the
mode `on γa`, the admin side's authority with its fuel (`auth.authOwnFu`), its write resource
`auth.authWR` but for the store's user's half of `be` (the backend's write side, the write token,
the half of `be` stays in the server's rest, `authBeOn`, which the admin request's application
borrows: "E2m of the auth plan"), the admin side's halves of `enabled` and of the permission cache
tied to the latest state of the history (`auth.tieRes`, E2v: what the checks at the latest state
need, `auth.latestRes`, and what the admin steps keep, `auth.X.specT`), and the provider's admin
share (`auth.tpAdmin`); `True` in the other modes. `NewServer.specM`'s construction hands it to the apply
thread (`applyBuiltNA`, then `srvApplyKV`). -/
def authApplyRes (M : auth.AuthMode) (stl : Loc) : IProp GF :=
  match M with
  | .on γa => iprop(∃ (hs : List auth.AuthState) (P : IProp GF) (f : val) (T : IProp GF)
      (be : GoInterface), auth.authOwnFu γa hs ∗ auth.tieRes stl (.on γa) hs ∗
      auth.authWBackendOk be (.on γa) P f T ∗ T ∗ auth.tpAdmin stl (.on γa))
  | _ => iprop(True)

/-- **The server's auth resource for its apply thread** (E2k): the store its `authStore` field
holds, with `authApplyRes` in the environment's mode. -/
def srvAuthApplyRes (s : Loc) (E : apply.AEnv GF) : IProp GF :=
  iprop(∃ stl : Loc, structFieldRef go_etcd_io.etcd.server.v3.etcdserver.EtcdServer go!"authStore" s ↦□
    (auth.authIface stl) ∗ authApplyRes E.authMode stl)

/-- **The apply thread's auth resource with the latest state of its history** (the auth plan's E3c,
2026-10-27): `authApplyRes`'s, with the history's latest state `st` (in the mode `on γa`; `True` in
the other modes). What ties the apply thread's auth state to the model's (`kvRunOn`'s): at the
server's start, the store's history `[bootState, bump bootState]` (`authStoreKit`'s post, at
`bump bootState`, `srvAuthSt0`). -/
def authApplyResAt (M : auth.AuthMode) (stl : Loc) (st : auth.AuthState) : IProp GF :=
  match M with
  | .on γa => iprop(∃ (hs : List auth.AuthState) (P : IProp GF) (f : val) (T : IProp GF)
      (be : GoInterface), auth.authOwnFu γa hs ∗ auth.tieRes stl (.on γa) hs ∗
      auth.authWBackendOk be (.on γa) P f T ∗ T ∗ auth.tpAdmin stl (.on γa) ∗
      ⌜hs.getLast? = some st⌝)
  | _ => iprop(True)

/-- **The server's auth resource for its apply thread, at the latest state `st`** (E3c). -/
def srvAuthApplyResAt (s : Loc) (E : apply.AEnv GF) (st : auth.AuthState) : IProp GF :=
  iprop(∃ stl : Loc, structFieldRef go_etcd_io.etcd.server.v3.etcdserver.EtcdServer go!"authStore" s ↦□
    (auth.authIface stl) ∗ authApplyResAt E.authMode stl st)

end defs

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

open Iris.ProofMode in
/-- `authApplyResAt` forgets its latest state into `authApplyRes`. -/
theorem authApplyRes_of_At (M : auth.AuthMode) (stl : Loc) (st : auth.AuthState) :
    authApplyResAt (GF := GF) M stl st ⊢ authApplyRes M stl := by
  cases M with
  | on γa =>
    unfold authApplyResAt authApplyRes
    iintro ⟨%hs, %P, %f, %T, %be, Ho, HX, Hw, HT, Htp, -⟩
    iexists hs, P, f, T, be
    iframe Ho HX Hw HT Htp
  | off => unfold authApplyResAt authApplyRes; iintro -; itrivial
  | any => unfold authApplyResAt authApplyRes; iintro -; itrivial

open Iris.ProofMode in
/-- `srvAuthApplyResAt` forgets its latest state into `srvAuthApplyRes`. -/
theorem srvAuthApplyRes_of_At (s : Loc) (E : apply.AEnv GF) (st : auth.AuthState) :
    srvAuthApplyResAt (GF := GF) s E st ⊢ srvAuthApplyRes s E := by
  unfold srvAuthApplyResAt srvAuthApplyRes
  iintro ⟨%stl, #Hf, H⟩
  iexists stl
  iframe Hf
  iapply authApplyRes_of_At $$ H

end lemmas

end EtcdGrove
end Perennial
