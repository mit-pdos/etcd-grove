/-
**The apply thread's auth resource** (the auth plan's E2k, 2026-10-26, moved here by E2m so that
the apply thread's state `srvApplyKV`, `InvApplier.lean`, can hold it; `notes/decisions.md`, "E2m
of the auth plan"). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRequest
public import Proof.go_etcd_io.etcd.server.v3.auth.Fuel
public import Proof.go_etcd_io.etcd.server.v3.auth.InvAuth

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
the admin side's half of `enabled`; the half of `be` stays in the server's rest, `authBeOn`, which
the admin request's application borrows: "E2m of the auth plan"), and the provider's admin share
(`auth.tpAdmin`); `True` in the other modes. `NewServer.specM`'s construction hands it to the apply
thread (`applyBuiltNA`, then `srvApplyKV`). -/
def authApplyRes (M : auth.AuthMode) (stl : Loc) : IProp GF :=
  match M with
  | .on γa => iprop(∃ (hs : List auth.AuthState) (P : IProp GF) (f : val) (T : IProp GF)
      (be : GoInterface), auth.authOwnFu γa hs ∗ auth.authWBackendOk be (.on γa) P f T ∗ T ∗
      auth.enabledHalf stl (.on γa) ∗ auth.cacheHalf stl (.on γa) ∗ auth.tpAdmin stl (.on γa))
  | _ => iprop(True)

/-- **The server's auth resource for its apply thread** (E2k): the store its `authStore` field
holds, with `authApplyRes` in the environment's mode. -/
def srvAuthApplyRes (s : Loc) (E : apply.AEnv GF) : IProp GF :=
  iprop(∃ stl : Loc, structFieldRef go_etcd_io.etcd.server.v3.etcdserver.EtcdServer go!"authStore" s ↦□
    (auth.authIface stl) ∗ authApplyRes E.authMode stl)

end defs

end EtcdGrove
end Perennial
