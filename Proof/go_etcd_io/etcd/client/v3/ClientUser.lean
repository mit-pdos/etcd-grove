/-
**C1: a user client's attempts carry its user's token** (the auth plan's C1, 2026-10-28;
`notes/c1-plan.md`). Lean-first (no Rocq counterpart).

A client built with a user name dials with its token bundle's per-RPC credentials, whose tokens
are `""` or meet `P` (`tokenBundleInv`, `tokMdOk`); grpc sends each attempt the credentials'
metadata before the context's (`grpcAttemptMd`), so the token the handler sees (`auth.mdTokenOf`,
what the server's `AuthInfoFromCtx` reads) is one meeting `P`, trimmed of `"Bearer "`, or, when
the bundle holds none, the context's own (`attemptTokOk`, `InvClientAuth`). With `P` the server's
issue to the user (`auth.tokIssued γa · u`) that is C1, `userClientAt`.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.KVServiceOn
public import Proof.go_etcd_io.etcd.client.v3.InvClientAuth

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **C1** (the auth plan's C1; E2f's `userAttemptOk` over the attempt's metadata): the handler
of every attempt of a call with the context `ctx` on the connection `conn` sees a token issued to
`u` at the member's names `γa` (trimmed of `"Bearer "`, as the server reads it), or the context's
own (the bundle held none yet, or `Authenticate` answered that auth is off): `attemptTokOk` at the
tokens issued to `u`. -/
def userClientAt (conn : Loc) (γa : auth.AuthNames) (u : GoString) : IProp GF :=
  attemptTokOk conn (fun t => auth.tokIssued γa t u)

instance userClientAt_persistent (conn : Loc) (γa : auth.AuthNames) (u : GoString) :
    Persistent (userClientAt (GF := GF) conn γa u) := by
  unfold userClientAt; infer_instance

/-- **C1 for a client `New` built with the user name `u`** (at `clientAuthPre`'s `P` the tokens
`Authenticate` issues to `u`, `authTokReg_of`): its `KV` over a connection whose attempts carry a
token issued to `u` or the context's own. -/
theorem clientTokAt_user (cl : Loc) (eps : List GoString) (γa : auth.AuthNames) (u : GoString) :
    clientTokAt (GF := GF) cl eps (fun t => auth.tokIssued γa t u) ⊢
      ∃ api conn : Loc,
        structFieldRef go_etcd_io.etcd.client.v3.Client go!"KV" cl ↦□
          (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty) #api :
            GoInterface) ∗
        kvObjAtC api conn eps ∗ userClientAt conn γa u := by
  unfold clientTokAt userClientAt
  iintro ⟨%api, %conn, #Hkv, #Hobj, #Htok, -⟩
  iexists api, conn
  iframe Hkv Hobj Htok

end defs

end EtcdGrove
end Perennial
