/-
**The gRPC services' auth guards** (the auth plan's A2, 2026-10-23; `notes/auth-plan.md`):
`auth.go`'s `AuthAdmin` (the admin and authenticated-user guards over the server's
`AuthGetter`), the guarded wrappers of `maintenance.go` (`authMaintenanceServer`) and `key.go`'s
`kvServer.Compact`. Lean-first (no Rocq counterpart); the tokens and outcomes are the server's
(`etcdserver/AuthGuard.lean`: `adminRes`, `authedRes`, `adminOut`, `authedOut`).

**The objects** (persistent): `authAdminIs aa s E` (the `*AuthAdmin` `aa` whose getter `ag` is
the server `s`, with the server's auth fields `srvAuthAt s E`); `amsIs p ms aa` (the
`*authMaintenanceServer` `p`: its embedded `*maintenanceServer` `ms` and `*AuthAdmin` `aa`).

**A guarded inner call** (`guardedOk2 tok Pin RD f ctx r Q`): the inner method's triple, taken
as a contract (the `maintenanceServer` methods are names only), callable only with the token
`tok ai` of a passing check (for the auth info `ai` the check saw), the caller's `Pin` and the
reader resource `RD`; its answer `Q resp err` with `RD` back. A wrapper's outcome (`guardOut Pin
Q resp err`): the inner call's answer, or `nil` and an error with `Pin` untouched (the guard
refused, through `togRPCError`). So in the mode `on γa` the inner method runs only after a
passing check (the token is the only way to its triple), and with auth off always (`authedOut`:
no refusal; the admin guard's refusal may be `AuthInfoFromCtx`'s error, which `isReqAuth` leaves
free, so `kvServer.Compact`'s and the admin wrappers' specs do not promise it).

**`kvServer.Compact`** (`compactOk`, `compactOut`): the server's `Compact` (the `RaftKV` interface
value the `*kvServer` holds is the server, `kvServerIs`) as a guarded contract, answering as the
KV handlers' contracts do (`kvAnswer`'s shape: a header the handler fills, or an error
`togRPCError` can take); the wrapper fills the header (`kvOut`'s shape).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvKV
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthGuard

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace v3rpc

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.etcdserver

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The `*AuthAdmin` `aa`** (read-only): its getter `ag` is the server `s` (`&AuthAdmin{s}`),
with the server's auth fields. -/
def authAdminIs (aa s : Loc) (E : apply.AEnv GF) : IProp GF :=
  iprop(⌜aa ≠ null⌝ ∗
    structFieldRef go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthAdmin go!"ag" aa ↦□
      (interface.mkOk (go.GoType.PointerType EtcdServer.ty) #s : GoInterface) ∗
    srvAuthAt s E)

instance authAdminIs_persistent (aa s : Loc) (E : apply.AEnv GF) :
    Persistent (authAdminIs aa s E) := by
  unfold authAdminIs; infer_instance

/-- **The `*authMaintenanceServer` `p`** (read-only): its embedded `*maintenanceServer` `ms` and
`*AuthAdmin` `aa` (`NewMaintenanceServer`'s `&authMaintenanceServer{srv, &AuthAdmin{s}}`). -/
def amsIs (p ms aa : Loc) : IProp GF :=
  iprop(⌜p ≠ null⌝ ∗
    structFieldRef go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.authMaintenanceServer
      go!"maintenanceServer" p ↦□ ms ∗
    structFieldRef go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.authMaintenanceServer
      go!"AuthAdmin" p ↦□ aa)

instance amsIs_persistent (p ms aa : Loc) : Persistent (amsIs (GF := GF) p ms aa) := by
  unfold amsIs; infer_instance

/-- **A guarded inner call** `rcv.m(ctx, r)` of the method `m` of the type `t` (see the file
header; the method value is built here, in a definition: `wp_start` rewrites the first `methods`
term of the goal with its `MethodUnfold` instance, and a names-only method has none): its triple
with the token `tok ai` of a passing check, the caller's `Pin` and the reader resource `RD`,
answering `Q resp err`. -/
def guardedOk2 (tok : Option go_etcd_io.etcd.server.v3.auth.AuthInfo → IProp GF)
    (Pin RD : IProp GF) (t : go.GoType) (m : GoString) (rcv : Loc) (ctx : GoInterface) (r : Loc)
    (Q : Loc → GoInterface → IProp GF) : IProp GF :=
  iprop(∀ ai : Option go_etcd_io.etcd.server.v3.auth.AuthInfo,
    {{ Pin ∗ RD ∗ tok ai }} (App (App (Val #(methods t m #rcv)) (Val #ctx)) (Val #r))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); RD ∗ Q resp err }})

instance guardedOk2_persistent (tok : Option go_etcd_io.etcd.server.v3.auth.AuthInfo → IProp GF)
    (Pin RD : IProp GF) (t : go.GoType) (m : GoString) (rcv : Loc) (ctx : GoInterface) (r : Loc)
    (Q : Loc → GoInterface → IProp GF) : Persistent (guardedOk2 tok Pin RD t m rcv ctx r Q) := by
  unfold guardedOk2; infer_instance

/-- **The guarded `ms.Snapshot(sr, srv)`** (`maintenanceServer`'s, a stream handler: it returns an
error only): as `guardedOk2`, answering `Q err`. -/
def guardedSnapOk (tok : Option go_etcd_io.etcd.server.v3.auth.AuthInfo → IProp GF)
    (Pin RD : IProp GF) (ms sr : Loc) (srv : GoInterface) (Q : GoInterface → IProp GF) :
    IProp GF :=
  iprop(∀ ai : Option go_etcd_io.etcd.server.v3.auth.AuthInfo,
    {{ Pin ∗ RD ∗ tok ai }}
      (App (App (Val #(methods
        (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.maintenanceServer.ty)
        go!"Snapshot" #ms)) (Val #sr)) (Val #srv))
    {{ (err : GoInterface), RET #err; RD ∗ Q err }})

instance guardedSnapOk_persistent (tok : Option go_etcd_io.etcd.server.v3.auth.AuthInfo → IProp GF)
    (Pin RD : IProp GF) (ms sr : Loc) (srv : GoInterface) (Q : GoInterface → IProp GF) :
    Persistent (guardedSnapOk tok Pin RD ms sr srv Q) := by
  unfold guardedSnapOk; infer_instance

/-- **A gRPC stream's `Context()`** (`srv.Context()`, the stream `srv` a `grpc.ServerStream`
interface value, names only): the context `ctx`. -/
def streamCtxOk (srv : GoInterface) (ctx : GoInterfaceOk) : IProp GF :=
  iprop(∃ si : GoInterfaceOk, ⌜srv = GoInterface.ok si⌝ ∗
    □ ({{ True }} (App (Val #(methods si.ty go!"Context" si.v)) (Val #()))
      {{ (c : GoInterface), RET #c; ⌜c = GoInterface.ok ctx⌝ }}))

instance streamCtxOk_persistent (srv : GoInterface) (ctx : GoInterfaceOk) :
    Persistent (streamCtxOk (GF := GF) srv ctx) := by
  unfold streamCtxOk; infer_instance

/-- **`ar.GetAction()`** (an `AlarmRequest`'s getter, names only): the action `act`
(`AlarmRequest_GET` is `0`). -/
def alarmActionOk (ar : Loc) (act : w32) : IProp GF :=
  iprop({{ True }} (App (Val (ar @!! go.GoType.PointerType etcdserverpb.AlarmRequest.ty @!!
      go!"GetAction")) (Val #()))
    {{ (a : w32), RET #a; ⌜a = act⌝ }})

instance alarmActionOk_persistent (ar : Loc) (act : w32) :
    Persistent (alarmActionOk (GF := GF) ar act) := by
  unfold alarmActionOk; infer_instance

/-- The token of `Alarm`'s guard: the authenticated-user check for a get (`AlarmRequest_GET`),
the admin check otherwise. -/
def alarmTok (M : auth.AuthMode) (act : w32) :
    Option go_etcd_io.etcd.server.v3.auth.AuthInfo → IProp GF :=
  if act = W32 0 then authedRes M else adminRes M

/-- **A guarded wrapper's outcome**: the inner call's answer, or `nil` and an error with `Pin`
untouched. -/
def guardOut (Pin : IProp GF) (Q : Loc → GoInterface → IProp GF) (resp : Loc)
    (err : GoInterface) : IProp GF :=
  iprop(Q resp err ∨ (⌜resp = null ∧ err ≠ GoInterface.nil⌝ ∗ Pin))

/-- **A guarded stream wrapper's outcome** (`Snapshot`): the inner call's answer, or an error
with `Pin` untouched. -/
def guardOut1 (Pin : IProp GF) (Q : GoInterface → IProp GF) (err : GoInterface) : IProp GF :=
  iprop(Q err ∨ (⌜err ≠ GoInterface.nil⌝ ∗ Pin))

/-- **The server's `Compact`, guarded** (`kvServer.Compact`'s inner call; the file header): with
the token `adminRes` of the request's auth info, the caller's `Pin` and the reader resource,
answering as the KV contracts do: `nil` and a non-null response whose header `hdrW`/`hdrRevIn`
the handler fills, with the caller's `Q resp`; or an error `togRPCError` can take, `nil` response,
with `Q null`. -/
def compactOk (s : Loc) (E : apply.AEnv GF) (A : KVAns GF) (Pin : IProp GF) (ctx : GoInterface)
    (r : Loc) (Q : Loc → IProp GF) : IProp GF :=
  iprop(∀ ai : Option go_etcd_io.etcd.server.v3.auth.AuthInfo,
    {{ Pin ∗ E.RD ∗ adminRes E.authMode ai }}
      (App (App (Val (srvM s go!"Compact")) (Val #ctx)) (Val #r))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); E.RD ∗
        ((⌜err = GoInterface.nil ∧ resp ≠ null⌝ ∗ ∃ (h : Loc) (rv : w64),
            structFieldRef etcdserverpb.CompactionResponse go!"Header" resp ↦□ h ∗ hdrW h ∗
            hdrRevIn A.revR h rv ∗ Q resp) ∨
          (⌜resp = null⌝ ∗ srvErrIs err ∗ Q null)) }})

instance compactOk_persistent (s : Loc) (E : apply.AEnv GF) (A : KVAns GF) (Pin : IProp GF)
    (ctx : GoInterface) (r : Loc) (Q : Loc → IProp GF) :
    Persistent (compactOk s E A Pin ctx r Q) := by
  unfold compactOk; infer_instance

/-- **`kvServer.Compact`'s outcome** (`kvOut`'s shape): the server's response with its header
filled (`cid`, `mid`), or `nil` and a non-nil error (the server's through `togRPCError`, with
`Q null`; or the guard's, with `Pin` untouched). -/
def compactOut (A : KVAns GF) (cid mid : w64) (Pin : IProp GF) (Q : Loc → IProp GF)
    (resp : Loc) (err : GoInterface) : IProp GF :=
  iprop((⌜err = GoInterface.nil ∧ resp ≠ null⌝ ∗ ∃ (h : Loc) (rv rv' : w64),
      structFieldRef etcdserverpb.CompactionResponse go!"Header" resp ↦□ h ∗
      hdrFilled h cid mid ∗ hdrRevOut A.revR h rv rv' ∗ Q resp) ∨
    (⌜resp = null ∧ err ≠ GoInterface.nil⌝ ∗ (Q null ∨ Pin)))

/-- **An error `togRPCError` can take, from the apply package's facts** (`ServerKV.lean`'s
`srvErrIs_of_applyErrIs`, whose module the handlers' specs do not import). -/
theorem srvErrIs_applyErrIs (err : GoInterface) (hne : err ≠ GoInterface.nil) :
    applyErrIs (GF := GF) err ⊢ srvErrIs err := by
  iintro #H
  iunfold srvErrIs
  isplitr
  · ipureintro; exact hne
  isplitr
  · iexact H
  ihave #Hkm : iprop(errKeyMsg err) $$ []
  · iunfold applyErrIs at H; icases H with ⟨-, #Hkm⟩; iexact Hkm
  iunfold errKeyMsg at Hkm
  icases Hkm with (%Hn | ⟨%Hsafe, %ei, %Hei, #Hm⟩)
  · exact absurd Hn hne
  isplitr
  · ipureintro; exact Hsafe
  iexists ei
  isplitr
  · ipureintro; exact Hei
  iunfold errMsgOk at Hm
  iexact Hm

end defs

end v3rpc
end EtcdGrove
end Perennial
