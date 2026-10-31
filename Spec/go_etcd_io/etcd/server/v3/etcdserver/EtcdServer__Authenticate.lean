/-
`s.Authenticate(ctx, r)` (`v3_server.go`): the read index (`s.read.LinearizableReadNotify`), then,
until the auth store's revision is the one the password was checked at, `CheckPassword(r.Name,
r.Password)`, `GenTokenPrefix()` and `raftRequest` on `&pb.InternalRaftRequest{Authenticate:
&pb.InternalAuthenticateRequest{Name: r.Name, SimpleToken: st}}`; a `defer` clears `r.Password`.
Lean-first (no Rocq counterpart); C1's A4 (2026-10-31, `notes/c1-plan.md`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AdminOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ReadOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthnStore

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

/-- **`s.Authenticate(ctx, r)` with auth on at the names `γa`**, for the request `r` (not nil) with
the user name `name` (read-only) and its password owned (the `defer` writes it), the server's auth
store `ast` (its `authStore` field, read-only) whose `Authenticate` side meets `authnStoreOk` at
the server's reader resource `E.RD`; with the server's views in the mode `on` (`isServerReqM`,
`isServerReadM`), an id per round of the retry loop (`□ |==> idCred`), a certificate of the index
log, and the run's reader slots (of `s.leadTimeMu`, `s.lgMu`, the read loop's lock, and `E.RD`),
which come back. The password field owned, cleared on success; the error one the gRPC layer can
take (`applyErrIs`); on `nil` an `*AuthenticateResponse` whose token was issued to `name`
(`auth.tokIssued`). The premise `E.authMode = .on γa` is a scope restriction, not one the code
needs (with auth off `CheckPassword` returns `ErrAuthNotEnabled`): the store's contract
`authnStoreOk` is had only with auth on (`notes/decisions.md`, "C1's A4"). -/
abbrev EtcdServer.Authenticate.spec : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (γa : auth.AuthNames)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (ast : GoInterfaceOk)
    (r : Loc) (name pw : GoString) (F : mvcc.Log),
  E.authMode = .on γa →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerReqM true s E ρ ∗ isServerReadM true s E γr ∗
      structFieldRef EtcdServer go!"authStore" s ↦□ GoInterface.ok ast ∗
      authnStoreOk (GoInterface.ok ast) E.RD ∗
      □ (|==> idCred ρ.ids 1) ∗ mvcc.idxCert E.γ.idx F ∗ context.isContext ctx cd ∗
      ⌜r ≠ null⌝ ∗ structFieldRef etcdserverpb.AuthenticateRequest go!"Name" r ↦□ name ∗
      structFieldRef etcdserverpb.AuthenticateRequest go!"Password" r ↦ pw ∗
      srvLeadTimeReader s ∗ srvLgReader s ∗ srvReadReader s γr ∗ E.RD }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"Authenticate"))
      (Val #(GoInterface.ok ctx))) (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
      srvLeadTimeReader s ∗ srvLgReader s ∗ srvReadReader s γr ∗ E.RD ∗
      (∃ pw' : GoString, structFieldRef etcdserverpb.AuthenticateRequest go!"Password" r ↦ pw' ∗
        ⌜err = GoInterface.nil → pw' = []⌝) ∗
      applyErrIs err ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ v : etcdserverpb.AuthenticateResponse,
          resp ↦ v ∗ auth.tokIssued γa v.Token' name) ∨
       ⌜resp = null ∧ err ≠ GoInterface.nil⌝) }}

end spec

end EtcdGrove
end Perennial
