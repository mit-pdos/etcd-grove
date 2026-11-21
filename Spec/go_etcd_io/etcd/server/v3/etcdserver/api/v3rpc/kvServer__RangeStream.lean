/-
`v3rpc.kvServer.RangeStream` (`key.go`): the KV service's streamed range, over the server's
`RangeStream` with the stream wrapped to fill each chunk's header. Lean-first (no Rocq counterpart);
auth-mediation M3 (2026-11-21), row 2 of `etc/auth-table.txt`; the vocabulary is
`v3rpc/RangeStreamOut.lean` and `etcdserver/RangeStreamDefs.lean`. (`SpecPlan`'s statement is over the
gRPC stream protocol's vocabulary, `rangeStreamSpec`, which this tree does not have yet.)
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.RangeStreamOut
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__RangeStream

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.api go_etcd_io.etcd.server.v3.etcdserver
  go_etcd_io.etcd.api.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **`kvServer.RangeStream(r, rs)`** of the range `o`, on the `*kvServer` `p` of the server `s`
(`kvServerIs`), in the environment's auth mode (`E.authOn`, at a mode other than `.any`), with the
server's resources as `EtcdServer.RangeStream.spec`'s (the request owned, `rangeRequestOwn`; a read
call's resources, `srvRdCall`; the stream's context `ctx`, `rangeStreamCtx`), on the stream `rs`
whose `Send` is a contract (`streamSendOk rs Ψ Ξ`, its errors ones `togRPCError` takes).

**Every chunk it sends passed the check** (auth-mediation M3): `Send`'s precondition `Ψ resp` is
given, through the caller's `□ (∀ resp, rangeChunkOut o cid mid resp -∗ rangeStreamPassed s E n tok o
-∗ Ψ resp)`, for a chunk of `o`'s range with its header `nil` or filled (`rangeChunkOut`) and the
passed check of `o`'s `[key, end)` at a state no older than `n` (`rangeStreamPassed`, what
`EtcdServer.RangeStream` states; the check is made once, before the first page:
`nonissues/etcd-rangestream-auth-revoked-midstream.md`).

It returns `checkRangeStreamRequest`'s error (the `rpctypes` variable `rangeCheck` names, or, for a
sort other than the default or a revision filter, `¬ streamOk`, a non-nil error); or `nil`; or what
`togRPCError` made of the server's error `e`: one the gRPC layer takes (`applyErrIs`) with why, if the
auth checks refused it (`rangeWhyOut`), or the error a `Send` returned (`Ξ resp e`). -/
abbrev v3rpc.kvServer.RangeStream.spec : Prop :=
  ∀ (p s : Loc) (A : v3rpc.KVAns GF) (cid mid nt : w64) (E : apply.AEnv GF) (ρ : ReqNames)
    (γr : ReadNames) (c : w64) (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (tok : Option GoString) (r : Loc) (o : OpFull) (rs : GoInterface)
    (Ψ : Loc → IProp GF) (Ξ : Loc → GoInterface → IProp GF)
    (ot : Option Loc) (te : Bool) (n : Nat),
  E.authMode ≠ .any →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
      v3rpc.kvServerIs p s A cid mid nt ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerReqM E.authOn s E ρ ∗ isServerReadM E.authOn s E γr ∗ srvAuthLb s E ∗
      auth.authPubLbM E.authMode n ∗ srvRdCall s E γr c ∗
      rangeStreamCtx rs ctx ∗ context.isContext ctx cd ∗ context.libCtxOk ctx ∗
      □ (⌜E.authOn = true⌝ → auth.ctxToken (GoInterface.ok ctx) tok) ∗
      traceutil.ctxTraceIs ctx ot ∗ traceutil.ownTraceOpt ot te ∗
      rangeRequestOwn r o ∗
      v3rpc.streamSendOk rs Ψ Ξ ∗
      □ (∀ (resp : Loc) (e : GoInterface), ⌜e ≠ GoInterface.nil⌝ -∗ Ξ resp e -∗
          Ξ resp e ∗ v3rpc.srvErrIs e) ∗
      □ (∀ resp : Loc, v3rpc.rangeChunkOut o cid mid resp -∗ rangeStreamPassed s E n tok o -∗
          Ψ resp) }}
    (App (App (Val (p @!! go.GoType.PointerType v3rpc.kvServer.ty @!! go!"RangeStream")) (Val #r))
      (Val #rs))
  {{ (err : GoInterface), RET #err; srvRdCall s E γr c ∗ rangeRequestBack r ∗
      match v3rpc.rangeCheck o with
      | some ce => txn.errVarIs ce.var err
      | none =>
        ⌜¬ v3rpc.streamOk o ∧ err ≠ GoInterface.nil⌝ ∨
        (⌜v3rpc.streamOk o⌝ ∗
          (⌜err = GoInterface.nil⌝ ∨
           (∃ e : GoInterface, ⌜e ≠ GoInterface.nil⌝ ∗ applyErrIs e ∗
              rangeWhyOut s E.authMode n tok o e ∗ v3rpc.grpcErrOut (fun _ => True) e err) ∨
           (∃ (resp : Loc) (e : GoInterface), Ξ resp e ∗
              ((⌜e = GoInterface.nil ∧ err = GoInterface.nil⌝) ∨
               (⌜e ≠ GoInterface.nil⌝ ∗ v3rpc.grpcErrOut (fun _ => True) e err))))) }}

end spec

end EtcdGrove
end Perennial
