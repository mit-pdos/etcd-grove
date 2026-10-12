/-
`s.Range(ctx, r)` (`v3_server.go`): a linearizable (unless `Serializable`) read of the KV, through `doSerialize`.
Lean-first (no Rocq counterpart); the request path's unit 3b (2026-10-12).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRead

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`s.Range(ctx, r)`**, any goroutine, at a context, for a range request `r` holding `o` with
a valid sort target, with a read call's resources (`srvRdCall`: the store's reader slots, the
logger's, the committed index `c` the caller knew of): success, the txn package's answer at a
certified log of at least two revisions, after the read index unless serializable, the header's
id fields owned (`rangeReadOk`); failure, no response and an error the gRPC layer can take (the
read loop's, the auth store's, mvcc's `ErrFutureRev`, or the context's: `fmt.Errorf`'s in
Perennial's model, `applyErrIs` by the server's package facts). -/
abbrev EtcdServer.Range.spec : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (c : w64)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (r : Loc) (o : OpFull),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerReq s E ρ ∗ isServerRead s E γr ∗ srvRdCall s E γr c ∗ context.isContext ctx cd ∗
      txn.rangeRequestIs r o ∗ ⌜txn.validSortTarget o⌝ }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"Range"))
      (Val #(GoInterface.ok ctx))) (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); srvRdCall s E γr c ∗
      ((⌜err = GoInterface.nil ∧ resp ≠ null⌝ ∗ rangeReadOk E γr c o resp) ∨
       (⌜resp = null ∧ err ≠ GoInterface.nil⌝ ∗ applyErrIs err)) }}

end spec

end EtcdGrove
end Perennial
