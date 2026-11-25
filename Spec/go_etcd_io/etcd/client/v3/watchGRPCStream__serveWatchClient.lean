/-
`(*clientv3.watchGRPCStream).serveWatchClient(wc)` (`client/v3/watch.go`; (the watch slice's unit W-C). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvWatch

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3 go_etcd_io.etcd.cache.v3 client

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- `w.serveWatchClient(wc)` on the client end of a gRPC watch stream with its receiver's token:
forwards every response it receives, in order, on `respc` (the producer's side, D25: for the
epoch `e` of `run` whose stream it serves, from the epoch's first position `b`; the `k`th element
is the stream's `(k - b)`th response, `respcE`, the epoch's count bumped past it), until the
receive fails (its error to `errc`, with the producer's side back, `errP`) or the stream is done
(`donec`). The stream's specification is at the token `tok` its metadata carried (G2,
2026-10-30). Since phase 7's switch (SW1, 2026-11-24, R2): at the member and the metadata each
response tells (`streamDispIs`, `watchMdW`), which the response's element of `respc` carries; until
then fixed when the stream was opened and recorded by the epoch. -/
abbrev watchGRPCStream.serveWatchClient.spec : Prop :=
  ∀ (V : WEnv GF) (G : WgsPrm GF) (callSl : GoSlice) (wc : GoInterface) (γs : StreamNames)
    (Dn : GoString → GrpcMd → Nat → v3rpc.WatchRespM → IProp GF)
    (cd' : context.ContextDesc (IProp GF)) (e : Nat) (γc : GName) (sent : List Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ levelTok 0 ∗ (isWGS V G callSl ∗
      v3rpc.cliWatchStreamIs wc γs (watchUpW V) (watchMdW V G.omd) Dn cd' ∗
      □ (∀ a md, watchMdW V G.omd a md -∗
        v3rpc.watchSpec (V.memOf a) (V.memWOf a) (auth.mdTokenOf md) γs (Dn a md)) ∗
      cliRecvTok (Rep := v3rpc.pbWatchResponse) γs [] ∗
      monoListIdxOwn G.γep e ((γs, sent.length, γc) : EpInfo) ∗ sspscProducer G.γr sent ∗
      monoNatAuthOwn γc 1 sent.length) }}
    (App (Val (G.wgs @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.watchGRPCStream.ty @!! go!"serveWatchClient")) (Val #wc))
  {{ RET #(); levelTok 0 ∗ (True) }}

end spec

end EtcdGrove
end Perennial
