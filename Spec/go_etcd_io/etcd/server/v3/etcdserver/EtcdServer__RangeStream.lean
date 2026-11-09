/-
## `(*EtcdServer).RangeStream(r, rs)`

**Users.** The gRPC KV handler (`api/v3rpc/key.go:66`, `kvServer.RangeStream`: the stream wrapped in
`headerFillingRangeStream`, after `checkRangeRequest`), whose chunks the client's `GetStream` reads
(W0's `wireStreamAt`, `streamMatches`). Snippet: `examples/specreq/etcdserverreq/kv.go`
(`ReqRangeStream`). Untranslated (names only, with `rangeStream` and `adjustChunkLimit`): an assumed
contract until its body is translated.

**Proof sketch.** `rs.Context()` (2a's sink: the stream's context, `reqPrin` of the principal);
as `Range` up to `doSerialize` (the registry's ticket, the read index, the permission check); `get`
= `rangeStream(ctx, r, rs)`: count-only, one `txn.Range` and one `Send` (the terminal chunk); else
pages of `txn.Range` from the key after the previous page's last (`append(key, 0)`), the first
page's header revision pinned (`r.Revision = headerRev` when `0`: every later page reads the same
revision of the history), each page sent (`rsSink`'s send law: a non-final chunk carries key-values
and no header), the last with the header, `More` and `Count` (`txn.Count` of the rest), sent with the
ticket's `Q` at the first page's state (`streamMatches`); a later page's `ErrCompacted` (the pinned
revision compacted meanwhile) ends the stream with that error and no `Q`. The request message is
rewritten (`r.Limit`, `r.Key`, `r.Revision`).

**Changes.** New (no old spec).

**Margin.** The chunk sizes (`adjustChunkLimit`, `--max-request-bytes`) are not stated.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiReq

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace EtcdServer

open Iris Iris.BI EtcdModel EtcdWire

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **A streamed range**: its pages sent on `rs`, the last with the update's `Q` (`rsSink`, `fin`);
or an error (the first page's answer, fired; a later page's compaction; outcome 2 or 3). -/
def EtcdServer.RangeStream.spec : Prop :=
  ∀ (s : Loc) (γ : Cluster) (who : Principal) (r : Loc) (rm : RangeReq) (rs : GoInterface)
    (Q : State → State → Resp → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ isServer s γ ∗ threadTok ∗ rangeReqOwn r (DFrac.own 1) rm ∗
      ⌜rm.key ≠ [] ∧ rm.validSort⌝ ∗ rsSink rs γ who rm Q [] false ∗
      □ AU <{ ∃∃ (σ : State), etcdState γ σ }> @ ⊤ \ ↑etcdN, ∅
        <{ ∀∀ (σ' : State) (res : Resp), ⌜srvStep who (.range rm) σ σ' res⌝ ∗ etcdState γ σ',
           COMM Q σ σ' res }> }}
    (App (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!! go!"RangeStream")) (Val #r)) (Val #rs))
  {{ (err : GoInterface), RET #err; threadTok ∗ (∃ rm', rangeReqOwn r (DFrac.own 1) rm') ∗
      ∃ ms fin, rsSink rs γ who rm Q ms fin ∗
      ((⌜err = GoInterface.nil ∧ fin = true⌝) ∨
       (⌜ms = [] ∧ fin = false⌝ ∗ ∃ σ σ' e, Q σ σ' (.err e) ∗ ⌜srvErrOf err e⌝) ∨
       ⌜fin = false ∧ (srvErrOf err .compacted ∨ srvUnfired err ∨ srvIndef err)⌝) }}

end spec
end EtcdServer
end EtcdGrove
end Perennial
