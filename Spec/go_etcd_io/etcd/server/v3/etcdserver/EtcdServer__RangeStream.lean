/-
## `(*EtcdServer).RangeStream(r, rs)`

**Users.** The gRPC KV handler (`api/v3rpc/key.go:66`, `kvServer.RangeStream`: the stream wrapped in
`headerFillingRangeStream`, after `checkRangeStreamRequest`: a valid sort, the default order, no
revision filters, a key), whose chunks the client's `GetStream` reads (W0's `wireStreamAt`,
`streamMatches`). Snippet: 2a's `examples/specreq/v3rpc/kv.go` (through the gRPC client).
Untranslated (names only, with `rangeStream` and `adjustChunkLimit`): an assumed contract until its
body is translated.

**Proof sketch.** `rs.Context()` (2a's sink: the stream's context, `reqPrin` of `p`, `tls`); as
`Range` up to `doSerialize` (the registry's ticket, the read index, the permission check at `kp`);
`get` = `rangeStream(ctx, r, rs)`: count-only, one `txn.Range` and one `Send`; else pages of
`txn.Range` from the key after the previous page's last (`append(key, 0)`: correct under
`rangeStreamOk`), the first page's header revision pinned (`r.Revision = headerRev`: every later page
reads the same revision of the history), each page sent as read (`rsSink`'s send: no `Q` with a
chunk), the last with the header, `More` and `Count` (`txn.Count` of the rest at the pinned revision).
After `get`, `doSerialize`'s revision re-check: unchanged, `nil`, and the ticket at the first page's
point (whose permission the unchanged revision confirms) gives `Q` with `streamMatches`; changed,
`ErrAuthOldRevision` **after every chunk was sent** (`nonissues/etcd-rangestream-auth-revoked-
midstream.md`: keys read after a revocation may have reached the client). A later page's (or the
count's) `ErrCompacted`, the pinned revision compacted meanwhile, ends the stream with that error and
no `Q`, possibly with no chunk sent (`nonissues/etcd-rangestream-count-compacted.md`). The request
message is rewritten (`r.Limit`, `r.Key`, `r.Revision`).

**Changes.** New (no old spec). Round 1: `Q` given with the `nil` return, not with the last chunk
(the code sends the last chunk before it knows the permission held: provability F2); the
`ErrAuthOldRevision`-after-sends and the compaction-with-no-chunk outcomes; `rangeStreamOk`.
Integration X: the scope premise `EtcdServerPb.endsDecoded` (the request decoded by protobuf: its
range ends `nil` or non-empty, `nonissues/etcd-auth-empty-range-end-point-check.md`; I5's request;
2a's handler has it from grpc's decoder, `Proto.decodedAt` and `endsDecoded_of_decoded`; a caller that
builds its range request, `endsDecoded_range_intro`).

**Margin.** The chunk sizes (`adjustChunkLimit`, `--max-request-bytes`) are not stated.

Changes: verify-round, second pass (grpc-v3rpc's request): `rsSink_send`'s new premise, no chunk sent so far has a header, holds: only the last chunk (`done`, or the count-only one, sent alone) sets `Header`, after which `rangeStream` returns. `endsDecoded` is now a share of the request message with the pure `endsOk` fact (2a's handler: `endsDecoded_of_canon` at a decoded message, `Proto.norm c = c`).
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

/-- **A streamed range**: its pages sent on `rs`; `nil` with the update's `Q` of the whole answer
(`streamMatches`); or an error: the first page's answer (fired, nothing sent), a stale auth revision
after the sends (no `Q`), a compaction of the pinned revision (no `Q`), outcomes 2 and 3. -/
def EtcdServer.RangeStream.spec : Prop :=
  ∀ (s : Loc) (γ : Cluster) (q : Qp) (p tls : Principal) (lo : Nat) (r : Loc) (rm : RangeReq)
    (rs : GoInterface) (Q : State → State → Resp → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ isServer s γ ∗ srvGate s q ∗ threadTok ∗ rangeReqOwn r (DFrac.own 1) rm ∗
      EtcdServerPb.endsDecoded go_etcd_io.etcd.api.v3.etcdserverpb.RangeRequest.ty r ∗
      ⌜rm.key ≠ [] ∧ rm.validSort ∧ rangeStreamOk rm⌝ ∗ rsSink rs γ p tls rm [] ∗ authLb γ lo ∗
      □ AU <{ ∃∃ (σ : State), etcdState γ σ }> @ ⊤ \ ↑etcdN, ∅
        <{ ∀∀ (σ' : State) (res : Resp), ⌜srvStep p tls (.range rm) σ σ' res lo⌝ ∗ etcdState γ σ',
           COMM Q σ σ' res }> }}
    (App (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!! go!"RangeStream")) (Val #r)) (Val #rs))
  {{ (err : GoInterface), RET #err; srvGate s q ∗ threadTok ∗ (∃ rm', rangeReqOwn r (DFrac.own 1) rm') ∗
      ∃ ms, rsSink rs γ p tls rm ms ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ σ σ' rev a, Q σ σ' (.ok (.range rev a)) ∗
          ⌜ClientV3.streamMatches rm ms rev a⌝) ∨
       (⌜ms = []⌝ ∗ ∃ σ σ' e, Q σ σ' (.err e) ∗ srvErr err e ∗ srvErrShape err) ∨
       ((srvErr err .authOldRevision ∨ srvErr err .compacted ∨ srvUnfired err ∨ srvIndef err) ∗
          srvErrShape err)) }}

end spec
end EtcdServer
end EtcdGrove
end Perennial
