/-
The trust boundary: `newSnapshotHandler` (untranslated: the snapshot stream, D22's contract).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.newSnapshotHandler

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **Trust boundary** (rafthttp stage 6c; the user's choice: the snapshot stream a smaller axiom,
cut at its own functions; D22 S-i's contract, which `Transport.Start`'s axiom stated): the
handler (`http.go:182-330`) is an `*snapshotHandler` of the transport's logger and id, `r`, `ss` and
`cid`, as an `http.Handler`. Its `ServeHTTP` of a request routed to `/raft/snapshot`:
* off `POST`, `405`; else it sets `X-Etcd-Cluster-ID` (not `X-Server-Version`: `verHdrOk`), checks
  the cluster headers (`412`), calls `addRemoteFromRequest` (the premise), decodes the envelope
  (a fresh `raftpb.Message`, `400` on an error) and refuses any other type than `MsgSnap` (`400`);
* it saves the rest of the body with `ss.SaveDBFrom(body, index)` (`snap/db.go:37-90`; `500` on an
  error, calling nothing), whose ghost steps on the directory (`snapDirInv`) are `Start`'s axiom's:
  at the rename, the index added to `M` with the file (a complete stream of the sender's reader:
  the body is chunked, the exact-size reader `NewMessage` wraps errors on a short or long stream)
  and to `E`; nothing at a kept file; so `snapSaved γd i` (`netSnapRecv`);
* then it calls `Process` (borrowing `R`, as `netRaftOk` allows) with the message: a POST to the
  snapshot path is a snapshot sender's (`snapReq`, the protocol's; (D42, stage 7b) its body a
  stream of the contract `snapSReq`, the handler's `reqBody`), whose envelope is a message a started transport was given by `SendSnapshot` for
  the member owning `a`, with its bundle (`netRecv`: its one-shot part, withdrawn once, by the
  request's ticket); on an error, a `writerToResponse`'s status (etcd's `Process` makes `403`,
  for a removed member, none here) or `500`; else `204`.
None of its statuses is `410` (no member is removed) or `200`: the protocol's (`raftProto`) other
clauses do not constrain a snapshot response. It does not panic (its envelope decode's limit and
`humanize`'s formatting do not), and returns its writer committed with `R` (and `T`) back. -/
axiom rafthttp.newSnapshotHandler.wp_proof : rafthttp.newSnapshotHandler.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
