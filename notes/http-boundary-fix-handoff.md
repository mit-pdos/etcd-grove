# http-boundary-fix handoff (etcd-grove-81's fix agent, 2026-11-14)

Branch `http-boundary-fix` (worktree `/shared/etcd-grove-auth3`, off `lean` `e6bde9edae`).

## Done

- Finding 1 (a replayed `GET` runs its handler twice, each run with the one exclusive ticket):
  `http.onceOnly`/`noIdemKey`/`reqTicketOnce` (`Proof/net/http/Boundary.lean`); `handlerOk` and
  `handlerFor` give a run `reqTicketOnce R γk`. rafthttp: `pipeReq`/`snapReq` carry
  `http.noIdemKey R.hdr` (the senders prove it: `createPostRequest`'s and `setPeerURLsHeader`'s posts
  strengthened), the pipeline and snapshot handlers get the ticket from `onceOnly_post`, the stream
  handler's spec takes `reqTicketOnce` (unused).
- Finding 2 (a status Go's server made): `http.srvStatuses`, `http.Proto.srvOk`; `http.reserve` takes
  `P.srvOk`; `raftProto_srvOk` (`Stream.lean`) discharges it in `TransportState.lean`.
- The coordinator's addition: the connect clause of `addrsUnclaimed`/`addrUnclaimed`
  (`Proof/runtime/Start.lean`), `netAddrFree`/`netListenerAt` (`Proof/net/InvNet.lean`),
  `net.Listen.wp_proof` (`Proof/net/Listen.lean`), `grpcRepliesFit`'s remark; docs only.
- Docs: `notes/grpc-stream-spec.md` §6 and line 76, `InvGrpcStream.lean`'s "only when".
- Go evidence: `examples/premisefix/{httpreplay,httpsrvstatus,foreignconn}` (pass at go1.27.1 and
  `GOTOOLCHAIN=go1.27.3`).
- Self-review: `notes/axiom-review/http-boundary-fix.md` (survives; the proxy gap found, open).
- Ledger: `notes/specs-only/ledger.md` 2026-11-14 (the plan's `roundTripperOk`, same defect 2).

## Next

Coordinator's review of the trusted-text diff, then `etc/land.sh` on its go. The
`ProxyFromEnvironment` gap is closed: `netAddrLit` loopback only (`examples/premisefix/httpproxy`).

## Build

`flock /shared/tmp/etcd-grove-build.lock systemd-run --scope -q -p MemoryMax=64G lake
--packages=/shared/tmp/manifest-ddc.json build`.

## Later the same day

- `netAddrLit` loopback only (etcd-grove-81's decision; `examples/premisefix/httpproxy`).
- The auth triage's `issues/etcd-v3election-shared-watch-wrong-user.md` (etcd#17502) and
  `nonissues/etcd-auth-corrupt-bucket-startup-panic.md` (etcd#22747); the matrix and Defs
  docstrings corrected.
- The independent review's fixes (`notes/axiom-review/http-boundary-fix.md`, last section): the
  closed-world clause in two parts, `raftProto`'s stream branch `streamPfx`, `respHdrsOk`,
  `reqHdrView`, `Flush_spec` committed-only.
- Next: the coordinator's review of `/shared/tmp/coord-81/http-boundary-fix/*.diff`, then
  `etc/land.sh` on its go.
