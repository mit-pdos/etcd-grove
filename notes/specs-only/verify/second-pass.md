# Second pass: requests to groups that had already finished (coordinator's list)

- rafthttp: decoders deliver msgRecv via raftpb's `msgRecv_intro.spec`; vars_init docstring (server-boot S4);
  the snapshot handler supplies SaveDBFrom's two updates (server-boot); cite ID.String_ptr / URLs pointer
  specs (client-core).
- backend-schema: `AuthBackend.lean` with authBackendAt_intro/_elim and authBeHook_intro (lease-auth);
  `beCrash` allows a backend file whose rename onto the path was not yet synced (server-boot); delete the
  `beSnap` alias once server-core uses `beSnapN`.
- mvcc: `wStep` states, outside the exactFrom guard, that each event is a kept history event with key in
  the watcher's range and modRevision its revision (client-watch); `ctxErr_not_errIs` and `rrOwn`'s
  `kvFits` (apply-txn).
- server-boot: electionServer.Observe spec once grpc-v3rpc gives the stream vocabulary; restate the hooks
  over 4a's contract once server-core says what cindex gives; ID.String_ptr / URLs pointer specs, three-view
  deniedSince, Context.Value (client-core).
- client-users: GetStream takes no thread token; KV triples take `emptyEnd = false`; callErr_errorsNew has an
  io.EOF disjunct; ctxPrin_todo is an entailment (client-core). Recipes' Dequeue may drop the exactFrom gate
  on the read path now that watchStep's in-range clause is unconditional (client-watch).
- lease-auth: the AuthReach law in auth/Api.lean (client-core).
- From server-core (its report has the exact edits): apply-txn — ApiResult lines 100/126 to `srvErr`, txn/Api
  comment, authnIdx conditional on the entry being applied, drop "provisional" on handles applyLent_opts
  introduces; lease-auth — WithRoot's post gives a value-child at the metadata key, TimeToLiveHTTP's decoded
  reply has a non-nil header; server-boot — check RaftCluster.Version / compactable_intro gate / membership
  sentinel encoding / SetVersion notifier against server-core's citations; mvcc — align Mvcc.init's sentinels
  with server-core's `sentinelAt`; then delete the deprecated srvErrOf/srvErrVal once nothing uses them.
- From grpc-v3rpc (its report has details): server-core — RangeStream meets rsSink_send's new no-header premise,
  sketches citing endsDecoded updated; apply-txn — realize endsDecoded/opsDecoded with 3h's read-only form,
  persistent stringerOk → stringerAt; client-core — W0 compact denial accepts adminDenied at two auth tables,
  connOk intro/elim laws, AttemptTriple/uiOk_call carry reqRight, otelgrpc handlers give statsOk, a clientConnOk
  law giving c.conn, stale retryKVClient__RangeStream note, Sprintf("%+v") triple; raft-conf-pb, backend-schema,
  lease-auth, mvcc, server-boot — each message relation gets a law that its model survives `Proto.norm`
  (cf. holds_norm); server-boot — NewElectionServer Users line, Observe spec (vocabulary now exists).
- From bbolt: backend-schema — Durable.lean starts a fresh path through `boltFresh_alloc`, boltCrash's new
  "no file, named = false, empty" case; sketches citing Tx.Commit use the nested `commitAU` shape;
  backend__Defrag's cited laws now exist (cite boltRelease etc.); boltOpenOptions' value as their own
  assumed fact (no keyed-literal spec).
- raft-core: confirm the split raftState_crash is in the tree (server-core reports citing "the current one").
- open-questions (coordinator): 1.13 now true (client-users); resolver race decision (b); new decisions in
  every repair-*.md.
