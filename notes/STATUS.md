# Status (Lean port)

**Last updated:** 2026-10-25 (auth E2d, branch `auth-e2d`: the client's write path with refusing members is the persistent-update case, no new spec; `clientv3.New` with a user name and password -- `client/v3/credentials`' bundle translated and proved, grpc's per-RPC credentials option, `Close` after a failed token fetch; +2 axioms, `Client.Close` and `grpc.WithPerRPCCredentials`; "E2d of the auth plan" in `notes/decisions.md`); 2026-10-25 (auth E2c, branch `auth-e2c`: `AuthInfoFromCtx`'s binding names the request context's own token (`auth.ctxTokenOf` over `metadata.incomingOf`; `ctxBound`, `principalBound`, the guards' bound variants take the context), a token issued to one user (`tokIssued_agree`) and of the simple shape (`tokIssued_shape`, the bad token issued to no one); trust base unchanged; "E2c of the auth plan" in `notes/decisions.md`); 2026-10-25 (auth S4f, decided by the user (option (b)): the history's authority split between the admin side and the backend's batch lock, the backend's write contract (`authBatchTxLkR`, `authWBackendOkR`) stated without the admin side's authority and the store's view derived (`authBatchTxLk_of_R`), `NewAuthStore`/`Recover` over it, what D22 discharges restated, `authHistHalf_lookup` (the history pinned while the admin side holds its half); trust base unchanged; "S4f of the auth plan" in `notes/decisions.md`); 2026-10-25 (auth E2a, branch `auth-e2a`: `NewAuthStore` and `setupMetricsReporter` translated (bcrypt's cost bounds), the reporter's lock a package fact; `auth.newAuthStore_on` proved -- the constructor in the mode `on γa` over the store's backend contracts, giving `authInv`, `authWR`, `tpAdmin`, the authority and the readers' slots; `NewAuthStore.spec` stays an axiom; no provisional schema axioms: the auth buckets are D22's tracked buckets, and S4's `Lock` contract is not derivable in the mode `on`; trust base +1 (bcrypt's `opaqueInitsOk`); "E2a of the auth plan" in `notes/decisions.md`); 2026-10-25 (auth E2b, branch `auth-e2b`: `examples/authkv`, the end-to-end auth example -- one member with the simple token provider, auth set up and enabled, four principals inside and outside the granted range, `Main` panics if the server let a principal do what the auth state does not permit -- tested (also `-race`) and translated; `Main`'s triple stated, its proof a `sorry` (+1 sorry); `Permitted` and the model's verdict at the set-up's state proved; the client's auth side a contract (C1-C4) and the server-side facts the proof needs recorded; "E2b of the auth plan" in `notes/decisions.md`); 2026-10-25 (T-M M2a, branch `membership-m2`: `StartNode`/`Bootstrap` in the dynamic mode, a new cluster's boot log there (its conf entries need no commit-fact witness; `raft_dyn_alloc_boot`), trust base unchanged; M2 done); 2026-10-25 (T-M M2b and M2c, branch `membership-m2`: raft's dynamic mode with pre-vote on and `StepDownOnRemoval` off, as etcd configures it; `RestartNode`'s two premises gone, trust base unchanged); 2026-10-25 (clean-up merged into `lean`, branch `cleanup/2026-10-24`: 252 unused declarations removed, main tree and witness part; the static `ownRaftPhys` a sealed alias of `ownRaftPhysC`, `ownTracker`/`ApplyCCOk`/`SwitchOk` gone; net -2,554 lines, no exported statement changed, trust base unchanged; "Clean-up: unused declarations, the static `ownRaftPhys` an alias"); 2026-10-25 (auth S5e, branch `auth-s5e`: the simple token provider with no hypothesis -- the TTL keeper's `run` proved (`keeper_run`, `auth/TokenKeeperRun.lean`; the tick `simpleTokenTTLResolution` appended to the auth package's fact), `newTokenProviderSimple` proved (`tokenSimple_new`), the provider meeting the contract with `info`'s context premise (`tokenProviderOkCtx`, `tokenSimple_okCtx`); trust base unchanged; "S5e of the auth plan" in `notes/decisions.md`); 2026-10-25 (`notes/membership-plan.md` written: track T-M planned; D43, its scope); 2026-10-25 (auth S5d in part, branch `auth-s5d`: the token provider's `enable`/`disable`/`invalidateUser` take the admin side's share (`tokenProviderOkA`, `tpAdmin`), the simple provider proved to meet the contract (`tokenSimple_okA`, `auth/TokenSimpleAdmin.lean`) over `ValidSpec` and the keeper goroutine's `RunSpec`, hypotheses; trust base unchanged); 2026-10-25 (D22's three `snap` statements of stage 7 settled by the user for the D22 owner, `notes/decisions.md`, D42); 2026-10-25 (rafthttp stage 7f, branch `rafthttp-snap`: stage 7 linked and checked, every collection unchanged by it but `server`, `linkv3p` and `putget3`; 712 axioms, 4 `sorry`s, with `lean` merged in at Perennial `24bef275e`); 2026-10-25 (rafthttp stage 7e, branch `rafthttp-snap`: the snapshot handler proved (`newSnapshotHandler`, `snapshotHandler.ServeHTTP`), its axiom gone; new trust items `fmt.SprintfArgs` (the user's choice), `(*time.Duration).String`, the streamed body's `bodyStreamRead_ok`/`ReadFull_stream_ok`, and `SaveDBFrom` (D22's, pending its owner); 717 trust-base entries); 2026-10-24 (Perennial pin `9f296e8cc`: `wp_auto` simplifies with `Lean.Meta.Sym.simp`, the largest proofs 10-35% faster, results unchanged; "Build performance"); 2026-10-24 (rafthttp stage 7d, branch `rafthttp-snap`: the snapshot sender proved (`createSnapBody`, `post`, `send`, `peer.sendSnap`, `Transport.SendSnapshot`), its three axioms gone; new trust items the user chose (`respReadAny`, `netErr`), `io.MultiReader`, the snapshot metrics' facts, and two `snap` statements pending the D22 owner; 713 trust-base entries); 2026-10-24 (rafthttp stage 7c: the snapshot sender, its handler, `SendSnapshot` and `peer.sendSnap` translated with bodies, `ReaderAndCloser`'s promoted `Read`/`Close`; the axioms stand until 7d/7e); 2026-10-24 (rafthttp stage 7b drafted: the HTTP boundary's streamed request bodies (`Proto.streamed`/`sreq`, `reqBody`, `bodyStream`, `streamReaderOk`), `snapReq` and `snapSReq` defined, `io.MultiReader`'s spec, three `snap` statements for the D22 owner (`Message` fields, `CloseWithError`, `SaveDBFrom`); the stage 4-6 proofs adjusted; trust base unchanged; 7a: D42 (A) chosen by the user; `notes/rafthttp-plan.md`, "Stage 7"); 2026-10-24 (auth E1 in part, branch `auth-e1`: the token binding at the server's guards -- bound variants of `EtcdServer.AuthInfoFromCtx`, `checkMembershipOperationPermission`, `requireAuthInfo`, `AuthAdmin.isPermitted`/`requireAuthInfo`, the maintenance server's `requireAuthInfo` and `isWatchPermitted`, over the store's bound contract as a premise (`srvAuthBound`, `etcdserver/AuthBound.lean`, `v3rpc/GuardBound.lean`, `v3rpc/WatchBound.lean`); `NewAuthStore` not proved (schema's auth write side over D22's buckets, `authInv`'s allocation); trust base unchanged; "E1 of the auth plan" in `notes/decisions.md`); 2026-10-24 (auth S4c, branch `auth-s4c`: the decoded user and role messages are the caller's -- `proto.UnmarshalUser`/`UnmarshalRole` return `ownUserX`/`ownRoleX` (their slices owned with capacity; no axiom added, 617), schema's reads return them, the batch transaction's contract gains the owned write-side reads; `UserGrantRole` proved as the model's step at the store and the apply layer (`apply_UserGrantRole_step`), `HasRole` proved; `RoleGrantPermission`, `UserGet`, `RoleGet`, the lists left; "S4c of the auth plan" in `notes/decisions.md`); 2026-10-24 (auth S5b in part, branch `auth-s5b`: the simple token provider's `info` and `assign` keep the token binding (`auth/TokenSimple.lean`: `tokenSimple_info`, `tokenSimple_assign`, `tokenSimple_assignToUser`, over the lock invariant `simpleLk`; `isValidSimpleToken` a hypothesis, Perennial has no `strconv`); the token contract's `assign` takes an `Authenticate` context (`authnCtx`: index, prefix and the right to issue the token, `tokFresh` under the new `AuthNames.fresh`); trust base unchanged at 617 axioms; "S5b of the auth plan, in part" in `notes/decisions.md`); 2026-10-24 (merge of `rafthttp-plan` into `lean`: rafthttp's stages 1-6f with lean's D22 receiver epochs, auth, k8s etcd3 and client work; the examples on lean's shared `common` start-up with 6d's resources (`netDirOk`, `netHttpOk`, the transport's key and token, the serve resources, the peer addresses' protocol rights; `memberBuilt`'s `served` flag, `memberUp`'s `srvPeerCtl`, `alloc3` reserving the peer addresses); `path` the etcd project's, with bodies, and k8s's `Join` axiom replaced by a theorem; lean's `zap.Strings`/`strings.TrimSuffix` boundary specs kept, `semver.MustParse.pure` and `strings.TrimSuffix.any` derived for rafthttp; the branch's D33-D36 renumbered D38-D41; baseline 617 -> 696 axioms, 4 sorries (k8s's); `notes/rafthttp-plan.md`); 2026-10-24 (rafthttp, stage 6f: rafthttp linked in the server's `Link.lean` (142 entries; `etc/gen-link.py`'s `=` callees for the HTTP boundary's axioms and Perennial's linked `time`/`sync`/`context`/`strings` results), the transport's six temporary axioms now theorems (`TransportSpecs.lean`); `ErrorStringNotWriter` a semantic premise of the results reaching the pipeline handler (the examples' closed theorems take it beside `ErrorStringLeaf`); no `sorry` reached: `http.Request`/`Response`'s `TypeRepr` taken from the translation's type assumptions, not the axiomatized types' `sorry` instances (`Proof/net/http/Boundary.lean`, `notes/perennial-changes.md`); no axiom added; baseline 555 -> 620; `notes/rafthttp-plan.md`); 2026-10-24 (rafthttp, stage 6e: the spec-only helpers proved over their callees (`setPeerURLsHeader`, `createPostRequest`, `checkPostResponse`, `checkStreamSupport`, `checkClusterCompatibilityFromHeader`, with `minClusterVersion` and `checkVersionCompatibility`), not linked; `types.URLs.Len` translated; rafthttp's fact with three errors' cells and `supportedStream`'s; new boundary items accepted by the user (`http.URLStringAny_ok`, `HeaderGetOwnPtr_ok`, `reqURL_ok`, `StatusText_ok`, `supportedStream_init`, `fmt.ErrorfPlain` strengthened); baseline 554 -> 555; `notes/rafthttp-plan.md`); 2026-10-24 (rafthttp, stage 6d, fourth part, D41: the user's two decisions (`swMsgBound_phys`, the `2^50` physical assumption; `netBundle` with raft's `MsgApp` facts and the sender); the transport's specs restated over its proved state and proved over their callees (`TransportSpecs.lean`), axioms until 6f; `RaftHandler` proved, `http.Serve_ok` replaces `net/http.Serve`; `NewServer` adds every other member, freezes the transport, hands out its reader tokens; `bootstrap`'s contract and `NewServer`'s premises stronger (`netDirOk`, `netHttpOk`, the members raft's peers); every example over them (exact directories, peer addresses reserved and served, linkv3p's partitioner with tokens and `PeerPausable`); baseline 552 -> 554, for the user's review; `notes/rafthttp-plan.md`); 2026-10-24 (rafthttp, stage 6d, third part: `Send` borrows the raft loop's resource (the user's choice); the transport's state from `Start` and its methods over it proved (`TransportState.lean`, `TransportFull.lean`), not linked; blocked on `swMsgBound` (a forked goroutine may not panic in Perennial, so the stage-6 choice (3) is not provable) and `netBundle`'s facts for `Send`, decisions for the user; baseline unchanged; `notes/rafthttp-plan.md`); 2026-10-24 (rafthttp, stage 6d, first and second parts: the three subpaths of `RaftPrefix` translated; D40, the handlers' `AddRemote` dead (the sender a recorded peer); not linked; baseline unchanged; `notes/rafthttp-plan.md`); 2026-10-24 (rafthttp, stage 6c, fifth part: `Start`'s boundary specs and the probe accepted by the user; `raftProto` allows the prober's `GET` and has an opaque snapshot-request clause (`snapReq`); `Handler` proved over the four handlers and the mux (`newPipelineHandler`, `newStreamHandler` proved; for review: the mux's three specs as axioms, `probing.NewHandler`, `newSnapshotHandler`); premises until 6d: two prefixes' values, the handlers' `AddRemote` returning; not linked; `notes/rafthttp-plan.md`); 2026-10-23 (rafthttp, stage 6c, fourth part: the third part's boundary items accepted by the user; `Start` proved field by field over four new boundary specs (`newStreamRoundTripper`, `NewRoundTripper`, `probing.NewProber`, `rate.Every`), not linked; `Handler` left; baseline unchanged; `notes/rafthttp-plan.md`); 2026-10-23 (rafthttp, stage 6c, first to third parts: the transport's lock invariant, `Get`, `Send`, `CutPeer`, `MendPeer`, `AddPeer`, `AddRemote`, `Stop` proved over it, not linked; `Start` and `Handler` left; for review: `ServerStats.SendAppendReq`, `PeerPausable`, `addPeerToProber`, `zap.Strings`, `rttSec_init`, `http.CloseIdleConnections_ok`, `probing.proberOk`; baseline 550 -> 552; `notes/rafthttp-plan.md`); 2026-10-23 (rafthttp, stage 6b done: the peer (`send`, `pick`, `Pause`, `Resume`, `stop`) and the remote (`startRemote`, `send`, `stop`) proved over `peerMsg`/`pipeMsg`; the 6b boundary specs accepted by the user; not linked; `notes/rafthttp-plan.md`); 2026-10-23 (rafthttp, stage 6a/6b, second part: `netRaftOk`'s report calls take no `R`; the transport's and peers' definitions (`trFixed`, `peerOk`, `peerStop`); `newURLPicker`, `newPeerStatus`, `startPeer` proved; boundary specs for review: `types.NewURLs`, `rate.NewLimiter`, `LeaderStats.Follower`, `newSnapshotSender`, `snapshotSender.stop`; not linked; `notes/rafthttp-plan.md`); 2026-10-23 (rafthttp, stage 6a, first part: D39 (`notes/decisions.md`): an address's protocol fixed before its listener (D39a, accepted by the user: program start also gives `httpProtoFree`, `http.reserve` a new axiom, `register` takes its token; the start axiom's statement changed), `NetNames` carries the streams' registry and `netRh` takes a host's owner from the directory, no `410` (`netRaftOk`'s `IsIDRemoved` is `false`; `raftProto` excludes it); the `R` re-budget for 6d; `notes/rafthttp-plan.md`); 2026-10-23 (rafthttp, stage 5f, accepted by the user: every boundary spec the stage-5 proofs take is an axiom (`respWrite_ok`, `ReadFull_resp_ok`, `RespCloseAny_ok` added), the stage's trust items listed together; trust check: `MinClusterVersion_init` new, baseline 549 -> 550; stage 6 scoped, the user's four decisions: the snapshot stream a smaller axiom, no `410` (`IsIDRemoved` false), `Counter.Add` may panic for `swMsgBound`, the prober an axiom; `notes/rafthttp-plan.md`); 2026-10-23 (rafthttp, stage 5e-3: `streamReader.dial` proved (no panic on a member's `X-Server-Version`), with `serverVersion`, `compareMajorMinorVersion`, `reportCriticalError`; `checkStreamSupport` and `setPeerURLsHeader` specs only; boundary items accepted by the user (`semver.New`/`Major`/`Minor`, `GracefulClose`, `TrimSuffix`, `ErrorfPlain`, `RoundTrip`'s `respCloser`, `MinClusterVersion_init`), and on the way, also accepted: `NewRequest_ok`, `URLString_ok` (on the pointer), `readerHas_nil`, `HeaderSetPtr_ok`, `reqRest` over the request's fields but its headers; not linked until stage 6; `notes/rafthttp-plan.md`); 2026-10-23 (rafthttp, stage 5e-2: `streamHandler.ServeHTTP`, the close notifier and `peer.attachOutgoingConn` proved, not linked until stage 6; boundary items accepted by the user: `types.IDFromString` (an axiom), `version.Version`'s value and `semverValid_simple` (an axiom); for review in 5f: `http.HeaderGetPtr_ok`; `notes/rafthttp-plan.md`); 2026-10-23 (rafthttp, stage 5e-1, accepted by the user: the HTTP boundary's response headers: `canonKey` defined (Go's `CanonicalMIMEHeaderKey`), the protocol's `rhdr` (raft's: `X-Server-Version` unset or parses), a writer's header map lent before the commit and checked at it, what the client sees of them, a handler returning its writer (`handlerDone`); the pipeline's proofs adapted; not reached by a linked result; `notes/rafthttp-plan.md`); 2026-10-23 (rafthttp, stage 5d: Go's `path` proved against models of its code (`Clean` with its lazy buffer, `Join`, `Split`, `Base`, `Dir`, `bytealg.LastIndexByteString`; `Proof/path/`), the stream path's lemmas (`Join` builds it, `Base`/`Dir` recover the reader's id and the endpoint; `Proof/path/Segs.lean`, `Stream.lean`), `types.idStr` (`ID.String`'s hex rendering; the boundary spec now names it, accepted by the user), `streamType.endpoint` proved; not linked until stage 6; `dial` waits for the response-header model, a decision for the user; `notes/rafthttp-plan.md`); 2026-10-23 (rafthttp, stage 5c: the stream reader proved over its callees' specs (`streamReader.decodeLoop`, `run`, `start`, `stop`, `close`, `pause`, `resume`; `rafthttp/Reader.lean`, `ReaderRun.lean`), not linked until stage 6; `dial` spec only: no panic, which its proof needs the response's headers in the HTTP boundary for (a design question for 5e); for review (5f): `http.errStrOk` also says an error is of a well-formed error tree (what `errors.Is` needs), `transport.IsClosedConnError` and `rate.Limiter.Wait` (axioms, not reached), `errUnsupportedStreamType` in rafthttp's `errorsNewVarsInit`; `notes/rafthttp-plan.md`); 2026-10-23 (rafthttp, stage 5b: the stream writer proved over its callees' specs (`streamWriter.run`, `close`, `closeUnlocked`, `writec`, `attach`, `stop`, `startStreamWriter`, `newMsgAppV2Encoder`; `rafthttp/Writer.lean`, `WriterRun.lean`), not linked until stage 6; `ConnReadTimeout` translated; `linkHeartbeatSize_init` (a new init axiom, accepted by the user, baseline 548 -> 549); for review: the open premise `swMsgBound` (a queued message encodes below `2^50` bytes); `notes/rafthttp-plan.md`); 2026-10-23 (rafthttp, stage 5 scoped and 5a done: the streams' protocol (`rafthttp/Stream.lean`: frame chains, a registry of connections under the request's ticket, per-frame deposits withdrawn with the reader's tokens; D38d, accepted by the user), `raftProto`'s stream part; no axiom, baseline 548; `notes/rafthttp-plan.md`); 2026-10-23 (rafthttp, stage 4e, D38c, accepted by the user with all of stage 4's trust items: an address's protocol registered once from its listener (`http.register`), so the HTTP boundary's specs are sound for any `HttpNet`; the eleven specs the proofs use are axioms (`Proof/net/http/Axioms.lean`), three over-claims fixed on review (`NewRequest` and a host `url.Parse` rejects, `WriteHeader`/`http.Error`'s status range); not reached by a linked result, baseline 548 unchanged; `notes/rafthttp-plan.md`); 2026-10-23 (rafthttp, stage 4d: the sender proved over its callees' specs, not linked until stage 6: `pipeline.post`, `handle`, `start`, `stop`, the URL picker, `peerStatus.activate`/`deactivate`, `isMsgApp`/`isMsgSnap`, and a local join `Add(4)` (`WaitGroupAdd.lean`, a Perennial gap, `notes/perennial-changes.md`); pending the user's acceptance at 4e: `fmt.SprintfID` and `FollowerStats.Fail` (axioms, not reached), `activePeers_init` and `disconnectedPeers_init` (reached through rafthttp's initializer; accepted by the user, baseline 546 -> 548); `createPostRequest`, `checkPostResponse`, `checkClusterCompatibilityFromHeader` specs only; `notes/rafthttp-plan.md`); 2026-10-23 (rafthttp, stage 4a-4c: request tickets, the mailbox (`Pipe.lean`), `pipelineHandler.ServeHTTP` proved; rafthttp's four metric-vector inits accepted, baseline 542 -> 546); 2026-10-22 (rafthttp, stage 3, what the encoders need of a sent message: no responses, for every message raft queues in every mode (`XfOk`, `isRaftMsg`, `raft.send`'s premise, `raft.Step`'s for a forwarded request, `NetMsgOk`), and a `MsgApp` from its sender (`AppFrom`, the node's id in `XfOk`, `isRaftMsg`, `NodeNames`); protobuf-go keeps undeclared enum values (a Go test), so `MsgMarshals` drops its enum bounds and no entry-type invariant is needed; `Send` takes messages with no responses and `Process` gets copies with none (`Net.lean`); the server's sender id stays existential until stage 6; no axiom added, baseline 542; D38a; `notes/rafthttp-plan.md`); 2026-10-22 (rafthttp, stage 3, the msgappv2 pair: `msgAppV2Encoder.encode` and `msgAppV2Decoder.decode` proved over a frame model (`rafthttp/MsgAppV2.lean`); `proto.MarshalOptions` translated; a finding, `issues/etcd-rafthttp-msgappv2-unbounded-lengths.md`; five new boundary axioms, accepted by the user (`proto.ClonePb`, `proto.MarshalAppendPb`, `pbEnc_ok`, `FollowerStats.Succ`, `linkHeartbeatMessage_init`), one reached by a linked result, baseline 542; `notes/rafthttp-plan.md`); 2026-10-22 (rafthttp, stage 3: raft's `SentMsgOk` gains the `MsgApp` shape (`AppShape`: no vote, rejection, hint, snapshot, context or responses), a premise of `raft.send` that `maybeSendAppend` proves, for msgappv2's short frame (D38a, option (a)); no closed statement changed, trust base unchanged); 2026-10-22 (rafthttp, stage 3, the simple codec: `messageEncoder.encode` and `messageDecoder.decodeLimit` proved over generic protobuf specs at the bytes (D38a: `PbType`, as grpc's `ProtoMsg`), `pbutil.MustMarshalMessage` translated and proved; msgappv2's MsgApp shape to go into the sender's promise (option (a)); six new boundary axioms (three `proto`, three `encoding/binary`) not yet reached by a linked result, and rafthttp's `errorsNewVarsInit`, reached through the package initializers: baseline 541; accepted by the user; `notes/rafthttp-plan.md`); 2026-10-22 (rafthttp, stage 1: D38 (A) approved; the message path translated with bodies (90 functions), no proof yet, no statement changed; trust base +2 init axioms (`path`, `pkg/v3/ioutil`), 539, accepted by the user; stage 2's HTTP boundary reviewed (`notes/rafthttp-http-boundary.md`), `path` translated with bodies, the boundary drafted in Lean (`Proof/net/http/Boundary.lean`, statements only); trust base +1 (`internal/bytealg`'s `init()` assumed to run, `initFuncsOk`: 540, accepted by the user); the rest of the boundary drafted (headers, `http.Error`, routing, `url.URL.String`, `encoding/binary`), statements only, for review; `notes/rafthttp-plan.md`); 2026-10-22 (rafthttp plan, stage 0: the inventory and a bytes-level HTTP boundary with a mailbox invariant proposed as D38, awaiting approval; nothing proved; `notes/rafthttp-plan.md`); 2026-10-24 (auth S4b, branch `auth-s4b`: the Perennial pin at `beb785eaf` (`sort.SearchStrings`, `sort.Strings`), `hasRootRole` translated and proved (S3's axiom gone: 617 axioms), `UserRevokeRole`, `RoleRevokePermission`, `RoleDelete` proved as model steps and added to `apply.isAuthSteps`; the grants left, they write into the read side's messages; "S4b of the auth plan" in `notes/decisions.md`); 2026-10-24 (auth S5 in part, branch `auth-s5`: the token binding -- `AuthNames.tok` and `tokIssued` (`auth/Tokens.lean`), the token provider's contract in the mode (`tokenProviderOk tp M`: an accepted token's info bound to it, `assign` issuing one), `authInfoFromToken`/`AuthInfoFromCtx` carrying it (`ctxBound`), the server's `isReqAuthBound` derived from the real store; `Authenticate` proved over the write side's `GetUser`; the no-op provider meets the contract; +2 axioms (zap's `Logger.Check`, zapcore's `CheckedEntry.Write`), 618; `issues/etcd-auth-simple-token-assign-prefix-panic.md`; "S5 of the auth plan, in part" in `notes/decisions.md`); 2026-10-24 (restore R6, branch `restore-r6`: the restore plan closed; the R4a decision (`store.restore` takes `s.revMu` as a caller-given lock protocol, `revLockW`/`revUnlockW`) in `notes/decisions.md`; the fingerprint check over the trust report: no closed theorem's text changed, and the server-based examples' `*_safe` theorems reach R5a's clean-view flag only through `bootstrap`'s contract (`backend.newPost`), true of `bootstrap` at the pin; trust base unchanged, 614 axioms; `notes/restore-plan.md`, R6); 2026-10-24 (auth S4's apply part, branch `auth-a5`: `apply.isAuthSteps` (`apply/AuthSteps.lean`), the auth store's six proved admin operations as model steps with the store's write resource abstracted, derived of the real store (`auth_apply_steps`, `etcdserver/Results.lean`); `applierV3backend.{AuthEnable, AuthDisable, UserAdd, UserDelete, UserChangePassword, RoleAdd}` perform the model's step on the latest recorded state or the model's refusal (`apply_*_step`); no axiom added, no closed theorem changed; the authority is not yet in the server's environment, whose workload admits no auth request; "S4's apply part" in `notes/decisions.md`); 2026-10-24 (auth S4 in part, branch `auth-s4`: the admin operations as steps of the model's state (`auth/Steps.lean`: `Outcome`, the step functions and relations, `adminOut`, the authority `authOwn`), the latest state a ghost variable shared by the authority and the revision invariant (`AuthNames` now `hist`/`cur`), the write side's contract (`authBatchTxLk`, `authWR`, `enabled` split in halves); `AuthEnable`, `AuthDisable`, `UserAdd`, `UserDelete`, `UserChangePassword`, `RoleAdd`, `Recover`, `commitRevision`, `setRevision` proved and linked; +2 trust-boundary axioms (`authStore.selectPassword`, `zap.Strings`); the grants and revocations, `RoleDelete`, the reads and the apply layer's admin clauses left; `notes/decisions.md`, "S4 of the auth plan"); 2026-10-24 (restore R5e-R5f, branch `restore-r5e`: `mvcc.store.Restore.wp_proof` a theorem (614 axioms) over `restore`'s spec and the ghost moves of `RestoreMoves.lean` (`restore_takeover`, `restore_switch`, `restore_finish`); the writer's invariant's restoring state without its eighth of `cur` and with half the history's authority (`writerInvBody`), the readers' pool counting retired tickets (`StoreNames.tkr`; `writerOwn` holds one, so `k + 1 ≤ nReaders`), `restore`'s unlock given the restored log's receipt bound; `notes/restore-plan.md`, R5e-R5f); 2026-10-24 (auth A3, the API layer, branch `auth-a3b`: the Auth service's seventeen gRPC wrappers (`v3rpc/AuthServer__*.lean`, over the server's methods as contracts, `InvAuthServer.lean`; `NewAuthServer` now gives `authServerIs`) and fourteen of its seventeen entry points (`etcdserver/EtcdServer__AuthEnable.lean`, ..., over `raftRequest` as the contract `authRaftOk`, `AuthEntry.lean`: `reqPropOk` admits no auth request); `Authenticate` translated, unproved (`auth.ErrAuthNotEnabled` has no package fact), `UserAdd`/`UserChangePassword` names only (bcrypt, base64); `AuthenticateRequest`/`AuthUserChangePasswordRequest` as data; Lock/Election not started; trust base unchanged; `notes/decisions.md`, "A3 of the auth plan, the API layer"); 2026-10-24 (auth A4, branch `auth-a4`: the watch service's request shapes -- a created response's watcher carries its registration's authorization (`v3rpc.watchAuthed` in `ctrlWatcher`: `apply.watchClass` of the request's normalized key and raw range end, in the server's auth mode, which the watchable store's new owner tag names, `mvcc.WsNames.tag`/`auth.modeTag`, so the stream specification's arity is unchanged), and every key the registered range covers is in the interval the check saw for every shape (`v3rpc/WatchClass.lean`, `createRangeOk_inRange`: what GHSA-xg4h-6gfc-h4m8 broke); the result `watch_registered_authorized`; no axiom; `notes/decisions.md`, "A4 of the auth plan"); 2026-10-24 (restore R5d, branch `restore-r5d`: `newTreeIndex`'s spec takes the event count's authority at any `n` and a fresh compactor state with the compaction revision's and the committed log's lower bounds (so `store.Restore`'s new index keeps the store's history, log and compaction names, `idx_renew`); `NewStore` splits its fresh names, `idxFresh_split`; trust base unchanged); 2026-10-24 (auth S2b, branch `auth-s2b`: the interval tree's proof generic in the key representation `adt.KeyRep` (`Defs.lean`: the `Comparable`'s type, "the value holds the key" at a fraction, the comparison contract `CompareOk`), the node's key fields as atoms (`ivAt`, `maxAt`), the exported functions' generic results `<fn>_gen` with string-affine (`ownIvt`) and bytes-affine (`ownIvtB`) wrappers, the internal specs generalized in place; S2's three axioms are the linked `wp_Insert_bytes`/`wp_Intersects_bytes`/`wp_Contains_bytes`; `Contains` proved for both (`visit` re-proved for a stopping visitor and a degenerate query, the holes predicate over explicit lent lists); 615 axioms; "S2b of the auth plan" in `notes/decisions.md`); 2026-10-24 (auth A3, the apply layer, branch `auth-a3`: the request's principal `principalOf rq` is an index of the chain's resources (`chainRes c a info`; the mutex holds the zero `AuthInfo`), the KV methods' posts state the request's class for it through the chain (`chainClass`, `reqClass`) up to `dispatch`, `uberApplier.Apply` and the package's `Apply` (`applyAuthRes`: the class with `shouldApplyV3` and `Apply`'s admin check passed, `adminPass`); `authApplierV3.{Put, DeleteRange, Range, Txn}` at the method level, `UserGet`'s self-or-admin case; `Results.lean`'s `chain_*` carry the class; trust base unchanged, no closed statement changes; `notes/decisions.md`, "A3 of the auth plan, the apply layer"); 2026-10-24 (auth S3, branch `auth-s3`: the store's checks return the model's verdicts in every mode -- `isOpPermitted` and the `Is*Permitted` `permVerdict`, `IsAdminPermitted` `adminVerdict` over an `Option AuthInfo` (a `nil` pointer covered; `apply.isAuthStore` gains the clause, A2's `srvAdminNilOk` is derivable), `IsAuthEnabled`/`Revision` theirs, from the flag's and the revision's recorded states in `authInv` (`enabledP st M`, `revInv st M`) and S1's/S2's reads (`auth/VerdictLemmas.lean`); `isAuthStore_of_authInv` derives the apply layer's contract in the store's own mode; A0's one-state verdict was unprovable (the four reads are of four states) and is corrected: `permitted` without the revision conjunct, the pass half names a state that permitted and a state whose revision admitted the token, the refused half the view of the four states read (`AuthView`, `refusedV`), the request's shape (`reqShape`) a premise inside the model, recorded states carry `permKeysOk`; `hasRootRole`'s axiom restated to return `isRoot` of a sorted-roles message (Perennial lacks a `sort.SearchStrings` spec, `notes/perennial-changes.md`); trust base unchanged, 618 axioms); 2026-10-23 (restore R5a-R5c, branch `restore-r5`: `store.restore` proved over a bucket with data, the restored log `[[], []] ++ R` (its spec over `R`, `NewStore` at `R = []`): the backend's read buffer known clean (`BNames.cln`, `bViewC`, `rtHeld_clean`; `newPost`'s view clean, so `storage.OpenBackend`'s axiom promises it), the limited range's prefix over it (`keyRangeLimSpec`'s `cl`, `keyCleanRead`), a held read transaction lending a share to a second reader (`rtHeldF`, `rdSplit`), the chunk loop (`RestoreChunks.lean`); trust base unchanged (615 axioms); `store.Restore` (R5d-R5f) next; `notes/restore-plan.md`, "R5's stages"); 2026-10-23 (auth S2, branch `auth-s2`: the permission cache computes the model -- `cacheP st M` holds, in `on γa`, one recorded state whose users are the map's keys and whose permissions' intervals each entry's two bytes-affine trees hold (`permsAt`, `cacheOk`, `cacheEntryIs`); `checkKeyPoint`/`checkKeyInterval` return membership and coverage over the trees' lists, `isRangeOpPermitted` the verdict `cacheVerdict` (the recorded state's `coversPoint`/`coversRange` iff the check passed, a missing user the refusal); `getMergedPerms`, `refreshRangePermCache`, `isValidPermissionRange`, `BytesAffineComparable.Compare` proved; the interval tree's `Contains` given its pure meaning (`adt/Contains.lean`: `containsRes_iff`, the greedy scan is coverage) and `Intersects` of a point membership (`stab_point_iff`); the bytes-affine tree `adt.ownIvtB` with its `Insert`/`Intersects`/`Contains` as **three axioms** pending the tree's generalization to a comparator (plan stage S2b); `notes/decisions.md`, "S2 of the auth plan"); 2026-10-23 (auth A2, branch `auth-a2`: the API layer's auth guards -- `EtcdServer.requireAuthInfo`/`checkMembershipOperationPermission`, `AuthAdmin.isPermitted`/`requireAuthInfo` (and their promotions) proved with the tokens `authedRes`/`adminRes` and outcomes `authedOut`/`adminOut` of `etcdserver/AuthGuard.lean`, and the guarded entry points `kvServer.Compact`, the eight `authMaintenanceServer` wrappers, `EtcdServer.RemoveMember`/`MemberList` proved over their inner operations as token-carrying contracts (`v3rpc/InvAuthAdmin.lean`: `guardedOk2`, `compactOk`; `configureRemoveOk`): 17 functions; `IsAdminPermitted(nil)` a premise (`srvAdminNilOk`); `AddMember`/`UpdateMember`/`promoteMember` not translated (`encoding/json`); trust base unchanged); 2026-10-23 (restore R4 option 1, branch `restore-r4b`: `store.restore` proved for the empty bucket `NewStore` hands it (its spec takes `bucketView γ q ∅`, a reader's token `RT` and `kbNoCmp`); the key backend's contract gains a range read with any limit (`keyRangeLimSpec`, the answer a `Sublist` of the range, proved of the real backend), `metaReadSpec rt nc` and the compaction-key reads' "not found" under `nc`, `keysGauge.Set`; trust base unchanged in count (615 axioms after auth S1): `mvcc.store.restore.wp_proof` gone, `mvcc.kbNoCmp_metaNone` (`NoCmpRead.lean`) added; `restore` with data (R4b's premise, R4d's split token) moved to R5; `notes/restore-plan.md`, "R4's progress" item 4); 2026-10-23 (auth S1, branch `auth-s1`: `authpb` translated as data (`authpb.toml` as `raftpb`'s), schema's auth backend translated with bodies and its read side proved over the buckets -- `unsafeReadAuthEnabled`/`unsafeReadAuthRevision`/`unsafeGetUser`/`unsafeGetRole`, the `authReadTx` wrappers with `RLock`/`RUnlock`, `authBackend.ReadTx`/`GetUser`/`GetRole` (13 functions) against the contracts `authReader`/`authRTx`/`authBE` of `etcdserver/InvAuthBackend.lean`, whose `authBucketsAre st D` says the buckets hold the model's state; the records `auth/Buckets.lean` (`UserRec`, `RoleRec`, `userEncode`/`roleEncode` opaque, `ownUser`/`ownRole`, `userOut`/`roleOut`, `authSnap`); the store's contract `authReadTxOk tx R M` returns the state in the mode `M`, which threads through `authInv`/`authRd`/`beP` and the 13 request-side specs; `schemaInit` gains the auth buckets, key names and `authEnabled`/`authDisabled`; +2 trust-boundary axioms, `proto.Unmarshal` on `authpb.User` and `authpb.Role` (540 axioms, 0 sorries); a finding, `issues/etcd-auth-readtx-getallroles-panics.md`; no closed theorem changed; see "The auth backend's read side (S1)" and `notes/decisions.md`, "S1 of the auth plan"); 2026-10-23 (restore R4 started and R2, branch `restore-r4`: the index private until `restore` makes its lock (`newTreeIndex` returns `ownIdxPriv` and `idxLockG`; `store.restore`'s spec, still an axiom, gives back `isTreeIndex` and takes all of `currentRev`, its half-permission write for an empty log having been unprovable); `NewStore` locks `s.mu` as private memory and makes its invariants after `restore`; `setupMetricsReporter` proved over the reporters' locks (R2); `restore`'s own proof needs three backend-contract extensions (`notes/restore-plan.md`, "R4's progress"); trust base unchanged); 2026-10-23 (auth A1, branch `auth-a1`: the class statement `apply/AuthClass.lean` (`classOk`/`classRes` over A0's verdicts; `putClass`, `deleteClass`, `rangeClass`, `cmpsClass`, `opsClass`/`opClass`, `txnClass`; `authEndOf`, the range end as the auth store reads it), the checks' specs with it (`checkPutAuth`, `checkTxnReqsPermission`, `checkTxnPermission`/`CheckTxnAuth`, `txnPermT`), `doSerialize.spec` with the check's class `C`, `EtcdServer.Range`'s success with `rangeClass`, `isWatchPermitted` with the range's read class; the method-level statement (the principal through `chainRes`) is the follow-up; no closed theorem or trust-base change; `notes/decisions.md`, "A1 of the auth plan"); 2026-10-23 (restore R3, branch `restore-r3`: a generation's `created` is its main revision in the model (the Go field's sub-revision is not a function of the log; `keyIndex.get`, `treeIndex.unsafeGet`/`Get`/`Range` return it unconstrained), sequential specs of a private `RWMutex` (`PlainRWMutex.lean`), `treeIndex.KeyIndex`/`Insert` on a private index (`IdxPriv.lean`), `restoreIntoIndex` proved over the code's fold `idxRestore`, and that fold equal to the log's index for a well-formed log (`idxRestore_logEnts'`, R3b); `notes/restore-plan.md`, "R3's progress"; no closed theorem changed in intent, trust base 538 axioms); 2026-10-23 (auth A0, branch `auth-a0`: the authorization model `auth/Model.lean` (`AuthState`, `permitted`, `adminOk`; the store's history `authHist`/`authStateAt`; the mode `AuthMode` `off`/`any`/`on γa` replacing the boolean, `AEnv.authOn` now `E.authMode.isOn`; the verdicts `permVerdict`/`adminVerdict`/`enabledVerdict`/`revisionVerdict`, two one-directional facts over recorded states, the checks' own TOCTOU), `apply.isAuthStore`/`permCheck2`/`permCheck3` restated over it, the real store derived in `any`, `NewAuthStore`'s axiom in `off`; the matrix `notes/auth-matrix.md` (49 methods, their classes and keys); no closed theorem or trust-base change; see `notes/decisions.md`, "A0 of the auth plan"); 2026-10-23 (auth plan, on `lean`: `notes/auth-plan.md`, specifying and proving etcd's auth/RBAC -- the authorization model first (A0), then the store's checks computing it (S, from `auth/store`, where unit P2 stopped) and every gRPC method enforcing its privilege class (A, PR #22541's matrix as the specification), an auth-enabled closed theorem (E); planned only); 2026-10-23 (k8s-etcd3 merged into `lean`: the Kubernetes etcd3 store's linearizability instance `k8setcd3_safe` (stage 6g of `notes/k8s-etcd3-plan.md`), on the `sorry`s `revRoom`, `clientErr_other`, `client_ctx_field`, `kvIs_ne_null`; the etcd pin `goose-lean-getproph2` `bc9c3868c`; see "Kubernetes' etcd3 storage backend"); 2026-10-23 (restore R1, branch `restore-r1`: `keyIndex.restore`, `keyIndex.restoreTombstone` and `restoreChunk` proved and linked (`notes/restore-plan.md`, "R1's findings"); the planned lemma that `restore` agrees with `put` is false when a key's first put has a non-zero sub-revision (etcd restores `created` with `Sub` 0), a decision for R3; no closed theorem changed, trust base 538 axioms); 2026-10-23 (with-timeout-bg, branch `with-timeout-bg`: the client-timeouts plan's T3 -- Perennial `c25bef57e` proves `WithDeadlineCause`/`WithDeadline`/`WithTimeout` of `Background()` (`wp_WithTimeout_Background`; `propagateCancel`'s spec takes any child of a `Background()` parent), the pin moved to it, the axiom `context.WithTimeoutBackground.wp_proof` is a theorem: 538 axioms, one fewer in the `read`, `server` and every etcd example's collection; the plan finished); 2026-10-23 (restore R0, branch `restore-r0`: `notes/restore-plan.md` R0 done: `store.restore`, `setupMetricsReporter`, `restoreIntoIndex`, `restoreChunk`, `keyIndex.restore`/`restoreTombstone` and `restoreChunkKeys` translated (Goose took them as they are), `restoreChunkKeys`'s value in `mvccInit` (its generated opaque-initializer axiom gone); the two restore axioms unchanged, over translated bodies; no closed theorem changed, trust base 539 axioms); 2026-10-23 (client-timeouts, branch `client-timeouts`: the examples' clients configured as etcd's clients are in practice, `notes/client-timeouts-plan.md` T0 and T1 -- one configuration in `examples/common` with etcdctl's timeouts (`DialTimeout` 2s, `RequestTimeout` 5s, keepalive 2s/6s; `common.NewClients`, linkv3p's `newClient` gone), every unary call in `context.WithTimeout(context.Background(), common.RequestTimeout)` cancelled after the call (ten call sites), the members' keepalive policy on every `common.Serve`; the proofs over the existing `WithTimeoutBackground` axiom through one lemma `client.wp_WithTimeout_bg`; `putget_safe`, `putget3_safe`, `linkvtxn_safe` and `linkv3p_safe` gain the premise `ContextErrsClient`, no conclusion changes, no new axiom (D28's policy axiom in five more collections); linkv3p's `TestFailover` rewritten around request timeouts; see "The examples' clients configured as in practice: request timeouts"); 2026-10-23 (restore plan, branch `restore-plan`: `notes/restore-plan.md`, proving `store.restore` and closing `store.Restore` (two axioms) in stages R0-R6, after checking both specs against the code (they agree; `setupMetricsReporter`'s writes to five package globals are unowned, as `readych` was); planned only); 2026-10-23 (norefusal-kv, branch `norefusal-kv`: `etcd_noRefusal` was false as stated (the Auth service's `UserAdd` of an empty name answers `"etcdserver: user name is empty"` with authentication off); `noRefusalAt` now speaks of the KV service only (`kvMethod`), the attempt contract reads it for KV calls only, the write path names its KV method (D29 amended); no closed theorem changed, trust base 539 axioms); 2026-10-23 (readych-closer, branch `readych-closer`: the axiom `publishV3.spec` closed `s.readych` without owning it (found checking the monitors' and `publishV3`'s specs against the code: the rest match, the hash and downgrade monitors only with their checks off); now `NewServer` allocates `readych` as a broadcast channel (Perennial's idiom, `Q = True`) and hands the right to close it (`srvReadyCloser`) through `Start` to `publishV3`'s goroutine; no closed theorem changed, trust base 539 axioms); 2026-10-23 (D22 receiver epochs, S7f, branch `worktree-agent-a5fae76133d772e18`: the apply protocol's per-backend names: `ApplyNames` split into logical names and the current backend's `ApplyPhys` (a ghost variable `cur`, a registry `reg`, the retired backends' mirrors in `consInv`), `commit_save_au`'s retired case (an old backend's `Close` commits through the shared hooks), the swap `ci_swap_au` at `SetBackend` and the boot allocation `consInv_alloc` proved; `applyAll`'s post and `run`'s loop invariant per backend (`beSucc`, `ApplyBe`); no closed theorem changed, `bootOk`'s text unchanged; trust base unchanged (539 axioms, 0 sorries); see "D22 receiver epochs, S7f"); 2026-10-23 (D22 receiver epochs, S7, branch `worktree-agent-a9f17bc977f014063`: the server's fields and the objects' backends stated truly: `s.uberApply` and half of `s.be` the apply thread's, `bemu` over the current backend's ghost variable `AEnv.γbe`, the write budget and the storage-version monitor's token of the current backend (`srvWTPool E`); `AlarmStore.Recover` translated and proved (over `restore`, a new trust-boundary axiom: 539 axioms, 0 sorries); the alarm store's, auth store's, lessor's and cluster's backend fields half their lock's (the cluster's owned), their users' halves pinning their writes (`alarmApplyOk`, `authApplyOk`, `lessorApplyOk`, `clusterApplyOk`, `srvObjsOn`); `bootOk` restated (the cluster's contract, `HclBe`); the apply protocol's per-backend names designed, not done; see "D22 receiver epochs, S7"); 2026-10-23 (D22 the stored-index window, branch `worktree-agent-abc119190b6e832f9`: a commit's request served by the backend's hooks (`backend.commitReq`, `hooksReq`; `ForceCommit`/`Commit`/`commit`/`unsafeCommit`, `BackendHooks.OnPreCommitUnsafe`, mvcc's `isKeyBackendG` (`Req`) and `store.Commit` carry it), the frozen mode of the apply protocol (`consFrozen`, `commit_freeze_au`, `unfreeze`), the snapshot's observation reading the stored index and the tracked buckets (`srvBeSnapOk_window`); `createMergedSnapshotMessage`'s snapshot resource from the commit's; trust base unchanged (538 axioms, 0 sorries); see "D22 the stored-index window"); 2026-10-23 (D22 the backend over every bucket, branch `worktree-agent-abc119190b6e832f9`: D22c revisited carried out: the backend's model tracks the buckets only the apply thread writes (`BParams.RB`, `rbData`, `rbOwn`), the apply thread holds them at the model of the applied log (`restModel`, `srvRest`), `bkRestAt` derived (`bkRestAt_of_rb`), no determinism axiom; `bootOk` and five trust-boundary specs restated; trust base unchanged (538 axioms, 0 sorries); see "D22 the backend over every bucket"); 2026-10-23 (client-err-cells, branch `client-err-cells`: a client error is no caller's `errors.New` value (D37): `errCellOk` (an `*errorString` among the client's errors holds `"EOF"` or `"context canceled"`), from grpc's invoke and `context.ErrAny` (both trust-boundary statements strengthened, true of Go), through the retry interceptor, `toErr` and the KV calls, into `kvErr` at the end of `client_put/range/delete/txn_any`, the `_st` family and linkvtxn's `txn_Commit_st`; for the Kubernetes driver's sentinels (`errDeleteRejected`, `errUpdateRejected`, `kvErr_ne`); no closed theorem changed, trust base 538 axioms); 2026-10-22 (D22 S-l sender items, branch `worktree-agent-a13029e4d33860881`: a `Ready`'s `MsgSnap` kept owned into `msgSnapC`'s bag (`rnSnapMsg`, `rnMsgR`), `store.Commit` translated and proved (`srvKVCommitOk_of_kv`), the merge's write tokens (`srvWTPool_take_extra`), `rnRtBound_of_rtOk`; the stored-index window designed, not carried out (it needs a hook request through `ForceCommit`); trust base unchanged (538 axioms, 0 sorries); see "D22 S-l sender items"); 2026-10-22 (D22 receiver epochs, S6, branch `worktree-agent-a65035decfc6b261e`: `store.Restore` a true trust-boundary axiom (+1: 538 axioms, 0 sorries), `watchableStore.Restore` proved over it; a restored backend's registration pending in the writer's invariant (`writerReg`, `storeRegd` out of `physOk`); the watch invariant with restoring watchers (`WsState.unsRst`, `chooseAll`'s reset, `syncWatchers`' past-the-log case, the synced watchers' events up to their `minRev`); no closed theorem changed; see "D22 receiver epochs, S6"); 2026-10-22 (dedup-pin, branch `dedup-pin`: the Perennial pin at `f97c83add` (`dedup-lemmas` landed: the points-to halves, `mask_ndot_ne2`, the replicate, fold, list and `GoStringLt` lemmas), the local copies in the client, the cache, the examples and raft deleted; no closed theorem's statement changed, trust base unchanged (537 axioms)); 2026-10-22 (dedup, branch `dedup`: `notes/dedup-plan.md` steps A, B, C5 (i), C7 applied: the exact duplicate lemmas merged into the files their users import, `PutThenGet.lean`'s put/get layer inlined into `ClientPutGet.lean`, the watch facts proved once generic in the model (`watchkv.wkSteps`, `chain_gen`/`prog_step_gen`/`resp_gen`; `resp_wk`, `linkv3p.resp_hist` instances), the `op_simps` simp set for the option models (130 simp lists); C1-C4 and D's generic lemmas on Perennial branch `dedup-lemmas` (`f97c83add`, not landed), the local copies kept until the pin moves; no closed theorem's statement changed, trust base unchanged (537 axioms)); 2026-10-22 (cleanup2 part 2, branch `cleanup2`: the examples' closed theorems through one generic lemma (D36): `examples/common/Adequacy.lean`'s `etcd_adequate` (over `goose_adequacy_start`) and `init_adequate` (over `goose_adequacy`, proposed for Perennial in `notes/perennial-changes.md`), parameterized by the program's initializer and body, the result set and the ghost-state bundle; putget, putget3, linkvtxn, linkv3p (both), watchkv, cachekv, kv, the counter and kvwitness (both) are instances; every `*_adequate`/`*_safe` header byte-identical, fingerprint unchanged, trust base unchanged (537 axioms)); 2026-10-22 (cleanup2 part 1, branch `cleanup2`: the client's KV call results one family (D35): `client_put/range/delete/txn_any` take a floor `F` and a write's update persistent or fired at most once, `client_txn_any` the members' write names; `client_put/get/delete/txn/range_end_to_end` keep their statements and are proved as their instances at one server's addresses (`srvsAt`); `Failover.lean` merged into `client/v3/Results.lean`; dead declarations deleted (`putReplied_ok`, `deleteReplied_ok`, `txnAuOk_of_box`, `head_filter_key`, `client_txn_value(_ro)`, `isEtcdKVE_of_kv`, `isEtcdPutKV_of_kv`, `isEtcdDeleteKV_of_kv`); the client's docstrings about the deleted one-attempt mode rewritten; every closed theorem's statement unchanged (fingerprint), trust base unchanged (537 axioms)); 2026-10-22 (retire-linkv, branch `retire-linkv`: the examples `linkv` and `linkv3` and their closed theorems `linkv_safe`, `linkv3_safe` retired, subsumed by `linkvtxn_safe` and `linkv3p_safe` (D34): their Go packages, Goose projects and translations, Spec/Proof trees, gen-init roots, gen-link modes `--linkv`/`--linkv3` and collections deleted; what linkvtxn and linkv3p used moved to them with names unchanged (`linkvtxn/{Proph,PendModel,TxnModel,TxnModelKV,ModelKV}.lean`, `linkv.kvRaftOf_boot` in `linkvtxn/Boot.lean`, the bundle `linkvGF`/`linkvHeapAt` in `linkv3p/Adequacy.lean`); every remaining closed theorem's statement unchanged, trust base unchanged (537 axioms); their sections were already in status-history.md); 2026-10-22 (example-ports, branch `example-ports`: each example its own TCP ports, so the examples module's `go test -race ./...` runs in parallel, no `-p 1`: linkv to client `127.0.0.1:23871`/peer `23881` (was putget3's `23791`/`23801`), watchkv to `23872`/`23882` (was linkv3p's `23831`/`23841`), cachekv to `23873`/`23883` (was on linkv3p's bridge `23851`); translations regenerated; `linkv_safe`, `watch_safe`, `cache_safe` (and their `*_Main`) change only in the address literals: the `addrsUnclaimed` premise's client address and the URLs of their `premises`' definitions (`peerURL`, `clientURL`, the peer directory); trust base unchanged; D33's last paragraph); 2026-10-22 (examples-module, branch `examples-module`: the etcd examples, `common` and `kv` in one Go module, `examples/go.mod` (module `github.com/mit-pdos/etcd-grove/examples`; import paths and translations unchanged), so a fork-pin bump is one go.mod edit; `kvwitness`, `lintest` and `third_party/{porcupine,bridge}` keep their own; `etc/goose.py --check` now fails if the go.mod replaces of etcd or raft differ from the projects' pins (`GO_MOD_PINS`); its tests run `go test -race -p 1 ./...` (the examples' ports overlap); `etc/verified-code.{py,go}` take a project directory inside a module (its numbers unchanged); no Lean change; D33's last paragraph); 2026-10-22 (examples-common, branch `examples-common`: the examples' shared Go code in one package, `examples/common` (D33), translated and proved once: the one-member start (`StartServer`), a cluster member's (`NewMember`, `StartMember`), the gRPC service (`Serve`, with the caller's ghost step), the client (`NewClient`), the ghost-state allocations (`alloc1`, `alloc3`), the watch workload's `Gen`, `GenAll`, `Writer`, `MaxRev`, `Collect`, `Attempted`, `Check`; 46 example spec/proof files deleted or moved to common; no closed theorem's statement changed, trust base unchanged; see "The examples' shared code"); 2026-10-22 (retry-bound clean-up, branch `retry-bound`: the client's retry-bound tracking (`maxAfter`, `retryOptsMax`, `optApplyMax`'s bound; D21 M6) deleted, `optApplyMax` now `optApplyKeep`; four intermediate specs lose a parameter or conjunct, no closed theorem's statement changed, trust base unchanged; see the clean-up section); 2026-10-22 (Perennial idioms, branch `perennial-idioms`: the synchronous SPSC channel, the thread-token join and `wp_fork_tok_upd` moved to Perennial (landed: the pin `537c426e0`; branch `idioms`, `537c426e0`) and the watch client's local copies deleted; needs that branch until the pin moves; no statement of a closed theorem changed, trust base unchanged; see "Perennial idioms: the watch client's three workarounds upstreamed"); 2026-10-22 (clean-up, branch `cleanup`: the watch client's `closeSubstream`/`run` joined again (CPU 52s -> 7s, 148s -> 131s), the one-attempt client machinery deleted (D31's follow-up), `gen-init.py`'s `CLOSEDCHAN` variant and kv's re-proof of raft's initialization removed; no statement of a closed theorem changed, trust base unchanged; see "Clean-up: the watch client's joins, the one-attempt client, the init variants"); 2026-10-22 (the repository is sorry-free: mvcc's `kvHasher` translated, its `hash.Hash32` field's package `hash` types-only here, so its generated instances are no longer `sorry -- axiomatized type`; trust base 543 axioms, 0 sorries; see "`kvHasher` translated: no sorry left"); 2026-10-22 (client-default: linkv, linkv3, linkvtxn, watchkv and cachekv use etcd's default client configuration, their members refusal-free (`etcd_noRefusal`, D29); one family of client call lemmas in `client/v3/ClientPutGet.lean`; D31; see "The examples' clients"); 2026-10-22 (watches across a cut, W4: `linkv3p_watch_safe`, watchkv's watch workload over linkv3p's partitioned cluster, the watch resumed at any member, its events the cluster's committed history's; no axiom added; see "Watches across a cut"); 2026-10-22 (watches across a cut, W1–W3: D32 carried out; mvcc's progress bound from etcd's own guard, no client start read; the clients' model over the cluster's history; the watch client's epochs at any member of its connection; see "Watches across a cut"); 2026-10-22 (D22 fork fixes: the etcd pin at `goose-lean` `188113160`, the alarm store recovered in place (`8fd98af04`) and a snapshot's older files released by `applySnapshot` after its open (`188113160`), each with its regression test; no proof change, trust base 543 axioms, 2 sorries; see "D22 fork fixes: the snapshot file's release and the alarm store's race"); 2026-10-22 (D22 receiver epochs, S1-S4 of the simplest true `Restore`: the certificate without the index's count, the writer's state out of the batch lock into `writerInv`, the four fields `Restore` writes out of `isStore` into lock-held shares, `s.revMu`'s restoring mode, the readers' pool of the index's slots; S5 (the physical names existential, the writer's fragment) designed, not done; trust base unchanged; see "D22 receiver epochs, S1-S4"); 2026-10-22 (the kv example's snapshot liveness: a `do` whose operation a snapshot covers is answered at the install, from the table of the operations applied, now with each one's answer; `kv_porcupine_safe` unchanged; see "The kv example's snapshot liveness: done"); 2026-10-22 (D22 S-r carried out: snapshots in the kv example, replicas compact and catch up by `MsgSnap`, `kv_porcupine_safe` re-closed with its statement and axioms unchanged; the data certificate `snapDataOk`; see "D22 S-r carried out (proof)"); 2026-10-21 (raft-retarget merged into lean: D22's snapshot track (S-0..S-d4, S-f..S-i, S-g/S-h, the three fork fixes) with lean's proof-perf, init facts, linkv3p/kv and watch-resume work; the etcd pin `goose-lean` `2aed163b1` (both sides' fork commits); lean's six examples ported to the server's D22 contract; trust base 543 axioms, 2 sorries; see "Merge of raft-retarget into lean (D22)"); 2026-10-21 (clean-up, on branch `clean-up`: `etc/dead-decls.py`, about 7,900 lines of unused declarations removed, proposals registered once and proposed any number of times (`prop_register`; `propMulti` gone), the adequacy coverage of the linked results, see "Clean-up"); 2026-10-21 (read retries: linkv3p's clients have the default retries, so a read held by a cut is retried on the next member, while a write is still sent at most once: the members are refusal-free; D29, 2 axioms; see "Read retries"); 2026-10-21 (keepalive: the client's configuration may enable gRPC keepalive, linkv3p's clients do and its members accept the pings, failover on a silent partition; D28, 2 axioms; see "Keepalive and failover on a silent partition"); 2026-10-21 (client-member cuts in linkv3p, K0, K1, K3: `linkv3p_safe` re-closed with client-member cuts through a copy of etcd's bridge, part of the network (D26: 5 trust-boundary axioms, its code not verified), a finding (`issues/nonissues/etcd-bridge-blackhole-twice-panic.md`); older entries: `notes/status-history.md`, "Last updated entries (all 164, until 2026-10-22)".; 2026-10-22 (v2stats's `NewLeaderStats` translated and proved, no longer an axiom; `ServerStats`'s three (`NewServerStats`, `BecomeLeader`, `RecvAppendReq`) stay axioms, its type has an anonymous struct field Goose does not translate; trust base 537 axioms, 0 sorries; see "The FIFO scheduler proved"); 2026-10-22 (the FIFO scheduler proved: `pkg/v3/schedule`'s `fifo` translated with its body, `NewFIFOScheduler`, `Scheduler.Schedule` and `Scheduler.Stop` no longer axioms, nor mvcc's `store.Close` and `store.HashStorage` (translated); trust base 538 axioms, 0 sorries; see "The FIFO scheduler proved"); 2026-10-22 (D22 receiver epochs, S5 of the simplest true `Restore`, branch `worktree-agent-ab03038efa73b7686`: the readers' backend tokens in the readers' pool (the apply thread's and the storage-version monitor's retired readers), the store's current objects and physical names a fractional ghost variable shared by the locks' shares (`γ.cur`, `PhysNames`, `γ.withPhys`), the physical facts out of `isStore`, the read transactions at the names their share pins, the writer's fragment in `hookIs`/`txn.kvWriter`; no closed theorem changed, trust base unchanged (537 axioms, 0 sorries); see "D22 receiver epochs, S1-S5"); 2026-10-22 (build performance, branch `perf/2026-10-22` merged into `lean`: the costliest tactic searches cut, about 16 CPU minutes; see "Build performance (2026-10-22)"); 2026-10-22 (v2stats's `NewLeaderStats` translated and proved, no longer an axiom; `ServerStats`'s three (`NewServerStats`, `BecomeLeader`, `RecvAppendReq`) stay axioms, its type has an anonymous struct field Goose does not translate; trust base 537 axioms, 0 sorries; see "The FIFO scheduler proved"); 2026-10-22 (the FIFO scheduler proved: `pkg/v3/schedule`'s `fifo` translated with its body, `NewFIFOScheduler`, `Scheduler.Schedule` and `Scheduler.Stop` no longer axioms, nor mvcc's `store.Close` and `store.HashStorage` (translated); trust base 538 axioms, 0 sorries; see "The FIFO scheduler proved"); 2026-10-22 (retry-bound clean-up, branch `retry-bound`: the client's retry-bound tracking (`maxAfter`, `retryOptsMax`, `optApplyMax`'s bound; D21 M6) deleted, `optApplyMax` now `optApplyKeep`; four intermediate specs lose a parameter or conjunct, no closed theorem's statement changed, trust base unchanged; see the clean-up section); 2026-10-22 (Perennial idioms, branch `perennial-idioms`: the synchronous SPSC channel, the thread-token join and `wp_fork_tok_upd` moved to Perennial (landed: the pin `537c426e0`; branch `idioms`, `537c426e0`) and the watch client's local copies deleted; needs that branch until the pin moves; no statement of a closed theorem changed, trust base unchanged; see "Perennial idioms: the watch client's three workarounds upstreamed"); 2026-10-22 (clean-up, branch `cleanup`: the watch client's `closeSubstream`/`run` joined again (CPU 52s -> 7s, 148s -> 131s), the one-attempt client machinery deleted (D31's follow-up), `gen-init.py`'s `CLOSEDCHAN` variant and kv's re-proof of raft's initialization removed; no statement of a closed theorem changed, trust base unchanged; see "Clean-up: the watch client's joins, the one-attempt client, the init variants"); 2026-10-22 (the repository is sorry-free: mvcc's `kvHasher` translated, its `hash.Hash32` field's package `hash` types-only here, so its generated instances are no longer `sorry -- axiomatized type`; trust base 543 axioms, 0 sorries; see "`kvHasher` translated: no sorry left"); 2026-10-22 (client-default: linkv, linkv3, linkvtxn, watchkv and cachekv use etcd's default client configuration, their members refusal-free (`etcd_noRefusal`, D29); one family of client call lemmas in `client/v3/ClientPutGet.lean`; D31; see "The examples' clients"); 2026-10-22 (watches across a cut, W4: `linkv3p_watch_safe`, watchkv's watch workload over linkv3p's partitioned cluster, the watch resumed at any member, its events the cluster's committed history's; no axiom added; see "Watches across a cut"); 2026-10-22 (watches across a cut, W1–W3: D32 carried out; mvcc's progress bound from etcd's own guard, no client start read; the clients' model over the cluster's history; the watch client's epochs at any member of its connection; see "Watches across a cut"); 2026-10-22 (D22 fork fixes: the etcd pin at `goose-lean` `188113160`, the alarm store recovered in place (`8fd98af04`) and a snapshot's older files released by `applySnapshot` after its open (`188113160`), each with its regression test; no proof change, trust base 543 axioms, 2 sorries; see "D22 fork fixes: the snapshot file's release and the alarm store's race"); 2026-10-22 (D22 receiver epochs, S1-S4 of the simplest true `Restore`: the certificate without the index's count, the writer's state out of the batch lock into `writerInv`, the four fields `Restore` writes out of `isStore` into lock-held shares, `s.revMu`'s restoring mode, the readers' pool of the index's slots; S5 (the physical names existential, the writer's fragment) designed, not done; trust base unchanged; see "D22 receiver epochs, S1-S4"); 2026-10-22 (the kv example's snapshot liveness: a `do` whose operation a snapshot covers is answered at the install, from the table of the operations applied, now with each one's answer; `kv_porcupine_safe` unchanged; see "The kv example's snapshot liveness: done"); 2026-10-22 (D22 S-r carried out: snapshots in the kv example, replicas compact and catch up by `MsgSnap`, `kv_porcupine_safe` re-closed with its statement and axioms unchanged; the data certificate `snapDataOk`; see "D22 S-r carried out (proof)"); 2026-10-21 (raft-retarget merged into lean: D22's snapshot track (S-0..S-d4, S-f..S-i, S-g/S-h, the three fork fixes) with lean's proof-perf, init facts, linkv3p/kv and watch-resume work; the etcd pin `goose-lean` `2aed163b1` (both sides' fork commits); lean's six examples ported to the server's D22 contract; trust base 543 axioms, 2 sorries; see "Merge of raft-retarget into lean (D22)"); 2026-10-21 (clean-up, on branch `clean-up`: `etc/dead-decls.py`, about 7,900 lines of unused declarations removed, proposals registered once and proposed any number of times (`prop_register`; `propMulti` gone), the adequacy coverage of the linked results, see "Clean-up"); 2026-10-21 (read retries: linkv3p's clients have the default retries, so a read held by a cut is retried on the next member, while a write is still sent at most once: the members are refusal-free; D29, 2 axioms; see "Read retries"); 2026-10-21 (keepalive: the client's configuration may enable gRPC keepalive, linkv3p's clients do and its members accept the pings, failover on a silent partition; D28, 2 axioms; see "Keepalive and failover on a silent partition"); 2026-10-21 (client-member cuts in linkv3p, K0, K1, K3: `linkv3p_safe` re-closed with client-member cuts through a copy of etcd's bridge, part of the network (D26: 5 trust-boundary axioms, its code not verified), a finding (`issues/nonissues/etcd-bridge-blackhole-twice-panic.md`); older entries: `notes/status-history.md`, "Last updated entries (all 164, until 2026-10-22)".; 2026-10-25 (auth S5c in part, branch `auth-s5c`: the pin at Perennial `24bef275e` (`time.Ticker`, `Time.After`, `strconv.ParseUint`), `strconv`'s initializer Perennial's and raft's local `strconv.opaqueInitsOk` gone (695 axioms); `isValidSimpleToken` proved on a context (`tokenSimple_isValid`), `info` on a context without its hypothesis (`tokenSimple_info_ctx`); the keeper and `enable`/`disable`/`invalidateUser` left: a ghost set of keepers and a caller-held share of the keeper field needed; "S5c of the auth plan, in part" in `notes/decisions.md`); 2026-10-24 (auth A3c, branch `auth-a3c`: the Lock and Election services' servers (`etcdserver/api/v3lock`, `v3election`) translated with their messages and proved over the client's `concurrency` package and the server's client as a contract (`lockClientOk`, `unlockKVOk`): `Lock`, `Unlock`, `Campaign`, `Proclaim`, `Leader`, `Resign`; `Observe` and the in-process client `v3client.New` left; the `concurrency` package's initializer proved; trust base unchanged; "A3c of the auth plan: Lock and Election" in `notes/decisions.md`); 2026-10-24 (auth S4e, branch `auth-s4e`: `authpb`'s permission-type name maps translated (`authpb.toml`), its package fact `authpbInit` (`cache/v3/Base.lean`, `etc/gen-init.py`), `auth.typeNamesOk` derived (`typeNamesOk_of_init`) and dropped from `RoleGrantPermission`'s spec and its apply clause; trust base unchanged; "S4e of the auth plan" in `notes/decisions.md`); 2026-10-24 (auth S4d, branch `auth-s4d`: `RoleGrantPermission` performs the model's step at the store and the apply layer -- `sort.Search` at any index (`auth.wp_Search_any`, Perennial's spec needs monotonicity), `permSlice` a sorter by key (`auth.permSlice_isSorter`), the decoded role's count bound in `ownRoleX` (a restatement), `authpb.Permission_Type_name` a premise (`auth.typeNamesOk`); every admin operation of the store proved; trust base unchanged); 2026-10-24 (auth E1 in part, branch `auth-e1`: the token binding at the server's guards -- bound variants of `EtcdServer.AuthInfoFromCtx`, `checkMembershipOperationPermission`, `requireAuthInfo`, `AuthAdmin.isPermitted`/`requireAuthInfo`, the maintenance server's `requireAuthInfo` and `isWatchPermitted`, over the store's bound contract as a premise (`srvAuthBound`, `etcdserver/AuthBound.lean`, `v3rpc/GuardBound.lean`, `v3rpc/WatchBound.lean`); `NewAuthStore` not proved (schema's auth write side over D22's buckets, `authInv`'s allocation); trust base unchanged; "E1 of the auth plan" in `notes/decisions.md`); 2026-10-24 (auth S4c, branch `auth-s4c`: the decoded user and role messages are the caller's -- `proto.UnmarshalUser`/`UnmarshalRole` return `ownUserX`/`ownRoleX` (their slices owned with capacity; no axiom added, 617), schema's reads return them, the batch transaction's contract gains the owned write-side reads; `UserGrantRole` proved as the model's step at the store and the apply layer (`apply_UserGrantRole_step`), `HasRole` proved; `RoleGrantPermission`, `UserGet`, `RoleGet`, the lists left; "S4c of the auth plan" in `notes/decisions.md`); 2026-10-24 (auth S5b in part, branch `auth-s5b`: the simple token provider's `info` and `assign` keep the token binding (`auth/TokenSimple.lean`: `tokenSimple_info`, `tokenSimple_assign`, `tokenSimple_assignToUser`, over the lock invariant `simpleLk`; `isValidSimpleToken` a hypothesis, Perennial has no `strconv`); the token contract's `assign` takes an `Authenticate` context (`authnCtx`: index, prefix and the right to issue the token, `tokFresh` under the new `AuthNames.fresh`); trust base unchanged at 617 axioms; "S5b of the auth plan, in part" in `notes/decisions.md`); 2026-10-24 (merge of `rafthttp-plan` into `lean`: rafthttp's stages 1-6f with lean's D22 receiver epochs, auth, k8s etcd3 and client work; the examples on lean's shared `common` start-up with 6d's resources (`netDirOk`, `netHttpOk`, the transport's key and token, the serve resources, the peer addresses' protocol rights; `memberBuilt`'s `served` flag, `memberUp`'s `srvPeerCtl`, `alloc3` reserving the peer addresses); `path` the etcd project's, with bodies, and k8s's `Join` axiom replaced by a theorem; lean's `zap.Strings`/`strings.TrimSuffix` boundary specs kept, `semver.MustParse.pure` and `strings.TrimSuffix.any` derived for rafthttp; the branch's D33-D36 renumbered D38-D41; baseline 617 -> 696 axioms, 4 sorries (k8s's); `notes/rafthttp-plan.md`); 2026-10-24 (rafthttp, stage 6f: rafthttp linked in the server's `Link.lean` (142 entries; `etc/gen-link.py`'s `=` callees for the HTTP boundary's axioms and Perennial's linked `time`/`sync`/`context`/`strings` results), the transport's six temporary axioms now theorems (`TransportSpecs.lean`); `ErrorStringNotWriter` a semantic premise of the results reaching the pipeline handler (the examples' closed theorems take it beside `ErrorStringLeaf`); no `sorry` reached: `http.Request`/`Response`'s `TypeRepr` taken from the translation's type assumptions, not the axiomatized types' `sorry` instances (`Proof/net/http/Boundary.lean`, `notes/perennial-changes.md`); no axiom added; baseline 555 -> 620; `notes/rafthttp-plan.md`); 2026-10-24 (rafthttp, stage 6e: the spec-only helpers proved over their callees (`setPeerURLsHeader`, `createPostRequest`, `checkPostResponse`, `checkStreamSupport`, `checkClusterCompatibilityFromHeader`, with `minClusterVersion` and `checkVersionCompatibility`), not linked; `types.URLs.Len` translated; rafthttp's fact with three errors' cells and `supportedStream`'s; new boundary items accepted by the user (`http.URLStringAny_ok`, `HeaderGetOwnPtr_ok`, `reqURL_ok`, `StatusText_ok`, `supportedStream_init`, `fmt.ErrorfPlain` strengthened); baseline 554 -> 555; `notes/rafthttp-plan.md`); 2026-10-24 (rafthttp, stage 6d, fourth part, D41: the user's two decisions (`swMsgBound_phys`, the `2^50` physical assumption; `netBundle` with raft's `MsgApp` facts and the sender); the transport's specs restated over its proved state and proved over their callees (`TransportSpecs.lean`), axioms until 6f; `RaftHandler` proved, `http.Serve_ok` replaces `net/http.Serve`; `NewServer` adds every other member, freezes the transport, hands out its reader tokens; `bootstrap`'s contract and `NewServer`'s premises stronger (`netDirOk`, `netHttpOk`, the members raft's peers); every example over them (exact directories, peer addresses reserved and served, linkv3p's partitioner with tokens and `PeerPausable`); baseline 552 -> 554, for the user's review; `notes/rafthttp-plan.md`); 2026-10-24 (rafthttp, stage 6d, third part: `Send` borrows the raft loop's resource (the user's choice); the transport's state from `Start` and its methods over it proved (`TransportState.lean`, `TransportFull.lean`), not linked; blocked on `swMsgBound` (a forked goroutine may not panic in Perennial, so the stage-6 choice (3) is not provable) and `netBundle`'s facts for `Send`, decisions for the user; baseline unchanged; `notes/rafthttp-plan.md`); 2026-10-24 (rafthttp, stage 6d, first and second parts: the three subpaths of `RaftPrefix` translated; D40, the handlers' `AddRemote` dead (the sender a recorded peer); not linked; baseline unchanged; `notes/rafthttp-plan.md`); 2026-10-24 (rafthttp, stage 6c, fifth part: `Start`'s boundary specs and the probe accepted by the user; `raftProto` allows the prober's `GET` and has an opaque snapshot-request clause (`snapReq`); `Handler` proved over the four handlers and the mux (`newPipelineHandler`, `newStreamHandler` proved; for review: the mux's three specs as axioms, `probing.NewHandler`, `newSnapshotHandler`); premises until 6d: two prefixes' values, the handlers' `AddRemote` returning; not linked; `notes/rafthttp-plan.md`); 2026-10-23 (rafthttp, stage 6c, fourth part: the third part's boundary items accepted by the user; `Start` proved field by field over four new boundary specs (`newStreamRoundTripper`, `NewRoundTripper`, `probing.NewProber`, `rate.Every`), not linked; `Handler` left; baseline unchanged; `notes/rafthttp-plan.md`); 2026-10-23 (rafthttp, stage 6c, first to third parts: the transport's lock invariant, `Get`, `Send`, `CutPeer`, `MendPeer`, `AddPeer`, `AddRemote`, `Stop` proved over it, not linked; `Start` and `Handler` left; for review: `ServerStats.SendAppendReq`, `PeerPausable`, `addPeerToProber`, `zap.Strings`, `rttSec_init`, `http.CloseIdleConnections_ok`, `probing.proberOk`; baseline 550 -> 552; `notes/rafthttp-plan.md`); 2026-10-23 (rafthttp, stage 6b done: the peer (`send`, `pick`, `Pause`, `Resume`, `stop`) and the remote (`startRemote`, `send`, `stop`) proved over `peerMsg`/`pipeMsg`; the 6b boundary specs accepted by the user; not linked; `notes/rafthttp-plan.md`); 2026-10-23 (rafthttp, stage 6a/6b, second part: `netRaftOk`'s report calls take no `R`; the transport's and peers' definitions (`trFixed`, `peerOk`, `peerStop`); `newURLPicker`, `newPeerStatus`, `startPeer` proved; boundary specs for review: `types.NewURLs`, `rate.NewLimiter`, `LeaderStats.Follower`, `newSnapshotSender`, `snapshotSender.stop`; not linked; `notes/rafthttp-plan.md`); 2026-10-23 (rafthttp, stage 6a, first part: D39 (`notes/decisions.md`): an address's protocol fixed before its listener (D39a, accepted by the user: program start also gives `httpProtoFree`, `http.reserve` a new axiom, `register` takes its token; the start axiom's statement changed), `NetNames` carries the streams' registry and `netRh` takes a host's owner from the directory, no `410` (`netRaftOk`'s `IsIDRemoved` is `false`; `raftProto` excludes it); the `R` re-budget for 6d; `notes/rafthttp-plan.md`); 2026-10-23 (rafthttp, stage 5f, accepted by the user: every boundary spec the stage-5 proofs take is an axiom (`respWrite_ok`, `ReadFull_resp_ok`, `RespCloseAny_ok` added), the stage's trust items listed together; trust check: `MinClusterVersion_init` new, baseline 549 -> 550; stage 6 scoped, the user's four decisions: the snapshot stream a smaller axiom, no `410` (`IsIDRemoved` false), `Counter.Add` may panic for `swMsgBound`, the prober an axiom; `notes/rafthttp-plan.md`); 2026-10-23 (rafthttp, stage 5e-3: `streamReader.dial` proved (no panic on a member's `X-Server-Version`), with `serverVersion`, `compareMajorMinorVersion`, `reportCriticalError`; `checkStreamSupport` and `setPeerURLsHeader` specs only; boundary items accepted by the user (`semver.New`/`Major`/`Minor`, `GracefulClose`, `TrimSuffix`, `ErrorfPlain`, `RoundTrip`'s `respCloser`, `MinClusterVersion_init`), and on the way, also accepted: `NewRequest_ok`, `URLString_ok` (on the pointer), `readerHas_nil`, `HeaderSetPtr_ok`, `reqRest` over the request's fields but its headers; not linked until stage 6; `notes/rafthttp-plan.md`); 2026-10-23 (rafthttp, stage 5e-2: `streamHandler.ServeHTTP`, the close notifier and `peer.attachOutgoingConn` proved, not linked until stage 6; boundary items accepted by the user: `types.IDFromString` (an axiom), `version.Version`'s value and `semverValid_simple` (an axiom); for review in 5f: `http.HeaderGetPtr_ok`; `notes/rafthttp-plan.md`); 2026-10-23 (rafthttp, stage 5e-1, accepted by the user: the HTTP boundary's response headers: `canonKey` defined (Go's `CanonicalMIMEHeaderKey`), the protocol's `rhdr` (raft's: `X-Server-Version` unset or parses), a writer's header map lent before the commit and checked at it, what the client sees of them, a handler returning its writer (`handlerDone`); the pipeline's proofs adapted; not reached by a linked result; `notes/rafthttp-plan.md`); 2026-10-23 (rafthttp, stage 5d: Go's `path` proved against models of its code (`Clean` with its lazy buffer, `Join`, `Split`, `Base`, `Dir`, `bytealg.LastIndexByteString`; `Proof/path/`), the stream path's lemmas (`Join` builds it, `Base`/`Dir` recover the reader's id and the endpoint; `Proof/path/Segs.lean`, `Stream.lean`), `types.idStr` (`ID.String`'s hex rendering; the boundary spec now names it, accepted by the user), `streamType.endpoint` proved; not linked until stage 6; `dial` waits for the response-header model, a decision for the user; `notes/rafthttp-plan.md`); 2026-10-23 (rafthttp, stage 5c: the stream reader proved over its callees' specs (`streamReader.decodeLoop`, `run`, `start`, `stop`, `close`, `pause`, `resume`; `rafthttp/Reader.lean`, `ReaderRun.lean`), not linked until stage 6; `dial` spec only: no panic, which its proof needs the response's headers in the HTTP boundary for (a design question for 5e); for review (5f): `http.errStrOk` also says an error is of a well-formed error tree (what `errors.Is` needs), `transport.IsClosedConnError` and `rate.Limiter.Wait` (axioms, not reached), `errUnsupportedStreamType` in rafthttp's `errorsNewVarsInit`; `notes/rafthttp-plan.md`); 2026-10-23 (rafthttp, stage 5b: the stream writer proved over its callees' specs (`streamWriter.run`, `close`, `closeUnlocked`, `writec`, `attach`, `stop`, `startStreamWriter`, `newMsgAppV2Encoder`; `rafthttp/Writer.lean`, `WriterRun.lean`), not linked until stage 6; `ConnReadTimeout` translated; `linkHeartbeatSize_init` (a new init axiom, accepted by the user, baseline 548 -> 549); for review: the open premise `swMsgBound` (a queued message encodes below `2^50` bytes); `notes/rafthttp-plan.md`); 2026-10-23 (rafthttp, stage 5 scoped and 5a done: the streams' protocol (`rafthttp/Stream.lean`: frame chains, a registry of connections under the request's ticket, per-frame deposits withdrawn with the reader's tokens; D38d, accepted by the user), `raftProto`'s stream part; no axiom, baseline 548; `notes/rafthttp-plan.md`); 2026-10-23 (rafthttp, stage 4e, D38c, accepted by the user with all of stage 4's trust items: an address's protocol registered once from its listener (`http.register`), so the HTTP boundary's specs are sound for any `HttpNet`; the eleven specs the proofs use are axioms (`Proof/net/http/Axioms.lean`), three over-claims fixed on review (`NewRequest` and a host `url.Parse` rejects, `WriteHeader`/`http.Error`'s status range); not reached by a linked result, baseline 548 unchanged; `notes/rafthttp-plan.md`); 2026-10-23 (rafthttp, stage 4d: the sender proved over its callees' specs, not linked until stage 6: `pipeline.post`, `handle`, `start`, `stop`, the URL picker, `peerStatus.activate`/`deactivate`, `isMsgApp`/`isMsgSnap`, and a local join `Add(4)` (`WaitGroupAdd.lean`, a Perennial gap, `notes/perennial-changes.md`); pending the user's acceptance at 4e: `fmt.SprintfID` and `FollowerStats.Fail` (axioms, not reached), `activePeers_init` and `disconnectedPeers_init` (reached through rafthttp's initializer; accepted by the user, baseline 546 -> 548); `createPostRequest`, `checkPostResponse`, `checkClusterCompatibilityFromHeader` specs only; `notes/rafthttp-plan.md`); 2026-10-23 (rafthttp, stage 4a-4c: request tickets, the mailbox (`Pipe.lean`), `pipelineHandler.ServeHTTP` proved; rafthttp's four metric-vector inits accepted, baseline 542 -> 546); 2026-10-22 (rafthttp, stage 3, what the encoders need of a sent message: no responses, for every message raft queues in every mode (`XfOk`, `isRaftMsg`, `raft.send`'s premise, `raft.Step`'s for a forwarded request, `NetMsgOk`), and a `MsgApp` from its sender (`AppFrom`, the node's id in `XfOk`, `isRaftMsg`, `NodeNames`); protobuf-go keeps undeclared enum values (a Go test), so `MsgMarshals` drops its enum bounds and no entry-type invariant is needed; `Send` takes messages with no responses and `Process` gets copies with none (`Net.lean`); the server's sender id stays existential until stage 6; no axiom added, baseline 542; D38a; `notes/rafthttp-plan.md`); 2026-10-22 (rafthttp, stage 3, the msgappv2 pair: `msgAppV2Encoder.encode` and `msgAppV2Decoder.decode` proved over a frame model (`rafthttp/MsgAppV2.lean`); `proto.MarshalOptions` translated; a finding, `issues/etcd-rafthttp-msgappv2-unbounded-lengths.md`; five new boundary axioms, accepted by the user (`proto.ClonePb`, `proto.MarshalAppendPb`, `pbEnc_ok`, `FollowerStats.Succ`, `linkHeartbeatMessage_init`), one reached by a linked result, baseline 542; `notes/rafthttp-plan.md`); 2026-10-22 (rafthttp, stage 3: raft's `SentMsgOk` gains the `MsgApp` shape (`AppShape`: no vote, rejection, hint, snapshot, context or responses), a premise of `raft.send` that `maybeSendAppend` proves, for msgappv2's short frame (D38a, option (a)); no closed statement changed, trust base unchanged); 2026-10-22 (rafthttp, stage 3, the simple codec: `messageEncoder.encode` and `messageDecoder.decodeLimit` proved over generic protobuf specs at the bytes (D38a: `PbType`, as grpc's `ProtoMsg`), `pbutil.MustMarshalMessage` translated and proved; msgappv2's MsgApp shape to go into the sender's promise (option (a)); six new boundary axioms (three `proto`, three `encoding/binary`) not yet reached by a linked result, and rafthttp's `errorsNewVarsInit`, reached through the package initializers: baseline 541; accepted by the user; `notes/rafthttp-plan.md`); 2026-10-22 (rafthttp, stage 1: D38 (A) approved; the message path translated with bodies (90 functions), no proof yet, no statement changed; trust base +2 init axioms (`path`, `pkg/v3/ioutil`), 539, accepted by the user; stage 2's HTTP boundary reviewed (`notes/rafthttp-http-boundary.md`), `path` translated with bodies, the boundary drafted in Lean (`Proof/net/http/Boundary.lean`, statements only); trust base +1 (`internal/bytealg`'s `init()` assumed to run, `initFuncsOk`: 540, accepted by the user); the rest of the boundary drafted (headers, `http.Error`, routing, `url.URL.String`, `encoding/binary`), statements only, for review; `notes/rafthttp-plan.md`); 2026-10-22 (rafthttp plan, stage 0: the inventory and a bytes-level HTTP boundary with a mailbox invariant proposed as D38, awaiting approval; nothing proved; `notes/rafthttp-plan.md`); 2026-10-24 (auth S4b, branch `auth-s4b`: the Perennial pin at `beb785eaf` (`sort.SearchStrings`, `sort.Strings`), `hasRootRole` translated and proved (S3's axiom gone: 617 axioms), `UserRevokeRole`, `RoleRevokePermission`, `RoleDelete` proved as model steps and added to `apply.isAuthSteps`; the grants left, they write into the read side's messages; "S4b of the auth plan" in `notes/decisions.md`); 2026-10-24 (auth S5 in part, branch `auth-s5`: the token binding -- `AuthNames.tok` and `tokIssued` (`auth/Tokens.lean`), the token provider's contract in the mode (`tokenProviderOk tp M`: an accepted token's info bound to it, `assign` issuing one), `authInfoFromToken`/`AuthInfoFromCtx` carrying it (`ctxBound`), the server's `isReqAuthBound` derived from the real store; `Authenticate` proved over the write side's `GetUser`; the no-op provider meets the contract; +2 axioms (zap's `Logger.Check`, zapcore's `CheckedEntry.Write`), 618; `issues/etcd-auth-simple-token-assign-prefix-panic.md`; "S5 of the auth plan, in part" in `notes/decisions.md`); 2026-10-24 (restore R6, branch `restore-r6`: the restore plan closed; the R4a decision (`store.restore` takes `s.revMu` as a caller-given lock protocol, `revLockW`/`revUnlockW`) in `notes/decisions.md`; the fingerprint check over the trust report: no closed theorem's text changed, and the server-based examples' `*_safe` theorems reach R5a's clean-view flag only through `bootstrap`'s contract (`backend.newPost`), true of `bootstrap` at the pin; trust base unchanged, 614 axioms; `notes/restore-plan.md`, R6); 2026-10-24 (auth S4's apply part, branch `auth-a5`: `apply.isAuthSteps` (`apply/AuthSteps.lean`), the auth store's six proved admin operations as model steps with the store's write resource abstracted, derived of the real store (`auth_apply_steps`, `etcdserver/Results.lean`); `applierV3backend.{AuthEnable, AuthDisable, UserAdd, UserDelete, UserChangePassword, RoleAdd}` perform the model's step on the latest recorded state or the model's refusal (`apply_*_step`); no axiom added, no closed theorem changed; the authority is not yet in the server's environment, whose workload admits no auth request; "S4's apply part" in `notes/decisions.md`); 2026-10-24 (auth S4 in part, branch `auth-s4`: the admin operations as steps of the model's state (`auth/Steps.lean`: `Outcome`, the step functions and relations, `adminOut`, the authority `authOwn`), the latest state a ghost variable shared by the authority and the revision invariant (`AuthNames` now `hist`/`cur`), the write side's contract (`authBatchTxLk`, `authWR`, `enabled` split in halves); `AuthEnable`, `AuthDisable`, `UserAdd`, `UserDelete`, `UserChangePassword`, `RoleAdd`, `Recover`, `commitRevision`, `setRevision` proved and linked; +2 trust-boundary axioms (`authStore.selectPassword`, `zap.Strings`); the grants and revocations, `RoleDelete`, the reads and the apply layer's admin clauses left; `notes/decisions.md`, "S4 of the auth plan"); 2026-10-24 (restore R5e-R5f, branch `restore-r5e`: `mvcc.store.Restore.wp_proof` a theorem (614 axioms) over `restore`'s spec and the ghost moves of `RestoreMoves.lean` (`restore_takeover`, `restore_switch`, `restore_finish`); the writer's invariant's restoring state without its eighth of `cur` and with half the history's authority (`writerInvBody`), the readers' pool counting retired tickets (`StoreNames.tkr`; `writerOwn` holds one, so `k + 1 ≤ nReaders`), `restore`'s unlock given the restored log's receipt bound; `notes/restore-plan.md`, R5e-R5f); 2026-10-24 (auth A3, the API layer, branch `auth-a3b`: the Auth service's seventeen gRPC wrappers (`v3rpc/AuthServer__*.lean`, over the server's methods as contracts, `InvAuthServer.lean`; `NewAuthServer` now gives `authServerIs`) and fourteen of its seventeen entry points (`etcdserver/EtcdServer__AuthEnable.lean`, ..., over `raftRequest` as the contract `authRaftOk`, `AuthEntry.lean`: `reqPropOk` admits no auth request); `Authenticate` translated, unproved (`auth.ErrAuthNotEnabled` has no package fact), `UserAdd`/`UserChangePassword` names only (bcrypt, base64); `AuthenticateRequest`/`AuthUserChangePasswordRequest` as data; Lock/Election not started; trust base unchanged; `notes/decisions.md`, "A3 of the auth plan, the API layer"); 2026-10-24 (auth A4, branch `auth-a4`: the watch service's request shapes -- a created response's watcher carries its registration's authorization (`v3rpc.watchAuthed` in `ctrlWatcher`: `apply.watchClass` of the request's normalized key and raw range end, in the server's auth mode, which the watchable store's new owner tag names, `mvcc.WsNames.tag`/`auth.modeTag`, so the stream specification's arity is unchanged), and every key the registered range covers is in the interval the check saw for every shape (`v3rpc/WatchClass.lean`, `createRangeOk_inRange`: what GHSA-xg4h-6gfc-h4m8 broke); the result `watch_registered_authorized`; no axiom; `notes/decisions.md`, "A4 of the auth plan"); 2026-10-24 (restore R5d, branch `restore-r5d`: `newTreeIndex`'s spec takes the event count's authority at any `n` and a fresh compactor state with the compaction revision's and the committed log's lower bounds (so `store.Restore`'s new index keeps the store's history, log and compaction names, `idx_renew`); `NewStore` splits its fresh names, `idxFresh_split`; trust base unchanged); 2026-10-24 (auth S2b, branch `auth-s2b`: the interval tree's proof generic in the key representation `adt.KeyRep` (`Defs.lean`: the `Comparable`'s type, "the value holds the key" at a fraction, the comparison contract `CompareOk`), the node's key fields as atoms (`ivAt`, `maxAt`), the exported functions' generic results `<fn>_gen` with string-affine (`ownIvt`) and bytes-affine (`ownIvtB`) wrappers, the internal specs generalized in place; S2's three axioms are the linked `wp_Insert_bytes`/`wp_Intersects_bytes`/`wp_Contains_bytes`; `Contains` proved for both (`visit` re-proved for a stopping visitor and a degenerate query, the holes predicate over explicit lent lists); 615 axioms; "S2b of the auth plan" in `notes/decisions.md`); 2026-10-24 (auth A3, the apply layer, branch `auth-a3`: the request's principal `principalOf rq` is an index of the chain's resources (`chainRes c a info`; the mutex holds the zero `AuthInfo`), the KV methods' posts state the request's class for it through the chain (`chainClass`, `reqClass`) up to `dispatch`, `uberApplier.Apply` and the package's `Apply` (`applyAuthRes`: the class with `shouldApplyV3` and `Apply`'s admin check passed, `adminPass`); `authApplierV3.{Put, DeleteRange, Range, Txn}` at the method level, `UserGet`'s self-or-admin case; `Results.lean`'s `chain_*` carry the class; trust base unchanged, no closed statement changes; `notes/decisions.md`, "A3 of the auth plan, the apply layer"); 2026-10-24 (auth S3, branch `auth-s3`: the store's checks return the model's verdicts in every mode -- `isOpPermitted` and the `Is*Permitted` `permVerdict`, `IsAdminPermitted` `adminVerdict` over an `Option AuthInfo` (a `nil` pointer covered; `apply.isAuthStore` gains the clause, A2's `srvAdminNilOk` is derivable), `IsAuthEnabled`/`Revision` theirs, from the flag's and the revision's recorded states in `authInv` (`enabledP st M`, `revInv st M`) and S1's/S2's reads (`auth/VerdictLemmas.lean`); `isAuthStore_of_authInv` derives the apply layer's contract in the store's own mode; A0's one-state verdict was unprovable (the four reads are of four states) and is corrected: `permitted` without the revision conjunct, the pass half names a state that permitted and a state whose revision admitted the token, the refused half the view of the four states read (`AuthView`, `refusedV`), the request's shape (`reqShape`) a premise inside the model, recorded states carry `permKeysOk`; `hasRootRole`'s axiom restated to return `isRoot` of a sorted-roles message (Perennial lacks a `sort.SearchStrings` spec, `notes/perennial-changes.md`); trust base unchanged, 618 axioms); 2026-10-23 (restore R5a-R5c, branch `restore-r5`: `store.restore` proved over a bucket with data, the restored log `[[], []] ++ R` (its spec over `R`, `NewStore` at `R = []`): the backend's read buffer known clean (`BNames.cln`, `bViewC`, `rtHeld_clean`; `newPost`'s view clean, so `storage.OpenBackend`'s axiom promises it), the limited range's prefix over it (`keyRangeLimSpec`'s `cl`, `keyCleanRead`), a held read transaction lending a share to a second reader (`rtHeldF`, `rdSplit`), the chunk loop (`RestoreChunks.lean`); trust base unchanged (615 axioms); `store.Restore` (R5d-R5f) next; `notes/restore-plan.md`, "R5's stages"); 2026-10-23 (auth S2, branch `auth-s2`: the permission cache computes the model -- `cacheP st M` holds, in `on γa`, one recorded state whose users are the map's keys and whose permissions' intervals each entry's two bytes-affine trees hold (`permsAt`, `cacheOk`, `cacheEntryIs`); `checkKeyPoint`/`checkKeyInterval` return membership and coverage over the trees' lists, `isRangeOpPermitted` the verdict `cacheVerdict` (the recorded state's `coversPoint`/`coversRange` iff the check passed, a missing user the refusal); `getMergedPerms`, `refreshRangePermCache`, `isValidPermissionRange`, `BytesAffineComparable.Compare` proved; the interval tree's `Contains` given its pure meaning (`adt/Contains.lean`: `containsRes_iff`, the greedy scan is coverage) and `Intersects` of a point membership (`stab_point_iff`); the bytes-affine tree `adt.ownIvtB` with its `Insert`/`Intersects`/`Contains` as **three axioms** pending the tree's generalization to a comparator (plan stage S2b); `notes/decisions.md`, "S2 of the auth plan"); 2026-10-23 (auth A2, branch `auth-a2`: the API layer's auth guards -- `EtcdServer.requireAuthInfo`/`checkMembershipOperationPermission`, `AuthAdmin.isPermitted`/`requireAuthInfo` (and their promotions) proved with the tokens `authedRes`/`adminRes` and outcomes `authedOut`/`adminOut` of `etcdserver/AuthGuard.lean`, and the guarded entry points `kvServer.Compact`, the eight `authMaintenanceServer` wrappers, `EtcdServer.RemoveMember`/`MemberList` proved over their inner operations as token-carrying contracts (`v3rpc/InvAuthAdmin.lean`: `guardedOk2`, `compactOk`; `configureRemoveOk`): 17 functions; `IsAdminPermitted(nil)` a premise (`srvAdminNilOk`); `AddMember`/`UpdateMember`/`promoteMember` not translated (`encoding/json`); trust base unchanged); 2026-10-23 (restore R4 option 1, branch `restore-r4b`: `store.restore` proved for the empty bucket `NewStore` hands it (its spec takes `bucketView γ q ∅`, a reader's token `RT` and `kbNoCmp`); the key backend's contract gains a range read with any limit (`keyRangeLimSpec`, the answer a `Sublist` of the range, proved of the real backend), `metaReadSpec rt nc` and the compaction-key reads' "not found" under `nc`, `keysGauge.Set`; trust base unchanged in count (615 axioms after auth S1): `mvcc.store.restore.wp_proof` gone, `mvcc.kbNoCmp_metaNone` (`NoCmpRead.lean`) added; `restore` with data (R4b's premise, R4d's split token) moved to R5; `notes/restore-plan.md`, "R4's progress" item 4); 2026-10-23 (auth S1, branch `auth-s1`: `authpb` translated as data (`authpb.toml` as `raftpb`'s), schema's auth backend translated with bodies and its read side proved over the buckets -- `unsafeReadAuthEnabled`/`unsafeReadAuthRevision`/`unsafeGetUser`/`unsafeGetRole`, the `authReadTx` wrappers with `RLock`/`RUnlock`, `authBackend.ReadTx`/`GetUser`/`GetRole` (13 functions) against the contracts `authReader`/`authRTx`/`authBE` of `etcdserver/InvAuthBackend.lean`, whose `authBucketsAre st D` says the buckets hold the model's state; the records `auth/Buckets.lean` (`UserRec`, `RoleRec`, `userEncode`/`roleEncode` opaque, `ownUser`/`ownRole`, `userOut`/`roleOut`, `authSnap`); the store's contract `authReadTxOk tx R M` returns the state in the mode `M`, which threads through `authInv`/`authRd`/`beP` and the 13 request-side specs; `schemaInit` gains the auth buckets, key names and `authEnabled`/`authDisabled`; +2 trust-boundary axioms, `proto.Unmarshal` on `authpb.User` and `authpb.Role` (540 axioms, 0 sorries); a finding, `issues/etcd-auth-readtx-getallroles-panics.md`; no closed theorem changed; see "The auth backend's read side (S1)" and `notes/decisions.md`, "S1 of the auth plan"); 2026-10-23 (restore R4 started and R2, branch `restore-r4`: the index private until `restore` makes its lock (`newTreeIndex` returns `ownIdxPriv` and `idxLockG`; `store.restore`'s spec, still an axiom, gives back `isTreeIndex` and takes all of `currentRev`, its half-permission write for an empty log having been unprovable); `NewStore` locks `s.mu` as private memory and makes its invariants after `restore`; `setupMetricsReporter` proved over the reporters' locks (R2); `restore`'s own proof needs three backend-contract extensions (`notes/restore-plan.md`, "R4's progress"); trust base unchanged); 2026-10-23 (auth A1, branch `auth-a1`: the class statement `apply/AuthClass.lean` (`classOk`/`classRes` over A0's verdicts; `putClass`, `deleteClass`, `rangeClass`, `cmpsClass`, `opsClass`/`opClass`, `txnClass`; `authEndOf`, the range end as the auth store reads it), the checks' specs with it (`checkPutAuth`, `checkTxnReqsPermission`, `checkTxnPermission`/`CheckTxnAuth`, `txnPermT`), `doSerialize.spec` with the check's class `C`, `EtcdServer.Range`'s success with `rangeClass`, `isWatchPermitted` with the range's read class; the method-level statement (the principal through `chainRes`) is the follow-up; no closed theorem or trust-base change; `notes/decisions.md`, "A1 of the auth plan"); 2026-10-23 (restore R3, branch `restore-r3`: a generation's `created` is its main revision in the model (the Go field's sub-revision is not a function of the log; `keyIndex.get`, `treeIndex.unsafeGet`/`Get`/`Range` return it unconstrained), sequential specs of a private `RWMutex` (`PlainRWMutex.lean`), `treeIndex.KeyIndex`/`Insert` on a private index (`IdxPriv.lean`), `restoreIntoIndex` proved over the code's fold `idxRestore`, and that fold equal to the log's index for a well-formed log (`idxRestore_logEnts'`, R3b); `notes/restore-plan.md`, "R3's progress"; no closed theorem changed in intent, trust base 538 axioms); 2026-10-23 (auth A0, branch `auth-a0`: the authorization model `auth/Model.lean` (`AuthState`, `permitted`, `adminOk`; the store's history `authHist`/`authStateAt`; the mode `AuthMode` `off`/`any`/`on γa` replacing the boolean, `AEnv.authOn` now `E.authMode.isOn`; the verdicts `permVerdict`/`adminVerdict`/`enabledVerdict`/`revisionVerdict`, two one-directional facts over recorded states, the checks' own TOCTOU), `apply.isAuthStore`/`permCheck2`/`permCheck3` restated over it, the real store derived in `any`, `NewAuthStore`'s axiom in `off`; the matrix `notes/auth-matrix.md` (49 methods, their classes and keys); no closed theorem or trust-base change; see `notes/decisions.md`, "A0 of the auth plan"); 2026-10-23 (auth plan, on `lean`: `notes/auth-plan.md`, specifying and proving etcd's auth/RBAC -- the authorization model first (A0), then the store's checks computing it (S, from `auth/store`, where unit P2 stopped) and every gRPC method enforcing its privilege class (A, PR #22541's matrix as the specification), an auth-enabled closed theorem (E); planned only); 2026-10-23 (k8s-etcd3 merged into `lean`: the Kubernetes etcd3 store's linearizability instance `k8setcd3_safe` (stage 6g of `notes/k8s-etcd3-plan.md`), on the `sorry`s `revRoom`, `clientErr_other`, `client_ctx_field`, `kvIs_ne_null`; the etcd pin `goose-lean-getproph2` `bc9c3868c`; see "Kubernetes' etcd3 storage backend"); 2026-10-23 (restore R1, branch `restore-r1`: `keyIndex.restore`, `keyIndex.restoreTombstone` and `restoreChunk` proved and linked (`notes/restore-plan.md`, "R1's findings"); the planned lemma that `restore` agrees with `put` is false when a key's first put has a non-zero sub-revision (etcd restores `created` with `Sub` 0), a decision for R3; no closed theorem changed, trust base 538 axioms); 2026-10-23 (with-timeout-bg, branch `with-timeout-bg`: the client-timeouts plan's T3 -- Perennial `c25bef57e` proves `WithDeadlineCause`/`WithDeadline`/`WithTimeout` of `Background()` (`wp_WithTimeout_Background`; `propagateCancel`'s spec takes any child of a `Background()` parent), the pin moved to it, the axiom `context.WithTimeoutBackground.wp_proof` is a theorem: 538 axioms, one fewer in the `read`, `server` and every etcd example's collection; the plan finished); 2026-10-23 (restore R0, branch `restore-r0`: `notes/restore-plan.md` R0 done: `store.restore`, `setupMetricsReporter`, `restoreIntoIndex`, `restoreChunk`, `keyIndex.restore`/`restoreTombstone` and `restoreChunkKeys` translated (Goose took them as they are), `restoreChunkKeys`'s value in `mvccInit` (its generated opaque-initializer axiom gone); the two restore axioms unchanged, over translated bodies; no closed theorem changed, trust base 539 axioms); 2026-10-23 (client-timeouts, branch `client-timeouts`: the examples' clients configured as etcd's clients are in practice, `notes/client-timeouts-plan.md` T0 and T1 -- one configuration in `examples/common` with etcdctl's timeouts (`DialTimeout` 2s, `RequestTimeout` 5s, keepalive 2s/6s; `common.NewClients`, linkv3p's `newClient` gone), every unary call in `context.WithTimeout(context.Background(), common.RequestTimeout)` cancelled after the call (ten call sites), the members' keepalive policy on every `common.Serve`; the proofs over the existing `WithTimeoutBackground` axiom through one lemma `client.wp_WithTimeout_bg`; `putget_safe`, `putget3_safe`, `linkvtxn_safe` and `linkv3p_safe` gain the premise `ContextErrsClient`, no conclusion changes, no new axiom (D28's policy axiom in five more collections); linkv3p's `TestFailover` rewritten around request timeouts; see "The examples' clients configured as in practice: request timeouts"); 2026-10-23 (restore plan, branch `restore-plan`: `notes/restore-plan.md`, proving `store.restore` and closing `store.Restore` (two axioms) in stages R0-R6, after checking both specs against the code (they agree; `setupMetricsReporter`'s writes to five package globals are unowned, as `readych` was); planned only); 2026-10-23 (norefusal-kv, branch `norefusal-kv`: `etcd_noRefusal` was false as stated (the Auth service's `UserAdd` of an empty name answers `"etcdserver: user name is empty"` with authentication off); `noRefusalAt` now speaks of the KV service only (`kvMethod`), the attempt contract reads it for KV calls only, the write path names its KV method (D29 amended); no closed theorem changed, trust base 539 axioms); 2026-10-23 (readych-closer, branch `readych-closer`: the axiom `publishV3.spec` closed `s.readych` without owning it (found checking the monitors' and `publishV3`'s specs against the code: the rest match, the hash and downgrade monitors only with their checks off); now `NewServer` allocates `readych` as a broadcast channel (Perennial's idiom, `Q = True`) and hands the right to close it (`srvReadyCloser`) through `Start` to `publishV3`'s goroutine; no closed theorem changed, trust base 539 axioms); 2026-10-23 (D22 receiver epochs, S7f, branch `worktree-agent-a5fae76133d772e18`: the apply protocol's per-backend names: `ApplyNames` split into logical names and the current backend's `ApplyPhys` (a ghost variable `cur`, a registry `reg`, the retired backends' mirrors in `consInv`), `commit_save_au`'s retired case (an old backend's `Close` commits through the shared hooks), the swap `ci_swap_au` at `SetBackend` and the boot allocation `consInv_alloc` proved; `applyAll`'s post and `run`'s loop invariant per backend (`beSucc`, `ApplyBe`); no closed theorem changed, `bootOk`'s text unchanged; trust base unchanged (539 axioms, 0 sorries); see "D22 receiver epochs, S7f"); 2026-10-23 (D22 receiver epochs, S7, branch `worktree-agent-a9f17bc977f014063`: the server's fields and the objects' backends stated truly: `s.uberApply` and half of `s.be` the apply thread's, `bemu` over the current backend's ghost variable `AEnv.γbe`, the write budget and the storage-version monitor's token of the current backend (`srvWTPool E`); `AlarmStore.Recover` translated and proved (over `restore`, a new trust-boundary axiom: 539 axioms, 0 sorries); the alarm store's, auth store's, lessor's and cluster's backend fields half their lock's (the cluster's owned), their users' halves pinning their writes (`alarmApplyOk`, `authApplyOk`, `lessorApplyOk`, `clusterApplyOk`, `srvObjsOn`); `bootOk` restated (the cluster's contract, `HclBe`); the apply protocol's per-backend names designed, not done; see "D22 receiver epochs, S7"); 2026-10-23 (D22 the stored-index window, branch `worktree-agent-abc119190b6e832f9`: a commit's request served by the backend's hooks (`backend.commitReq`, `hooksReq`; `ForceCommit`/`Commit`/`commit`/`unsafeCommit`, `BackendHooks.OnPreCommitUnsafe`, mvcc's `isKeyBackendG` (`Req`) and `store.Commit` carry it), the frozen mode of the apply protocol (`consFrozen`, `commit_freeze_au`, `unfreeze`), the snapshot's observation reading the stored index and the tracked buckets (`srvBeSnapOk_window`); `createMergedSnapshotMessage`'s snapshot resource from the commit's; trust base unchanged (538 axioms, 0 sorries); see "D22 the stored-index window"); 2026-10-23 (D22 the backend over every bucket, branch `worktree-agent-abc119190b6e832f9`: D22c revisited carried out: the backend's model tracks the buckets only the apply thread writes (`BParams.RB`, `rbData`, `rbOwn`), the apply thread holds them at the model of the applied log (`restModel`, `srvRest`), `bkRestAt` derived (`bkRestAt_of_rb`), no determinism axiom; `bootOk` and five trust-boundary specs restated; trust base unchanged (538 axioms, 0 sorries); see "D22 the backend over every bucket"); 2026-10-23 (client-err-cells, branch `client-err-cells`: a client error is no caller's `errors.New` value (D37): `errCellOk` (an `*errorString` among the client's errors holds `"EOF"` or `"context canceled"`), from grpc's invoke and `context.ErrAny` (both trust-boundary statements strengthened, true of Go), through the retry interceptor, `toErr` and the KV calls, into `kvErr` at the end of `client_put/range/delete/txn_any`, the `_st` family and linkvtxn's `txn_Commit_st`; for the Kubernetes driver's sentinels (`errDeleteRejected`, `errUpdateRejected`, `kvErr_ne`); no closed theorem changed, trust base 538 axioms); 2026-10-22 (D22 S-l sender items, branch `worktree-agent-a13029e4d33860881`: a `Ready`'s `MsgSnap` kept owned into `msgSnapC`'s bag (`rnSnapMsg`, `rnMsgR`), `store.Commit` translated and proved (`srvKVCommitOk_of_kv`), the merge's write tokens (`srvWTPool_take_extra`), `rnRtBound_of_rtOk`; the stored-index window designed, not carried out (it needs a hook request through `ForceCommit`); trust base unchanged (538 axioms, 0 sorries); see "D22 S-l sender items"); 2026-10-22 (D22 receiver epochs, S6, branch `worktree-agent-a65035decfc6b261e`: `store.Restore` a true trust-boundary axiom (+1: 538 axioms, 0 sorries), `watchableStore.Restore` proved over it; a restored backend's registration pending in the writer's invariant (`writerReg`, `storeRegd` out of `physOk`); the watch invariant with restoring watchers (`WsState.unsRst`, `chooseAll`'s reset, `syncWatchers`' past-the-log case, the synced watchers' events up to their `minRev`); no closed theorem changed; see "D22 receiver epochs, S6"); 2026-10-22 (dedup-pin, branch `dedup-pin`: the Perennial pin at `f97c83add` (`dedup-lemmas` landed: the points-to halves, `mask_ndot_ne2`, the replicate, fold, list and `GoStringLt` lemmas), the local copies in the client, the cache, the examples and raft deleted; no closed theorem's statement changed, trust base unchanged (537 axioms)); 2026-10-22 (dedup, branch `dedup`: `notes/dedup-plan.md` steps A, B, C5 (i), C7 applied: the exact duplicate lemmas merged into the files their users import, `PutThenGet.lean`'s put/get layer inlined into `ClientPutGet.lean`, the watch facts proved once generic in the model (`watchkv.wkSteps`, `chain_gen`/`prog_step_gen`/`resp_gen`; `resp_wk`, `linkv3p.resp_hist` instances), the `op_simps` simp set for the option models (130 simp lists); C1-C4 and D's generic lemmas on Perennial branch `dedup-lemmas` (`f97c83add`, not landed), the local copies kept until the pin moves; no closed theorem's statement changed, trust base unchanged (537 axioms)); 2026-10-22 (cleanup2 part 2, branch `cleanup2`: the examples' closed theorems through one generic lemma (D36): `examples/common/Adequacy.lean`'s `etcd_adequate` (over `goose_adequacy_start`) and `init_adequate` (over `goose_adequacy`, proposed for Perennial in `notes/perennial-changes.md`), parameterized by the program's initializer and body, the result set and the ghost-state bundle; putget, putget3, linkvtxn, linkv3p (both), watchkv, cachekv, kv, the counter and kvwitness (both) are instances; every `*_adequate`/`*_safe` header byte-identical, fingerprint unchanged, trust base unchanged (537 axioms)); 2026-10-22 (cleanup2 part 1, branch `cleanup2`: the client's KV call results one family (D35): `client_put/range/delete/txn_any` take a floor `F` and a write's update persistent or fired at most once, `client_txn_any` the members' write names; `client_put/get/delete/txn/range_end_to_end` keep their statements and are proved as their instances at one server's addresses (`srvsAt`); `Failover.lean` merged into `client/v3/Results.lean`; dead declarations deleted (`putReplied_ok`, `deleteReplied_ok`, `txnAuOk_of_box`, `head_filter_key`, `client_txn_value(_ro)`, `isEtcdKVE_of_kv`, `isEtcdPutKV_of_kv`, `isEtcdDeleteKV_of_kv`); the client's docstrings about the deleted one-attempt mode rewritten; every closed theorem's statement unchanged (fingerprint), trust base unchanged (537 axioms)); 2026-10-22 (retire-linkv, branch `retire-linkv`: the examples `linkv` and `linkv3` and their closed theorems `linkv_safe`, `linkv3_safe` retired, subsumed by `linkvtxn_safe` and `linkv3p_safe` (D34): their Go packages, Goose projects and translations, Spec/Proof trees, gen-init roots, gen-link modes `--linkv`/`--linkv3` and collections deleted; what linkvtxn and linkv3p used moved to them with names unchanged (`linkvtxn/{Proph,PendModel,TxnModel,TxnModelKV,ModelKV}.lean`, `linkv.kvRaftOf_boot` in `linkvtxn/Boot.lean`, the bundle `linkvGF`/`linkvHeapAt` in `linkv3p/Adequacy.lean`); every remaining closed theorem's statement unchanged, trust base unchanged (537 axioms); their sections were already in status-history.md); 2026-10-22 (example-ports, branch `example-ports`: each example its own TCP ports, so the examples module's `go test -race ./...` runs in parallel, no `-p 1`: linkv to client `127.0.0.1:23871`/peer `23881` (was putget3's `23791`/`23801`), watchkv to `23872`/`23882` (was linkv3p's `23831`/`23841`), cachekv to `23873`/`23883` (was on linkv3p's bridge `23851`); translations regenerated; `linkv_safe`, `watch_safe`, `cache_safe` (and their `*_Main`) change only in the address literals: the `addrsUnclaimed` premise's client address and the URLs of their `premises`' definitions (`peerURL`, `clientURL`, the peer directory); trust base unchanged; D33's last paragraph); 2026-10-22 (examples-module, branch `examples-module`: the etcd examples, `common` and `kv` in one Go module, `examples/go.mod` (module `github.com/mit-pdos/etcd-grove/examples`; import paths and translations unchanged), so a fork-pin bump is one go.mod edit; `kvwitness`, `lintest` and `third_party/{porcupine,bridge}` keep their own; `etc/goose.py --check` now fails if the go.mod replaces of etcd or raft differ from the projects' pins (`GO_MOD_PINS`); its tests run `go test -race -p 1 ./...` (the examples' ports overlap); `etc/verified-code.{py,go}` take a project directory inside a module (its numbers unchanged); no Lean change; D33's last paragraph); 2026-10-22 (examples-common, branch `examples-common`: the examples' shared Go code in one package, `examples/common` (D33), translated and proved once: the one-member start (`StartServer`), a cluster member's (`NewMember`, `StartMember`), the gRPC service (`Serve`, with the caller's ghost step), the client (`NewClient`), the ghost-state allocations (`alloc1`, `alloc3`), the watch workload's `Gen`, `GenAll`, `Writer`, `MaxRev`, `Collect`, `Attempted`, `Check`; 46 example spec/proof files deleted or moved to common; no closed theorem's statement changed, trust base unchanged; see "The examples' shared code"); 2026-10-22 (retry-bound clean-up, branch `retry-bound`: the client's retry-bound tracking (`maxAfter`, `retryOptsMax`, `optApplyMax`'s bound; D21 M6) deleted, `optApplyMax` now `optApplyKeep`; four intermediate specs lose a parameter or conjunct, no closed theorem's statement changed, trust base unchanged; see the clean-up section); 2026-10-22 (Perennial idioms, branch `perennial-idioms`: the synchronous SPSC channel, the thread-token join and `wp_fork_tok_upd` moved to Perennial (landed: the pin `537c426e0`; branch `idioms`, `537c426e0`) and the watch client's local copies deleted; needs that branch until the pin moves; no statement of a closed theorem changed, trust base unchanged; see "Perennial idioms: the watch client's three workarounds upstreamed"); 2026-10-22 (clean-up, branch `cleanup`: the watch client's `closeSubstream`/`run` joined again (CPU 52s -> 7s, 148s -> 131s), the one-attempt client machinery deleted (D31's follow-up), `gen-init.py`'s `CLOSEDCHAN` variant and kv's re-proof of raft's initialization removed; no statement of a closed theorem changed, trust base unchanged; see "Clean-up: the watch client's joins, the one-attempt client, the init variants"); 2026-10-22 (the repository is sorry-free: mvcc's `kvHasher` translated, its `hash.Hash32` field's package `hash` types-only here, so its generated instances are no longer `sorry -- axiomatized type`; trust base 543 axioms, 0 sorries; see "`kvHasher` translated: no sorry left"); 2026-10-22 (client-default: linkv, linkv3, linkvtxn, watchkv and cachekv use etcd's default client configuration, their members refusal-free (`etcd_noRefusal`, D29); one family of client call lemmas in `client/v3/ClientPutGet.lean`; D31; see "The examples' clients"); 2026-10-22 (watches across a cut, W4: `linkv3p_watch_safe`, watchkv's watch workload over linkv3p's partitioned cluster, the watch resumed at any member, its events the cluster's committed history's; no axiom added; see "Watches across a cut"); 2026-10-22 (watches across a cut, W1–W3: D32 carried out; mvcc's progress bound from etcd's own guard, no client start read; the clients' model over the cluster's history; the watch client's epochs at any member of its connection; see "Watches across a cut"); 2026-10-22 (D22 fork fixes: the etcd pin at `goose-lean` `188113160`, the alarm store recovered in place (`8fd98af04`) and a snapshot's older files released by `applySnapshot` after its open (`188113160`), each with its regression test; no proof change, trust base 543 axioms, 2 sorries; see "D22 fork fixes: the snapshot file's release and the alarm store's race"); 2026-10-22 (D22 receiver epochs, S1-S4 of the simplest true `Restore`: the certificate without the index's count, the writer's state out of the batch lock into `writerInv`, the four fields `Restore` writes out of `isStore` into lock-held shares, `s.revMu`'s restoring mode, the readers' pool of the index's slots; S5 (the physical names existential, the writer's fragment) designed, not done; trust base unchanged; see "D22 receiver epochs, S1-S4"); 2026-10-22 (the kv example's snapshot liveness: a `do` whose operation a snapshot covers is answered at the install, from the table of the operations applied, now with each one's answer; `kv_porcupine_safe` unchanged; see "The kv example's snapshot liveness: done"); 2026-10-22 (D22 S-r carried out: snapshots in the kv example, replicas compact and catch up by `MsgSnap`, `kv_porcupine_safe` re-closed with its statement and axioms unchanged; the data certificate `snapDataOk`; see "D22 S-r carried out (proof)"); 2026-10-21 (raft-retarget merged into lean: D22's snapshot track (S-0..S-d4, S-f..S-i, S-g/S-h, the three fork fixes) with lean's proof-perf, init facts, linkv3p/kv and watch-resume work; the etcd pin `goose-lean` `2aed163b1` (both sides' fork commits); lean's six examples ported to the server's D22 contract; trust base 543 axioms, 2 sorries; see "Merge of raft-retarget into lean (D22)"); 2026-10-21 (clean-up, on branch `clean-up`: `etc/dead-decls.py`, about 7,900 lines of unused declarations removed, proposals registered once and proposed any number of times (`prop_register`; `propMulti` gone), the adequacy coverage of the linked results, see "Clean-up"); 2026-10-21 (read retries: linkv3p's clients have the default retries, so a read held by a cut is retried on the next member, while a write is still sent at most once: the members are refusal-free; D29, 2 axioms; see "Read retries"); 2026-10-21 (keepalive: the client's configuration may enable gRPC keepalive, linkv3p's clients do and its members accept the pings, failover on a silent partition; D28, 2 axioms; see "Keepalive and failover on a silent partition"); 2026-10-21 (client-member cuts in linkv3p, K0, K1, K3: `linkv3p_safe` re-closed with client-member cuts through a copy of etcd's bridge, part of the network (D26: 5 trust-boundary axioms, its code not verified), a finding (`issues/nonissues/etcd-bridge-blackhole-twice-panic.md`); older entries: `notes/status-history.md`, "Last updated entries (all 164, until 2026-10-22)".; 2026-10-22 (v2stats's `NewLeaderStats` translated and proved, no longer an axiom; `ServerStats`'s three (`NewServerStats`, `BecomeLeader`, `RecvAppendReq`) stay axioms, its type has an anonymous struct field Goose does not translate; trust base 537 axioms, 0 sorries; see "The FIFO scheduler proved"); 2026-10-22 (the FIFO scheduler proved: `pkg/v3/schedule`'s `fifo` translated with its body, `NewFIFOScheduler`, `Scheduler.Schedule` and `Scheduler.Stop` no longer axioms, nor mvcc's `store.Close` and `store.HashStorage` (translated); trust base 538 axioms, 0 sorries; see "The FIFO scheduler proved"); 2026-10-22 (D22 receiver epochs, S5 of the simplest true `Restore`, branch `worktree-agent-ab03038efa73b7686`: the readers' backend tokens in the readers' pool (the apply thread's and the storage-version monitor's retired readers), the store's current objects and physical names a fractional ghost variable shared by the locks' shares (`γ.cur`, `PhysNames`, `γ.withPhys`), the physical facts out of `isStore`, the read transactions at the names their share pins, the writer's fragment in `hookIs`/`txn.kvWriter`; no closed theorem changed, trust base unchanged (537 axioms, 0 sorries); see "D22 receiver epochs, S1-S5"); 2026-10-22 (build performance, branch `perf/2026-10-22` merged into `lean`: the costliest tactic searches cut, about 16 CPU minutes; see "Build performance (2026-10-22)"); 2026-10-22 (v2stats's `NewLeaderStats` translated and proved, no longer an axiom; `ServerStats`'s three (`NewServerStats`, `BecomeLeader`, `RecvAppendReq`) stay axioms, its type has an anonymous struct field Goose does not translate; trust base 537 axioms, 0 sorries; see "The FIFO scheduler proved"); 2026-10-22 (the FIFO scheduler proved: `pkg/v3/schedule`'s `fifo` translated with its body, `NewFIFOScheduler`, `Scheduler.Schedule` and `Scheduler.Stop` no longer axioms, nor mvcc's `store.Close` and `store.HashStorage` (translated); trust base 538 axioms, 0 sorries; see "The FIFO scheduler proved"); 2026-10-22 (retry-bound clean-up, branch `retry-bound`: the client's retry-bound tracking (`maxAfter`, `retryOptsMax`, `optApplyMax`'s bound; D21 M6) deleted, `optApplyMax` now `optApplyKeep`; four intermediate specs lose a parameter or conjunct, no closed theorem's statement changed, trust base unchanged; see the clean-up section); 2026-10-22 (Perennial idioms, branch `perennial-idioms`: the synchronous SPSC channel, the thread-token join and `wp_fork_tok_upd` moved to Perennial (landed: the pin `537c426e0`; branch `idioms`, `537c426e0`) and the watch client's local copies deleted; needs that branch until the pin moves; no statement of a closed theorem changed, trust base unchanged; see "Perennial idioms: the watch client's three workarounds upstreamed"); 2026-10-22 (clean-up, branch `cleanup`: the watch client's `closeSubstream`/`run` joined again (CPU 52s -> 7s, 148s -> 131s), the one-attempt client machinery deleted (D31's follow-up), `gen-init.py`'s `CLOSEDCHAN` variant and kv's re-proof of raft's initialization removed; no statement of a closed theorem changed, trust base unchanged; see "Clean-up: the watch client's joins, the one-attempt client, the init variants"); 2026-10-22 (the repository is sorry-free: mvcc's `kvHasher` translated, its `hash.Hash32` field's package `hash` types-only here, so its generated instances are no longer `sorry -- axiomatized type`; trust base 543 axioms, 0 sorries; see "`kvHasher` translated: no sorry left"); 2026-10-22 (client-default: linkv, linkv3, linkvtxn, watchkv and cachekv use etcd's default client configuration, their members refusal-free (`etcd_noRefusal`, D29); one family of client call lemmas in `client/v3/ClientPutGet.lean`; D31; see "The examples' clients"); 2026-10-22 (watches across a cut, W4: `linkv3p_watch_safe`, watchkv's watch workload over linkv3p's partitioned cluster, the watch resumed at any member, its events the cluster's committed history's; no axiom added; see "Watches across a cut"); 2026-10-22 (watches across a cut, W1–W3: D32 carried out; mvcc's progress bound from etcd's own guard, no client start read; the clients' model over the cluster's history; the watch client's epochs at any member of its connection; see "Watches across a cut"); 2026-10-22 (D22 fork fixes: the etcd pin at `goose-lean` `188113160`, the alarm store recovered in place (`8fd98af04`) and a snapshot's older files released by `applySnapshot` after its open (`188113160`), each with its regression test; no proof change, trust base 543 axioms, 2 sorries; see "D22 fork fixes: the snapshot file's release and the alarm store's race"); 2026-10-22 (D22 receiver epochs, S1-S4 of the simplest true `Restore`: the certificate without the index's count, the writer's state out of the batch lock into `writerInv`, the four fields `Restore` writes out of `isStore` into lock-held shares, `s.revMu`'s restoring mode, the readers' pool of the index's slots; S5 (the physical names existential, the writer's fragment) designed, not done; trust base unchanged; see "D22 receiver epochs, S1-S4"); 2026-10-22 (the kv example's snapshot liveness: a `do` whose operation a snapshot covers is answered at the install, from the table of the operations applied, now with each one's answer; `kv_porcupine_safe` unchanged; see "The kv example's snapshot liveness: done"); 2026-10-22 (D22 S-r carried out: snapshots in the kv example, replicas compact and catch up by `MsgSnap`, `kv_porcupine_safe` re-closed with its statement and axioms unchanged; the data certificate `snapDataOk`; see "D22 S-r carried out (proof)"); 2026-10-21 (raft-retarget merged into lean: D22's snapshot track (S-0..S-d4, S-f..S-i, S-g/S-h, the three fork fixes) with lean's proof-perf, init facts, linkv3p/kv and watch-resume work; the etcd pin `goose-lean` `2aed163b1` (both sides' fork commits); lean's six examples ported to the server's D22 contract; trust base 543 axioms, 2 sorries; see "Merge of raft-retarget into lean (D22)"); 2026-10-21 (clean-up, on branch `clean-up`: `etc/dead-decls.py`, about 7,900 lines of unused declarations removed, proposals registered once and proposed any number of times (`prop_register`; `propMulti` gone), the adequacy coverage of the linked results, see "Clean-up"); 2026-10-21 (read retries: linkv3p's clients have the default retries, so a read held by a cut is retried on the next member, while a write is still sent at most once: the members are refusal-free; D29, 2 axioms; see "Read retries"); 2026-10-21 (keepalive: the client's configuration may enable gRPC keepalive, linkv3p's clients do and its members accept the pings, failover on a silent partition; D28, 2 axioms; see "Keepalive and failover on a silent partition"); 2026-10-21 (client-member cuts in linkv3p, K0, K1, K3: `linkv3p_safe` re-closed with client-member cuts through a copy of etcd's bridge, part of the network (D26: 5 trust-boundary axioms, its code not verified), a finding (`issues/nonissues/etcd-bridge-blackhole-twice-panic.md`); older entries: `notes/status-history.md`, "Last updated entries (all 164, until 2026-10-22)".

This file is where the port is now: a summary checked against the repository, then the
sections that still describe the current design or state, by area. Its history -- the
sections of states since superseded, stage-by-stage logs of finished tracks, the full "Last
updated" list -- is `notes/status-history.md` (append-only). When a section here is superseded,
move it there whole and leave a pointer; the index at the end of this file lists every heading
that moved, so a reference `notes/STATUS.md, "..."` to one of them resolves there. The design
record is `notes/decisions.md`; the Rocq development's notes are on branch `main`
(`git show main:notes/STATUS.md`).

## Current summary (2026-10-23, at `lean` `6511e2f660`)

### Pins

- **Perennial** `24bef275ea91746aef1ed7fff9ddf4baf04aba0f`, branch `lean` (`lakefile.toml`,
  `lake-manifest.json`); the pin follows Perennial's `lean` (section "Perennial: the pin follows
  `lean`" below; CLAUDE.md, "Changes to Perennial").
- **Go projects** (`etc/goose.py`, `PROJECTS`):
  - `raft`: `upamanyus/etcd` `c8217eb91ae5948182c1035ff0464b1e54b8f1d0`, branch
    `raft37-goose-lean-a1` (raft v3.7.0 `b867cf13` plus the single-voter read-index fix and the
    probe-to-replicate fix at `pr.Next == pr.Match+1`).
  - `etcd`: `upamanyus/etcd` `bc9c3868ced67e518fb2fecba44ce0fa70b7303b`, branch
    `goose-lean-getproph2`: `goose-lean`'s `188113160` (upstream main of 2026-10, the commits that
    make it translatable, and the bug fixes `etc/goose.py`'s comment lists, each with its `issues/`
    file; the latest two, `8fd98af04` and `188113160`, are "D22 fork fixes" below) plus the
    prophetic `kubernetes.Client.Get` (D30n, verification only; `goose-lean-getproph`'s `942601555`
    cherry-picked, 2026-10-23). Not yet on `goose-lean`.
  - `raft-witness`: `upamanyus/etcd` `99cb9e2d98d40d423aa7e7ec1f12f0877a45570e`, branch
    `raft-witness-goose-lean` (etcd-io/raft#168 rebased onto the `raft` pin, with fixes;
    translated into `RaftWitness/`).
  - In this repository (no rev): `kv`, `common` (the examples' shared start and watch workload,
    D33), `putget`, `putget3`, `linkvtxn`, `linkv3p`, `watchkv`, `cachekv`,
    `lintest` (`examples/`), `kvwitness` (`examples/kvwitness`,
    translated into `RaftWitness/`), `porcupine` and `bridge` (`third_party/`). Go modules: one for
    the examples (`examples/go.mod`: every example but kvwitness and k8setcd3, and `common`; not the lintest driver), whose replaces of
    etcd and raft `etc/goose.py --check` compares with the pins; kvwitness's (the witness raft),
    k8setcd3's (it requires `k8s.io/apiserver`; also checked against the pins), lintest's,
    porcupine's and bridge's of their own (D33).
  - `k8s-apiserver`: `examples/k8setcd3` (no rev): the Kubernetes etcd3 store
    (`k8s.io/apiserver` at the driver's `go.mod` pseudo-version) and the driver.

### Trust base

- `etc/tcb-baseline.txt`: **712 axioms, 4 `sorry`s** (2026-10-25, rafthttp stage 7 on branch `rafthttp-snap`, the snapshot stream: four gone, the sender's and the handler's (`Transport.SendSnapshot`, `newSnapshotSender`, `snapshotSender.stop`, `newSnapshotHandler`, all proved, with `snapshotHandler.ServeHTTP`); 21 new: the user's choices `http.respReadAny_of_ok`, `http.ReadAll_any_ok`, `rafthttp.netErrNotRemoved_ok` (7d) and `fmt.SprintfArgs` (7e), the D42 boundary's `http.bodyStreamRead_ok` and `http.ReadFull_stream_ok`, `io.MultiReader`, `(*time.Duration).String`, the ten snapshot metrics'/timeout's/`errMemberNotFound`'s `_init` facts, and D22's `snap.Message.fields`, `snap.Message.CloseWithError` and `snap.Snapshotter.SaveDBFrom`, settled by the user for the D22 owner; `notes/rafthttp-plan.md`, "Stage 7") on 695 (2026-10-25, the pin at Perennial `24bef275e`: raft's `strconv.opaqueInitsOk` gone; 696 since 2026-10-24, the merge of `rafthttp-plan`: rafthttp linked, stage 6f, its 87 boundary items reached, accepted at stages 1 to 6e; eight gone: the transport's five names-only axioms (`Start`, `AddPeer`, `AddRemote`, `CutPeer`, `MendPeer`), `net.http.Serve` (now `http.Serve_ok`), `EtcdServer.RaftHandler` (proved), `path.Join` (`path` translated with its bodies; k8s's `Join(["/", p])` derived, `Proof/path/CleanAbs.lean`)) on 617: S4b's removal of S3's `auth.hasRootRole.wp_proof`
  (2026-10-24, proved over Perennial's `sort.SearchStrings`) on 618: S5's two (2026-10-24: `zap.Logger.Check.wp_proof`,
  `zapcore.CheckedEntry.Write.wp_proof`, logging; "S5 of the auth plan, in part" in
  `notes/decisions.md`) on 616: S4's two (2026-10-24: `auth.authStore.selectPassword.wp_proof`,
  bcrypt and base64, and `zap.Strings.wp_proof`; "S4 of the auth plan" in `notes/decisions.md`) on
  614 (615 until restore R5f): 613 since k8s-etcd3's merge, plus S1's two
  `proto.UnmarshalUser.wp_proof`/`proto.UnmarshalRole.wp_proof` (2026-10-23, "The auth backend's
  read side (S1)" below); S2's three bytes-affine interval tree facts
  `adt.intervalTree.wp_Insert_bytes`/`wp_Intersects_bytes`/`wp_Contains_bytes` (2026-10-23, "The
  permission cache (S2)" below) were axioms until S2b made them theorems (2026-10-24, the tree's
  proof generic in the key representation; `notes/decisions.md`, "S2b of the auth plan"); the 613 (2026-10-23: the
  Kubernetes etcd3 store's and its driver's trust-boundary and initializer axioms; the marked
  `sorry`s `k8setcd3.revRoom`, `k8setcd3.clientErr_other`, `k8setcd3.client_ctx_field` and
  `kubernetes.kvIs_ne_null`, "Kubernetes' etcd3 storage backend" below). Before: 538 axioms, 0
  `sorry`s (sorry-free since 2026-10-22, "`kvHasher`
  translated: no sorry left" below; 537 since "The FIFO scheduler proved" and v2stats's `NewLeaderStats`;
  538 with `mvcc.store.Restore.wp_proof`, "D22 receiver epochs, S6"; 539 with
  `v3alarm.AlarmStore.restore.wp_proof`, S7c; 538 since `context.WithTimeoutBackground.wp_proof`
  is a theorem, 2026-10-23, the client-timeouts plan's T3). Restore R4 option 1
  (2026-10-23) left the count as it was: `mvcc.store.restore.wp_proof` a theorem,
  `mvcc.kbNoCmp_metaNone` added. Restore R5f (2026-10-24): 614, `mvcc.store.Restore.wp_proof` a
  theorem.
- Collections (`etc/tcb-collections/*.txt`; the counts are each file's `axiom` lines; only
  `k8s` (1: `kvIs_ne_null`) and `k8setcd3` (4) have `sorry` lines):
  | collection | axioms | what |
  |---|---|---|
  | `adt` | 0 | etcd's interval tree (`pkg/v3/adt`) |
  | `apply` | 31 | the server's apply package |
  | `backend` | 84 | etcd's backend (`server/v3/storage/backend`), bbolt's boundary |
  | `btree` | 0 | the cache's B-tree (k8s fork of google/btree) |
  | `cache` | 7 | etcd's `cache` package (but `cache_end_to_end_client`) |
  | `cache-client` | 87 | the cache over etcd's client and server (`cache_end_to_end_client`) |
  | `cachekv` | 547 | `cachekv`'s closed theorem `cache_safe` |
  | `client` | 109 | the client's KV path over gRPC (`client/v3/Link.lean`) |
  | `concurrency` | 7 | `client/v3/concurrency` |
  | `k8s` | 75 | the Kubernetes etcd3 store and its kubernetes client (`--k8s`, `--k8s-etcd3` Links) |
  | `k8setcd3` | 601 | the Kubernetes etcd3 store's linearizability instance `k8setcd3_safe` |
  | `kv` | 18 | the key-value store example (`kv_porcupine_safe`) |
  | `lease` | 24 | the client's lessor (`client/v3/lease.go`) |
  | `lease-served` | 65 | the Lease service's unary path from the gRPC handlers |
  | `leasing` | 3 | `client/v3/leasing` |
  | `linkv3p` | 565 | `linkv3p_safe` and `linkv3p_watch_safe` |
  | `linkvtxn` | 529 | `linkvtxn_safe` |
  | `mvcc` | 34 | mvcc's KV core |
  | `mvcc-compaction` | 21 | mvcc's compaction |
  | `putget` | 528 | `putget_safe` |
  | `putget3` | 544 | `putget3_safe` |
  | `raft` | 13 | raft (`Proof/go_etcd_io/raft/v3/Link.lean`, `Results.lean`) |
  | `raft-witness` | 19 | the witness part (`RaftWitness/`: raft and kvwitness) |
  | `read` | 9 | the server's linearizable read loop |
  | `recipes` | 35 | `client/v3/experimental/recipes` |
  | `server` | 256 | etcd's server (`etcdserver/Link.lean`; 187 with the auth backend's `proto.Unmarshal` on `authpb.User`/`Role`, 190 with the permission cache's bytes-affine tree facts, 2026-10-23) |
  | `server-raft` | 7 | the server's raft wrapper (`raft.go`) |
  | `slice` | 55 | the vertical slice, client to server |
  | `snapshot` | 42 | the snapshot path (track T-S, D22) |
  | `txn` | 22 | the server's txn package |
  | `v3rpc` | 98 | the gRPC KV service |
  | `watch` | 60 | the gRPC watch service over mvcc's watch stream |
  | `watchkv` | 544 | `watch_safe` |

  `#print axioms` of a closed theorem counts more (Lean's three, the generated declarations of
  untranslated types and values, Perennial's trusted specs): `kv_porcupine_safe` 342 (section
  "D22 S-r carried out (proof)" below), `linkvtxn_safe` 3116 ("linkv-txn stage G" below).

### The closed theorems

Each is about every real execution of a Go program (its package initialization, then `Main`)
from a fresh state with one thread: no thread is stuck, none ended in a panic (so the program's
own check never failed), and the main thread's result, if any, is as stated. The statements and
`#print axioms` are in each `Results.lean`, whose header says more.

- **`k8setcd3_safe`** (`Proof/github_com/mit_pdos/etcd_grove/examples/k8setcd3/Results.lean`,
  from `Adequacy.lean`'s `k8setcd3_adequate`): `examples/k8setcd3` -- one member (the shared
  start), a kubernetes client, two seeded objects in an older encoding, the Kubernetes API server's
  etcd3 store over the client, `clients` clients of `ops` random `Create`/`Get`/`Delete`/
  `GuaranteedUpdate` calls checked by porcupine against the driver's model of the store -- returns
  `Ok` or `Unknown`. Premises: linkvtxn's at the driver's configuration, the Kubernetes packages'
  semantics assumptions, `objTyOk` (a method-set fact). Rests on the four marked `sorry`s above
  (`notes/k8s-etcd3-plan.md`).
- **`kv_porcupine_safe`** (`Proof/github_com/mit_pdos/etcd_grove/examples/kv/Results.lean`, from
  `AdequacyLinked.lean`'s `kv_adequate`): `examples/kv` -- three raft nodes of a replicated
  key-value store (snapshots and catch-up by `MsgSnap` live since D22 S-r), 4 clients of 25
  random `Put`/`Get`/`Append` on random replicas, porcupine's check -- returns `#()`: porcupine
  always answers `Ok`. Premises: `n < 2^63` steps, the package assumptions, `context`'s
  method-set facts, `log.NewModel`. Raft only (no etcd server).
- **`counter_adequate`** (`examples/lintest/counter/Adequacy.lean`; its `Results.lean` restates
  `wp_CheckCounterClock`): porcupine's translated checker accepts the traces of a counter (4
  clients of 10 operations); `n < 2^63`, `context`'s facts.
- **`putget_safe`** (`examples/putget/Results.lean`): one etcd member in process, its gRPC
  server, a client, a `Put` then a `Get` of the key; returns `#()` (the `Get` saw the `Put`).
  Premises (D19a's kinds; `notes/decisions.md`, D19r): the package assumptions and method-set
  classes, `ContextReadErrs` and, since the calls have request timeouts (2026-10-23, D-T4),
  `ContextErrsClient`, `v3rpc.ServerMethodSets`, the boot facts (`BootFacts`), the
  environment premises `ckptEffectsOk`, `authRecordsFit`, `apply.backendUnderQuota`,
  `storage.dbOpensOk`, unclaimed prometheus names and addresses, `putget.premises`,
  `n + 2 ≤ 2^31`, `n + 7 ≤ backend.wbInit`.
- **`putget3_safe`** (`examples/putget3/Results.lean`): putget's with three members, each serving
  raft on its peer listener; putget's premises for three members.
- **`linkvtxn_safe`** (`examples/linkvtxn/Results.lean`): one member, the robustness tester's KV
  workload (gets, lists, puts, deletes, transactions, compare-and-sets; no leases, no stale
  reads) against the model of etcd's KV; `Ok` or `Unknown`. putget's premises at linkvtxn's
  configuration and `Run`'s bounds on `clients` and `ops`.
- **`linkv3p_safe`** (`examples/linkv3p/Results.lean`): three members whose peer links a schedule
  cuts and mends, and whose client links (through copies of etcd's test bridge) it blackholes,
  unblackholes and drops; three clients each of every member (failover, default retries);
  linkvtxn's workload; `Ok` or `Unknown`, **for every schedule**. putget3's premises, `Run`'s
  bounds, the schedule's length `< 2^63`, `n + 2 ≤ 2^29`.
- **`linkv3p_watch_safe`** (same file): watchkv's workload over the partitioned cluster, a prefix
  watch through the first client, resumed at any member after a cut; result `0`, `1` or `2`
  (`WatchOk`/`WatchFailed`/`WatchEnded`), for every schedule. `linkv3p_safe`'s premises but
  `Run`'s bounds, and watchkv's watcher classes and bounds.
- **`watch_safe`** (`examples/watchkv/Results.lean`): one member, `nw` writers, a prefix watch
  from revision 1; the check that the watched events are exactly the writes (revisions `2, 3,
  ...`, every successful put at its revision) never fails; result `0`, `1` or `2`. putget's
  premises, the client watcher's classes (`ErrorStringNoGRPCStatus`, `ContextErrsClient`, the
  `errors`/`fmt`/`rpctypes` assumptions), `0 ≤ nw < 2^31`, `nw * nops < 2^62`, `n + 2 ≤ 2^29`.
- **`cache_safe`** (`examples/cachekv/Results.lean`): watchkv's program with the watch through
  etcd's `cache` (from revision 2); the same result; `watch_safe`'s premises at cachekv's
  configuration.
- **The witness part**
  (`RaftWitness/Proof/github_com/mit_pdos/etcd_grove/examples/kvwitness/Results.lean`):
  `kv_porcupine_safe` (the kv example on the witness raft) and **`kv_witness_porcupine_safe`**
  (`MainWitness`: two voters and an in-process witness, raft's static mode); kv's premises.
  `RaftWitness/Proof/go_etcd_io/raft/v3/Results.lean` restates no theorem (`#print axioms` of
  the linked results).

Retired (2026-10-22, `notes/decisions.md` D34): **`linkv_safe`** (`examples/linkv`: one member,
`lintest.Run` of random Puts and Gets against a values-only key-value model) and **`linkv3_safe`**
(`examples/linkv3`: linkv's workload over three members, a client to the first), subsumed by
`linkvtxn_safe` (Puts, Gets, Deletes, Txns against etcd's KV model, on the same axioms) and
`linkv3p_safe` (three members, every client of every member, any partition schedule). Their
sections are in `notes/status-history.md` ("D20 (c): linked, initialized, closed", "D20: linkv3,
the three-member instance" and their earlier stages); what linkvtxn and linkv3p took from linkv
moved to them (D34).

Raft's own results are `Proof/go_etcd_io/raft/v3/Results.lean` (the model-level safety lemmas no
linked result used were removed on 2026-10-21: "Clean-up: unused declarations removed, ..."
below).

### What is verified

`etc/verified-code.py` (needs an up-to-date `lake build`, and `go`) counts it per project,
package and file: run it for current numbers. The last counts recorded in these notes
(2026-10-23, at `lean` 17fdef90d0, Perennial c25bef57e): raft 264 of 327 functions (3,126 of
3,707 code lines), etcd 1,077 of 3,602 (12,646 of 45,631 lines; 77 assumed, 55 names-only),
raft-witness 291 of 360, kvwitness 44 of 53, kv 43 of 52, porcupine 25 of 45, lintest 8 of 9;
every function of `common` (14), `linkvtxn` (46), `linkv3p` (11), `watchkv` and `cachekv`
(putget's and putget3's `Main`, linked by hand in their `Results.lean`, are not attributed by
the script). Before: raft 260 of 327, etcd 997 of 3,599 (2026-10-16, stage R8b). How much
of the linked code a closed theorem reaches (2026-10-21): "Clean-up: unused declarations
removed, ..., adequacy coverage" below.

### Open work, by track

- **Snapshots (track T-S, D22).** Done: S-0..S-d4, S-f..S-i, S-g/S-h, S-r (snapshots in
  `examples/kv`), the fork fixes, the receiver epochs' S1-S7f and S8a-S8c (S6's `store.Restore`
  axiom proved since restore R5f, 2026-10-24). Open:
  - **S8d of the receiver epochs** (`applySnapshot` past the empty case; S8a-S8c done, section
    "D22 receiver epochs, S8" below): the spec and proof. Done: W1 (`Rm := snapTakenLb`,
    `storage.Release`'s axiom), W5 (`storage.snapOpensOk` with `backend.dbCloseOk`), W6
    (`RaftCluster.Recover`'s axiom; `bootOk`'s persistent `Members()` contract), W7's first part
    (the readers' open shares fixed, `backend.rdOpen`; `store.Restore` returning exactly
    `nReaders - 1` old tokens; user-confirmed). Open, questions for the user (`notes/decisions.md`,
    "D22 S8d, W7 carried out (first part)"): W7's second part (where the old backend's stop channels
    and `bOpen ½` reach `applySnapshot`: every route changes a predicate a closed theorem reaches);
    `RemoveAllPeers` over `trLive` (the membership track's M5 plans its spec and proof); W8 a named
    premise (user-confirmed), S-j1's with the rafthttp track. Since: W7's second part and W8 named
    premises (the user's), `RemoveAllPeers.spec` over `trLive` with its proof a `sorry` for M5;
    the auth store's `Recover` a named premise (the user's (a)); **blocked on two questions**
    (`notes/decisions.md`, "D22 S8d, second pass against the callees"): `RaftCluster.Recover`'s axiom
    ignores `clusterMem` (a gap in a trusted statement, no proof uses it yet) and `lessor.Recover`'s
    wants `leaseOwn γl []`. Both restated (the user's (a)). **Since 2026-10-26**: `specSnap` stated
    and proved from `applySnapshot_walk` (the whole code, proved) and `srvSnapApplied_of_walk` (the
    post's assembly: **`sorry`**, its seven steps listed in `notes/snapshot-s8-plan.md`, "S8d, where
    it stopped"); not linked (linking adds the cache's assumptions to `applyAll_model` and the run
    results: a question, `notes/decisions.md`, "D22 S8d: the spec stated, the walk proved").
  - **S-j, the receiver** (`raftNode.start`'s snapshot branch; `applySnapshot` past the empty
    case: the backend swap, the `Recover`s, `kv.Restore`, the transport's peers re-made; +6 to +8
    axioms estimated) and **S-k** (the quota after the swap, with S-j): wait on the epochs.
    `s.alarmStore` stays read-only, `Recover` to be translated and proved ("D22 fork fixes"
    below).
  - **S-l, lifting the bound** (last): `bootOk` without `"%Hnosnap"`, `NewServer.spec` without
    `receiptBound ≤ SnapshotCatchUpEntries + 1`, putget/putget3 at etcd's defaults, their closed
    theorems re-checked. The stages: `notes/decisions.md`, "T-S: the snapshot path, scope and
    staging (D22)".
  - **D22c revisited**: done (2026-10-23), section "D22 the backend over every bucket" below;
    the compaction keys (`bkNoCmp`) stay an opaque token.
- **Kubernetes' etcd3 storage backend (D30).** Planned, nothing proved: `notes/k8s-etcd3-plan.md`
  (next step: merge the survey branch `k8s-etcd3-goose`, which changes the etcd project's
  configuration and waits on an OK from the etcd client proof's owner; then phase 1). Partly
  blocked on Perennial changes (below). Decisions D30a-f in `notes/decisions.md`.
- **Raft.** The static `ownRaftPhys` is a sealed alias of `ownRaftPhysC` since 2026-10-24
  (`ownTracker`, `ApplyCCOk`, `SwitchOk` gone; "Clean-up: unused declarations, the static
  `ownRaftPhys` an alias" below); the predicate itself goes with the static mode.
  `ownRaftGhost`'s `md : Bool` (tried and reverted). Raft's 42 linked results that no
  closed theorem reaches (the storage's snapshot path, the public `RawNode` methods,
  `ProposeConfChange`/`TransferLeadership`/`ForgetLeader`, ...); etcd's server runs raft in the
  static mode only: a dynamic-mode server needs the membership writers translated and a stopping
  server (D21d (B)). All in "Clean-up: unused declarations removed, ..." below.
- **The witness part.** The premises W4 left (`notes/raft-witness.md`, "W4"): configuration
  changes and snapshots only at witness-free configurations (status-history.md, "Witness
  support, W3b-A").
- **Client and examples, duplication.** `notes/dedup-plan.md` (2026-10-22): 9 exact duplicate
  lemmas, the points-to-halves, set-replicate, option-fold, namespace-mask and option-model
  families, the watch facts proved twice over two models, the thread-token wait groups of the cache
  and leasing (Perennial's `tokJoin` plus owed tokens), the witness part's 26 identical files;
  ordered steps, the Perennial lemmas first. Applied (branch `dedup`): A, B, C5 (i), C7; C8
  checked and left; C1-C4, D landed in Perennial (`f97c83add`, the pin) and the local copies
  deleted; C5 (ii)-(iii) judged not worth it; C6 and E wait on their decisions.
- **Client.** `concurrency`, `recipes` and `leasing` are verified but in no closed theorem. (The
  retry-bound tracking went on 2026-10-22, branch `retry-bound`: "Clean-up: the watch client's
  joins, ..." below.)
- **Leases in the KV model (unit T3).** The lease table in `KVState`, leased puts and
  transactions; discharges `kvLeasedPutTodo`/`kvLeasedCommitTodo`
  (`client/v3/ServerKVPut.lean`), which the recipes' results take; needs `lessor.Revoke` proved
  (status-history.md, "Open work: the client→server path ...", item 1; `notes/decisions.md`,
  "Unit T3").
- **cachekv.** A check of the cache's `Get` after the writers (not cheap: "cachekv" below).
- **Initialization.** `os`'s and `strconv`'s four init axioms (`os.opaqueInitsOk`,
  `os.initFuncsOk`, `os.Stderr_init`, `strconv.opaqueInitsOk`) need a Perennial change
  ("Trusted initializers" below; deferred, the user's choice).
- **Out of scope for now** (the user's choices, 2026-10-14/15; status-history.md, "Open work: the
  client→server path ..."): crashes and durability (Perennial's Lean port has no crash
  semantics; persist-before-send is neither stated nor checked); floats (`Promote`,
  `scheduleCheckpointIfNeeded` stay axioms). (The client libraries on top of the server, out of
  scope then, have since been verified: cache, concurrency, leasing, recipes.)
- From the old "Next" list (status-history.md, "Next"): follow the Rocq RawNode branch past
  `857d09190` (its worktree has an uncommitted edit to `proof_RawNode__Ready.v`, not ported).

### Open Perennial changes (`notes/perennial-changes.md`, "Open")

- `word`'s caches shared between parallel declarations (workaround here: one proof's heartbeat
  limit raised; "`word`'s shared cache" below).
- Goose: range over a function (`iter.Seq`/`iter.Seq2`): blocks the k8s store's `GetList`.
- Goose: field selection through a type alias of a struct: the k8s watcher and compactor.
- Goose: imports of packages whose types a body names, and same-named packages (a silent
  mistranslation).
- Specs of `reflect`: the k8s store's unary methods.
- Standard library: `encoding/json`, `encoding/base64`, `iter`, `path` not translated; specs of
  `strconv`, `fmt.Sprint*`, ...; `hash` (types-only here; `hash/crc32` has no model).

Landed: the three proof idioms (a synchronous SPSC channel, a thread-token join,
`wp_fork_tok_upd`), in the pin `537c426e0` ("Perennial idioms" below); `WithTimeout`/
`WithDeadline` of `Background()`, in the pin `c25bef57e` (2026-10-23, the client-timeouts plan's
T3).

### Plan files (`notes/*-plan.md`)

- `auth-plan.md`: etcd's authentication and authorization (the auth store, RBAC at the API
  layer, an auth-enabled closed theorem; etcd-io/etcd#22595, #22540). **Active**: A0 done
  (2026-10-23, the authorization model `auth/Model.lean`, the contracts over it,
  `notes/auth-matrix.md`); A1 done for the checks and the API layer (2026-10-23,
  `apply/AuthClass.lean`; the method-level statement is its follow-up); S1 done (2026-10-23,
  `authpb` as data, schema's auth backend's read side over the buckets, the store's contract
  with the mode; "The auth backend's read side (S1)" below); S3 done (2026-10-24, the store's
  checks return the model's verdicts in every mode, `isAuthStore_of_authInv` in the store's own
  mode, the verdict's shape corrected; "The checks compute the verdicts (S3)" below); S2 done (2026-10-23, the
  permission cache computes the model's coverage of a recorded state, the bytes-affine tree's
  three facts axioms until S2b; "The permission cache (S2)" below); S4b done (2026-10-24, the pin at Perennial's sort specs, `hasRootRole` proved, the revocations and `RoleDelete` as model steps; the grants left; "S4b of the auth plan" in `notes/decisions.md`); S2b done (2026-10-24, the
  tree's proof generic in the key representation `adt.KeyRep`, the three axioms theorems,
  `Contains` proved; "S2b of the auth plan" in `notes/decisions.md`); A4 done (2026-10-24, the
  registered watcher's authorization in the stream specification; "The watch shapes (A4)"
  below); A3's API layer done for the Auth service (2026-10-24, seventeen gRPC wrappers over the server's methods as contracts, fourteen entry points over `raftRequest` as a contract, three unproved (`Authenticate` for a package fact, `UserAdd`/`UserChangePassword` names only); "The Auth service at the API layer (A3)" below); S4 begun (2026-10-24, the
  admin operations as steps of the model's state: `AuthEnable`, `AuthDisable`, `UserAdd`,
  `UserDelete`, `UserChangePassword`, `RoleAdd`, `Recover` proved over the write side's contract,
  +2 axioms; "S4 of the auth plan" in `notes/decisions.md`); S4's apply part (2026-10-24, the six
  proved operations as model steps at the apply layer, `apply/AuthSteps.lean`; "S4's apply part" in
  `notes/decisions.md`); S5b in part (2026-10-24, the simple provider's `info` and `assign` over a lock invariant, `assign`'s `Authenticate` context premise; "S5b of the auth plan, in part" in `notes/decisions.md`); S5 begun (2026-10-24, the token
  binding over the provider's contract, `AuthInfoFromCtx` and `Authenticate` carrying it, +2
  logging axioms; "S5 of the auth plan, in part" in `notes/decisions.md`); S4c (2026-10-24, the
  decoded messages the caller's, `UserGrantRole` and `HasRole` proved; "S4c of the auth plan" in
  `notes/decisions.md`); S4d (2026-10-24, `RoleGrantPermission` proved at the store and the apply layer: every admin operation a step; "S4d of the auth plan" in `notes/decisions.md`); A3c (2026-10-24, Lock and Election over the server's client as a contract, six of seven handlers; "A3c of the auth plan: Lock and Election" in `notes/decisions.md`); the reads, S5's rest
  (the simple and JWT providers; S5c, 2026-10-25: `isValidSimpleToken` proved on a context, "S5c of the
  auth plan, in part" in `notes/decisions.md`; S5d, 2026-10-25: the admin share, the simple provider meeting the contract over `RunSpec`, "S5d of the auth plan"), `Observe` and `v3client.New`, E open.
- `membership-plan.md`: membership changes in the server (track T-M, D21d (B)): the server in raft's
  dynamic mode, a member removed at run time (then added), the stopping server. **Planned**
  (2026-10-25); M0 in part: Q1-Q4 decided (D43: removal only, pre-vote and `StepDownOnRemoval =
  false` proved in the dynamic mode, the removed member's own stop). **M2 done** (2026-10-25, branch
  `membership-m2`): raft's dynamic mode with pre-vote on (M2b), `StepDownOnRemoval` off (M2c) and a
  new cluster's boot log (M2a: `StartNode`/`Bootstrap` in either mode); D43, "M2a"-"M2c".
- `client-cut-plan.md`: cuts between clients and members in linkv3p. **Finished** (2026-10-21,
  K0-K4; K2 dropped, D26).
- `client-timeouts-plan.md`: the examples' clients configured as etcd's clients are in practice
  (etcdctl's dial, request and keepalive timeouts; every call under `context.WithTimeout`).
  **Finished** (2026-10-23: T0-T2 on `client-timeouts`, T3 on `with-timeout-bg`; "The examples'
  clients configured as in practice: request timeouts" below).
- `dedup-plan.md`: duplicated and near-duplicated lemmas in the examples, the client and the
  cache (an audit of 2026-10-22: exact duplicates, lemma families, Perennial candidates, the
  witness part's copies). **Active**: A, B, C1-C5 (i), C7, D done (the Perennial lemmas landed,
  the pin `f97c83add`); C6, E wait on decisions.
- `k8s-etcd3-plan.md`: the Kubernetes etcd3 storage backend. **Active**, planned (D30).
- `restore-plan.md`: proving `store.restore` and closing `store.Restore` (R0-R6). **Finished**
  (2026-10-24). `restore` is proved, with data, and `store.Restore` is proved over its ghost moves;
  both axioms are gone. In R6's fingerprint check, no closed theorem's text changed. The
  server-based examples' `*_safe` theorems reach the R5a clean-view flag through `bootstrap`'s
  contract (`newPost`), which is true of `bootstrap` at the pin (the plan, R6).
- `keepalive-plan.md`: keepalive and failover on a silent partition. **Finished** (2026-10-21,
  D28).
- `linkv-txn-plan.md`: linkv over Delete and Txn. **Finished** (2026-10-20, `linkvtxn_safe`).
- `linkv3p-txn-plan.md`: linkv3p over linkvtxn's workload. **Finished** (2026-10-20).
- `partition-plan.md`: linkv3p under network partitions. **Finished** (2026-10-20, S0-S3b).
- `raft-retarget-plan.md`: raft v3.7 over protobuf-go v2. **Finished** (R0-R8b, 2026-10-15/16;
  status-history.md, "Retargeting raft to v3.7, stage R0" to "stage R8b").
- `read-retry-plan.md`: read retries with the default configuration. **Finished** (2026-10-21,
  D29).
- `watch-cut-plan.md`: watches across a cut. **Finished** (W4, `linkv3p_watch_safe`, 2026-10-22:
  "Watches across a cut" below; the plan's own Status line predates W1-W4).

Other notes in use: `notes/snapshot-receiver-epochs.md` (S5's plan),
`notes/snapshot-rest-buckets.md` (D22c revisited), `notes/raft-witness.md` and its companions,
`notes/perennial-changes.md`, `notes/audit.md` (the axiom audit).

# Raft and the witness part

In status-history.md: the raft v3.7 retarget ("Retargeting raft to v3.7, stage R0" to "stage R8b"), reconfiguration (stages 0, A1-A3, B1-B8, D, L, N), the read index and proposals (stage R, stage F), CheckQuorum and PreVote, the multi-member stages "D21 M0" to "D21 M6", and the witness stages W1-W3b-A and W5.

## The server's token facts (E2c) (2026-10-25, branch `auth-e2c`)

The auth plan's E2c (`notes/auth-plan.md`; `notes/decisions.md`, "E2c of the auth plan"): the
server-side facts E2b found `Main` needs.

- **The context's own token**: `AuthInfoFromCtx`'s auth info is `nil` or bound to the token the
  request context's incoming metadata carries (`auth.ctxTokenOf ctx`, over the opaque
  `metadata.incomingOf`; `FromIncomingContext`'s trust-boundary spec and `rpctypes`' token-key
  initializers say more, same axioms). `ctxBound`, `ctxBoundOrTLS`, `principalBound`,
  `principalBoundI`, `adminOutB`, `authedOutB` and the guards' bound variants take the context.
- **One user per token** (`tokIssued_agree`): `tokIssued` keyed by the token, issuing spends the
  exclusive right (`tokFresh`), the authority keeps each issued token's spent right.
- **The simple shape** (`tokIssued_shape`): every issued token is `<prefix>.<raft index>`; the bad
  token was issued to no one (`tokIssued_badToken`, `authkv_badToken_not_issued`).
- Trust base unchanged (718 axioms, 5 sorries).

## The end-to-end auth example (E2b) (2026-10-25, branch `auth-e2b`)

The auth plan's E2b (`notes/auth-plan.md`; `notes/decisions.md`, "E2b of the auth plan").

- **The program** `examples/authkv` (project `authkv`): one member with the simple token
  provider, auth set up and enabled through a client (`SetUp`), four principals (`u` with role
  `r` on `[a, b)`, `v` with none, no token, the token `badtoken`) running puts, ranges, deletes,
  transactions (both branches, nested) and watches inside and outside `[a, b)`; `Main` panics if
  a refused request returned no error, a reply holds a key its principal may not read, or root's
  watch of the history shows a write its principal was not permitted. Go test passes, also under
  `-race`; translated; its `Init`/`PkgTable` generated.
- **Proved**: `InRange`, `Permitted` (`Link.lean`) and, pure, the model's verdict at the
  set-up's state (`Model.lean`'s `setupSt`, `granted_setupSt_iff`) and the bad token's shape
  (`ClientAuth.lean`); restated in `Results.lean`, collection `etc/tcb-collections/authkv.txt`.
- **Stated, not proved**: `Main`'s triple (`Spec/.../authkv/Main.lean`; the proof a `sorry`, +1
  to the baseline), with watchkv's premises for the server's start.
- **Found**: `ctxBound` must name the context's token (a bad principal's request was bound to
  "some issued token"); the issued tokens' shape and one user per token are needed facts (all
  three done in E2c);
  D29's refusal-freedom is false of an auth-enabled member (the bad principal's writes are
  refused with a refusal and resent by the client). Each is in the decision, with the client's
  auth contract C1-C4.

## The watch shapes (A4) (2026-10-24, branch `auth-a4`, worktree `/shared/etcd-grove-a4`)

The auth plan's A4 (`notes/auth-plan.md`; `notes/decisions.md`, "A4 of the auth plan").

- **The statement**: a created, not canceled, control response's watcher (`v3rpc.ctrlWatcher`,
  in the stream specification `watchDn`) carries `v3rpc.watchAuthed γ c`: in some mode the
  store's owner tag names (`auth.modeTag γ.tag M`; the server's, `watchSrvOk`), the class of the
  request's read for some principal (`apply.watchClass M info c.key c.rangeEnd`, the key
  normalized -- empty is `"\x00"` -- and the range end as the request gave it, the check's
  arguments) and the request's shape (`auth.reqShape`). `recvLoop` keeps `isWatchPermitted`'s
  class (A1's) and builds it at the registration.
- **The bridge to mvcc's range** (`v3rpc/WatchClass.lean`): `createRangeOk_inRange`, every key
  the registered `mvcc.WatchRange` covers is in the model's interval of the check, for a point,
  a proper range, `"\x00"` (`WithFromKey`: the rewritten end `[]`, or `none` in the model) and the
  empty key; `watch_permitted_covers`; `ctrlWatcher_authorized`, restated as `Results.lean`'s
  `watch_registered_authorized`: in `on γa`, a recorded state at which auth was disabled, or the
  principal a root user, or one whose READ permissions cover every covered key. GHSA-xg4h-6gfc-h4m8
  (the check after the rewrite of `"\x00"` to `[]byte{}`, a point check for an open-ended watch) is
  what this lemma excludes at the pinned revision.
- **The mode's name**: the stream specification (`watchDn γs γ cid mid j m`) has no auth mode in
  scope and its arity is fixed by the client's proofs and the examples; the mode is recorded
  under a ghost name of the watchable store's names (`mvcc.WsNames.tag`, the owner's tag:
  `newWatchableStore`/`mvcc.New` take it as `γtag`, of no meaning to mvcc), tagged by
  `server_kv_watchable_of` with the server's mode (`.off` in `NewServer`), exported by
  `srvWatchBuilt`/`srvWatchReaders` and held by `watchSrvOk`.
- **Progress/cancel requests** register nothing (`ctrlWatcher` is `True` of them); `Fragment` and
  the filters change no class. The principal is per create request (`AuthInfoFromCtx` of the
  stream's context, S5's binding): a watcher registered under a token later revoked keeps
  delivering, as etcd documents.
- Trust base unchanged; no closed theorem's statement changed (the examples run in `off`).

## The API layer's auth guards (A2) (2026-10-23, branch `auth-a2`, worktree `/shared/etcd-grove-a2`)

The auth plan's A2 (`notes/auth-plan.md`; `notes/decisions.md`, "A2 of the auth plan").

- **Translated** (`etc/goose.py --project etcd`; `v3rpc.toml`, `etcdserver.toml`):
  `v3rpc/auth.go`'s `AuthAdmin.isPermitted` and `AuthAdmin.requireAuthInfo` with their promotions
  through `authMaintenanceServer`, the eight `authMaintenanceServer` wrappers (`maintenance.go`),
  the server's `checkMembershipOperationPermission`, `RemoveMember` and `MemberList`
  (`server.go`); the inner operations (`maintenanceServer`'s methods, `mayRemoveMember`,
  `configure`) stay names only; `etcdserverpb.MemberListRequest` as data (`etcdserverpb.toml`:
  the spec names its `Linearizable` field, and a field of an axiomatized message reaches the
  message's `sorry` instances). Not `AddMember`/`UpdateMember`/`promoteMember`: they call
  `encoding/json.Marshal`, which Perennial has no model of (the translation does not compile).
- **Proved** (17 functions, linked in the server's and `v3rpc`'s `Link.lean`): the guards
  `EtcdServer.requireAuthInfo`, `EtcdServer.checkMembershipOperationPermission`,
  `AuthAdmin.isPermitted`, `AuthAdmin.requireAuthInfo` and the two promotions, with the outcomes
  `authedOut`/`adminOut` (`Proof/go_etcd_io/etcd/server/v3/etcdserver/AuthGuard.lean`: on `nil`
  the token `authedRes`/`adminRes` for the request's auth info, in the mode `on γa` a recorded
  state that passes; `authedOut` never an error with auth off, and auth enabled at a recorded
  state on an error); the guarded entry points `kvServer.Compact`,
  `authMaintenanceServer.{Defragment, Snapshot, Hash, HashKV, Alarm, Status, MoveLeader,
  Downgrade}`, `EtcdServer.RemoveMember`, `EtcdServer.MemberList`, each over its inner
  operation's triple as a contract whose precondition carries the token
  (`v3rpc/InvAuthAdmin.lean`: `guardedOk2`, `guardedSnapOk`, `compactOk`; `AuthGuard.lean`:
  `configureRemoveOk`; `MemberList` over the read loop's `isReadNotify` and
  `RaftCluster.Members`): the inner operation runs only after a passing check, and with auth off
  always (`guardOut`: the inner answer, or `nil` and an error with the caller's resource
  untouched).
- **A premise** (`srvAdminNilOk s E`, `adminNilOk`): `IsAdminPermitted(nil)`. The admin guards
  pass `AuthInfoFromCtx`'s `nil` answer (no token) to it; `apply.isAuthStore`'s clause and the
  store's spec take a non-`nil` auth info. Until the store's spec covers `nil` (track S), the
  admin guards' specs take the clause as a premise (decisions). `kvServer.Compact`'s spec takes
  the `aa` field as a premise (`kvServerIs` does not record it; `NewKVServer`'s statement is
  closed).
- **Not done**: the member operations above and the `ClusterServer` wrappers; the lease entry
  points (`EtcdServer.LeaseGrant`/`LeaseRevoke` go through `raftRequest`, whose `reqPropOk` has
  no lease request; the gRPC lease handlers' specs are closed over the server's contract);
  `checkLeaseTimeToLive`/`checkLeaseLeases`/`checkLeaseRenew` (a lessor with a key model). No Go
  findings.
- **Trust base**: unchanged (`etc/tcb-baseline.txt`; the `server` and `v3rpc` collections gain
  roots, no axiom). `etc/gen-link.py --server`/`--v3rpc` regenerated.

## The auth backend's read side (S1) (2026-10-23, branch `auth-s1`, worktree `/shared/etcd-grove-s1`)

The auth plan's S1 (`notes/auth-plan.md`; `notes/decisions.md`, "S1 of the auth plan").

- **Translated**: `authpb` as data (`Code/go_etcd_io/etcd/api/v3/authpb.toml`, as `raftpb`'s:
  the messages' types and getters, `Permission_Type.Enum`; the protobuf plumbing and the enum's
  name maps names only); schema's `auth.go`, `auth_users.go`, `auth_roles.go` with bodies, the
  auth buckets, their names, the two key names and `authEnabled`/`authDisabled` as package
  variables (`schemaInit` gains seven conjuncts, appended; `etc/gen-init.py`'s schema entry
  extended; the cache's `Base.lean` declares `protoreflect`'s package-init instance before
  `authpb`'s).
- **Proved** (13 functions, `Spec/Proof/go_etcd_io/etcd/server/v3/storage/schema/`, linked in
  the server's `Link.lean`): `unsafeReadAuthEnabled`, `unsafeReadAuthRevision`, `unsafeGetUser`,
  `unsafeGetRole`; `authReadTx.{UnsafeReadAuthEnabled, UnsafeReadAuthRevision, UnsafeGetUser,
  UnsafeGetRole, RLock, RUnlock}`; `authBackend.{ReadTx, GetUser, GetRole}` -- over the contracts
  of `Proof/go_etcd_io/etcd/server/v3/etcdserver/InvAuthBackend.lean`: `authReader r H D` (an
  `UnsafeReader` whose point reads of the three buckets are the snapshot `D : AuthData`'s under
  the token `H`), `authRTx rt R Held` (a `ReadTx`: `RLock` gives a well-formed snapshot's token
  with its reader, `RUnlock` takes it back), `authBE bi R Held` (a `Backend`); their posts over
  `D` (`enabledOf`, `revisionOf`, `userOutD`, `roleOutD`), `authWf D` the premise (every user and
  role value an encoding, the revision 8 bytes).
- **The records** (`Proof/go_etcd_io/etcd/server/v3/auth/Buckets.lean`): `UserRec`, `RoleRec`,
  `PermW` (`permOfWire`: an unknown type grants nothing), `userEncode`/`roleEncode` opaque,
  `ownUser`/`ownRole` (the message owned, its byte fields read-only slices), `userOut`/`roleOut`
  (what the reads return of a state), `authSnap M st` (a read transaction's state in the mode).
  **`authBucketsAre st D`** (`InvAuthBackend.lean`): the buckets hold the state (`userOutD_are`,
  `roleOutD_are`).
- **The store's contract** (`auth/InvAuth.lean`): `authReadTxOk tx R M` -- `RLock` gives the token
  `Hs st` of a state `st` of the mode (`authSnap`), the reads under it are the state's
  (`authTxReads`: `userOut`, `roleOut`, the flag, the revision), `RUnlock` gives `R` back;
  `authBackendOk`, `beP`, `authInv`, `beRd`, `authRd`, `authReadTxLocked` take `M`; the 13
  request-side specs quantify over `M` (their proofs drop the new facts), the derivations
  `isAuthStore_of_authInv`, `isReqAuth_of_authInv`, `authRevision_of_authInv` are for any `M`.
- **Trust base**: +2 axioms, `proto.UnmarshalUser.wp_proof` and `proto.UnmarshalRole.wp_proof`
  (`Spec/google_golang_org/protobuf/proto/Unmarshal{User,Role}.lean`, the pattern of the
  `mvccpb.KeyValue` one): 540 axioms, 0 sorries; the `server` collection. No closed theorem
  changed (nothing produces `authInv` yet: `NewAuthStore` is an axiom over the derived
  contracts in `off`).
- **Not done**: `unsafeGetAllUsers`/`GetAllUsers` (`backend.UnsafeForEach` has no spec);
  `unsafeGetAllRoles` through a read transaction (it panics: `issues/etcd-auth-readtx-
  getallroles-panics.md`, the finding of this stage); the batch-transaction methods and
  `CreateAuthBuckets`/`ForceCommit` (the write side, S4); the derivation of `authReadTxOk` from
  schema's proofs with the link of the history's latest state to the tracked buckets (S4).
- **A tactic finding**: `wp_apply` of a Lean spec at a deferred call admits silently
  (`notes/perennial-changes.md`, "`wp_apply`'s frame list can admit a goal silently", the second
  instance); `wp_bind` + `iapply` works.

## The permission cache (S2) (2026-10-23, branch `auth-s2`, worktree `/shared/etcd-grove-s2`)

The auth plan's S2 (`notes/auth-plan.md`; `notes/decisions.md`, "S2 of the auth plan").

- **The tree's queries, pure** (`Proof/go_etcd_io/etcd/pkg/v3/adt/Contains.lean`): `inIvl`,
  `stab_point_iff` (`Intersects` of `[k, k ++ "\x00")` is membership), `containsRes` (the loop of
  `Contains`) and `containsRes_iff` (the scan is the coverage of the query, for a query whose begin
  is below its end, over entries in the tree's order; no premise on the entries).
- **The bytes-affine tree** (`adt/BytesIvl.lean`): `ownIvtB t L dq`, the string-affine `ownIvt`
  with each key a read-only slice; proved: `ownIvtB_of_empty`, `ownIvtB_persist`, `ownIvtB_sorted`.
  **Axioms** (the trust boundary; `etc/tcb-baseline.txt`): `intervalTree.wp_Insert_bytes`,
  `wp_Intersects_bytes`, `wp_Contains_bytes`, stated as the string-affine specs and `containsRes`;
  removed by S2b (the tree's proof over a comparator: about 130 node unfoldings and 25 `Compare`
  calls of 8,200 lines, and the pure model's uses of `affCmp_eq_zero_iff`). `Contains` for
  string-affine keys is not proved either (`Visit`'s visitors never stop).
  `BytesAffineComparable.Compare` proved (`affCmp` on the contents, through `bytes.wp_Compare`).
- **The cache** (`auth/InvAuth.lean`, `auth/PermTree.lean`): `permsAt p Lr Lw` (the entry's two
  trees, read-only), `cacheOk M Mp` (in `on γa`: one recorded state, its users the map's keys,
  each entry's lists the user's permissions' intervals as multisets, `cacheEntryIs`/`ivlsOf`/
  `permIvl`; else the entries), `cacheP st M q`, `cacheVerdict M user k e pt b`
  (`isRangeOpPermitted`'s: in `on γa` a recorded state whose user's permissions of the type cover
  the point/range iff the check passed, for a non-empty key and an empty, open-ended or proper
  range, under `permKeysOk`; a missing user the refusal). The bridge `inIvl_permIvl`,
  `coversPoint_iff`, `coversRange_iff` (a non-empty key: the affine `""` is the top, the model's
  the least key). `authReaderOk ti Hs` (the `UnsafeAuthReader`'s reads, with `UnsafeGetAllUsers`)
  split out of `authTxReads`.
- **Proved** (`Spec/Proof/go_etcd_io/etcd/server/v3/auth/`, the server's `Link.lean`):
  `checkKeyPoint`, `checkKeyInterval`, `isOpenEnded` (restated), `isRangeOpPermitted` (the
  verdict), `getMergedPerms` (nil iff no such user, else `permsAt` with `cacheEntryIs`),
  `refreshRangePermCache` (the map rebuilt under the write lock, `cacheOk` of the transaction's
  state), `isValidPermissionRange` (`rangeValid`); `isOpPermitted`/`IsAdminPermitted` adapted
  (the verdict dropped: S3's). New model premises: `permKeysOk`, `permsFit`, `rangeValid`
  (`Model.lean`); `ownPermW`'s key fits a slice with room for one byte (`Buckets.lean`).
- **Not done**: S2b (above); schema's `unsafeGetAllUsers` (no `backend.UnsafeForEach` spec; it
  does not panic on a read transaction, unlike `UnsafeGetAllRoles`); `isOpPermitted` returning
  `permVerdict` (S3).

## The principal through the apply chain (A3, the apply layer) (2026-10-24, branch `auth-a3`, worktree `/shared/etcd-grove-a3`)

A1's follow-up and the apply part of the auth plan's A3 (`notes/auth-plan.md`;
`notes/decisions.md`, "A3 of the auth plan, the apply layer").

- **The model** (`Proof/go_etcd_io/etcd/server/v3/etcdserver/apply/{Chain, AuthClass, InvUber}.lean`):
  `chainRes c a info` (the outermost auth layer's `authInfo` holds the principal `info`; the inner
  chain's resources at any, `chainResAny`); `authInfoIdle p` (the mutex holds the zero
  `AuthInfo`); `principalOf rq` (the header's `Username`/`AuthRevision`, else zero); `reqClass`
  (the request's KV class from A1's `putClass`/`deleteClass`/`rangeClass`/`txnClass`),
  `chainClass M info c rq oc` (each wrapper: if it did not reject, the rest; the auth layer: the
  class), `authPassed`, `chainClass_alarm`; `adminPass M c rq` (`Apply`'s admin check passed for
  `principalOf rq`); `applyAuthRes` (the uber-applier's and the package's `Apply`); `userGetClass`.
  Every pre/post of `applierTriples` takes `info`; `mPost` returns the resources at any principal
  (`UserGet`/`RoleGet` reset the field when they reject).
- **Proved** (the apply package's 70-odd method and constructor proofs rethreaded; no new spec
  file, `Link.lean` unchanged): the KV posts carry the class through every layer
  (`auth_pass_kvPostF`, the dispatch proof's `fin_kv`/`fin_same`); `authApplierV3.Apply` hands
  the `applyFunc` the resources at `principalOf rq` (the header's fields written into the zero
  field, or none) and states `adminPass`; `uberApplier.dispatch`'s post has `∀ _ : v3 = true,
  chainClass …`, `uberApplier.Apply`'s and `apply.Apply`'s `applyAuthRes`;
  `authApplierV3.Range`/`DeleteRange` derive their class from the checks' verdicts
  (`rangeClass_of_verdict`, `deleteClass_of_verdicts`); `authApplierV3.UserGet` says a `nil` error
  is an admin's or the user's own request; `Results.lean`'s `chain_put`/`chain_deleteRange`/
  `chain_range`/`chain_txn` restate the class for the uber-applier's chains.
- **Not done**: `RoleGet`'s has-role case (`HasRole` has no model), `LeaseRevoke`'s keys (the
  lessor's key model), the class through the generic `respMethods` triple (`UserGet` at the
  method level only), the server-level statement in `applyEntryNormal`/`entryStep` (E). No Go
  findings.
- **Trust base**: unchanged (`etc/tcb-report.py --check`); no closed theorem's statement changes.
## The Auth service at the API layer (A3, the API layer) (2026-10-24, branch `auth-a3b`, worktree `/shared/etcd-grove-a3b`)

The API-layer part of the auth plan's A3 (`notes/auth-plan.md`; `notes/decisions.md`, "A3 of the
auth plan, the API layer").

- **The vocabulary** (`Proof/go_etcd_io/etcd/server/v3/etcdserver/AuthEntry.lean`): the requests
  `irrAuthEnable`, ..., `irrRoleGet name`, `irrAuthenticate am` (`apply.irrEmpty` with one
  field); `authRaftOk s ctx rq T P Q`, `raftRequest` on the request `rq` as a contract (its spec's
  `reqPropOk` admits no auth request), answering a response of the type `*T` or an error the apply
  package's facts describe; `authEntryOut`. The gRPC side
  (`.../api/v3rpc/InvAuthServer.lean`): `authServerIs p s`, `authInnerOk s m ctx r P Q`,
  `authWrapOut`.
- **Proved**: the seventeen `AuthServer` wrappers (`v3rpc/AuthServer__{AuthEnable, ...,
  RoleDelete}.lean`: the server's method, then `togRPCError`), `NewAuthServer` with its object;
  fourteen entry points (`etcdserver/EtcdServer__{AuthEnable, AuthDisable, AuthStatus, UserDelete,
  UserGrantRole, UserGet, UserList, UserRevokeRole, RoleAdd, RoleGrantPermission, RoleGet,
  RoleList, RoleRevokePermission, RoleDelete}.lean`: the request built with the one field,
  `raftRequest` on it, the response asserted to its type). The admin check of every one of them
  is the apply layer's (`apply.adminPass` for the header's principal, the apply part above).
- **Not proved**: `Authenticate` (translated; `auth.ErrAuthNotEnabled` is not in the auth
  package's fact `authInit`); `UserAdd`, `UserChangePassword` (names only: translating them
  imports bcrypt and base64, whose initializer axioms would reach every closed theorem, and
  `base64.StdEncoding` has no fact). `UserChangePassword` of oneself is not in the pinned
  code (`needAdminPermission`).
- **Not started**: Lock and Election (`v3lock`, `v3election` over the client's `concurrency`
  package, whose proofs exist; the in-process client's premises are the question).
- **Translation**: fifteen `EtcdServer` Auth methods (not `UserAdd`, `UserChangePassword`) and
  the seventeen `AuthServer` wrappers with bodies; `AuthenticateRequest`,
  `AuthUserChangePasswordRequest` as data.
- **Trust base**: unchanged (`etc/tcb-report.py --check`); no closed theorem's statement changes.

## The checks compute the verdicts (S3) (2026-10-24, branch `auth-s3`, worktree `/shared/etcd-grove-s3`)

The auth plan's S3 (`notes/auth-plan.md`; `notes/decisions.md`, "S3 of the auth plan").

- **The verdict's shape corrected** (`auth/Model.lean`): A0's `permVerdict` promised one recorded
  state at which `permitted` (with the revision conjunct) held on a pass and one at which it failed
  on a refusal; neither is true of `isOpPermitted`, which reads the flag, the revision, the user and
  the cache under four locks (an admin change between the revision read and the user read defeats
  the first; a missing user is read at another state than the flag for the second). Now `permitted
  st ai key rangeEnd op := st.enabled = false ∨ granted st ai key rangeEnd op` (no revision), and
  the `on γa` verdict is: a state that permitted and a state whose revision admitted the token (or
  at which auth was disabled) on a pass, a view of the four states read (`AuthView`, `recordedV`)
  in which the check refuses (`refusedV`) on a refusal; `adminVerdict`'s refusal names the flag's
  and the user's states (`adminRefused`). `reqShape` (a non-empty key; a point, an open-ended or a
  proper range: what the cache decides) is a premise inside `granted`/`refusedV`. `authStateAt`/
  `authHist` carry `permKeysOk`. A1's `classOk` and A2's `adminRes` consume the unchanged first
  conjunct.
- **The invariant** (`auth/InvAuth.lean`): `enabledP st M q` and `revInv st M` hold the mode's
  verdict beside the flag and the atomic; `enabledRd st M`, `authRd`, `authInv` thread the mode;
  `authInfoAt a dq ai` (`Option AuthInfo`: `nil` or the message).
- **The specs** (`Spec/.../auth/`): `isOpPermitted` for an `AuthInfo` whose fields are the
  arguments, returning `permVerdict M info k e (permOp pt) err`; the three `Is*Permitted`
  `permVerdict` with their type; `IsAdminPermitted` over `authInfoAt` returning `adminVerdict M ai
  err`; `IsAuthEnabled` `enabledVerdict`, `Revision` `revisionVerdict`; `hasRootRole`'s axiom
  restated (a sorted-roles message, `decide (isRoot ur.roles)`, the message kept). Proved by
  `auth/VerdictLemmas.lean` (one lemma per branch of the Go code, for every mode).
- **The contract** (`apply/Contracts.lean`, `apply/AuthDerive.lean`, `etcdserver/AuthGuard.lean`):
  `isAuthStore` gains `IsAdminPermitted(nil)` as its last clause (A2's premise `adminNilOk`/
  `srvAdminNilOk` is derivable: `adminNilOk_of_isAuthStore`, `srvAdminNilOk_of_srvAuthAt`;
  dropping it from the 12 guarded entry points' specs is a mechanical follow-up);
  `isAuthStore_of_authInv` derives the contract in the store's own mode (was `.any`).
- **Trust base unchanged** (618 axioms; `hasRootRole`'s statement changed); no closed theorem's
  statement changes (nothing produces `authInv` yet).
- **Not done**: `hasRootRole` translated (needs a Perennial spec of `sort.SearchStrings`);
  `AuthInfoFromCtx`'s token binding (S5); the premise's removal from A2's specs; S4 produces
  `authInv` in `on γa`.
## Kubernetes' etcd3 storage backend: phase 4's unary methods proved (2026-10-22, branch `k8s-etcd3`)

**2026-10-23: merged into `lean`.** The merge ported the work to lean's changes: the driver's
`Main` starts its member through the shared start (`common.StartServer`, `common.Serve`, D33; a
write sent at most once because the member is refusal-free, D29, so `kubernetes.New`'s spec no
longer gives a one-attempt fact), the kubernetes client's proofs read `clientErr`/`statusErrOk`
out of D37's `kvErr` and use `ClientPutGet.lean`'s lemmas (D35), linkv's modules come from
linkvtxn (D34), and the etcd pin is `goose-lean-getproph2` (`bc9c3868c`). `k8setcd3_safe` and its
four `sorry`s unchanged; D37 discharges the sentinel half of `clientErr_other` only (plan, item 5).

**2026-10-23: the driver's closed theorem** (stage 6g of `notes/k8s-etcd3-plan.md`).
`k8setcd3_safe` (`Proof/github_com/mit_pdos/etcd_grove/examples/k8setcd3/Results.lean`): one
in-process member, the kubernetes client, the seeded store, the etcd3 store over it and porcupine's
check of `Create`/`Get`/`Delete`/`GuaranteedUpdate` traffic against the driver's model never panic
or get stuck, and return `Ok` or `Unknown`. Its hypotheses are linkvtxn's at the driver's
configuration, the Kubernetes packages' semantics assumptions and `objTyOk` (a method-set fact).
It rests on four `sorry`s: `revRoom` (the revision bound, D30n), `clientErr_other` and
`client_ctx_field` (from the client proof's owner: items 5 and 6 of the plan), and `kvIs_ne_null`
(item 3). The trust base adds the trust-boundary axioms of the names-only functions on the
initialization and constructor paths (`etc/tcb-collections/k8setcd3.txt`); Perennial limitations
found: `≤u` without a transitive instance, embedded interfaces' type sets, `os.Getenv`/
`strconv.ParseBool` (`notes/perennial-changes.md`).

`notes/k8s-etcd3-plan.md` (decisions D30a-l; D30h-j and D30l proposed). Branch `k8s-etcd3`: `lean` with the
translation survey `k8s-etcd3-goose` merged; merged into `lean` 2026-10-23, the etcd pin moved
to the fork's `goose-lean-getproph2` (`bc9c3868c`: `goose-lean`'s `188113160` with the prophetic
`kubernetes.Client.Get`).

- **A finding**: `correctness.Model` rejects the store's intended rewrite of non-canonical or stale
  data on a no-op update (`issues/k8s-correctness-model-noop-rewrite.md`, Go reproduction). D30g
  (decided): the generic specs use a model with a canonical bit per item; the driver keeps its
  non-canonical codec and checks against a fixed copy of the Model in `examples/k8setcd3/`.
- **The model** (`Proof/k8s_io/apiserver/pkg/storage/etcd3/Model.lean`, sorry-free): `create`,
  `delete`, `update`, `get` over linkv's abstraction (D30i), `correctness.Model`'s update on
  canonical states; the store's transactions move it as the model (`absK_create`, `absK_delete`,
  `absK_update`), keeping the store's states (`KWf_put`, `KWf_del`).
- **The object contract** (`Contract.lean`, D30k): the codec, versioner, transformer and decoder
  as a premise (`contractOk`), the WPs of the exact calls the store makes (`runtime.Encode(codec,
  obj)` among them), errors with an `Error()`.
- **The kubernetes client** (`Spec`/`Proof/go_etcd_io/etcd/client/v3/kubernetes/`, linked):
  `Get`, `OptimisticPut`, `OptimisticDelete` over linkvtxn's failover calls (`Calls.lean` now
  needs only the client's and v3rpc's assumptions). Their errors are the client's (`clientErr`,
  `statusErrOk`: the failover lemmas `client_*_any` and `txn_Commit_st` now keep them). One
  `sorry`, `kvIs_ne_null`: a response's key-value pointer is not `nil`, which `txn.kvIs` does not
  state (the plan's request 3 to the client proof). `Count` not done.
- **The store** (`Proof/k8s_io/apiserver/pkg/storage/etcd3/`, linked by `etc/gen-link.py
  --k8s-etcd3`; collection `etc/tcb-collections/k8s.txt`):
  - `store.Get`: a linearizable read (the caller's persistent read update at each member, whose
    state is the store's): the model's `get` at the state it fired at (`respIs`: the object at
    its mod revision, the zero object, "not found"), or the client's error.
  - `store.Create`: a write fired at most once (`k8sAu1`, D30h's one-shot part: the caller's
    relational update, whose next state the store chooses; `k8sAu1_kvAu1` turns it into the
    client's for the transaction it sends, by `stepOk_create`): the model's `create` at the state
    it fired at (the object at the new revision, or "key exists", `create_out`), or an error.
  - Helpers: `prepareKey`, `storage.PrepareKey` (against `prepareKeyM`), `getTypeName`,
    `txnError`, `validateMinimumResourceVersion` (no minimum), the storage error constructors.
  - Restrictions for now: a valid key, no minimum resource version on `Get`, an input object
    without a resource version on `Create`, `ttl = 0`.
- **Trust base added**: trust-boundary axioms for the names-only calls of the unary paths
  (tracing `Start`/`AddEvent`/`End`, `audit.GetAuditIDTruncated`, the store's metrics,
  `strings.HasSuffix`/`Contains`, `reflect.TypeOf`); the package facts in
  `Proof/k8s_io/apiserver/pkg/storage/etcd3/Base.lean` (`True`, but the metrics package's
  `ErrTransactionConflict`).

- **`store.Delete`** (linked; D30l: the caller's persistent read-or-write update `k8sAuRW` with
  a write token `W`): its outcome is the model's `delete` (`delOut`): at the state the write fired
  at, the deleted object at the new revision; or at the read a read-like answer came from ("not
  found", `validateDeletion`'s error, nothing changed, `W` back); or the client's error. The
  pieces, each proved and linked: `stateFromEtcdResponse` (the store's reading of a key-value into
  a fresh object of the store's type, through `reflect`), `getCurrentState` (a persistent closure,
  `getStateOk`), `refreshOnError` (a current state), `deleteOnce` (`OptimisticDelete` from the
  caller's updates, `k8sAusRW_kvAu1`; a key-value at the read mod revision has the read value by
  the caller's history, `kvSeen_same`, D30j; success is the model's `delete`, `delete_at`; a
  conflict leaves etcd's state as it was, `del_cases`), `conditionalDelete` (the retry loop).
  Restrictions for now: a valid key, no preconditions, no cached object, no unsafe deletion of a
  malformed object (`opts.ExpectTransformOrDecodeError` false); `validateDeletion` is the caller's
  callback answering a function of the object (`validateOk`).
- **`store.GuaranteedUpdate`** (linked; D30l's update with the model's `update`): its outcome is
  the model's `update` with the canonical bit (`updOut`): the write at the state it fired at
  (`destination` the result at the new revision); a read-like answer at a read (`tryUpdate`'s
  error, "not found", or the no-op of an unchanged canonical object: the store's
  `!stale && bytes.Equal(data, origState.data)` is the model's test, `update_skip` by
  `noop_iff`); or an error (the client's, the codec's, the transformer's). `tryUpdate` is the
  caller's callback answering a function of the object and its revision (`tryUpdateOk`,
  persistent: it runs at each retry, D30h's "repeatable spec"). The pieces: `updateState`,
  `updateOnce` (as `deleteOnce`, by `put_cases`/`update_at`/`updStepOk`),
  `storage.Preconditions.Check` on `nil`; `refreshOnError` now on `ownStateX` (the state without
  its object, which `tryUpdate` took). Restrictions for now: a valid key, `ignoreNotFound` false,
  no preconditions, no cached object, no TTL.
- **The caller's updates, reworked for the driver's linearization points (D30n, 2026-10-23)**:
  `k8sAuRW` (`Updates.lean`) no longer has a read postcondition `Q` and a write token returned at
  reads: it fires as a plain read any number of times, and once as the linearization point, which
  hands the caller's timeless token `W` (the model's `step` must hold there: the write, or, at a
  read, a state where the step is the identity, `stepHand`). The first read goes through a call
  invariant (`FirstRead.lean`, `rwInv`): `Client.Get` is now prophetic (the etcd fork's branch
  `goose-lean-getproph`, `942601555`, off the pinned `2aed163b1`: `Get` resolves a prophecy of the
  response's revision and the key's mod revision, so its spec's single read update fires at the
  state with that pair), and `rwInv_after` gives the caller's result at a state with the answer's
  item and revision (`update_local`/`delete_local`) or `W` back. `deleteOnce`/`updateOnce` hand the
  result at a conflict whose state is the identity; `conditionalDelete`/`GuaranteedUpdate` carry it
  in their loops. The outcome predicates (`delOut`, `updOut`) are two cases: the client's error, or
  the caller's result at a state with the model's answer. All proved and linked; the trust base is
  unchanged.
- **The driver's linearization (stage 6f, 2026-10-23)**: `examples/k8setcd3`'s `Apply` proved
  logically atomic against the driver's model (`k8setcd3S g0`) in `lintest`'s `applySpec` form:
  the invariant (`Proof/.../k8setcd3/Inv.lean`), the updates and commits (`InvSteps.lean`),
  `errOut`, `call`, `Apply`. Two marked `sorry`s (D30n): etcd's revisions do not run out
  (`revRoom`), a client error is neither a `*StorageError` nor the driver's sentinels
  (`clientErr_other`). The store's `Get` is now prophetic (a read update per prophesied pair) and
  the caller's write updates report `KvNext` (`Updates.lean`); the store's history authority is
  `History.lean`. Not yet linked: 6e and 6g remain.
- The contract now names the objects' Go type (`ObjSpec.objTy`: a non-nil pointer to it,
  `objAt_ptr`; `reflect.New`'s allocation is the zero object, `newObj`; a `runtime.Object` and not
  a `runtime.Unstructured`, `tyOk` in `contractOk`).
- `reflect`'s reasoning principles, as axioms for now (the user's choice, 2026-10-22; a trusted
  model with proved principles later, in Perennial): `Proof/reflect/Values.lean` (`reflect.Value`'s
  typed points-to, `reflElem`/`reflPtr`/`reflType`/`reflNew`) and the specs of `reflect.New`,
  `Value.Addr`/`Type`/`Interface`, `conversion.EnforcePtr` (`notes/perennial-changes.md`); linked
  by `Delete`.
- More trust base: `klog.V`/`Verbose.Infof` (axioms, now linked); `util/feature`'s package fact
  (`featureInit` in `Base.lean`: `DefaultFeatureGate` holds a gate whose `Enabled` answers some
  `bool`); `features.AllowUnsafeMalformedObjectDeletion` is not a panic value
  (`Proof/k8s_io/apiserver/pkg/features/Values.lean`, `notes/perennial-changes.md`).

Next: the driver (phase 6, unary traffic first), with the restrictions above lifted as its
traffic needs; `Get`'s minimum resource version, preconditions, cached objects,
`ignoreNotFound` on updates.
## The examples' clients configured as in practice: request timeouts (2026-10-23, branch `client-timeouts`, worktree `/shared/etcd-grove-ct`)

`notes/client-timeouts-plan.md` (T0, T1 and T2's gates done; T3 waits on Perennial),
`notes/decisions.md` D-T1..D-T5. The etcd examples' clients made every call with
`context.Background()` and set no `DialTimeout`; keepalive was linkv3p's alone. Now:

- **The configuration** (`examples/common/common.go`): etcdctl's defaults, `DialTimeout` 2s,
  `RequestTimeout` 5s, `KeepAliveTime` 2s (grpc's 10s floor applies), `KeepAliveTimeout` 6s;
  `common.NewClients(eps, lg)` (`NewClient(addr, lg)` is `NewClients({addr}, lg)`); linkv3p's
  `newClient` (10s / 2s) is gone. Every member's `common.Serve` passes embed's keepalive policy
  (`MinTime` 5s), as linkv3p's `startMember` did.
- **Every unary call** in `ctx, cancel := context.WithTimeout(context.Background(),
  common.RequestTimeout)`, `cancel()` after the call (client/v3's documented form): putget's and
  putget3's Put and Get, `common.Writer`, linkv3p's `writer`, linkvtxn's five `call*`. Watches keep
  `WithCancel`.
- **The proofs.** One lemma, `client.wp_WithTimeout_bg`
  (`Proof/go_etcd_io/etcd/client/v3/TimeoutCtx.lean`), over the read loop's trust-boundary axiom
  `context.WithTimeoutBackground` and `context.ErrAny`: the context is `ctxOk` and `ctxErrClient`
  (`ctxErrClientAllW_of`'s argument, under `ContextReadErrs` and `ContextErrsClient`), `cancel`
  callable. Each call site applies it, calls at the new context, and `cancel`'s triple; every
  spec on the call chains takes the two classes. `common.NewClients` is linkv3p's `newClient`
  spec and proof moved (`clientCfgOk` leaves `DialTimeout` free, keepalive by `kaOpts`).
- **Statements.** The conclusions of the closed theorems are unchanged; `putget_safe`,
  `putget3_safe`, `linkvtxn_safe` and `linkv3p_safe` take `ContextErrsClient` (the watch theorems
  did), since a timed-out call's error now flows through the client.
- **Trust base.** No new axiom (the baseline stays at 539); `grpc.KeepaliveEnforcementPolicy.wp_proof` enters the
  `putget`, `putget3`, `linkvtxn`, `watchkv` and `cachekv` collections (+1 each).
- **The Go tests.** All pass (`go test` of every example, linkv3p with `-race`). linkv3p's
  `TestFailover` rewritten: the blackholed member's calls fail at 5s, 10s and 15s (request
  timeouts, reads too: the client never retries past the caller's deadline) until the keepalive
  close at 16s fails the calls in flight; then failover and the return. `cutRun` accepts a read
  that failed at its request timeout and no other read failure; `TestWatchFailover`'s blackholes
  are 18s (past the 16s close). `TestFailover` takes about two minutes (12000 operations per
  worker).
- **T3 (branch `with-timeout-bg`, the same day).** Perennial `c25bef57e` (branch
  `with-timeout-background`): `wp_WithDeadlineCause_Background_of`, `wp_WithDeadline_Background_of`,
  `wp_WithTimeout_Background_of` (`Proof/context/WithDeadlineBackground.lean`: the no-deadline
  branch of `WithDeadlineCause`'s proof over `Background()`'s facts), exposed in its `Results`;
  `propagateCancel`'s spec takes any child for a `Background()` parent (Go never looks at the
  child when the parent's `Done()` is `nil`; a `*timerCtx` registers itself). The pin moved to
  it; `context.WithTimeoutBackground.wp_proof` is a theorem over `wp_WithTimeout_Background`
  (its spec unchanged, so no Link changed): 538 axioms, one fewer in `read`, `server` and the
  six etcd examples' collections.

## The examples' shared code: `examples/common` (2026-10-22, branch `examples-common`)

`notes/decisions.md` D33. A Go package of this repository, `examples/common` (a package of the
examples' module `examples/go.mod`, its own module until branch `examples-module`; project `common`
of `etc/goose.py`), holds what the
etcd examples each had a copy of, with what differed (names, ports, the cluster's map and token, the
keys, the panic messages' prefix) as parameters; its proofs are `Proof/.../examples/common/` (linked
in its `Link.lean`, `etc/gen-link.py --common`), which the examples' Links take as `@` callees.

- **Stage 1, the one-member start and the client** (putget, linkv, linkvtxn, watchkv, cachekv):
  `newServer` (the member's configuration and `NewServer`), `StartServer` (`newServer`, `Start`:
  `wp_Start_built`), `Serve` (`v3rpc.Server`, `Listen`, `go gs.Serve(l)`; its spec takes the
  caller's ghost step from `grpcUp` to `grpcServeTok` and the caller's `Q`, since the step differs:
  `kv_served`, `grpcUp_noRefusal` then `kv_served`, or watchkv's `wk_served`), `NewClient`;
  `alloc1` (putget's and watchkv's allocations at a workload parameter). Each example's
  `premises` stay its own; `bootPremise_of` gives the shared form.
- **Stage 2, the three-member start** (putget3, linkv3, linkv3p): `NewMember` (`newServer`, the
  raft handler served at the peer address), `StartMember` (`NewMember`, `Start`); `alloc3`
  (putget3's `putget3_alloc`, linkv3's and linkv3p's `cluster3_alloc`). linkv3p keeps its own
  `startMember` over `NewMember` (its client listener before `Start`, the keepalive policy, the
  watch stream served).
- **Stage 3, the watch workload** (watchkv, cachekv, linkv3p's `MainWatch`): the types `KV`,
  `PutRec`, `Event`, `Writes`; `Gen(keys)`, `GenAll`, `Writer` (one client), `MaxRev`, `Collect`
  (generic over the watch's model and the caller's response lemma: watchkv's `resp_wk`, linkv3p's
  `resp_hist`), `Attempted`, `Check(name, put, ...)` (the panic messages each example's,
  verbatim), `checkOk_of`; `WatchBase.lean` and `Writes.lean` moved from watchkv (re-exported
  there). Kept: cachekv's `collect` (the cache's cancels, not `Err()`), linkv3p's `writer` (a
  client per put at random) and `checkOkH_of` (the history's `revAtH`).
- Statements: no `Results.lean`, `Adequacy.lean` or example `Main` spec changed; the programs the
  closed theorems name call `common`'s functions (their translations changed). Trust base 543
  axioms, every collection unchanged. `go test -race` passes for every example (linkv3p's
  `TestFailover` failed once under a concurrent Lean build, a timing flake; it passes on a quiet
  machine, before and after).

## Clean-up: unused declarations, the static `ownRaftPhys` an alias (2026-10-24, branch `cleanup/2026-10-24`)

The proof-cleanup skill's pass over `origin/lean` `5e1c1155a9`: 102 files, +442/-2,996 lines (net
-2,554), 258 declarations removed and 6 added. No closed theorem, exported result or definition
they reach changed; trust base unchanged (615 axioms, 4 `sorry`s, every collection); no function
left the verified count (`etc/verified-code.py`).

- **Unused declarations** (`etc/dead-decls.py`: 9,889 lines before, 8,115 after): 252 removed
  where no remaining code names them, in the main tree (-544 lines, 46 files) and in `RaftWitness/`
  (-1,477 lines, 44 files: mostly the part's copies of what the main tree removed on 2026-10-21,
  "Clean-up: unused declarations removed, ..." below). The build is the check of the uses that
  leave no trace in terms; those it found (`@[simp]` lemmas `dsimp` uses, the `op_simps`
  attribute's registration, a lemma used by dot notation, `omit ... in` prefixes) are why the pass
  keeps every `@[simp]` lemma and instance. Also kept on purpose: the auth store and Kubernetes'
  store (active plans), bbolt (unlinked), the modules no root imports (D22's `SnapSend*`,
  `RestorePre`, `SnapMint`; auth's `*Derive`), what a plan or design note names for work to come
  (D22's receiver lemmas `bkRestAt_boot`, `imageAt_*`, `keyView_of_keyImage`,
  `restoreLogOk_len`, `srvWTPool_take_two`, `consInv_withPh`, the freeze/swap of `InvApply`;
  mvcc's `muHeld_*`; `node_ready_receive_ns`, `snapDataOk_triv`, `SnapScopeIf.of_scope`; adt's
  `visitL_sublist`; the client's `kvErr_ne`), and the witness part's presented results
  (`Results.lean` imports `MemstorageInstance`, `ResultsDyn`, `Facts` "so the build checks them")
  and the witness-free accessors `notes/raft-witness.md` lists. Removed although a note names
  them: watch-cut's lifting lemmas `kv_cert_cmp`/`kv_cert_rev` (W2b; the plan finished without
  them) and the dedup plan's list of unused client and example lemmas ("Pending").
- **The static `ownRaftPhys` an alias of `ownRaftPhysC`** (-535 lines, -16 declarations): the
  bullet "The static `ownRaftPhys` is an alias" in the 2026-10-21 section below; the design in
  `notes/decisions.md`, "The static `ownRaftPhys` as an alias of `ownRaftPhysC`". Fingerprint
  (`.claude/skills/proof-perf/fingerprint.py --diff`): `ownRaftPhys` changed (its body), the
  private `ownRaftPhysDef` and `ownTracker` gone, `LearnerFlags`/`LearnersOk` no longer reached
  (they were through `ownTracker`'s body), and `CfgM.simple` now reached in the main tree too
  (through `ownRaftPhys`; its definition is unchanged) -- all reached by intermediate specs only.
- **Not done.** The remaining `Timeless`/`Persistent` instances nothing uses (about 30 in the
  witness part's ghost state): kept, a predicate's standard interface. The `muHeld_*` and D22
  lemmas above wait on their plans; if a plan changes course they are the next to go.

## Clean-up: unused declarations removed, proposals registered once, adequacy coverage (2026-10-21, branch `clean-up`, merged into `lean`)

The goal (the user, 2026-10-21): adequacy for all the raft/etcd code -- snapshots and
reconfiguration included, not only what today's closed theorems call -- with simpler proofs,
invariants and predicates, and no lemma that a complete etcd system's adequacy does not need.

- **`etc/dead-decls.py`** (new; needs an up-to-date `lake build`, `--assume-built` to read the
  `.olean`s as they are): this repository's declarations that no root (a `Link.lean` theorem, a
  `Results.lean` theorem) reaches through statements, definition bodies and proofs, per file,
  and the modules no root imports. Unlike the textual scan of "Dead code removed" it sees what
  the elaborated terms use; it does not see what leaves no trace in a term (`@[simp]`/`rfl`
  lemmas `dsimp` uses, a lemma named in a `simp` set it did not use, a definition behind a body
  Lean does not export, anonymous instances), so a removal is checked by the build and by a
  scan for names a remaining file still mentions. A matcher (`match_n`) shared by two
  definitions does not make its owner used.
- **Removed** (four commits, about 8,800 lines; trust base unchanged, `tcb-report.py --check`):
  in raft, the model-level safety results no linked result or closed theorem uses
  (`raft_dyn_committed_agree`/`_election_safety`/`_read_states`/`_read_index`, `log_matching`,
  `state_machine_safety`, `leader_completeness`, `is_Storage_MemoryStorage`/
  `memStorage_isStorage`) and their print lines in `Results.lean`; the old static model `Step`
  (`Protocol/Model.lean`, 400 lines), its derivation `step_of_stepC`, the `step_*`/`stepC_*`
  lemmas and the last simple-configuration spec forms (`FollowerStepResult`,
  `CandidateStepResult`, `HupOk`, the `*.simple` derivations); unused `raftOwn_access_*` loads
  and stores, tracker, memstorage, protobuf and log helpers. In the rest of the main tree the
  same, conservatively: kept whatever a remaining file names, `@[simp]`/`rfl` lemmas, `bbolt`
  (unlinked) and the auth store (the unlinked `AuthDerive`/`AuthReqDerive` derive its contract
  from the real store: future adequacy work). The curated etcd-level results nothing linked
  uses, as raft's: mvcc's watch guarantees (`watchGuarantee_unfiltered`, `watchRecvOk_*`),
  `csContract_noHook`, `kiCompact_kiCompact_le`, txn's history laws (`stateAt_revs`,
  `stateAtPfx_*`, `LogOk.snoc`, `NoDupKeysPerRev.*`, `sel_keys_nodup`), v3rpc's
  `intervalsOk*Stmt_*`, adt's `inorder_rotate*`/`maxEnd_eq_of_inorder`, with their print lines. `RaftWitness/` untouched (its own copies).
- **Proposals: one kind, registered once, proposed any number of times** (the user: "raft has
  a disjunction for proposals to be multi or single ... unnecessary"; then the design of
  2026-10-21: a public ghost step commits a data to its result predicate). The spec:
  `node_prop_register : propFresh γ d ={E}=∗ propIs γ d Q` (raft's public ghost step, once per
  data: the client commits `d` to `Q`), `node.Propose.spec`'s precondition `propIs γ d Q ∗
  propAu1 γ d Q` (`propArg`), its postcondition the error alone; committed entries as before
  (`isCommitted`, `entDataIs`), and `prop_collect : propIs γ d Q ∗ isCommitted γ L ∗ L[m] = e ∗
  entDataIs e (some d) ⊢ ▷▷□ Q (L.take m)`. The same `d` may be proposed again, each proposal
  with its own update. The ghost state (`Protocol/Ghost.lean`, `GhostState.lean`): the registry
  `d ↦ (γq, γd)` (`PropRec`: `Q`'s saved predicate, `d`'s map of deposits); `d`'s slot holds its
  results (`□` at every committed occurrence, each as `qRes γq`, a result carrying its own copy of
  the saved predicate, so that nothing in raft compares predicates: no later credit at a firing)
  and its deposits `k ↦ γt`, each unfired (the update `Propose` handed in) or fired (its ticket
  spent at an index within the log); a deposit's ticket `γt` (`propTk`) travels with the
  proposal and the leader that appends it records its index (`propIdx`: some deposit of `d` was
  appended there). Firing a committed entry of `d` (`LeaderCompleteness.lean`) fires the deposit
  its record names, which cannot have fired before (a fired deposit's index is within the log,
  the entry's past it). Gone: `propMulti`, the `once` flag, `propOnce`, `propOcc`,
  `propIdx_agree` (no longer true: two deposits of one `d`), the handle in `Propose`'s
  postcondition (`propRes`, `isProp`), raft's persistent `propAu` and the server's `srvPropAu`
  (each built only to be weakened to `propAu1`/`srvPropAu1`). The server keeps its interface
  (`srvPropArg`/`srvPropRes`): its bridge (`NodeBridge.lean`) registers then proposes, and its
  handle `srvIsProp` is `propIs` of the lifted predicate. The register (`examples/kv`) retries a
  dropped proposal again (the Go code as on `lean`, `for Propose(...) != nil {}`): `KV.do`
  registers the operation's datum once and its loop's invariant is `True` (each attempt takes the
  registration and a new update from `kv_propAu`, whose premises are persistent); its invariant's
  escrow (`opSlot`, `firstOcc`) and `apply`'s dedupe handle a datum committed more than once, as
  before. (On 2026-10-21, before this design, the register stopped instead of retrying, and every
  proposal was "once" with the fresh token in `Propose`'s precondition: superseded the same day.)
- **Not done: `ownRaftGhost`'s `md : Bool`.** It restates `γ.reDyn.isSome`, and within
  `ownStepGhost` the mode is also `ghostRest`'s (`CfgStatic`'s `γ.reDyn = none`, the dynamic
  configuration). But at the static allocation paths -- `NewRawNode`'s `rnInit` (a bare
  `ownRaftGhost`), `RawNode.Bootstrap`, `RestartNode` -- `md = false` is the only carrier of
  `γ.reDyn = none`, so removing it adds that fact to their linked specs and to the server's
  start path: the fact moves, it does not go. Tried and reverted (2026-10-21).
- **Simple-configuration statements retired** where the caller can take the `C` spec
  (`becomeFollower`, `switchToConfig`, `ProgressTracker.VoterNodes`, `confchange.Restore`; net
  -190 lines). Kept: `raft.applyConfChange.specS`/`spec_simple`, a shared derivation for three
  static callers (`wp_rn_raft_applyConfChange`, `RawNode.ApplyConfChange`'s two static arms);
  since 2026-10-24 it returns `ApplyCCOkC (CfgM.simple cfg lrn')` with `lrn' = domSet s'.progress
  \ cfg`, read by `applyCCOkC_step` in `rawNode_applyCC_reseal` (below).
- **The static `ownRaftPhys` is an alias** (2026-10-24, branch `cleanup/2026-10-24-raftphys`; net
  -535 lines). `ownRaftPhys cfg r id s` is the sealed alias of `ownRaftPhysC (CfgM.simple cfg
  (domSet s.progress \ cfg)) r id s` (`ownRaftPhys_toC`/`ownRaftPhys_ofC`); `ownRaftPhysDef`,
  `ownRaftPhys_intro`, `ownRaftPhys_tracker` and the static `iNamed_phys`/`reseal` macros are
  gone, and every other static lemma keeps its statement, reproved from its `C` counterpart (most
  in one line). `ownTracker` (`InvTracker.lean`) with its lemmas and the conversions
  (`ownTracker_toC`, `ownTrackerC_toSimple`/`_toTracker`) went too: `ownRaftPhys_tracker_same`
  and `ownRaftPhys_intro_trk` (intermediate) now hand out/take `ownTrackerC` at the simple
  configuration, with `ownTrackerC_resimple` (a non-joint tracker is at its simple configuration)
  and `ownTrackerC_empty`. `applyConfChange.specS` returns `ApplyCCOkC`; `ApplyCCOk`/
  `applyCCOk_step`, `SwitchOk`, `LeaderSwitch`, `CommitOk` are gone. No exported statement
  changed (`ownRaftPhys`, `ownTracker`, `ApplyCCOk`, `SwitchOk`, `CommitOk` were in none). Still
  static: `ownRaftPhys` itself (its users: `rawNodeFresh`, `newRaft.spec`, `raft.loadState.spec`,
  `RestartNode`, `RawNode.Bootstrap`, `ownRawNode_static_open`) -- the static mode's view, which
  goes with the static mode.

**Adequacy coverage** (`Link.lean` theorems reached by a closed theorem -- `putget_safe`,
`putget3_safe`, `linkv_safe`, `linkv3_safe`, `linkv3p_safe`, `linkvtxn_safe`, `watch_safe`,
`cache_safe`, `kv_porcupine_safe` -- over the linked ones, 2026-10-21): raft 279/321, server
`etcdserver` 237/273, `v3rpc` 111/123, `apply` 87/90, `txn` 72/75, `read` 30/30, `mvcc`
138/177, `backend` 81/117, client 155/184, cache 91/149, btree 30/51, `adt` 25/28; the client's
`concurrency` (0/107), `recipes` (0/76) and `leasing` (0/140) are verified but in no closed
theorem. Raft's 42 unreached are the gaps the goal names: the snapshot path of the storage
(`MemoryStorage.ApplySnapshot`/`Compact`/`CreateSnapshot`/`SetHardState`/`InitialState`), every
public `RawNode` method (etcd drives raft through `node`), `node.ProposeConfChange`/
`TransferLeadership`/`ForgetLeader`, `confChangeToMsg`, the conf-change and `ConfState`
getters. The structural reason for reconfiguration: **etcd's server runs raft in the static
mode** (`RNMode.static`: `NodeStart`, `InvRaftNode`, `BuildGap`, `newRaftNode`), only the
register uses the dynamic mode; a dynamic-mode server needs the membership writers translated, a
stopping server and the rest of D21d (B) (decisions.md, the static-membership restrictions). With
it the static mode -- a second code path through every raft spec (`RNMode`, `CfgStatic`, the
static ghost state) -- could go.

## Witness support: the `RaftWitness` part (2026-10-21, branch `raft-witness`)

The witness work (W1-W4 below, done in place on the main raft and kv trees) moved into a parallel
tree so that it lands in `lean` without changing any main proof: `RaftWitness/{Code,TrustedCode,
GeneratedProof,ManualProof,Spec,Proof}/` (lean_lib `RaftWitness`, in the default build), and
`examples/kvwitness` (its own Go module). The main `Code/`, `GeneratedProof/`, `Spec/`, `Proof/`,
`TrustedCode/`, `ManualProof/` and `examples/` (but `kvwitness/`) are `lean`'s exactly: raft at
`c8217eb9`, no witness. History: the move was pure renames (`git mv`), the main tree then checked
out from the merge base, `lean` merged, and the part set up on lean's Perennial (`a39a3d14c`).
- Translations: `etc/goose.py` projects `raft-witness` (fork `99cb9e2d9`, raft's packages and
  configuration, `RaftWitness/Code/**.toml`; raftpb's trusted no-op initializers copied into
  `RaftWitness/TrustedCode/`, its message table 10 long) and `kvwitness`.
- The part imports the main tree but never the main raft or kv (same declarations). The main
  modules it imported that reach them are copied into it: the Spec/Proof pairs of `slices.Sort`,
  `strings.Join`, `fmt.Sprintf`, `strconv.FormatUint` (its spec importing the part's raft `Base`
  instead of the server's `BaseApply`), `crypto/rand.Int`, `math/big.{NewInt,Int.Int64}` and
  protobuf-go's `proto.{CloneConfState,CloneEntry,CloneSnapshot,EqualConfState,
  MarshalConfChange(V2),UnmarshalConfChange(V2),SizeEntry}`; and the generated initializers of
  porcupine, lintest, protobuf's `internal/impl`, `internal/pragma`, `reflect/protoreflect`,
  `runtime/protoimpl` and `Proof/runtime/PkgInitExt` (it imports raft's translation), now
  generated by `etc/gen-init.py` for the part too (`PART_INITS`).
- Lean's raft changes since the merge base (the perf rewrites of `raft__Step/*`, `raft__send`,
  `stepLeader/*`, the trusted initializers in `Init.lean`) ported into the part's copies (a file
  the witness work did not change taken as is, the others merged three-way; one conflict,
  `MsgRest.lean`'s `local_leader`, resolved by hand); the part built at once.
- kv became kvwitness: Go package path `.../examples/kvwitness` (package name still `kv`), Lean
  namespaces `github_com.mit_pdos.etcd_grove.examples.kvwitness`, the specs' qualifier
  `kvwitness.` (`etc/verified-code.py` finds them by it), the link list's `kvwitness_` names.
- Links `etc/gen-link.py --raft-witness`/`--kvwitness` (from `etc/link-lean-first-raft-witness.txt`,
  `-kvwitness.txt`: specs searched in both roots, the part's first); the `Link` of an `@` callee is
  looked up in its spec's root.
- Trust base: `etc/tcb-baseline.txt` unchanged (the copies' axioms have the main names);
  `etc/tcb-collections/raft-witness.txt`, 19 axioms (raft's and kv's, and `strconv.FormatUint`,
  which raft#168's `ReplicationSet.String` calls), no `sorry`; `kv_witness_porcupine_safe` without
  `sorryAx`. `etc/verified-code.py`: raft-witness 291 of 360 functions, kvwitness 44 of 53.
- Not kept: W1's witness-free adjustments of the server, putget, putget3 and linkv (they use the
  main raft).

## Witness support, W4: the kv example with a witness (2026-10-21, branch `raft-witness`)

Closed theorem `kv_witness_porcupine_safe` (`examples/kv/Results.lean`) for the new Go entry
point `MainWitness()`: the cluster `StartClusterWitness([]uint64{1, 2}, 3)` (two voters and an
in-process `raft.Witness`, raft's static mode, no conf change) passes the randomized
linearizability test; same axioms as `kv_porcupine_safe` (unchanged), no `sorry`; trust base
unchanged. On the way: `RestartNode` at a witness conf state, the Ready's witness requests
reported (to the cluster's witness, from the node, within the term budget), the witness at a term
bound (`InvWitnessIfaceT.lean`), kv's `witnessDeliver`. Details and the premises left:
`notes/raft-witness.md`, "W4".

# The snapshot path (D22) and the server

In status-history.md: the D22 stages "D22: T-S scoped" to "D22 S-d4 items 3-4 carried out", the server's construction (units N0-N4, items 4-8), the request path, the apply and txn packages, mvcc, the backend, and "Open work: the client→server path for Put/Get (and Delete/Txn), next steps" (its still-open items are in the summary above).

## Merge of raft-retarget into lean (D22) (2026-10-21)

Branch `raft-retarget` (D22, the snapshot track T-S: S-0..S-d4, S-f..S-i, S-g/S-h, the three fork
fixes; S-j/S-l and S-r designed) merged into `lean`. What the merge itself changed:

- The etcd pin is `goose-lean` `2aed163b1`: raft-retarget's three server commits (`8f793b820`,
  `d52eec43e`, `de825d8c6`) with lean's four watch-resume fixes (`watch-resume-fixes`
  `04375baaa..b3c29bc17`) cherry-picked on top (`cafce83d8`, `c15c7dda8`, `2e2dc077c`,
  `2aed163b1`; the trees differ from `b3c29bc17` by exactly the three server commits).
  `Code/.../etcdserver.toml` takes both sides' translated names (the partition hooks and the merged
  snapshot's sender); the etcd project re-translated, every project `--check` clean.
- raft's `Step` branches and `raft.send`: lean's proof-perf restructurings (joined flag and type
  splits) kept, with D22's premises put back in (the `tsSrc` certificate, `SnapStep`/`SnapLogStep`,
  the `stableTo` window).
- lean's examples `linkv`, `linkv3`, `linkv3p`, `linkvtxn`, `watchkv`, `cachekv` ported to the
  server's D22 contract the way D22 ported putget/putget3: `storage.dbOpensOk` replaces
  `mvcc.backendNoCompaction` in their `Main` specs and closed theorems (`Hdbo` for `Hnoc`), raft's
  no-transfer mode (`γ.reNoXfer = true`) beside the no-snapshot mode in their boot premises, the two
  new parts of `NewServer`'s result, the backend mutex's reader slots (`srvBemuReader`) in
  `etcdGrpcSlots_of_started` and putget3's `memberUp`.
- Trust base: lean 530 axioms (528 before D29's two), raft-retarget 538, merged 543 (lean's ∪
  raft-retarget's: since their common base lean's eleven new axioms and its six removed init
  axioms, raft-retarget's 13 new), 2 sorries. Collections:
  `backend.fileHolds` joins the six lean examples' (as it joined putget/putget3's in D22),
  `strconv.FormatUint.wp_proof` joins `snapshot.txt` (lean's `BaseApply.lean`).
- lean's clean-up (`etc/dead-decls.py`, merged into lean during this merge) against D22: the
  declarations it removed that D22's proofs use are restored (`csOpt_persistent`, `InvPbLog.lean`;
  `csOpt_csOptA`, `smPts_of_struct`, `ownSnapM_of_struct`, `InvPb.lean`: the merged snapshot's
  message); those D22 had touched but nothing uses stay removed (the old static `Step` model,
  `memStorage_isStorage`/`is_Storage_MemoryStorage`, `ownRaftGhost_alloc`, `nodeDriver_lb`,
  `runCfg_flw`, `XfOk.sub`, `initKsn_zero`, `isRaftMsg_sent`, `ownStepGhost_vcfg`,
  `isMessageC_of_ne`, `nstateRel_ready`, `isMessage_timeless`/`isMessageC_timeless`). D22's other
  new declarations nothing uses yet are kept (the track is in progress).
- No D22 name collision in the notes: lean's `decisions.md` has no other "D22" (the KV
  state-machine specs' D22 of `worktree-kv-sm-specs` is not on `lean`), so the track's headings are
  kept as they were.

## D22 receiver epochs, S1-S5: nothing persistent names what `store.Restore` writes (2026-10-22)

`notes/decisions.md`, "D22 receiver epochs, S1-S5 carried out" (S1-S4, branch
`worktree-agent-ac204083d5bd27672`) and "D22 receiver epochs, S5 carried out" (S5, branch
`worktree-agent-ab03038efa73b7686`). The store-level steps of `notes/snapshot-receiver-epochs.md`
§4, each commit a full build, no top-level statement changed, no re-translation, trust base
unchanged. S1-S4: the certificate without the index's count, the writer's state out of the batch
lock (`writerInv`), the four fields `Restore` writes shared by the locks (`fieldShare`),
`s.revMu`'s restoring mode, the readers' pool of the index's slots (the S1-S4 section:
`notes/status-history.md`). **S5a**: the readers' backend tokens in the pool's slots, a slot out
under the watchable store's lock (`wsDep`, `readerPool_checkout_ws`), the apply thread's and the
storage-version monitor's tokens retired readers (`storeReader_retire`; `mvcc.writerOwn` in
`apply.kvOwn`). **S5b**: `PhysNames`/`γ.withPhys`; `γ.cur` a fractional ghost variable of the
objects and physical names (`curAt`) shared by the fields' shares, `s.revMu`'s body, `writerInv`,
the pool and the writer's fragment; the physical facts (`physOk`) in the shares, `isStore` logical
(`isStore_withPhys`, `rfl`); a read transaction at the names its share pins (`isTxnRead` ∃ `p`);
`hookIs` = `hookOk` (persistent) ∗ `writerFrag` (the sole writer's, kept in `txn.kvWriter`).
Next (done since): S6, below.

## D22 receiver epochs, S6: `store.Restore` a true axiom, `watchableStore.Restore` proved (2026-10-22)

(Since restore R5f, 2026-10-24, `mvcc.store.Restore.wp_proof` is a theorem: `notes/restore-plan.md`.)

`notes/decisions.md`, "D22 receiver epochs, S6 carried out" (branch
`worktree-agent-a65035decfc6b261e`). **`mvcc.store.Restore.spec`** (`Spec/.../mvcc/store__Restore.lean`,
the axiom in `Proof/.../store__Restore.lean`; the docstring argues it line by line against
`kvstore.go:292-314` and names S-g2 as what would discharge it): over the caller's parts of the
store's current objects and names (closer, the watchable store's quarter and deposit, the writer's
fragment and retired token), never compacted, the sole writer at `L`, a new real backend holding
`[[], []] ++ R` extending `L`; back at fresh physical names the new closer, fragment and token, the
certificate and budget at the restored log, the old backend's `k + 1` tokens and the new one's
left over. A true spec needed one change to S5: `storeRegd` out of `physOk` into the writer's
invariant, where a restored backend's registration is pending until the next writer's lock
(`writerReg`, `writerInv_checkout`). **`watchableStore.Restore` proved** over the axiom (linked):
the synced watchers moved to the unsynced group with `restore` set, delivered up to their
`minRev`, no event delivered. The watch invariant: `restore` free in `WsOk`, `WsState.unsRst` in
`watchStoreInv`, the synced watchers' events up to their `minRev` in `popFacts`, an unsynced one's
`minRev` at most `max lo |Lc|`; `chooseAll`/`choose` clear the flag of members above `curRev`,
`syncWatchers` moves them to the synced group, `rangeEvents` allows `minRev > maxRev`. No caller
yet: `etcdserver.restorePre_of_apply` (`etcdserver/RestorePre.lean`) assembles the store half of the
precondition from `apply.kvOwn` and `srvKVCloser`, its docstring what S7/S8 must supply.

## D22 receiver epochs, S8a-S8c: no hook on the new backend before `SetBackend`; the future status; the callees (2026-10-24, branch `worktree-agent-a9a2649236a655331`)

`notes/decisions.md`, "D22 receiver epochs, S8 carried out"; plan `notes/snapshot-s8-plan.md` (two
commits, each a full build). S7f's open issue resolved: the new backend's batch-lock resource is
made at its open, before `ci.SetBackend` registers its names, and a hook in between would save the
old `ci`; Go relies on no commit then. **S8a** (backend): every commit is paid (`payIn`, now framed
into the hooks' triples, and `bgOk`'s `w ≤ ver`), the creator holds all payments (`bFresh`:
`wbInit` write-back tokens, `bOpen 1`), `hook_fresh_false` refutes a payment beside them, and the
open's batch-lock step receives them and gives `K` back (`newPostK`; `openPre`, `backend.New`,
`newBackend`, `OpenBackend` (axiom, generalized), `OpenSnapshotBackend`). **S8b** (apply protocol):
`ApplyPhys` with the backend's `wb`/`opn` names, `ApplyNames.fut` (announced backends, their
deposited `bFresh`), `batchLockInv`'s registration `applyRegd ∨ applyFut`; `ci_announce` (at the
open), `fut_resolve` (in a hook: registered since, or refuted), `ci_swap_au` restated (from the
announcement, the deposit back), `hooksOk_server_fut` (the server's hooks for the new backend).
No axiom added in S8a-S8b; no closed theorem's text; exported results with one more premise:
`cindex_hook_backend`, `cindex_hookFnSpec`, `backend_server_hooks`, `server_kv_backend_hooks`.
**S8c** (the orchestrator's decisions on W1-W4, `notes/decisions.md`, "D22 S8's four questions
decided" and "D22 receiver epochs, S8c carried out"): W3, the transport's peers right (`netPeers`,
`netTrIs`; `Transport.Start` and `AddPeer` restated, `RemoveAllPeers` new; `RNEnv.TS`, the raft node's
`stopped` carrying it to `onStop`'s `Stop`); W2 needs no `NewAuthStore` restatement in mode `.off`;
W1's decided `Rm` is not establishable at `Release` (a variant proposed); new axioms
`lessor.Recover`, `authStore.Recover`, `RaftCluster.SetBackend`, the gauge's initializer;
`NewMembershipBackend` proved; S8d's lemmas `kv_cert_jump` (W4) and `srv_be_swap`. Axioms 615 ->
620. Issue filed: `issues/etcd-rafthttp-leaderstats-followers-race.md`. Then W1 and W5
(`notes/decisions.md`, "D22 S8d's premises"): `snapTakenLb`, `storage.Release`'s axiom (620 -> 621),
the opaque `snap.dirReadOk`, `backend.renameOk`, `storage.releaseOk`, `storageSnap` and the bundle
`storage.snapOpensOk`; `os.Rename`, `DBFilePath` (now over the held file) and `OpenSnapshotBackend`
restated (an error implies the fact fails). **Left** (S8d): the open-work item above.

## D22 receiver epochs, S7f: the apply protocol per backend (2026-10-23, branch `worktree-agent-a5fae76133d772e18`)

`notes/decisions.md`, "D22 receiver epochs, S7f carried out" (two commits, each a full build).
**S7f-a** `ApplyNames` = logical names (`ci`, `st`, `fz`, new `cur`, `reg`) and the current backend's
physical ones (`ph : ApplyPhys`: `mt`, `wr`, `pend`, `m0`); `consInv` reads only the logical ones:
the current physical names a ghost variable (half the apply thread's, `curOwn` in `applyThread`
and `freezeY`), the registry of every backend's names, the retired backends' mirror halves
(`retiredInv`, bounded by `ciEff`, which never decreases); `batchLockInv` carries the registration
(`applyRegd`), so `commit_save_au` serves an old backend's `Close` (its retired case). Proved for S8:
`ci_swap_au` (the swap at `ci.SetBackend`'s store of 0) and `consInv_alloc` (the boot backend).
**S7f-b** `applyAll`'s post gives the backend after the batch (`∃ γ' TM' E' b'`, `beSucc`, `isServer`
at them; `AEnv.onBe`); `run`'s `applyRes` holds it per batch (`ApplyBe`). No closed theorem's text
changed, `bootOk`'s text unchanged (its protocol parts hold more, allocatable); exported
`applyAll_model` changed (the spec's post); trust base unchanged (539 axioms, 0 sorries).
**Left for S8** (`applySnapshot`): the new backend's batch lock needs its registration at
`OpenSnapshotBackend`, before `SetBackend` registers it: S8 needs the backend's guarantee that no
hook runs before the first write (Go's `run` commits only with `pending ≠ 0`), or a "future"
registry status; `ci_swap_au`'s premise `ciEff ≤` the snapshot's stored index; then the axioms S7
lists.

## D22 receiver epochs, S7: the server's fields and the objects' backends (2026-10-23, branch `worktree-agent-a9f17bc977f014063`)

`notes/decisions.md`, "D22 receiver epochs, S7 carried out" (five commits, each a full build).
**S7a** `s.uberApply` the apply thread's (`srvApplyKV` owns it; `applyConfChange`'s axiom takes it
owned). **S7b** half of `s.be` the apply thread's (`srvBeOwn`, in `srvApplyKV`), half `bemu`'s
(`bemuP s γbe`, with the backend's facts `srvBeRO`); the current backend a ghost variable
`AEnv.γbe` (half `bemuP`, a quarter the apply thread's, a quarter the write budget's); the write
budget `srvWTPool E γp` of the current backend, with the storage-version monitor's read token
(checked out per session; `srvSVRes s E` a `bemu` reader at `γbe` and the logger's);
`Backend()` returns some backend with its facts. **S7c** `AlarmStore.Recover` translated and
proved over `AlarmStore.restore` (names-only: +1 trust-boundary axiom, 539); the alarm store's and
the auth store's backend fields half their lock's, half their user's (`alarmBeOn`, `authBeOn`),
their apply contracts for whichever backend the user's half names (`alarmApplyOk`, `authApplyOk`,
given a write right lending it, `rwLens`); the server's environment with its objects' parts
(`srvRestOwnH`, `srvRestRWH`). **S7d** the lessor's `le.b` likewise (`lessorBackend` without
`↦□`, `lessorBeOn`, `lessorApplyOk`). **S7e** the cluster's `be` field owned by the apply thread
(`clusterBeOn`), its contract for whichever backend it names (`clusterApplyOk`, `roLens`);
`bootOk` restated (`#Hisc`, a new row `HclBe`): a change of the closed theorems' bootstrap
premise; `srvEnvOk` pins the objects' parts to the store's backend (`srvObjsOn`). Every closed
theorem's text unchanged; collections unchanged but `server` (the new axiom). **Left for S8**:
the apply protocol's per-backend names: carried out since (S7f, above); then `applySnapshot` itself
with the `Recover`/`SetBackend` axioms the decisions section lists.

## D22 the stored-index window (2026-10-23, branch `worktree-agent-abc119190b6e832f9`)

`notes/decisions.md`, "D22 the stored-index window carried out". Between `s.KV().Commit()` and
`s.be.Snapshot()` the apply thread holds the protocol frozen at its state `s`: its `Commit()`
asks the backend's hooks (`backend.commitReq`/`hooksReq`, through `store.Commit` and
`isKeyBackendG`'s `Req`, `mvcc.storeReq`) to trade `applyThread γA s` for `freezeY γA s` at the
consistent index's save (`commit_freeze_au`; `consInv` is now `consInvAt ∨ consFrozen`), every
commit while frozen stores `s.k` again, and the snapshot's observation reads `s.k` and the tracked
buckets in the committed data (`snapObs_window`, `srvBeSnapOk_window`); `unfreeze` gives the state
back. `createMergedSnapshotMessage.spec` and `snapBranch_send` take `RC' -∗ RS`. The window's
lemmas are in `etcdserver/SnapSendBranch.lean` (`commitReq_freeze`, `storeReq_freeze`,
`srvKVCommitOk_of_kv`, `srvBeSnapOk_window`). Restated: `bootOk`'s `inv applyN (consInv γA)` (the
window's token in the invariant). Trust base unchanged (538 axioms, 0 sorries); 11 collections
now list the backend's bbolt-boundary predicates (`isDB`, `ownDB`, `ownWTx`, `txDB`: `mvcc.kbReq`
names the real backend's commit request). Left for S-l
proper: the branch's assembly (`s.k = ai`, the rest model's `rb`), the key half of the image
(`keyView`), the compaction keys (`bkNoCmp`).

## D22 the backend over every bucket (2026-10-23, branch `worktree-agent-abc119190b6e832f9`)

`notes/decisions.md`, "D22 the backend over every bucket carried out" (D22c revisited,
`notes/snapshot-rest-buckets.md`). The backend's model tracks the buckets a client names
(`BParams.RB`; the real instance's `mvcc.restBuckets`): `rbData P S`, the writer's contents of
those, half a ghost variable in the batch lock and half the client's (`rbOwn`), which
`UnsafePut`/`UnsafeDelete`/`UnsafeCreateBucket`/`UnsafeDeleteBucket` update (`rbPut`) and the hook
keeps (`hookStep`); `backend.Snapshot`'s observation and post are over `rbData` too. The apply
package's environment gets `AEnv.RO`/`AEnv.RW` (the rest buckets and in-memory members; the write
right of the request kinds `dispatch` never reaches), the cluster's contracts update `RO` to the
model (`apply.restAfter`), the apply loop carries `srvRest E γr A` (`etcdserver/InvRest.lean`:
`restModel c0 bootLog L`), `NewServer` starts it at the boot state. `bkRestAt` and
`clusterBktOf` are now definitions over `restModel`; `imageAt_of_snap` takes `rbData P D =
(restModel …).bk` (`bkRestAt_of_rb`). Restated trusted statements: `bootOk` (fresh buckets
empty, `membership.clusterMem`, the `isCluster`/`isAuthStore`/`isAlarmStore`/`isApplyLessor`
contracts at `srvRestOwn`/`srvRestRW`), `lease.NewLessor`, `auth.NewAuthStore`,
`v3alarm.NewAlarmStore`, `EtcdServer.applyConfChange`, `semver.MustParse`, `backend.Snapshot`; no
axiom added or removed (538 axioms, 0 sorries). Left: the compaction keys (`bkNoCmp`), the
stored-index window (the image's index half, below), S-l proper.

## D22 S-l sender items: the `MsgSnap` owned, `store.Commit` proved; the stored-index window designed (2026-10-22)

`notes/decisions.md`, "D22 S-l sender items carried out" (branch
`worktree-agent-a13029e4d33860881`). Done: a `Ready`'s `MsgSnap` stays owned (`rnSnapMsg`: owned,
`isRaftMsg`, `termLB`) through `rnReadyData` (`rnMsgR`) and `processMessages` into `msgSnapC`'s bag
(`isRNMsgSnapC γ`), `rnSnapMsg_false` for the no-snapshot mode; `store.Commit` translated and proved
(no axiom), `srvKVCommitOk_of_kv` discharges S-h's `KV().Commit()` contract over `txn.isKV`;
`srvWTPool_take_extra`/`_two` (the merge's two write-back tokens); `rnRtBound_of_rtOk` (D22l's
bound from the batch's `rnRtOk`). Not done: the stored-index window (`consInv` frozen at `ai`
between `KV().Commit()` and `be.Snapshot()`): `backend.Snapshot`'s observation is a plain wand, so
the apply thread needs a quarter of the stored index's mirror *before* the call, which only a
commit's hook can hand it, and no contract on the commit path carries a resource out of the hook.
Designed (a hook request through `ForceCommit`, a frozen mode of `consInv`), not carried out; so
`srvBeSnapOk` for the server's backend and the image's index half stay `snapBranch_send`'s
premises, with the non-key buckets (`bkRestAt`, the all-bucket backend spec) and what the
no-snapshot mode hides (S-l proper). (Since 2026-10-23 the window and the non-key buckets are
carried out: "D22 the stored-index window" and "D22 the backend over every bucket" above.) The branch stays dead in `applyAll`. Trust base unchanged
(538 axioms, 0 sorries).

## D22 fork fixes: the snapshot file's release and the alarm store's race (2026-10-22)

The etcd pin moves to `goose-lean` `188113160` (two commits on `2aed163b1`, both approved by the user):
`8fd98af04` (`issues/etcd-alarm-store-snapshot-race.md`: `AlarmStore.Recover`, the upstream candidate's
fix; test `TestV3AlarmsDuringSnapshotInstall`, `-race`) and `188113160`
(`issues/etcd-release-snapdb-before-open.md`: `applySnapshot` calls `storage.Release` after opening the
snapshot's backend, the raft goroutine no longer does; deterministic test
`TestSnapshotDBKeptUntilOpened`). Re-translated (`etcdserver.lean`, `v3alarm.lean`); `raftNode.start`'s
and `applySnapshot`'s proofs unchanged (both changes are in the non-empty-snapshot branches they do not
reach); trust base unchanged (543 axioms, 2 sorries). For S-j: `s.alarmStore` stays read-only
(`srvAlarmStoreAddr s ↦□` holds through the snapshot path; `Recover` to be translated and proved), and
`snapDirInv`'s `Rm j` can be "the applied index is past `j`" (`notes/decisions.md`, "D22 fork fixes").

## D22 S-r carried out (proof): snapshots in the kv example, `kv_porcupine_safe` re-closed (2026-10-22, branch `worktree-agent-a852fca4e45c1cc35`)

`notes/decisions.md`, "D22 S-r carried out (proof)". The Go change of the side branch below,
translated and proved: `run` installs a `Ready`'s snapshot (`decodeState`, `ApplySnapshot`) and
takes one every 100 applied entries (`encodeState`, `CreateSnapshot`, `Compact`), `deliverable`/
`deliver` pass `MsgSnap`. `kv_porcupine_safe`'s statement unchanged, closed, its axioms unchanged
(342, Lean's three included). Raft carries a snapshot's data certificate (`snapDataOk`, the
cluster's `RaftNames.reSnapOkRaw`, every other cluster's trivial; not the design's `SnapData`
class) and hands a snapshot `Ready` only past the committed log handed out; raft's
`isInitialized` gains `ErrSnapOutOfDate`. The cluster is in raft's static mode (`KVStat`,
`ownRaftGhost_alloc_snap`, `RestartNode … sn := true`). The encoding is over any order of the
bindings (`StateEnc`), not a model round trip. No new axiom or `sorry`; trust base unchanged (543
axioms, 2 sorries). `RaftWitness/` unchanged (needed only if kvwitness takes snapshots). No Go bug.

- Next (not part of S-r): kv's liveness for a `do` whose operation commits inside a snapshot the
  replica installs (it waits forever: `run` does not answer the waiters of the operations the
  snapshot covers; the snapshot holds no per-operation results, so a fix would fail those waiters
  for a retry, or keep the results it needs). Done 2026-10-22, below.

## The kv example's snapshot liveness: done (2026-10-22, branch `worktree-agent-a6c9ce26ba53f6b32`)

`notes/decisions.md`, "The kv example's snapshot liveness: carried out". A replica's `do` whose
operation commits inside a snapshot the replica installs is now answered: the table of the
operations applied (`KV.applied`) maps each to its answer (the key's value right after it), the
snapshot carries it, and the install (`KV.install`) answers this replica's waiters among them with
the recorded value, what `apply` would have sent. `TestSnapshotCatchUp` reproduces the hang
deterministically (it fails without the fix) and checks the answer. Go: `putMap`/`getMap` write
and read both maps (`encodeState`/`decodeState` call them). Proof: `AppliedOk` over `AnsOk` (the
form `waitP` uses), `StateEnc` with the table's answers, `KV.install` proved (the waiter's
operation is the table's by `kv_deposited_minted`; no new invariant), `run`'s install branch calls
it; `kv_porcupine_safe`'s statement and axioms (342) unchanged; no new axiom or `sorry`. No Go bug.

# The client, the watch client and the cache

In status-history.md: "watch-resume: the watch client's reconnection" (the stages of D25), the vertical slice, the watch slice, the client lease, units C1/C2a/P1-P4, the cache, recipes, leasing, concurrency.

## Perennial idioms: the watch client's three workarounds upstreamed (2026-10-22, branch `perennial-idioms`)

- **The Perennial pin was `537c426e0`** (since `f97c83add`, "dedup-pin"; Perennial `lean`: the three idioms, landed 2026-10-22,
  on `a39a3d14c`).
- **What moved to Perennial** (each general, no etcd names; `notes/perennial-changes.md`):
  - the synchronous SPSC channel: `Proof/go_etcd_io/etcd/client/v3/SyncSpsc.lean` deleted, its
    definitions and lemmas now Perennial's `Idioms/SyncSpsc.lean` (same names, in `Perennial`;
    `flagsOk` is `sspscFlagsOk`); `InvWatch.lean` and `WatchRecon.lean` import it;
  - the thread-token join: `InvWcJoin.lean`'s local join (`WcjNames`, `wcjInv`, `isWcj`,
    `wcjAdder`, `wcjDone`, `wcjDoneB`, `wcj_init`'s body, `wcjAdder_wand`, `wp_wcj_Add`/`Done`/
    `Wait`) deleted for `sync.tokJoin` at `wcjN` with the receipt `wcjL γS` (a running token of
    the stream's wait group); what stays is etcd's: the lending law `wcj_law` (the borrowed slots'
    tokens are in the stream's counter invariant), `wcj_init`, `wp_wgsWg_Add_wcj` (now through
    `lend_acc`), `wp_wcj_fork` (through `unlend_acc`) and the shared adder (`wgsWgShared`);
  - `wp_fork_tok_upd`: the local copy deleted, Perennial's used.
- **Proofs.** `waitCancelSubstreams` re-proved mechanically (the join's specs renamed);
  `newWatchClient`, `run`, `serveSubstream` and the rest unchanged. No statement of a closed
  theorem changed (every `Results.lean`'s `theorem ... :=` headers identical); the trust base
  unchanged.

## Clean-up: the watch client's joins, the one-attempt client, the init variants (2026-10-22, branch `cleanup`)

- **The watch client's proofs joined again** (proof-perf, as lean `7617c74d89`/`b9234c174f` did for
  the versions before D25). `watchGRPCStream.closeSubstream`: the removal from `substreams`/`resuming`
  was verified 17 times (the `outc`-nil case twice, the live case's three ways out of the `select`
  times five ways of closing); the `if ws.outc != nil { select }` is joined (`wp_join ... at next`)
  over its four ways, the close-or-fork `if` over its ways, so the removal is verified once and the
  macros `close_tail`/`close_rest` are gone. `watchGRPCStream.run`: the seven `if err := Send(..);
  err != nil { log }` statements joined in frame mode (the next iteration verified once), the
  substream-closing loop bound to its invariant only (`wp_join at (doFor ..) with [IH2]`), the
  unused-variables linter off for the theorem. CPU (user+sys, `lake env lean`, quiet machine):
  closeSubstream 52.2s -> 6.6s, run 148.0s -> 131.2s. Fingerprint unchanged.
- **The one-attempt client machinery deleted** (D31's follow-up; `notes/decisions.md` D31, "Done").
  Deleted: `clientKVOnce`, `kvOnce`, `isEtcdConn1`, `etcdInterceptorOk1`, `AttemptMode.one` (and
  `modePre`'s case), `clientKVOnce_api`; the one-attempt disjunct of `reqPre`, `kvReqPre`,
  `txnReqPre`, `putAuOk`, `txnAuOk`; `writeOnce`/`clientWriteOnce`/`txnWriteOnce` are now the
  refusal-free case alone (pure); the `MaxUnaryRetries' = 1` clauses of `New.spec`, `newClient.spec`,
  `Client.dial(WithBalancer).spec`, `Client.dialSetupOpts.spec`, the retry-bound clause of
  `Client.unaryClientInterceptor.spec`, `NewKV.spec`'s `kvOnce` clause; `etcdInterceptorOkM_split`
  over two modes. No axiom mentioned the one-attempt configuration (the interceptor, `dial` and
  `New` are proved), so the trust base is unchanged (543 axioms, 2 sorries, every collection). The
  examples' closed theorems' statements and their definitions are unchanged (fingerprint); the
  client results `client_put_end_to_end`, `client_delete_end_to_end`, `client_txn_end_to_end`,
  `putAuOk_of_box`, `txnAuOk_of_box` keep their text but `putAuOk`/`txnAuOk` lost the one-attempt
  disjunct (their update is persistent only; the at-most-once write is `Failover.lean`'s), and
  `AttemptMode` lost `.one` (reached through `isEtcdConn` by most client/cache/recipes results,
  which use `.any`/`.write` only: their meaning is unchanged). The retry-bound tracking
  (D21 M6), which no result used any more, went in a follow-up (branch `retry-bound`): `maxAfter`,
  `maxAfter_nones`, `retryOptsMax` (with its instance and `retryOptsMax_at`) deleted;
  `optApplyMax f k kp` is `optApplyKeep f kp` (the policy clause alone, `k` and its `max'`
  conjunct gone), and its lemmas follow (`optApplyKeep_ok`, `optApplyKeep_of_retryApplyOk(s)`, now
  over `[∗list]` instead of `[∗list] ;`). Specs whose statements changed (all intermediate:
  each is used by a proof, none is exported): `withMax.spec`, `withBackoff.spec` (return
  `optApplyKeep … true`); `reuseOrNewWithCallOptions.spec` (no `ks`, `mx`; `retryOptsAt` before and
  after instead of `retryOptsMax`); `Client.unaryClientInterceptor.spec` (no `ks`). The fingerprint
  differs only in those four spec definitions, the three deleted ones and `optApplyKeep` (no root
  line); the Results headers are identical; trust base unchanged (543 axioms, 0 sorries, every
  collection).
- **The init variants the init facts made redundant, removed** (the "Init facts" follow-up).
  `etc/gen-init.py`'s `CLOSEDCHAN` variant is gone (`gen_cc`, `lb_cc`, `CC_*`, the re-proof of
  `context`'s initialization `context_wp_initialize'_closedchan`, `PorcupineInitTable`): porcupine,
  lintest and the counter are generated in the ordinary form. kv joins `ROOTS`, so
  `examples/kv/Init.lean` is generated (its hand-written re-proof of raft's initialization,
  `go_etcd_io.raft.v3.wp_initialize'_closedchan` with `CCInitTable`/`KVInitTable`, is gone), and kv
  and the counter join `PROGRAMS` (new generated `kv/PkgTable.lean`, `lintest/counter/PkgTable.lean`).
  Their adequacy proofs take the generated table and get `context.isClosedchanInit`, which their
  `Main.spec`s still take, from `context`'s `isPkgInit` (`context.isClosedchanInit_of_init`,
  `iPkgInit`); `RaftWitness/`'s `kvwitness/Init.lean` (hand-written: the part is not generated) is
  the ordinary form too, its adequacy at a plain table. Regenerated files that changed:
  `Proof/github_com/anishathalye/porcupine/Init.lean`, `examples/lintest/Init.lean`,
  `examples/lintest/counter/Init.lean`, `examples/kv/Init.lean` (now generated), the new
  `examples/kv/PkgTable.lean` and `examples/lintest/counter/PkgTable.lean`, and the part's copies
  `RaftWitness/Proof/github_com/anishathalye/porcupine/Init.lean`,
  `RaftWitness/.../examples/lintest/Init.lean`. Closed theorems unchanged (fingerprint identical);
  trust base unchanged.

## The examples' clients: etcd's default configuration, one family of call lemmas (2026-10-22, branch `client-default`)

`notes/decisions.md` D31. linkv, linkv3, linkvtxn, watchkv and cachekv no longer set
`MaxUnaryRetries: 1`: their clients have etcd's default configuration, as linkv3p's (D29) and
putget's. A write is still sent at most once: each `Main` gets its member refusal-free
(`etcd_noRefusal` before `etcd_kv_started`) and passes `clientWriteOnce`'s refusal-free case.

- **The family.** Every example's calls of `New`'s client are `client/v3/ClientPutGet.lean`'s:
  `client_Put_own`/`client_Get_own` (persistent, putget), and over a client of members `ms`
  `client_Get_st`, `client_Put_rep`, `client_Put_st`, `client_Delete_st`, `client_Txn_st`.
  Deleted: linkv's `client_Put_once`, `client_Get_plain`, `client_Get_au`, `getReply_state`;
  watchkv's `client_Put_rev`; linkvtxn's copies (moved). linkvtxn keeps `client_List_st` and
  `txn_Commit_st` (its model's).
- **Statements.** No closed theorem changes; the programs they are about do. The `Apply`, `Check`
  and `writer` specs take `clientWriteOnce` instead of `clientKVOnce`.
- **Trust base.** No axiom added; `etcd_noRefusal` now in linkv's, linkv3's, linkvtxn's, watchkv's
  and cachekv's collections. `clientKVOnce` is no longer used by an example (kept, D31).

## Watches across a cut (2026-10-21, branch `watch-cut`, worktree `/shared/etcd-grove-wc`)

The plan: `notes/watch-cut-plan.md` (W0–W4). Today a watch is tied to one address and one member at
every layer (`NewStream`'s axiom, D25's resume proof, the per-member event facts, linkv3p's
`noWatch`).

**W0 done (Go only).** `TestWatchFailover` (`examples/linkv3p/linkv3p_test.go`): Main's clients
(each of every bridge), a prefix watch from revision 1 through client 1, three put-only writers,
the bridges blackholed in turn for 14s each. The run (`-race`, 49s): 6285 puts, 6270 succeeded;
6277 events, revisions 2 to 6278, no gap or repeat, every successful put its event. The stream was
cut in all three blackholes: each time the events stopped for 12s (keepalive's 10s and 2s), and the
watch resumed on the member blackholed next (grpc's round robin), so the resume across members ran
three times. No finding for `issues/`. The workload stays in the test until W4 decides how Main
runs it (the plan's Q4); linkv3p's translation and proofs are untouched.

The lifting lemma, scoped (the plan's section): small, but the boundary is per member (D32 (b)),
and a resume at a lagging member needs a cluster-wide `startRead` case (W2). The examples'
`go.mod` files now replace etcd by the translation's pin `b3c29bc17` (they were at `8a24be2a3`,
before the watch-resume fixes F1–F4). D32 approved. W2a done: mvcc's progress bound comes from etcd's own guard
(`progressIfSync`'s `rev < w.startRev`), so a watch's create needs nothing of the member it reaches
(`startRead` removed; the watcher's bit `now` is the server's). W2b done: the lifting lemma
(`kv_cert_cmp`, `KVCertCmp.lean`). W2c done: linkv3p's members serve the watch stream and export its
registration (`memberServed`); `linkv3p_safe`'s step bound is now `n + 2 ≤ 2^29` (watchkv's), and
its collection gains 8 axioms already in watchkv's. W1 done: D32 carried out (`NewStream` over a list of addresses,
the stream at one of them with its spec; the bridge forwards streams; no axiom added). W3 done (W3a: the history model; W3b-1: the
contract's model a field, `watchLaws`; W3b-2: `run`'s epochs at members, the stream at any member
of the connection, D32).

**W4 done (2026-10-22): `linkv3p_watch_safe`.** `MainWatch(nw, nops, sched)` (Go, with
`startCluster` shared with `Main`; `TestMainWatch` under `-race`): watchkv's workload over the
cluster under the partitioner, writers through clients picked at random, a prefix watch through
the first client, the check that it reported exactly the writes. Its closed theorem: no panic, no
stuck thread, the result `WatchOk`, `WatchFailed` or `WatchEnded`, for every schedule, under
`linkv3p_safe`'s hypotheses (but `Run`'s bounds) and watchkv's. The proof's pieces: the clients'
watched logs are prefixes of history logs (`histWL`: a member's logs of at most two revisions are
prefixes of the start log its store sealed); `watchLaws_hist`; a client of several members
(`watchConnFacts_of_members`, `isNewClient_watcher_of`); watchkv's per-server facts over the
history (`linkv3p/WatchHist.lean`); `startCluster`'s spec, with `Main` over it (its theorem
unchanged). No axiom added (530 axioms, 2 sorries); linkv3p's collection gains 7 entries, the watch
client's stream axioms, all in watchkv's (487 entries).

## Read retries (2026-10-21, branch `read-retry`)

`notes/read-retry-plan.md`, `notes/decisions.md` D29. linkv3p's clients have the client's default
configuration (`MaxUnaryRetries` unset: 100 attempts). A read that fails with `Unavailable` is
retried on the next member, so in the tests no read fails. A write is still sent at most once.

- **Why a write is not resent.** The retry interceptor resends a `nonRepeatable` call only after a
  **refusal**: an auth error, a learner's refusal, or grpc's old balancer's "no address" or "no
  connection". linkv3p's members never send one (D29's new axiom `etcd_noRefusal`, by etcd's code:
  authentication off, voters). The bridges pass the fact on.
- **The client proves it.** The interceptor's contract has a third mode, a write on a
  refusal-free connection with scalar call options. Its loop's retry paths are contradictions
  there: the context error returns for `nonRepeatable`, a token refresh follows an auth refusal,
  and `isSafeRetry` is `true` only on a refusal or for a read.
- **The descriptions.** The errors' descriptions (`errDesc`) are a function of the error through
  `status.FromError`, `errors.Is`, rpctypes' initializers, and `rpctypes.errDesc_etcdError` (the
  second new axiom).
- **The tests.** `TestWriteOnce` checks that no put is applied twice under cuts. `linkv3p_safe`'s
  statement is unchanged.
- **Trust base:** +2 axioms (530 axioms, 2 sorries) and restated specs (D29).

## Keepalive and failover on a silent partition (2026-10-21, branch `keepalive`, merged into `lean`)

`notes/keepalive-plan.md`, `notes/decisions.md` D28. `clientv3.New`'s configuration may enable
gRPC keepalive (`clientCfgOk` no longer requires `DialKeepAliveTime ≤ 0`; `dialSetupOpts`'
branch proved, its dial option `.keepalive`, which sets no interceptor and no resolver). linkv3p's
clients ping every 10s (grpc's floor) with a 2s timeout, and its members' gRPC servers take etcd's
`embed` policy (pings every 5s allowed): without it grpc's server refuses the pings (`GOAWAY
too_many_pings` after 31s, a probe). `TestFailover` now cuts member 1 by a blackhole alone: the
calls hung on it fail at a keepalive close, each client finding the dead member on its own (a
client pings only with calls in flight, as etcd's server requires), and then every client works
through the other two. `linkv3p_safe`'s statement is unchanged. Trust base: +2 axioms
(`grpc.WithKeepaliveParams`, `grpc.KeepaliveEnforcementPolicy`: 528 axioms, 2 sorries).

## Client-member cuts in linkv3p (2026-10-21, branches `client-cut` and `failover`, merged into `lean`)

`notes/client-cut-plan.md`: the schedule of `linkv3p`'s `Main` also cuts and mends the link
between each client and its member, through a copy of etcd's integration tests' bridge
(`third_party/bridge`), and the clients recover (gRPC re-dials; clientv3's calls wait for a
connection, `WaitForReady`). **`linkv3p_safe` is re-closed over it** (K0, K1, K3 done): linkv3p's
`peerStep`, `clientStep`, `startBridge`, `partitioner`, `Main` and `Adequacy` over the bridge.
**The bridge is part of the network** (`notes/decisions.md` D26, the user's decision): its code
is not verified; the calls linkv3p makes (`New`, `Blackhole`, `Unblackhole`, `DropConnections`)
have trust-boundary specs over one axiomatized predicate (`bridgeAt`), `New`'s giving the
forwarding fact (the bridge's address serves what the member's does): 5 axioms, exactly what
`etc/tcb-collections/linkv3p.txt` gains (463 -> 468; the global baseline 521 -> 526 axioms, 2
sorries). The network model already let every attempt fail, so the theorem covered client-member
failures before the bridge; the bridge makes the test produce them. (A first K1, a relay's 16
axioms over `net`'s connections with the bridge's 11 functions proved, K2, was carried out and
then removed: D26, the branch's history.) Findings: a second `Blackhole` of a bridge panics
(`issues/nonissues/etcd-bridge-blackhole-twice-panic.md`; `clientStep` skips it, `Blackhole`'s spec takes
the bridge not blackholed); the test's occasional minutes-long runs were porcupine's check, not
the network (a failed write stays pending in linkvtxn's model: `TestMainRun` and `TestClientCuts`
run 3 clients; the plan's K0). `go test -race` passes. **K4, failover (2026-10-21, branch
`failover`, `notes/decisions.md` D27):** the gRPC boundary and the client over a list of endpoints
(each attempt to one of them; streams, so watches and the lease keep-alive, at one), a call through
a client of several members at the conjunction of their specs
(`Proof/go_etcd_io/etcd/client/v3/Failover.lean`; since 2026-10-22 the `_any` results of `client/v3/Results.lean`), linkvtxn's `Apply` for such a client, and
linkv3p's three clients each of all three bridges; no axiom added, the closed theorem's statement
unchanged, the other examples' statements at one endpoint. `TestFailover` shows every client
working while one member's link is cut.

# The examples and their closed theorems

In status-history.md: the partition stages ("Partitions, S0" to "S3b"), linkv-txn stages A-F, "D20: linkv3", "D21 M5: putget3", "Item 9, stage 3: the closed theorem" (putget) and their earlier stages, the register example.

## linkv3p over linkvtxn's workload (2026-10-20, branch `linkv3p-txn`, worktree `/shared/etcd-grove-lt`)

`notes/linkv3p-txn-plan.md`, done: **`linkv3p_safe`** (the partitioned three-member cluster,
clients at every member, for every cut/mend schedule) is re-closed over **linkvtxn's KV
workload** -- gets, lists, puts, deletes, transactions and compare-and-sets, checked by porcupine
against the model of etcd's KV -- in place of linkv's Puts and Gets, on exactly its previous
trust base (`etc/tcb-collections/linkv3p.txt`: 463 axioms, no `sorry`; the global baseline
unchanged, 521 axioms, 2 sorries). The Go program's `Apply`/`Check` call `examples/linkvtxn`
(`TestMainRun` with partition schedules and `-race` pass). The proof: the members keep etcd's
`DeleteRange`/`Txn` registrations (`memberServed`), `clientOk` is linkvtxn's `Apply` premises,
`Main` allocates linkvtxn's invariant, and `Apply`/`Check` restate linkvtxn's triples over the
client slice; no server, client or raft proof changed (`notes/decisions.md`, "linkv3p over
linkvtxn's workload"). `verified-code.py`: linkv3p's 6 functions (109 lines) verified.

## cachekv: `cache_safe`, watchkv through etcd's cache (2026-10-20, branch `cachekv`)

Goal: `cache_safe`, a closed theorem like `watch_safe` for a program whose watcher reads through
etcd's cache. Done: closed, with watchkv's four checks unweakened.

- **The program** (`examples/cachekv`; client `127.0.0.1:23873`, peer `127.0.0.1:23883`, until 2026-10-22 `23851`/`23861`; its own
  module, watchkv's replaces and the cache module's): watchkv's `Main` (the Puts `genAll` picks,
  keys `ck/k0..2`, one member, a one-attempt client, `nw` writers, `collect`, `check`) with the watch
  `cache.New(cli, "ck/")` (default options), then `c.Watch(wctx, "ck/", WithPrefix(),
  WithRev(2))` before any write. `collect` ends on `Canceled || CompactRevision != 0` instead of
  `Err() != nil`: the cache's error responses are cancels, and its channel contract says nothing
  of the unexported `closeErr` that `Err()` reads. `go test -race` passes (`TestMainRun`,
  `TestCheck`, `TestMaxRev`, `TestCollect`).
- **The cache's API and spec allow it**: a cache watch from revision `2` (`Cache.Watch.spec`,
  `cache_Watch_delivery`) is, unless it ends with a cancel, exactly etcd's events under the range
  from revision `2` on, each batch certified by etcd's step (`certChain (etcdStepCert pfx) p₀ bs`,
  `p₀ < 2`); a watch the cache cannot serve from its history (its first `Get` after a write, or
  more than `HistoryWindowSize` revisions behind) ends with a compaction's cancel, `WatchEnded`.
  So the four checks hold unweakened (`CacheFacts.lean`: `step_ck`, `certChain_ck`, `log_ck`, from
  watchkv's `wk_log`, `revEvs_low/hi`, `evFact`).
- **Proofs** (`Proof/.../examples/cachekv/`): reused from watchkv: the workload (`watchkv.workload`,
  `WkLog`, `wk_log`, `srvNoDupKeys_wk`), `revAt`, `evFact`, `watchkv_alloc`, `wk_served`,
  `cert0_of_server`, `client_Put_rev`. New: `Defs` (names, ports, `CheckOk`), `Writes` (the client's
  KV state in `client.kvClientInv`, `put_au` from it), `CacheFacts`, the functions' specs and proofs
  (copies of watchkv's but `collect`'s, which follows the cache watch's received log, and `Main`'s,
  which builds the cache's client and calls `cache.New` and `Cache.Watch`), `Adequacy`
  (`cache_adequate`), `Results` (`cache_safe`, `#print axioms`); linked (`etc/gen-link.py
  --cachekv`, `etc/link-lean-first-cachekv.txt`), initialized (`etc/gen-init.py`: `ROOTS`,
  `PROGRAMS`, and a `SPECIAL` entry for the cache package, whose `Init.lean` is new: its four
  translated error variables, `cacheInit`).
- **Spec changes** (statements of existing theorems unchanged):
  - `client.kvRangeAu` (`kvAnyAu` at the ranges; `kvAnyAu_range`, `kvRangeAu_of_inv`, no workload
    premise): the cache's gets need only ranges' updates, and watchkv's workload lets a client
    deposit only the plan's puts, so `kvAnyAu` is unavailable. `kv_get_server`,
    `isEtcdKVE_of_kv`, `isEtcdClient_of_server`, `isEtcdClient_of_new` are corollaries of new
    `_r` versions.
  - `isEtcdKVE` (the cache's client contract) asks only for gets without a sort option
    (`sortSet = false`; the cache's two gets do not sort): a sorted get's client needs
    `sortNamesOk`, whose `rpctypes.ErrInvalidSortOption` part no package fact gives. The `_r`
    lemmas drop `sortNamesOk`; `kv_get_server_r` takes `sortNamesIf` of the get's flag.
- **`cache_safe`'s hypotheses**: exactly `watch_safe`'s (at cachekv's configuration,
  `cachekv.premises`, with `noRetryableStreamErr` until watch-resume's S1e); the cache's thread bound follows from
  `n + 2 ≤ 2 ^ 29`.
- **Trust base**: `etc/tcb-collections/cachekv.txt`, 477 axioms: watchkv's 474 and three of the
  cache's trust boundary (`context.Err.wp_proof`, `fmt.Printf.wp_proof`,
  `time.Duration.String.wp_proof`), all in the baseline (519/2 unchanged; every other collection
  unchanged); no `sorry`.
- **Not done**: a check of the cache's `Get` after the writers (each key's value the last write's
  at the cache's revision). Not cheap: `Cache.Get`'s answer is etcd's state at the cache's
  revision (`isEtcdKvs`), which may be above the last watched revision (a Put that returned an
  error may still apply), so the program would read the watch up to the `Get`'s revision, and the
  proof needs a lemma relating `stateAt` of a watchkv log to the puts' `revAt`s (none exists).

## linkv-txn stage G: `linkvtxn_safe` (2026-10-20, branch `linkv-txn-g`)

**The closed theorem `linkvtxn_safe`** (`linkvtxn/Results.lean`, `Adequacy.lean`'s
`linkvtxn_adequate`): every real execution of `examples/linkvtxn`'s initialization followed by
`Main(clients, ops)` -- one member in process, a one-attempt client, `clients` clients of `ops`
random operations of robustness's `EtcdPutDeleteLease` workload without leases and stale reads
(gets, lists, puts, deletes, multi-operation transactions, compare-and-sets), porcupine's check
against the model of etcd's KV, a panic on `Illegal` -- has no stuck thread and no panic, and
`Main` returns `Ok` or `Unknown`. Its hypotheses are `linkv_safe`'s at linkvtxn's configuration;
**its axioms are exactly `linkv_safe`'s** (3116; the collection `etc/tcb-collections/linkvtxn.txt`
equals `linkv.txt`, retired with linkv on 2026-10-22, D34), no `sorry`. `etc/verified-code.py`: all 46 functions of `linkvtxn.go`
verified.
- **Go change** (re-translated; the tests pass): `genFrom` builds its two transaction shapes as
  struct literals (`mkTxn`, moved to the tests, branched five ways on its slices' lengths); a
  multi-operation transaction's operations take the same picks as before.
- **The generator** (`GenLemmas.lean`, `workloadKeys`, `pick`, `genFrom`, `Gen`): every input is
  one `Apply` takes (`GenIn`: decodable, the workload's keys, a transaction not empty);
  `workloadKeys`, `pick` and `genFrom` need no package fact (`lintest.genSpec` gives none).
- **`Check`, `Main`** (as linkv's): `Main` registers the four KV methods (`etcd_kv_started`) and
  allocates the invariant at the boot state (`Boot.lean`'s `linkvInv_alloc_boot`: the empty store
  at revision `1`, good, the model's initial state); `MainDefs.lean`, linkv's premises at
  `linkvtxn`'s ports and names; `etc/gen-init.py` emits `linkvtxn`'s `Init.lean` and
  `PkgTable.lean`; `etc/gen-link.py --linkvtxn` opens the driver's package and assumes
  `NaInvG` (porcupine's checker), as `--linkv`.

linkv stays: `linkv3` and `linkv3p` run its `Check`; whether linkvtxn's workload replaces
linkv's there is a later plan. (It did in linkv3p, "linkv3p over linkvtxn's workload" above;
linkv and linkv3 were retired on 2026-10-22, `notes/decisions.md` D34.)

## watchkv: `watch_safe`, the watch example's closed theorem (2026-10-20, branch `watchkv`)

Goal: `watch_safe`, a closed theorem (as `putget_safe`/`linkv_safe`) for a Go program that
watches one member's writes. Done: closed, with the four checks (decisions.md, D23).

- **The program** (`examples/watchkv`; client `127.0.0.1:23872`, peer `127.0.0.1:23882`, until 2026-10-22 `23831`/`23841`):
  `Main(nw, nops)` picks the writers' `nw * nops` Puts first (`genAll`, keys `wk/k0..2`, values
  `a..d`), starts one member as putget's, a client with `MaxUnaryRetries: 1`, a prefix watch
  `cli.Watcher.Watch(wctx, "wk/", WithPrefix(), WithRev(1), WithProgressNotify(),
  WithCreatedNotify())` in a `WithCancel(Background())` context, `nw` writers (a `WaitGroup`;
  each Put that returned no error logged with its revision under a mutex), takes the log, reads
  the watch up to the highest successful revision (`collect`; `WatchEnded` if the channel closes or
  a response errs first), cancels, and checks (`check`: every event a put, revisions exactly
  `2, 3, ...`, each event a Put tried, every successful Put the event at its revision); a
  violation panics. `go test -race` passes.
- **The fixes (D23).** Finding 1: `NewServer.spec` exports 64 watchable-store readers
  (`srvWatchReaders`); `progressReportIntervalMu`'s reader slots are pooled in v3rpc's package
  fact (`v3rpc.intervalPool`, borrowed against a thread token in `GetProgressReportInterval`;
  `etc/gen-init.py`'s v3rpc entry: v3rpc's `Init.lean` is the one regenerated existing file).
  Finding 2: the workload record `SrvWorkload.writes` (every client deposit's op satisfies it;
  `putgetWorkload`'s is `True`), certified watch steps, `srvNoDupKeys` over certified sealed logs,
  derived for watchkv (`srvNoDupKeys_wk`). Finding 3: the Puts are picked before the member starts,
  so the workload is `workload (tried.map pairOf)` and every revision `≥ 2` of a certified log is
  one put of a pair tried (`wk_log`, `WkLog`); `collect` proves the events are puts at `2, 3, ...`
  of pairs tried, each the store's put at its revision (`revAt`), and `check`'s premise
  `CheckOk` follows with the Puts' replies (`okFact`, `revAt_agree`).
- **Proofs** (`Proof/github_com/mit_pdos/etcd_grove/examples/watchkv/`): `Workload`, `LogFacts`,
  `WatchModel`, `WatchFacts` (`resp_wk`), `Writes`, `Alloc` (`watchkv_alloc`), `Served`
  (`wk_served`: the cache's `etcd_cache_served` keeping `Put`; `cert0_of_server`), the functions'
  proofs, `Main`; linked (`etc/gen-link.py --watchkv`, `etc/link-lean-first-watchkv.txt`),
  initialized (`etc/gen-init.py`: `ROOTS`, `PROGRAMS`; new `Init.lean`, `PkgTable.lean`), closed
  (`Adequacy.lean`'s `watch_adequate`, `Results.lean`'s `watch_safe`, `#print axioms`).
- **`watch_safe`'s hypotheses**: putget's at watchkv's configuration (`watchkv.premises`, with
  `noRetryableStreamErr` until watch-resume's S1e), the marked `EofFromIoInit`, `ClosedchanFromContextInit` and
  `EofOkFromIoInit` (false under the then Perennial pin; gone since "Init facts" above), the client watcher's classes
  (`ErrorStringNoGRPCStatus`, `ContextErrsClient`; `errors`'/`fmt`'s/`rpctypes`' assumptions),
  `n + 2 ≤ 2 ^ 29` (the interval pool's reader limit), `0 ≤ nw < 2 ^ 31`, `0 ≤ nops`,
  `nw * nops < 2 ^ 62`. Result: the main thread returns `0`, `1` or `2`, no thread stuck or panicked.
- **Trust base**: `etc/tcb-collections/watchkv.txt`, 480 axioms: putget's 465 and 15 of the watch
  path (grpc's stream axioms, `grpc.serveStream`, `context.WithCancelValCtx`, `rand.Int63n`,
  `mvcc.ReportEventReceived`, `streamKeyFromCtx`, `v3rpc.isClientCtxErr`, ...), all already in the
  baseline (525/2 unchanged; every other collection unchanged); no `sorry`.
- Every existing closed theorem's statement is unchanged; every existing generated file is
  byte-identical but v3rpc's `Init.lean` (stage 1).

## The key-value store example and its porcupine test (2026-10-19, branch `kv-porcupine`, merged into `lean`)

The register example (`examples/register`) is now `examples/kv`: a replicated string-to-string
key-value store on a cluster of three raft nodes (`Put`, `Get`, `Append`, and `Read` by read
index; reconfiguration `RemoveMember` and `TransferLeadership` kept), with a randomized
linearizability test on porcupine and a closed theorem that the test never fails. No crash or
restart (as before).

- **The Go program** (`examples/kv/{kv.go,cluster.go,check.go}`, runnable): `StartCluster` starts
  the cluster (the register's `Main`'s bring-up); `check.go` has the store's porcupine model
  (`Model`: the state an immutable `map[string]string`, `Step` copies before it writes, `Equal`
  and `Hash` over the map), random traffic (`Gen`: Put/Get/Append of keys `a`-`c` and values
  `000`-`999` on random replicas, from `primitive.RandomUint64`), `Check` (lintest's `Run` with
  the store as the library) and `Main` (4 clients of 25 operations, counter clock, panic unless
  `Ok`). `go test` (also with `-race`) passes: unit tests of the store and the encoding, model
  tests (a stale read, a phantom value and an impossible order rejected), and `Check` with 8
  clients of 50 operations under both clocks; `go run ./cmd/kvcheck` runs `Main`, and with flags
  larger tests (8 clients x 200 operations take about a second; 16 concurrent clients make
  porcupine's unpartitioned search exponential, which the verified checker's lack of
  `Partition` does not let us avoid).
- **The specs** (`Spec/github_com/mit_pdos/etcd_grove/examples/kv/`): `Put`/`Get`/`Append`
  logically atomic over the store's state `rkvVal γr m` (`KVMap`: every key's value); `Read` with
  lower bounds as before. The state's ghost variable holds the history (a map is not countable),
  `rkvVal γr m` is the client's half at a history whose fold is `m`. The operation credits
  (`opCred`) are gone: `do`/`Read` loop forever in Go at `maxSeq` (the driver could not supply
  credits through `applySpec`). Keys and values are bounded by `2^61` (with `2^62` each,
  `encode`'s capacity overflowed an `int`; found by the port).
- **The test's proof**: `ModelDefs.lean` (`kvS`, the model over boxed `Input`s and strings; a
  boxed `Input` determines its fields, `boxIn_inj`, from the deterministic field getters); the
  model's closures, `Gen`, `Check`, `StartCluster`, `Main`; `Init.lean` (the package's
  initialization carrying `context.isClosedchanInit`, as the counter's), `Adequacy.lean`
  (`kv_adequate_of`, the bundle with iris-lean's `NaInvF`), `AdequacyLinked.lean` (`kv_adequate`)
  and `Results.lean` (`kv_porcupine_safe`): every real execution of `initialize'(); Main()` of
  fewer than `2^63` steps has no stuck thread and no panic, so porcupine answers `Ok`.
  `Check`'s `apply` cannot hand the driver's atomic update to the store's specs directly (the
  driver's is a one-shot update, the store's take Iris's abortable `AU`, and the masks differ):
  `Check` keeps a copy of the store's state in an invariant (`checkN`) and builds the store's
  `AU` from the driver's, committing both at the store's linearization point (`kvAu_of_run`).
- **Trust base**: `etc/tcb-collections/kv.txt` (the register's, renamed) matches unchanged: 24
  axioms (the raft/protobuf trust boundary, `fmt.Errorf`, `context.ErrAny`, the untranslated
  initializers' `opaqueInitsOk`/`initFuncsOk`, `initLb_of_spec`) and, since the merge with `lean`
  (Perennial `e81f4a6ce`, its initializers proved), no `sorry`; lintest and porcupine add none.
  `etc/tcb-report.py --check` after the merge: 525 axioms, 2 `sorry`s, `lean`'s.
- **Workarounds** (Perennial gaps, recorded in `notes/decisions.md`, "The key-value store's porcupine
  test"): `context`'s `isPkgInit` lacks `isClosedchanInit`, so `kv/Init.lean` re-proves raft's
  initialization over porcupine's `context` re-proof (`wp_initialize'_closedchan`, ~130 lines);
  Perennial's `allG` has no `NaInvF`, so the bundle adds it.
- **Renames**: `register`→`kv` (modules, `etc/goose.py` project `kv`, `etc/gen-link.py --kv`,
  `etc/link-lean-first-kv.txt`), and the example's own names that clashed with the server's in
  `Perennial.EtcdGrove` (`KVNames`, `kvInv`, `kvN`, `kvVal`) carry the prefix `rkv`.

## Porcupine: adequacy of the counter example (2026-10-19, branch `porcupine-nainv2`)

A closed theorem about executions of porcupine's real (translated) code, with no Iris in its
statement: `counter_adequate`
(`Proof/github_com/mit_pdos/etcd_grove/examples/lintest/counter/Adequacy.lean`).

- **The program.** `Main()` (`examples/lintest/counter/counter.go`, new; `go test` calls it)
  runs `Check(lintest.CounterClock(), 4, 10, 0)` -- 4 goroutines of 10 operations each of a
  counter under a mutex, traced with a counter clock, the trace checked by porcupine's
  `CheckOperationsVerbose` with no timeout -- and panics unless the answer is `Ok`.
  `counterProgram` is `initialize'(); Main()` of the counter package.
- **The theorem.** From any state with no package initialized (`IsInit σ`) and one live
  thread, every real execution of `n < 2^63` steps (`RealNsteps n`): if the main thread has
  finished, its value is `#()`; every thread is a value or can step; no thread has ended in a
  panic. So for every interleaving of the clients and every choice of the scheduler, porcupine
  answered `Ok` on the recorded trace: a non-`Ok` answer would have made `Main` panic.
- **Premises.** As the register's ("Adequacy of the register's driver"): the Go semantics
  (`GoGlobalContext`, `GoLocalContext`, `go.Semantics`, `counter.Assumptions`, which includes
  every import's), `context`'s method-set facts `ErrorStringIsError` and
  `DeadlineExceededIsError` (its initialization needs them). The **length bound** `n < 2^63`:
  `CounterClock`'s spec takes `receiptBound GF ≤ 2^63` (time receipts bound the `atomic.Int64`
  the clock increments), and `goose_adequacy`'s receipt bound is `N = n + 1`. **No `NaInvG`
  assumption**: the bundle `counterGF` (the register's slots, plus iris-lean's `NaInvF` at slot
  11) provides the instance concretely.
- **Proof.** `goose_adequacy` at the disk FFI with `T = n + 2` (`realThreadsBelow_of_one`,
  `Proof/runtime/Threads.lean`, shared with the register's and putget's adequacy), the
  package-init table of the 16 packages the counter reaches, the counter's `wp_initialize'`, and
  `counter.wp_Main` (`Main.wp_proof` from `CounterClock.spec` and `Check.spec`, linked in
  `counter/Link.lean` through `etc/link-lean-first-lintest-counter.txt`; the clock's invariant
  at `counterClockN`, apart from `lintestN`; `r = Ok` since the timeout is 0 refutes the panic
  branch).
- **`context.isClosedchanInit`** (a Perennial gap). Porcupine's specs take it
  (`WithCancel(Background())` needs `closedchan` closed, an invariant), but Perennial's
  `context.wp_initialize'` does not return it (its proof closes `closedchan` and drops the
  channel's state) and `context`'s `isPkgInit` does not contain it, so no package's
  initialization spec can give it. `Proof/github_com/anishathalye/porcupine/Init.lean` proves
  `context`'s initialization again (`context_wp_initialize'_closedchan`: Perennial's proof plus
  the invariant `inv closedchanN (ownChan γ (Closed []))`), at a `get_is_pkg_init` whose entries
  for `context` and the packages importing it (porcupine, lintest, the counter) are
  `isPkgInit _ ∗ isClosedchanInit` (so a second initialization, from the map, gives it too), and
  porcupine's, lintest's (`lintest/Init.lean`) and the counter's (`counter/Init.lean`)
  initializations on it. `Main.spec` takes the fact; the adequacy proof gets it from the
  initialization, with no assumption (putget's theorem takes it as the marked Prop
  `ClosedchanFromContextInit` instead). **The right fix is in Perennial**: put
  `isClosedchanInit` in `context`'s `isPkgInit` (its `isInit` is at any `HasLC`,
  `isClosedchanInit` at `HasLC.hasLC`); then no spec takes it and the re-proof goes.
- **`#print axioms counter_adequate`**: 46. Lean's three; 42 data axioms of `Code/` (opaque
  types of `fmt`, `strings`, `sync` with their `underlying`/`zero_val`, `internal/synctest`'s
  three constants, `errors.errorType.init` and 17 `time` package-variable initializers); and
  `sorryAx`, from Perennial's `time.wp_initialize'` and `errors.wp_initialize'` (package
  initializers that run opaque initializers; the register's theorem has them too). No axiom or
  `sorry` of this repository: `counter.wp_Main`, `porcupine.wp_CheckOperationsVerbose`,
  `lintest.wp_Run` and `wp_CheckCounterClock` reach no `sorryAx`.

# Initialization, Perennial and the trust base

In status-history.md: "Item 8: package initialization", "The TCB and verified-code scripts" (CLAUDE.md describes them now), the Perennial pin moves before `lean` was followed, the axiom audit's stages (B1-B4b), "Sorry-free (2026-10-09)" (sorries came back later), the standard-library axioms.

## The FIFO scheduler proved (2026-10-22, branch `fifo-sched`)

`pkg/v3/schedule`'s `fifo` (mvcc's compaction jobs, the server's apply jobs) translated with its
body (`Code/go_etcd_io/etcd/pkg/v3/schedule.toml`: `NewFIFOScheduler`, `Schedule`, `Stop`, the
worker `run` and `executeJob`; `Pending`/`Scheduled`/`Finished`/`WaitFinish` names only, unused)
and proved against the existing contracts (`isFifo`, the FIFO chain of saved postconditions,
`Proof/go_etcd_io/etcd/pkg/v3/schedule/Defs.lean`, "The `fifo` scheduler"): the lock invariant
holds the pending jobs' resources, the queue's other half (`schedQueue` is now half the
authority), the baton (the last tracked job's `Post`) and the worker's state; `f.resume` and
`f.donec` are in invariants, closed only by the worker once stopped; the context's `PDone` is the
`stopped` flag, which `Stop` sets before cancelling it. `Scheduler.Schedule`/`Stop` are proved from
`(*fifo)`'s. Statements unchanged except `isFifo`'s definition (it now carries the `*fifo`'s facts
at the later-credit instance; `isFifoOf`). `verify.Assert` (an existing axiom) now reaches the
`mvcc` collection.

- **mvcc's `store.Close` and `store.HashStorage`** translated (`mvcc.toml`) and proved: `Close`
  closes `stopc` with the closer's right and stops the scheduler with its stop token and the
  compaction queue's scheduler queue (`storeCloser`), both read through the closer's field share;
  `HashStorage` reads `s.hashes` (`isStore`).
- **Trust base**: 543 → 538 axioms (`NewFIFOScheduler`, `Scheduler.Schedule`, `Scheduler.Stop`,
  `store.Close`, `store.HashStorage` gone), 0 sorries; collections updated.
- **v2stats** (the same pass, the server's statistics): `NewLeaderStats` translated and proved
  (over zap's `NewNop`), 538 → 537 axioms. `NewServerStats`, `ServerStats.BecomeLeader` and
  `ServerStats.RecvAppendReq` stay trust-boundary axioms: `serverStats` has an anonymous struct
  field (`LeaderInfo`), which Goose does not translate, so the type is axiomatized. Proving them
  would take a fork commit naming that struct (or Goose support for anonymous structs), the rate
  queue's ring-buffer invariant, and `isServerStats` threaded through the server's invariants
  (decided 2026-10-22: not now; statistics no result depends on).
- **A Perennial gap**: `context.WithCancel`'s specs do not say the cancel function is not `nil`,
  which `Schedule`'s panic check needs; worked around by a local copy
  (`schedule/WithCancel.lean`), `notes/perennial-changes.md`.
## Perennial idioms: the watch client's three workarounds upstreamed (2026-10-22, branch `perennial-idioms`)

- **The Perennial pin was `537c426e0`** (since `f97c83add`, "dedup-pin"; Perennial `lean`: the three idioms, landed 2026-10-22,
  on `a39a3d14c`).
- **What moved to Perennial** (each general, no etcd names; `notes/perennial-changes.md`):
  - the synchronous SPSC channel: `Proof/go_etcd_io/etcd/client/v3/SyncSpsc.lean` deleted, its
    definitions and lemmas now Perennial's `Idioms/SyncSpsc.lean` (same names, in `Perennial`;
    `flagsOk` is `sspscFlagsOk`); `InvWatch.lean` and `WatchRecon.lean` import it;
  - the thread-token join: `InvWcJoin.lean`'s local join (`WcjNames`, `wcjInv`, `isWcj`,
    `wcjAdder`, `wcjDone`, `wcjDoneB`, `wcj_init`'s body, `wcjAdder_wand`, `wp_wcj_Add`/`Done`/
    `Wait`) deleted for `sync.tokJoin` at `wcjN` with the receipt `wcjL γS` (a running token of
    the stream's wait group); what stays is etcd's: the lending law `wcj_law` (the borrowed slots'
    tokens are in the stream's counter invariant), `wcj_init`, `wp_wgsWg_Add_wcj` (now through
    `lend_acc`), `wp_wcj_fork` (through `unlend_acc`) and the shared adder (`wgsWgShared`);
  - `wp_fork_tok_upd`: the local copy deleted, Perennial's used.
- **Proofs.** `waitCancelSubstreams` re-proved mechanically (the join's specs renamed);
  `newWatchClient`, `run`, `serveSubstream` and the rest unchanged. No statement of a closed
  theorem changed (every `Results.lean`'s `theorem ... :=` headers identical); the trust base
  unchanged.

## Clean-up: the watch client's joins, the one-attempt client, the init variants (2026-10-22, branch `cleanup`)

- **The watch client's proofs joined again** (proof-perf, as lean `7617c74d89`/`b9234c174f` did for
  the versions before D25). `watchGRPCStream.closeSubstream`: the removal from `substreams`/`resuming`
  was verified 17 times (the `outc`-nil case twice, the live case's three ways out of the `select`
  times five ways of closing); the `if ws.outc != nil { select }` is joined (`wp_join ... at next`)
  over its four ways, the close-or-fork `if` over its ways, so the removal is verified once and the
  macros `close_tail`/`close_rest` are gone. `watchGRPCStream.run`: the seven `if err := Send(..);
  err != nil { log }` statements joined in frame mode (the next iteration verified once), the
  substream-closing loop bound to its invariant only (`wp_join at (doFor ..) with [IH2]`), the
  unused-variables linter off for the theorem. CPU (user+sys, `lake env lean`, quiet machine):
  closeSubstream 52.2s -> 6.6s, run 148.0s -> 131.2s. Fingerprint unchanged.
- **The one-attempt client machinery deleted** (D31's follow-up; `notes/decisions.md` D31, "Done").
  Deleted: `clientKVOnce`, `kvOnce`, `isEtcdConn1`, `etcdInterceptorOk1`, `AttemptMode.one` (and
  `modePre`'s case), `clientKVOnce_api`; the one-attempt disjunct of `reqPre`, `kvReqPre`,
  `txnReqPre`, `putAuOk`, `txnAuOk`; `writeOnce`/`clientWriteOnce`/`txnWriteOnce` are now the
  refusal-free case alone (pure); the `MaxUnaryRetries' = 1` clauses of `New.spec`, `newClient.spec`,
  `Client.dial(WithBalancer).spec`, `Client.dialSetupOpts.spec`, the retry-bound clause of
  `Client.unaryClientInterceptor.spec`, `NewKV.spec`'s `kvOnce` clause; `etcdInterceptorOkM_split`
  over two modes. No axiom mentioned the one-attempt configuration (the interceptor, `dial` and
  `New` are proved), so the trust base is unchanged (543 axioms, 2 sorries, every collection). The
  examples' closed theorems' statements and their definitions are unchanged (fingerprint); the
  client results `client_put_end_to_end`, `client_delete_end_to_end`, `client_txn_end_to_end`,
  `putAuOk_of_box`, `txnAuOk_of_box` keep their text but `putAuOk`/`txnAuOk` lost the one-attempt
  disjunct (their update is persistent only; the at-most-once write is `Failover.lean`'s), and
  `AttemptMode` lost `.one` (reached through `isEtcdConn` by most client/cache/recipes results,
  which use `.any`/`.write` only: their meaning is unchanged). Not done: the retry-bound tracking
  (`optApplyMax`'s bound, `maxAfter`, `retryOptsMax`'s bound, D21 M6) is now used by no result's
  conclusion and could go too (`withMax`, `withBackoff`, `reuseOrNewWithCallOptions` specs).
- **The init variants the init facts made redundant, removed** (the "Init facts" follow-up).
  `etc/gen-init.py`'s `CLOSEDCHAN` variant is gone (`gen_cc`, `lb_cc`, `CC_*`, the re-proof of
  `context`'s initialization `context_wp_initialize'_closedchan`, `PorcupineInitTable`): porcupine,
  lintest and the counter are generated in the ordinary form. kv joins `ROOTS`, so
  `examples/kv/Init.lean` is generated (its hand-written re-proof of raft's initialization,
  `go_etcd_io.raft.v3.wp_initialize'_closedchan` with `CCInitTable`/`KVInitTable`, is gone), and kv
  and the counter join `PROGRAMS` (new generated `kv/PkgTable.lean`, `lintest/counter/PkgTable.lean`).
  Their adequacy proofs take the generated table and get `context.isClosedchanInit`, which their
  `Main.spec`s still take, from `context`'s `isPkgInit` (`context.isClosedchanInit_of_init`,
  `iPkgInit`); `RaftWitness/`'s `kvwitness/Init.lean` (hand-written: the part is not generated) is
  the ordinary form too, its adequacy at a plain table. Regenerated files that changed:
  `Proof/github_com/anishathalye/porcupine/Init.lean`, `examples/lintest/Init.lean`,
  `examples/lintest/counter/Init.lean`, `examples/kv/Init.lean` (now generated), the new
  `examples/kv/PkgTable.lean` and `examples/lintest/counter/PkgTable.lean`, and the part's copies
  `RaftWitness/Proof/github_com/anishathalye/porcupine/Init.lean`,
  `RaftWitness/.../examples/lintest/Init.lean`. Closed theorems unchanged (fingerprint identical);
  trust base unchanged.

## `kvHasher` translated: no sorry left (2026-10-22, branch `kvhasher`)

The last two `sorry`s, `mvcc.kvHasher.kvHasher_typed_pointsto` and `kvHasher_into_val_typed`,
were the generated instances of an axiomatized type: `kvHasher` (`server/storage/mvcc/hash.go`)
has a field `hash hash.Hash32`, and Perennial does not translate the standard-library package
`hash`, nor did mvcc's configuration import it, so Goose declared `kvHasher` (`axiom kvHasher :
Type`, `axiom kvHasher.underlying`) and proofgen sorried its instances. Fix, as for
`encoding/hex`: `hash` translated types-only in this repository (`Code/hash.toml`; `etc/goose.py`:
`-lean-root hash=`, the package, the owned output; its interfaces `Hash`, `Hash32`, `Hash64`,
`Cloner`, `XOF` over Perennial's `io`) and `hash` among mvcc's imports, so Goose translates
`kvHasher` as a struct with generated, proved instances. `hash`'s `isPkgInit` (`True`) is in
mvcc's `Base.lean`, its `Init.lean` generated (`etc/gen-init.py`; mvcc's `Init.lean` and the
examples' `PkgTable.lean`s regenerated, one hypothesis index in mvcc's `SPECIAL` moved). No proof
changed: the compaction job holds the hasher as `h ↦ hv` with the opaque `kvHasherOk hv`, which
the struct does not affect. `newKVHasher`, `kvHasher.WriteKeyValue` and `kvHasher.Hash` stay
trust-boundary axioms (`hash/crc32` has no model; `notes/perennial-changes.md`, "Standard
library"). Trust base: 543 axioms, 0 sorries (`etc/tcb-baseline.txt`; collections `mvcc`,
`mvcc-compaction` updated).

## Init facts: the three marked hypotheses gone (2026-10-20, branch `init-facts`; Perennial pin `a39a3d14c`)

**The Perennial pin is `a39a3d14c`** (Perennial's `lean`: its `init-facts`, two commits on
`e81f4a6ce`, landed 2026-10-20): `io.isInit` keeps the nine `errors.New` variables
(`errors.newVar X msg`, `io.eof_of_init : isPkgInit io ⊢ errors.newVar EOF "EOF"`), and
`context.isInit` keeps `isClosedchanInit` (`context.isClosedchanInit_of_init`).

- **Theorems** in place of the named Props: `v3rpc.eofVar_of_init [io.Assumptions]
  [ErrorStringLeaf] [context.ErrorStringIsError] : isPkgInit io ⊢ eofVar` (`InvWatch.lean`) and
  `client.eofOk_of_init [ErrorStringLeaf] [ErrorStringNoGRPCStatus] hAs : isPkgInit io ⊢ eofOk`
  (`ErrorsNewOk.lean`); `context.isClosedchanInit_of_init` is Perennial's.
- **Statements**: `putget_safe`, `putget3_safe`, `linkv_safe`, `linkv3_safe` lose `HEof`/`HCc`,
  `watch_safe` also `HEo` (and their `_adequate` theorems); nothing else changes (the classes the
  theorems use were already their hypotheses). The five `Main.spec`s lose
  `EofFromIoInit → ClosedchanFromContextInit →` (watchkv's also `EofOkFromIoInit →`) and take the
  method-set classes `[ErrorStringLeaf] [context.ErrorStringIsError]` instead (watchkv's had
  `ErrorStringLeaf`, adds `context.ErrorStringIsError`). The defs `putget.EofFromIoInit`,
  `putget.ClosedchanFromContextInit`, `putget3.`'s and `watchkv.EofOkFromIoInit` are deleted.
- **Hand-written**: `raft/v3/Init.lean`'s `io_isPkgInit_Discard` takes `io.isInit`'s first
  conjunct. **Generated**: `etc/gen-init.py`'s `context_wp_initialize'_closedchan` builds
  `isPkgInit context` with its new `"#Hcci"` conjunct; regenerated
  `Proof/github_com/anishathalye/porcupine/Init.lean` (the only file that changed).
- **Follow-up** (not done): the `CLOSEDCHAN` variant of `etc/gen-init.py` (porcupine, lintest, the
  counter) and `kv/Init.lean`'s re-proof of raft's initialization are now redundant: the
  packages could be of the ordinary form, the specs that take `isClosedchanInit` getting it from
  `isPkgInit context`. (Done 2026-10-22: "Clean-up: the watch client's joins, the one-attempt
  client, the init variants".)
- **Trust base**: unchanged (`etc/tcb-report.py --check`: 519 axioms, 2 `sorry`s; every collection
  matches): the marked Props were hypotheses, not axioms, and no axiom compensated for them.
- **Gates** (against the Perennial branch): full `lake build`; every `Link.lean` regenerates
  unchanged; `tcb-report.py --check` and every collection; `goose.py --check --perennial`;
  `gen-init.py --check`; `issues-status.py --check`.

## Trusted initializers: six init axioms of the kv adequacy theorem gone (2026-10-20, branch `worktree-issue-statuses`, merged into `lean`)

The kv adequacy theorem's trust base (`etc/tcb-collections/kv.txt`) had ten package-init axioms;
the six on this repository's translations are gone: `raftpb.opaqueInitsOk`/`initFuncsOk`,
protobuf-go `proto.opaqueInitsOk`/`initFuncsOk`, `protoreflect.opaqueInitsOk`,
`internal/impl.opaqueInitsOk` (also gone from putget's, putget3's, linkv's and linkv3's; no
other collection had them). Following Perennial's trusted initializers (`948699d06`), the
untranslated initializers are goose `trusted` declarations with no-op models in the new
`TrustedCode/` (`notes/decisions.md`, "Trusted initializers"): `impl`'s 170 variables and its
`_` assertions, `protoreflect`'s 11 type descriptors, `proto`'s `wireTypes`, three errors and
`init`, raftpb's `file_raft_proto_enumTypes`/`_msgTypes` and `init` (the descriptor's build and
registration); raftpb's `file_raft_proto_goTypes`/`_depIdxs` are translated (slice literals,
`wp_slice_literal` in raft's `Init.lean`). `etc/gen-init.py` steps through a trusted
initializer (`wp_call`) and unfolds a trusted `init.<k>`; `ManualProof/<pkg>.lean` is the empty
module proofgen imports for a package with trusted declarations; `etc/proof_roots.py` and the
TCB report know the two new roots. No proof statement changed: every `wp_initialize'` keeps its
statement (the server's `Init.lean` files are unchanged), and `raftpb.Assumptions` gains
`init.0_unfold`. Gates: `lake build` (5704 jobs), `etc/goose.py --check`, `etc/gen-init.py
--check`, `etc/tcb-report.py --check` and every collection's `--check`.

Left (deferred, the user's choice): `os`'s and `strconv`'s four (`os.opaqueInitsOk`,
`os.initFuncsOk`, `os.Stderr_init`, `strconv.opaqueInitsOk`) are on Perennial's names-only
translations and need a Perennial change (and moving `os`'s fact out of raft's `Base.lean`).

## Perennial: the pin follows `lean` (2026-10-19)

The pin (`lakefile.toml`, `lake-manifest.json`) was Perennial `864598b33`, on branch `lean`.
Perennial's `lean` was reset that day to the tree of its former branch `lean-temp`
(`b0a0fb557`: `a54e1999f` plus `append` reduced to `copy`, `wp_slice_append_fits`,
`wp_slice_append_grow`, `wp_slice_append_dfrac`/`_undo` re-proved on them, and Go's in-place
deletion `wp_slice_delete_range`, `wp_slice_delete`, which replaced this repository's
`Proof/Lib/Slice.lean`), by a merge commit whose second parent is `b0a0fb557`; `lean-temp`
was then deleted. The files are those of the previous pin, so nothing here changes.

The 62 commits `lean` had gained past `a54e1999f` (Goose's evaluation-order translation,
byte-addressed memory and package `unsafe`, ...) remain in its history, ending at
`b09644c20`, but their changes are undone. Their translator rejected raft (`raft.go:1098`, an
empty `case` clause holding only a comment becomes an unsupported `*ast.EmptyStmt`), so
bringing any of them back is a project of its own. Perennial changes this repository needs
go on branches off Perennial's `lean` (`CLAUDE.md`, "Changes to Perennial").

The pin has since moved to `8d53c9e0d` (2026-10-19), which adds the facts of this repository's
former `Proof/Lib/` (below, "Proof/Lib: the package-independent facts").

The pin has since moved to `be3eb77cc` (2026-10-19): a negative index panics (string and array
index, array index reference), string slicing has a semantics (`StringSemantics.string_slice`),
Goose converts `append(s, x...)`'s and `copy(dst, src)`'s source to the slice's type and
translates a constant call (`unsafe.Sizeof`, ...) as its constant, and a package's `func init()`s
are ordinary functions `init.<k>` (as gc names them), which `initialize'` calls in order by
`FuncResolve`. An untranslated `init` used to be dropped silently by the translator; now it is a
name without a `FuncUnfold`, stuck. What changed here:

* Goose configurations name inits per name: `wait.toml` translates `init.0` (was `init`, which
  no longer matched, leaving `closec`'s initialization out), and `raftpb.toml` and `apply.toml`
  exclude `init.*` (was `!init`, which no longer matched, so their inits were translated).
  `read`'s and `leasing`'s inits are translated as before, now as functions.
* `etc/gen-init.py` steps into a translated `init` (`wp_func_call`, `wp_call`) and gives each
  untranslated one the trust-boundary axiom `<pkg>.initFuncsOk` (it returns: a fact about the
  Go code, like `MustRegister.wp_proof`, since `@! init.<k>` is the semantics' unconstrained
  `functions`); 32 generated files have one. A configuration's steps for variable initializers
  that run last go in `before['$inits']` (emitted before the first `init`), not `$end` or
  `finish` (`etcdserverpb`, `client/v3`, `mvcc`, `read`'s counters). The raft `Init.lean` has the same
  axiom for `os`, `proto` and `raftpb`. Porcupine's `Init.lean`, which proves `context`'s
  initialization again, steps into `context`'s `init.0`, as Perennial's proof now does.
* The negative-index semantics and string slicing needed no proof change.
* Follow-up: with `string_slice`, `authority`'s spec need not be restricted to plain endpoints
  (`plainEndpoint`, "Item 5: client construction").

The pin has since moved to `5fab1f144` (2026-10-19): Perennial's own initializer proofs have no
`sorry` left (`errors`, `crypto/ed25519`, `math`, `math/big`, `time`, `log`, `crypto/rand`).
Goose lets a `trusted` package variable's initializer be a TrustedCode model (`X.init`); the
std packages' variables are translated where goose can (`math`'s tables, `math/big`'s,
`time`'s including `UTC` and `Local`, `log.bufferPool`) and otherwise trusted (no-ops for
`errors.errorType`, `math.useFMA`, `math/big.hasADX`, two `godebug.New` sites, `log.std`,
`log`'s `init`; a value of Go's dynamic type for `crypto/rand.Reader`); untyped float
negation got a semantics rule. Five of those models are graded REWORK by Perennial's
trusted-base review and accepted for now (Perennial `README.md`, "Trusted package-variable
initializers"). What changed here:

* `time`, `log`, `math/big` and `crypto/rand` now import `errors`, `sync`, `errors` and `io`,
  so `putget/PkgTable.lean` (`etc/gen-init.py`) has four new dependency facts; the
  translations, every `Link.lean` and every proof are unchanged.
* The six Perennial `sorry`s are gone from the trust base: `etc/tcb-baseline.txt` (521 axioms,
  2 `sorry`s, both this repository's), and the `putget` (463 axioms) and `register` (24 axioms)
  collections, which now have no `sorry`. No axiom was added.
* `#print axioms`, counting what the collections leave out (generated declarations of
  untranslated types and values, Perennial's): `register_adequate` and `register_cluster_safe`
  rest on 539 axioms (3 Lean standard, the 24 of the collection, 429 generated here, 83
  generated in Perennial); `putget_safe` on 3308 (3 Lean standard, the 463 of the collection,
  2627 generated here, 210 generated in Perennial, and Perennial's 5 trusted specs
  `errors.As`, `time.Now`, `time.NewTimer`, `Timer.Reset`, `Timer.Stop`). None reaches
  `sorryAx`.

Dropped for now (2026-10-19), kept on branches: the method-set semantics, `log.New`'s
translation and the register's adequacy without semantic premises (Perennial
`lean-temp-method-sets`, `7b576e562`, branched from the former `lean-temp`; etcd-grove `adequacy-clean`, which pins it; the same
fix on top of `lean`: Perennial `method-sets`, `e65eff1cc`). Its trusted-base review found an
open BLOCK: the predeclared `error` is the reducible literal `interface{ Error() string }`,
which Go distinguishes from it, so with method sets the model decides some type assertions
`true` where Go says `false` (fix: make `error` a named type); also that local types of
generic functions share one descriptor across instantiations (pre-existing in Goose).

## The wait-group counter and thread tokens (2026-10-10)

Perennial `105fb79f5` (merged into `lean`) reverts `614fa61d3`: `WaitGroup.Add` is
Goose's translation again and `WaitGroup.wp_Add` asks its caller to bound the new counter by
`2^31` (two `Add(1 << 30)` calls panic in Go, so the overflow was reachable and must not be
assumed). The bound is discharged with Perennial's **thread tokens** (`GooseLang/Threads.lean`;
`docs/PERENNIAL_PROOF_REFERENCE.md`, "Thread tokens"): the trusted semantics counts the live
threads (`GlobalState.threads`; `Fork e` spawns `e ;; ThreadExit`), the bounded layer has a
thread fuel next to the step fuel, and `threadToks n ⊢ n < threadBound GF` for a bound `T`
fixed at adequacy time (`goose_adequacy N T`, about executions along which fewer than `T` threads
are live). `Fork` hands the forking thread a token (`wp_fork_tok`, `wp_fork_tok_self`,
`wp_fork_tok_body`) and the forked thread returns one at its exit.

- **`cacheWgInv`** (`InvCache.lean`): the counter is `k + d`; `k` goroutines (`cacheWgRunning`,
  `γwr`) have their **thread token deposited** in the invariant (`threadToks k`), `d` goroutines
  (`cacheWgRunningOwed`, `γwo`) keep their own token and spent a capacity (`cacheWgOwedCap`,
  `γwc`; `cacheWgOwedMax = 3`: the resync loop, the watch loop, the progress requestor, for the
  cache's lifetime). `k` tokens give `k < threadBound GF`, so the counter is below
  `threadBound GF + 3`; **`New` assumes `threadBound GF + cacheWgOwedMax ≤ 2^31`** (a pure
  premise of `New.spec`/`newCache.spec`, kept in `isCacheFields` as `%Hthreads`): fewer than
  `2^31 - 3` threads are live at once. The `cacheWgBudget` slots are unchanged.
- **Who deposits.** The watch loop (`getWatchLoop`, `getWatch`, `watch`: `cacheWgLoopRunning`,
  its owed running token and its own thread token) deposits its token at each iteration's
  `Add(1)` (`wp_cacheWg_AddRunning`) and gets a fresh one at the `go` statement
  (`wp_fork_tok_self`); the iteration's goroutine exits with the token its deferred `Done`
  returns (`wp_cacheWg_Done`). `Watch` (`threadTok` in and out of its spec) does the same with a
  budget slot (`wp_cacheWg_Add`). `NewDemux`'s slot protocol and `newCache`'s `Add(2)` start the
  three owed goroutines (`wp_cacheWg_AddOwed`, `wp_cacheWg_Add2`; `wp_cacheWg_DoneOwed` returns
  the capacity); `New`'s spec needs no token of its own.
- **Changed statements**: `New`, `newCache` (the thread-bound premise), `Watch` (`threadTok`),
  `watch`, `getWatch`, `getWatchLoop` (`cacheWgLoopRunning` for `cacheWgRunning`). `Close` and
  the delivery theorem are unchanged.
- **Trust base**: the model assumption is gone from Perennial's trusted code; what replaces it is
  the semantic thread count and thread fuel (Perennial's `Lang.lean`, `BoundedLang.lean`,
  `Threads.lean`, `Lifting.lean`, `Adequacy.lean`; see Perennial's README) and the adequacy
  hypothesis `RealThreadsBelow T`, instantiated here by `New`'s premise. `etc/tcb-report.py
  --check` is unchanged (the premise is a hypothesis of a spec, not an axiom).

# Build

In status-history.md: "Build performance (2026-10-12, branch `proof-perf`)", "Parallel elaboration and tactic state".

## Build performance (2026-10-24, Perennial `9f296e8cc`: `wp_auto`'s simp by `Lean.Meta.Sym`)

Perennial `9f296e8cc` simplifies WP expressions (`gooseExprSimp`, the simp call of `wp_auto`) with
`Lean.Meta.Sym.simp` instead of `Meta.simp`, set up to give the same result: the same lemmas and
unfoldings, the user simprocs, the `@[congr]` lemmas with binder hypotheses, and a proof exactly
where `Meta.simp` has one (`goose.wp.symSimp`, on by default; `false` returns to `Meta.simp`).
`set_option goose.wp.symSimpCheck true` runs both and fails where they differ (but in a `Decidable`
instance argument); with it the whole repository builds, so no proof here changed. Full timed builds,
CPU per module, `Meta.simp` -> `Sym.simp`: `node.run` 79s -> 53s, `raftNode.start` 102s -> 76s,
`watchGRPCStream.serveSubstream` 90s -> 73s, `serverWatchStream.sendLoop` 215s -> 191s, the witness
`stepLeader/Rest` 210s -> 179s, the 30 modules over 60s 3009s -> 2788s; the whole build's CPU about
the same (8h28m vs 8h38m, the `Sym` build on a busier machine, where modules that never call
`wp_auto` were 4-5% slower too): most of `wp_auto`'s time is not in its simp.

## Build performance (2026-10-24, branch `perf/2026-10-23`)

On the Perennial `ef0f3eef4` pin (native-compiled tactics). Profiling with `trace.profiler` must load
`PerennialMeta`'s shared library as the build does (`lean --setup .lake/build/ir/<module>.setup.json`):
a plain `lake env lean` interprets the tactics and overstates their cost. The fingerprint of every
root statement, the definitions they reach and the axioms is the same; `etc/tcb-report.py --check`
and every collection pass. Cold builds of the repository's 6393 modules: CPU 7.71h -> 7.69h (the
untouched modules' noise is as large as the gains), wall 21m01s on the branch. Each change, the
module alone, base vs branch:

- **`iframe #` by name** (`watchGRPCStream.run`, `NewServer`, `EtcdServer.{start,Txn,run}`,
  `unaryClientInterceptor`): `iframe #` runs a `Frame` search for every persistent hypothesis (about
  130 in `NewServer`), 0.5-1s a call; each site now names those it framed (a throwaway probe framed
  them one by one and kept a site only if the goals came out identical). `watchGRPCStream.run` (on
  the critical path) 172s -> 145s, `NewServer` 141s -> 120s, the others 4-9%.
- **`raftLog.append`**: three `repeat' split; all_goals omega` ran over the truncated log's
  `toNat`-laden length facts; cleared there: 33s -> 19s.
- **`btree node.iterate`**, **`moveVictims`**: `simp_all` over a large context replaced by a simp of
  the one fact: 32s -> 22s, 24s -> 17s.
- **`StepGhost`**: `iframe % # ∗` -> `iframe # ∗ <;> iframe %`: 21s -> 18s.

Tried and dropped: `iframe #` by name in `EtcdServer.Range`, `serverWatchStream.{recvLoop,sendLoop}`,
`VerdictLemmas`, `ReadLemmas`, `newApplierV3Backend`, `lessor.recvKeepAliveLoop` (within noise),
client `Results` (the probe's names broke it); `simp only` for `rw [decide_eq_* _]` on a WP goal
(`raft.restore`, 3%). Found, not changed: `wp_auto_lc` is the largest single cost everywhere
(0.4-0.6s a call, Perennial); `iframe #` itself could skip hypotheses whose head symbol matches no
conjunct (a proposal for iris-lean/Perennial); the 6197 modules under 5s are 44% of the CPU, mostly
importing.

## Perennial pin `ef0f3eef4` (2026-10-24)

The pin moved from `c25bef57e` to Perennial `lean` `ef0f3eef4`, which brings its own build-speed
changes: the proof automation compiled to native code (the `PerennialMeta` library), the
`needsGooseSimp`/`PureWp` caches kept for a whole declaration, `solve_typed_pointsto_agree` building
a direct proof term, and in the translator, every generated definition `noncomputable` with no
linters in generated files and a large package's translation split into chunk modules
(`Code/go_etcd_io/etcd/api/v3/etcdserverpb/chunk*.lean`). The translations are regenerated
(`etc/goose.py`, 362 files); no proof needed a change. Trust base unchanged (615 axioms, 4
`sorry`s; every collection passes). A cold full build (`LAKE_ARTIFACT_CACHE=false`, 32 cores,
Perennial's included): wall 23m38s, CPU 8h25m, the longest import chain 12m28s.

## Build performance (2026-10-22, branch `perf/2026-10-22`, merged into `lean`)

Cold full builds (`LAKE_ARTIFACT_CACHE=false`, 24 cores shared with other jobs) of the base `c3dc7114e7`
and of the branch: wall 47m07s -> 37m33s, CPU 10h08m -> 9h28m, the longest import chain 23m23s ->
18m51s; most of that is the machine's load (the 5828 modules the branch does not touch: 33003s ->
31550s CPU). The 66 modules it touches: 3515s -> 2573s CPU. The fingerprint of every root statement,
the definitions they reach and the axioms is the same; `etc/tcb-report.py --check` and every
collection pass. What changed, each commit with its measurements:

- **`kv/deliverable`'s getter dispatch**: its `wp_getter` tried four getter specs in turn inside a
  `repeat` over 80 cases; it now reads the method off the next redex (`raft__Step/Dispatch.lean`):
  180s -> 45s.
- **`w32_ne`/`nonsnap` decide** (`raft__Step/Base.lean`): both close a goal of message-type literals
  with `word`, whose `word_unfold_lit` is `simp ... at *` and so rewrites every hypothesis (a step
  result's: 11s a `nonsnap`); `of_decide_eq_true rfl` first. The 49 raft__Step modules 1214s -> 984s.
- **The unused-variables linter off** for `NewServer` (31s of linting; on the critical path),
  `watchGRPCStream.run` (19s; also turned off on `lean` meanwhile, the merge keeps one), `raftNode.start` (8s), `serveSubstream` (7s).
- **`solve_pkg_init` memoized** (`Proof/github_com/mit_pdos/etcd_grove/PkgInitMemo.lean`, an
  `elab_rules` override for its importers): Perennial's search walks the package-dependency tree of
  each `isPkgInit` hypothesis without remembering failed packages, about 10s a call where the context
  holds a main package's (the examples' `Main`s, `v3rpc/Server`, `EtcdServer.Range`/`Txn`/
  `applyEntryNormal`): `linkv3/Main` 69s -> 23s, `v3rpc/Server` 58s -> 36s, `Txn` 90s -> 75s. The
  general fix is Perennial's (memoize `pkgInitChain`), not yet proposed there.
- **`stepLeader/Rest` in sequence** (`set_option Elab.async false`): its eight theorems took 384s CPU
  in parallel, 156s in sequence (presumably the WP tactics' per-thread caches); 424s -> 177s in the
  cold builds.

Tried and dropped: Perennial's `goose.wp.letRun` (1, 4, 8), `goose.wp.introSimp false`,
`goose.iframe.prepass false` on the costliest WP proofs (within noise, or proofs break); the
`PkgInitMemo` import in `NewServer`, `watchGRPCStream.run`, `dispatch`, `sendLoop` and six others
(no gain: their contexts hold no deep `isPkgInit`); `Elab.async false` for `Refinement`,
`InvRaftPhys`, `MsgRest` (10-15% less CPU, more wall). Found, not changed: the `RaftWitness` copies of
`stepLeader/Rest` (401s), `kvwitness/deliverable` (165s) and `Base`'s macros have the same costs (the
part is outside `Proof/`); `word` everywhere simplifies the whole context (a goal-only mode in
Perennial would help every WP proof); the long WP proofs (`NewServer`, `watchGRPCStream.run`,
`sendLoop`) spend their time over hundreds of 1-10s steps on large function bodies, with no single
hot spot.

## Build performance (2026-10-20, branch `perf/2026-10-20`)

Cold full build of the branch at its base `20f336b31a` (`LAKE_ARTIFACT_CACHE=false`: without it Lake restores every module from the
toolchain's artifact cache and compiles nothing), 24 cores shared with other jobs: wall 1h03m ->
28m47s, CPU 8h53m -> 6h58m, the longest import chain 47m03s -> 17m19s; the fingerprint of every
root statement, the definitions they reach and the axioms is the same, and `etc/tcb-report.py
--check` passes. What changed, each commit with its measurements:

- **Getter dispatch** (`raft__Step/Dispatch.lean`): `Step`'s `wp_get`/`wp_gets`/`wp_drive`
  (`ElectionLemmas.lean`, `ReplLemmas.lean`) and `raft.send`'s `getters` tried each getter spec
  (and field load) in turn, and a failing `wp_apply` costs ~0.5s on `Step`'s body (`wp_pures`
  twice); they now read the method or field off the next redex and apply that spec only. The 46
  raft__Step modules: 5223s -> 1250s CPU; `raft.send` 290s -> 51s.
- **Joins** (`wp_join`) where a case split was followed by `all_goals <the rest of the
  function>`: `Step`'s lease check (`wp_lease_check`: MsgVote_gt 911s -> 63s with the dispatch),
  the stale-term `(checkQuorum || preVote) && ...` test in ten branch files, stepLeader's switches,
  `Txn`'s serialize tail and its ten returns' deferred closure, `Range`, `processInternalRaft
  RequestOnce`, `closeSubstream` (the removal verified 15 times), `updateLeadership`, the watch
  streams' send-error tests.
- **A loop sees only what it reads**: `wp_for` generalizes the whole spatial context into the
  invariant and `wp_for_post` reframes it each iteration; `NewServer`'s two transport loops ran
  over 200 hypotheses (460s of ~740s; since the merge with `lean` the first loop's body is dead,
  no remotes at bootstrap, and only the second is joined). `wp_join at (App (App (App (Val doFor) _) _) _) with [...]`
  gives the loop its hypotheses only: 798s -> 335s.
- **A later out of sight**: a `□ ▷ P` hypothesis makes `wp_auto`/`wp_apply` search every
  hypothesis for a later to strip (`IntoLaterN`) at every step; `unaryClientInterceptor` holds it
  as a private `laterHid` inside its proof: 91s -> 39s.

Found, not changed: `solve_pkg_init` (Perennial `Pkg.lean`) walks every `isPkgInit` hypothesis's
dependency tree without memoization at each `wp_apply` (~10s over 42 calls in `Range`); 51
`iframe #` over ~130 persistent hypotheses in `NewServer`; `kv/deliverable`'s 80 eager case splits
(a lazy split stalls on getter calls `wp_getter`'s `+noauto` cannot reach). Tried and dropped:
joins in `uberApplier.dispatch` (3-8%), `raftNode.start` (1.5%), the unused-variables linter off
in `recvLoop` (none). The 3570 modules under 5s are 157 min of the CPU, mostly importing.

## `word`'s shared cache: heartbeat timeouts that depend on scheduling (2026-10-21, branch `raft-retarget`)

Under a parallel full build, `raft__Step/MsgStorageAppendResp.lean:497` (in
`wp_Step_MsgStorageAppendResp_snap`, S-d3b) once ran out of its 1000000 heartbeats, and passed when
built alone, on the same tree. Cause: `word`'s caches (`Perennial/Std/Word/Cache.lean`:
`wordCache` and `failCache`, process-global `IO.Ref`s) are shared between the declarations Lean
elaborates in parallel within one module, so whether a `word` call hits the cache, and hence the
heartbeats a proof uses, depends on which declaration ran first: a proof near its limit fails on
some runs only. The same class as the flaky `stepLeader.lean` build (`notes/flaky-stepleader-build.md`,
fixed in Perennial `fb1ecb030`, "no global mutable state shared between parallel declarations").
Worked around locally: that theorem's limit raised to 4000000 (what is proved is unchanged). To
propose to Perennial as its own change: the caches keyed per declaration (or held in the tactic's
own state), so that elaboration is deterministic. Other proofs near their limits may show the same.

# Planned

## Kubernetes' etcd3 storage backend: planned (2026-10-22)

`notes/k8s-etcd3-plan.md`: generic logically atomic specs of `k8s.io/apiserver/pkg/storage/etcd3`'s
`*store` methods against a Lean copy of Kubernetes' `correctness.Model`, for any codec meeting a
contract (encoding not canonical), then a closed driver theorem (`TestCorrectness`'s traffic and
porcupine check over in-process etcd, a simple non-canonical codec; a failed write ends a run
unchecked at first). Needs from the client proof: `Range`'s error identity (`ErrFutureRev`,
`ErrCompacted`). Translation survey: branch `k8s-etcd3-goose`. Nothing proved yet.

# Index

## Sections moved to status-history.md

Every heading of this file that moved to `notes/status-history.md` (2026-10-22, the restructuring),
in the file's order (mostly newest first): a reference `notes/STATUS.md, "..."` to one of them
resolves there.

- D22 receiver epochs, S1-S4: the store's fields lock-held; S5 designed (2026-10-22, branch `worktree-agent-ac204083d5bd27672`)
- Witness support, W3b-A: the raft predicates with a witness (2026-10-20, branch `raft-witness`, in progress)
- Witness support, W5: the witness across reconfiguration (2026-10-20, branch `raft-witness-w5`)
- Witness support, W3b: `Process`, at W2's ghost state, and the `Witness` interface (2026-10-20, branch `raft-witness-w3b`)
- Witness support, W3a: the tracker's epoch and `witness.go` specified with a witness (2026-10-20, branch `raft-witness`)
- Witness support, W2: the protocol with a witness (2026-10-20, branch `raft-witness-w2`)
- Witness support, W1: the build green on witness-free configurations (2026-10-20, branch `raft-witness`)
- watch-resume: the watch client's reconnection (2026-10-20, branch `watch-resume`; done)
- Partitions, S3b: `Main` and the closed theorem `linkv3p_safe` (2026-10-20, branch `linkv3p`, worktree `/shared/etcd-grove-pt`)
- Partitions, S3a: the example's functions proved (2026-10-20, branch `linkv3p`, worktree `/shared/etcd-grove-pt`)
- Partitions, S1/S2: the partition hooks' axioms and proofs (2026-10-20, branch `linkv3p`, worktree `/shared/etcd-grove-pt`)
- Partitions, S0: `examples/linkv3p`, its test and translation (2026-10-20, branch `linkv3p`)
- Plan: network partitions, `linkv3p` (2026-10-20, planned; nothing started)
- linkv-txn stage F: `Apply` (2026-10-20, branch `linkv-txn-f`)
- linkv-txn stage E: the Go model's proofs (2026-10-20, branch `linkv-txn-e`)
- linkv-txn stage D: the Go program `examples/linkvtxn` (2026-10-20, branch `linkv-txn-d`)
- linkv-txn stage C: the robustness model and its relation to etcd's state (2026-10-20, branch `linkv-txn-c`)
- linkv-txn stage B1: a delivered writing Txn ran its ranges (2026-10-20, branch `linkv-txn-b`)
- linkv-txn stage B2, B3: read-only Txn's read update; the replies' values (2026-10-20, branch `linkv-txn-b`)
- linkv-txn stage A: at-most-once Delete and Txn (2026-10-20, branch `linkv-txn`)
- Plan: linkv over Delete and Txn (2026-10-20, stage A done, see above)
- D22 S-f carried out: the backend boundary (2026-10-19)
- D22 S-b: the merged snapshot's content, `!found`, the term's witness (2026-10-19, branch off `raft-retarget`)
- D22 S-i carried out: the snapshot stream in the network contract (2026-10-20)
- D22 S-g carried out: `restore` with data; `Restore` stopped on the store's fixed fields (2026-10-19)
- D22 S-b′ designed: the certificate on the message (2026-10-20)
- D22 S-c carried out: `MsgSnap` at `RawNode.Step` (2026-10-20)
- D22 S-h carried out: the merged snapshot's sender (2026-10-20)
- D22 S-j2 stopped: the receiver's `applySnapshot` needs the store's epochs first (2026-10-20)
- D22 S-b′ part 1 carried out, the rest designed (2026-10-20)
- D22 S-d designed: a pending snapshot through `Ready`/`Advance` (2026-10-20)
- D22 D22l carried out: the term witness over later batches (2026-10-20)
- D22 S-b′2 carried out: the storage's certificate registry (2026-10-20)
- D22 S-b′3 carried out: the snapshot's certificate on the network message (2026-10-20)
- D22 S-b′4 carried out (2026-10-20, branch `raft-retarget`)
- D22 S-d1 part 1 carried out (2026-10-20, branch `raft-retarget`)
- D22 S-d1b carried out (2026-10-21, branch `raft-retarget`)
- D22 S-d2 carried out (2026-10-21, branch `raft-retarget`)
- D22 S-d3 designed precisely, stopped (2026-10-21, branch `raft-retarget`)
- D22 S-d3a carried out (2026-10-21, branch `raft-retarget`)
- D22 S-d3b carried out (2026-10-21, branch `raft-retarget`)
- D22 S-d4 designed precisely, stopped after S-d3b (2026-10-21, branch `raft-retarget`)
- D22 S-d4 carried out (2026-10-21, branch `raft-retarget`)
- D22 S-d4 items 3-4 carried out (2026-10-21, branch `raft-retarget`)
- D22 S-r carried out: the Go change made and tested (side branch), the proof designed (2026-10-21, branch `raft-retarget`)
- D22g and D22k carried out (2026-10-19, branch `raft-retarget`)
- D22 S-a: the no-transfer mode split (2026-10-19, branch `raft-retarget`)
- D22 S-0: the plan checked (2026-10-19, branch `raft-retarget`)
- D22: T-S scoped, the snapshot path (2026-10-19, branch `raft-retarget`)
- `lean`'s key-value store merged into `raft-retarget` (2026-10-19)
- D20: linkv3, the three-member instance (2026-10-19, branch `linkv3`)
- D20 (c): linked, initialized, closed (2026-10-19, branch `linkv-apply`)
- D20 (c): `Check` and `Main` (2026-10-19, branch `linkv-apply`)
- D20 (c): `Apply` (2026-10-19, branch `linkv-apply`)
- D21 M5: putget3 and `putget3_safe` (2026-10-19, branch `raft-retarget`)
- D21 M6: at-most-once firing of a client write (2026-10-19, branch `raft-retarget`)
- D21 M2: the network contract and `Process` (2026-10-19, branch `raft-retarget`)
- D21 M2r: the sender's promise and transfers off (2026-10-19, branch `raft-retarget`)
- D21 M3: no `MsgSnap` without compaction (2026-10-19, branch `raft-retarget`)
- D21 M4: the cluster's resources split (2026-10-19, branch `raft-retarget`)
- D21 M2: the network contract designed; stopped (2026-10-19, branch `raft-retarget`)
- D21 M1: the sender's message bundle (2026-10-19, branch `raft-retarget`)
- D21 M0: the no-`MsgSnap` argument (2026-10-19, branch `raft-retarget`)
- Item 9, stage 3: the closed theorem (D19r carried out) (2026-10-18, branch `raft-retarget`)
- Item 9, stage 2: `Main` proved; stage 3 stopped (D19r) (2026-10-18, branch `raft-retarget`)
- D20: the linearizability instance's local pieces (2026-10-19, branch `slice-wk`)
- The lessor's keep-alives aligned: the invariant checks `closeRequireLeader`'s fix (2026-10-18, branch `slice-wk`)
- The etcd pin 8a24be2a3: `closeRequireLeader` and the retry interceptor (2026-10-18, branch `slice-wk`)
- D19q: the server's workload parameter (2026-10-18, branch `raft-retarget`)
- The client lease, stage (c): the gRPC half (2026-10-18, branch `slice-wk`)
- The client lease: done, stages (a), (b), (d) (2026-10-18, branch `lease-client`)
- The client lease: survey, stopped for decisions (2026-10-18, branch `lease-client`)
- D19i part 1 carried out: the floor published at `advancec`; `snapshot`/`compactRaftLog` restated (2026-10-18, branch `d19i1-raft`)
- D19l (v), D19m `store.Close`: `restore`'s premise, the store's stop token (2026-10-18, branch `raft-retarget`)
- D19l (iii): the prometheus label specs restated, per-vector label facts (2026-10-18, branch `raft-retarget`)
- D19l (i), (ii): the ticker-reset and `AuthInfoFromTLS` fixes in the fork (2026-10-18, branch `raft-retarget`)
- D19j carried out: `watch.go`'s package facts from `v3rpc`'s, `io.EOF` stays (2026-10-18, branch `raft-retarget`)
- Audit B4b: latent axioms and premise gaps; ten stopped (D19l) (2026-10-18, branch `raft-retarget`)
- Audit B4a: four false etcd-internal axioms restated, four stopped (D19m) (2026-10-18, branch `raft-retarget`)
- `raftRequestAlarm`: D19k, stopped then carried out (2026-10-18, branch `raft-retarget`)
- D19i part 2: the backend's dedupe fix in the fork; `monitorStorageVersion` restated (2026-10-18, branch `raft-retarget`)
- `localKept` from the cluster's invariant; `watchVars` stopped (D19j) (2026-10-18, branch `raft-retarget`)
- D19i part 1: stopped, needs a decision (2026-10-18, branch `raft-retarget`)
- Audit B2: stopped, needs a decision (D19i) (2026-10-18, branch `raft-retarget`)
- Audit B1: no axiom over every semantics (2026-10-18, branch `raft-retarget`)
- Audit B3: `applyConfChange` restricted; the quota under `backendUnderQuota` (2026-10-18, branch `raft-retarget`)
- D19b: mvcc compaction's `CompactSmall` from receipts (2026-10-18, branch `raft-retarget`)
- D19c's move: the size clauses at execution, `clusterLogBound` gone (2026-10-18, branch `raft-retarget`)
- D17d: `rnSnapOnce` proved (2026-10-18, branch `raft-retarget`)
- D19b stage 5: `rnLogFits` from receipts (2026-10-18, branch `raft-retarget`)
- D19b stage 5: `rnLogFits` stopped (2026-10-18, branch `raft-retarget`; superseded the same day, see above)
- D19g carried out: `NewServer.spec` meets the allocation and serving (2026-10-18, branch `raft-retarget`)
- Item 9, point 7: `Main`'s local pieces (2026-10-18, branch `raft-retarget`)
- Proof/Lib: the package-independent facts (2026-10-18, branch `proof-lib`)
- D19d and D19e: program start's rights, once (2026-10-18, branch `raft-retarget`)
- D19c: option (a), the workload clause proved but its size bound (2026-10-18, branch `raft-retarget`)
- D19c: unit N3 stopped (2026-10-18, branch `raft-retarget`)
- D19b: the lifetime bounds from time receipts (2026-10-18, branch `raft-retarget`)
- Item 9: the adequacy example (stage 1; stopped) (2026-10-18, branch `raft-retarget`)
- D18: the client's Put-then-Get from the persistent updates (2026-10-17, branch `raft-retarget`; adopted 2026-10-18: the monotone route for the example, the prophecy deferred)
- D15: `CheckQuorum` and `PreVote` off by a patched `bootstrap` (2026-10-17, branch `raft-retarget`; temporary, reverted the same day)
- D17: srvBuildGap's rows (2026-10-17, branch `raft-retarget`)
- Raft: CheckQuorum and PreVote on (2026-10-17, branch `raft-checkquorum`)
- D14i: the uber-applier's rows built (2026-10-17, branch `raft-retarget`)
- Integration: `construct` and `lean` into `raft-retarget` (2026-10-17, branch `raft-retarget`)
- Server construction, unit N4: `NewServer` proved (2026-10-17, branch `raft-retarget`)
- Server construction, unit N4, D14g and the constructors (2026-10-17, branch `raft-retarget`)
- Server construction, unit N4, continued: the write budget threaded; stopped at the server's write-back budget (2026-10-17, branch `raft-retarget`)
- Server construction, unit N4: the KV over both stores, the hook installed late; stopped at the constructors' contracts (2026-10-17, branch `raft-retarget`)
- Server construction, unit N1: stopped at `NewServer`'s proof (2026-10-17, branch `raft-retarget`)
- Server construction, stage N0: `NewServer`'s interface (2026-10-16, branch `raft-retarget`)
- Server construction, unit N2: the allocations and the residual (2026-10-17, branch `raft-retarget`)
- Item 4: server start and gRPC (branch `construct`)
- Item 5: client construction (branch `construct`)
- Item 6: the backend's construction and the files (branch `construct`)
- Item 8: package initialization (branch `construct`)
- Special cases derived (2026-10-18, branch `derive-pairs`)
- Proof families as lemmas (2026-10-17, branch `proof-families`)
- Repeated in-proof blocks as macros (2026-10-17, branch `proof-macros`)
- Copied helper lemmas merged (2026-10-17, branch `helper-moves`)
- Dead code removed (2026-10-17, branch `dead-specS`)
- Retargeting raft to v3.7, stage R8b: the new cluster's start, `StartNode` and the server's raft wrapper (2026-10-16, branch `raft-retarget`)
- The compaction premise `NoDelPutAt` is not met by the gRPC checks (2026-10-14)
- Retargeting raft to v3.7, stage R8a: the bare `MemoryStorage` without a snapshot is a `Storage` (2026-10-16, branch `raft-retarget`)
- Retargeting raft to v3.7, stage R7c: the errors named, two premises retired (2026-10-16, branch `raft-retarget`)
- Retargeting raft to v3.7, stage R7b: the server's raft contracts are theorems (2026-10-16, branch `raft-retarget`)
- Retargeting raft to v3.7, stage R7a: raft's side of the server's contract (2026-10-16, branch `raft-retarget`)
- Retargeting raft to v3.7, stage R6: the swap, the server and the register over the one raft tree (2026-10-16, branch `raft-retarget`)
- Retargeting raft to v3.7, stage R5: the node layer over pointer messages (2026-10-16, branch `raft-retarget`)
- Retargeting raft to v3.7, stage R4: raft.go over pointer messages (2026-10-16, branch `raft-retarget`)
- Retargeting raft to v3.7, stages R2 and R3: confchange, the log layer over read-only entries (2026-10-15, branch `raft-retarget`)
- Retargeting raft to v3.7, stage R1: the model final and ported, raftpb for protobuf-go v2 (2026-10-15, branch `raft-retarget`)
- Retargeting raft to v3.7, stage R0: the parallel tree, the inventory, the design (2026-10-15, branch `raft-retarget`)
- Open work: the client→server path for Put/Get (and Delete/Txn), next steps (2026-10-15)
- Unit T2: every KV operation as a persistent atomic update on the whole state (2026-10-15, branch `worktree-backend`)
- Merge M1: `origin/lean` (the vertical slice's V2b, porcupine) into unit T1 (2026-10-15, branch `worktree-backend`)
- Merge: `worktree-raft-rest` into `lean` (2026-10-15)
- Snapshots at the public API (stage S) (2026-10-15, partial)
- node.go and the register under reconfiguration (stage N) (2026-10-15)
- The new ReadIndex and proposal specs (stage R) (2026-10-14)
- The single-voter read-index fix (2026-10-14, stage F)
- Reconfiguration, stage B7, part 2: the `RawNode` API in the dynamic model (2026-10-14)
- Reconfiguration, stage B8 (snapshots at a changing configuration) (2026-10-14)
- Reconfiguration, stage B7, part 1: `raft.Step` in the dynamic model (2026-10-14)
- Reconfiguration, stage B8 (standalone part): snapshots carrying a configuration (2026-10-14)
- Reconfiguration, stage B6: the read-index guarantee under reconfiguration, at the model level (2026-10-14)
- Reconfiguration, stage B5: safety under reconfiguration, at the model level (2026-10-14)
- Reconfiguration, stage B4: the ghost state shaped for dynamic configurations, at a static configuration (2026-10-14)
- Reconfiguration, stage B3: the model with what reconfiguration reads, at a static configuration (2026-10-14)
- Reconfiguration, stage B2: the refinement on `StepC`, at a constant configuration (2026-10-14)
- Reconfiguration, stage A3: `stepLeader` and snapshots at any configuration (2026-10-14)
- Reconfiguration, stage B1: adversarial review (2026-10-14, parallel task 3)
- Parallel tasks 1, 2, 4, 5 (2026-10-14, notes/parallel-work.md)
- Reconfiguration, stage B1: the safety argument on paper, its pure foundation (2026-10-14)
- Reconfiguration, stage A2: the raft functions at any configuration (2026-10-14)
- Reconfiguration, stage A1: the foundation for arbitrary configurations (2026-10-13)
- Reconfiguration, stage D: `ApplyConfChange` for an unchanged configuration (2026-10-13)
- Reconfiguration, stage L: learners (2026-10-13; parts 1-3 done, with the limits below)
- Leader transfer at the node layer and in the register (2026-10-13)
- Reconfiguration, stage D: conf-change entries in the log as data (2026-10-13)
- Leader transfer and the rest of the message types (2026-10-13)
- Read-index (`ReadOnlySafe`) (2026-10-13, branch `worktree-raft-rest`)
- The register's linearizable reads by read index (2026-10-13)
- Reconfiguration, stage 0: the conf-change messages and their encoding (2026-10-13)
- `MemoryStorage`: the rest of the storage (2026-10-12)
- `confchange`, `quorum`, `tracker`: general specs for reconfiguration (2026-10-12)
- Porcupine: complete on linearizable traces, and a generic driver traced as etcd's robustness tests (2026-10-14, branch `worktree-porcupine`)
- Unit C (porcupine): `checkParallel`, `checkOperations`, `CheckOperations*` (2026-10-14, branch `worktree-agent-a737c43dbb7a0d1b3`)
- Unit D (porcupine): the generic driver `examples/lintest` (2026-10-14, branch `worktree-agent-ac7993c0361a09294`)
- Unit E (porcupine): the instance `examples/lintest/counter` (2026-10-14, branch `worktree-agent-afea469cf4311342e`)
- Unit T1: Put and Get as persistent atomic updates linearized by raft (2026-10-14, branch `worktree-backend`)
- Adequacy for a minimal client example: what is left (2026-10-14; superseded)
- Unit A2: the server's auth premises in forms the real auth store meets (2026-10-14, branch `worktree-backend`)
- The vertical slice: client to server
- The watch slice
- Unit C2a: a `Get` after a `Put` sees the `Put` (one server) (2026-10-14, branch `worktree-backend`)
- Unit P3b: the server end of the gRPC boundary (2026-10-14, branch `worktree-backend`)
- Integration I1: the Links of units P1b, P2, P3a (2026-10-14, branch `worktree-backend`)
- Unit P3a: the client's retry interceptor proved, `rpctypes.Error` proved (2026-10-14, branch `worktree-backend`)
- Unit P2: the auth store's request side (2026-10-14, branch `worktree-backend`)
- Units P1/P1b/P4: the etcd leaf functions on the request path (2026-10-14, branch `worktree-backend`)
- Unit C1: the client meets the server (2026-10-14, branch `worktree-backend`)
- The backend (`server/v3/storage/backend`, 2026-10-12/13, branch `worktree-backend`)
- Perennial `a54e1999f`: the proof layout (2026-10-12)
- The request path (`v3rpc`, `v3_server.go`, `wait`, `idutil`)
- Build performance (2026-10-12, branch `proof-perf`)
- Parallel elaboration and tactic state (2026-10-12, branch `flaky-iframe`)
- etcd's server: the raft wrapper (`server/v3/etcdserver/raft.go`): proved (2026-10-12)
- Perennial `5857c495a`: soundness fixes (2026-10-12)
- The server's apply package (`server/v3/etcdserver/apply`)
- Standard-library axioms from Perennial (2026-10-12, branch `std-axioms-from-perennial`)
- Adequacy of the register's driver: the closed theorem and its trust base (2026-10-12)
- Merge: lean into mvcc, the hook (2026-10-12)
- Merge: lean into mvcc, the request path (2026-10-12)
- Merge: lean into mvcc, the request path's unit 4d (2026-10-13)
- Merge: lean into mvcc, the request path's unit 4c (2026-10-13)
- Merge: lean into mvcc, the backend meets the compaction (2026-10-13)
- Merge: lean into mvcc, the request path's unit 4b (2026-10-13)
- Merge: lean into mvcc, the request path's unit 4a (2026-10-13)
- Merge: lean into mvcc, the request path's unit 3b (2026-10-12)
- Merge: lean into mvcc (2026-10-12)
- The store's compaction (2026-10-13, branch `mvcc`)
- The watchable store (2026-10-11, branch `mvcc`)
- Small etcd axioms (2026-10-12)
- The server's txn package (`server/v3/etcdserver/txn`)
- Merge: mvcc into lean (2026-10-11)
- mvcc: the KV core, phase one (2026-10-10)
- Recipes (`client/v3/experimental/recipes`)
- Perennial `cb6a5921e`: one `AllG` (2026-10-11)
- The register's cluster driver: a closed program, safe from package initialization (2026-10-11)
- Panic and recover: Perennial's panics adopted, the STM's axioms gone (2026-10-10)
- client/v3/leasing: the protocol premise and the lease cache (2026-10-10)
- Merge: the register, `node.go` and thread tokens (2026-10-10)
- STM (2026-10-10)
- Election (2026-10-10)
- Mutex: mutual exclusion (2026-10-10)
- The register example: verified over raft, logically atomic (2026-10-10)
- `node.go`: the concurrent `Node` (2026-10-10)
- bbolt: not goosable as written; the `unsafe` it needs (2026-10-10)
- `node.go` groundwork: abandoning a `Ready`, pre-vote off, the messages' terms (2026-10-10)
- `RawNode.Ready` split: `readyWithoutAccept` and `acceptReady`, for `node.go` (2026-10-10)
- The storage contract: a pending append, for `node.go` (2026-10-10)
- Merge: upstream's RawNode work (2026-10-10)
- `RawNode.Step`: a `MsgApp` between `Ready` and `Advance` (2026-10-10)
- The `Advance` gap closed (2026-10-10)
- `RawNode.Campaign`, `RawNode.Step` (2026-10-09)
- `raft.Step` frames the log and bounds the term (2026-10-09)
- Perennial `f52ce33dc`; retargeting raft to upstream (2026-10-09)
- Perennial `7d0b56b07`: Goose with per-iteration loop variables (2026-10-09)
- Merge: the cache as shipped and client/v3/concurrency (2026-10-09)
- The cache as shipped: shared writers, a revision bound, no code change but the fix (2026-10-09)
- client/v3/concurrency: the transaction and lease model, Session (2026-10-09)
- Perennial models of `fmt.Sprintf`, `strings.Join`, `crypto/rand.Int` (2026-10-09)
- The TCB and verified-code scripts: generic, per-collection trust base (2026-10-09)
- Sorry-free (2026-10-09)
- The cache: linearizability as a model fact, `etcdReached` (2026-10-09)
- Merged with upstream's server work (2026-10-09)
- Perennial `8c33774d0`: Goose without `-lean` (2026-10-09)
- Merged with upstream's layout (2026-10-09)
- Done (at `857d09190`)
- etcd `cache`: the `EtcdCache` library (2026-10-08; translation only, no proofs)
- The cache's btree: verified (`Proof/k8s_io/utils/third_party/forked/golang/btree/`)
- Next
- Differences from the Rocq besides the language
- etcd's server: the consistent index and the apply thread (`server/v3/etcdserver`): proved (2026-10-09)
