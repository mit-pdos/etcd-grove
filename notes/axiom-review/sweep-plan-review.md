# axiom sweep plan review (82's workflow wf_1c7b6091-414, 2026-11-07)

## Surviving

- **blocker**: errors.IsCtxErr.wp_proof is excluded under isdeadline-g1a (plan :98), but nothing attacks it, and it looks false. Its only premise on err is `context.isTypedErr err`, which says only that the dynamic type is in error's type set. Go's errors.Is calls the error's own Is and Unwrap methods, and either may panic.
  - evidence: /shared/etcd-grove-sweep/Spec/errors/IsCtxErr.lean:34-40 takes only `context.isTypedErr err` and has no errorIsTree premise. Its docstring (:26-33) argues from what etcd passes. isTypedErr is `typeSetContains ii.ty error` (perennial Proof/context/Base.lean:182). `git grep IsCtxErr axiom/isdeadline-g1a -- notes` matches only STATUS, audit, decisions and similar files, never the review report. Reach recomputed from .lake/tcb.json: 17 of 23 `_safe` roots, 137 roots in all.
  - fix: Remove it from the exclusions and make it a Batch 1 target (S, Go). Counterexample: `type bad struct{}; func (bad) Error() string {return ""}; func (bad) Unwrap() error {panic("x")}`, then `errors.Is(bad{}, context.Canceled)`. Fix: add errorIsTree as IsDeadlineExceeded does, or require isCtxErr err (which is what callers actually have).

- **major**: http.Handle_ok (with NewServeMux_ok) is neither in the plan's exclusions nor among its targets, and Go refutes it directly. Handle_spec requires only that `pat` is not already in `regs`, for any `h`. Go's ServeMux.register panics on the empty pattern "", on a nil handler, on a pattern that fails to parse ("b"), and on two distinct pattern strings that conflict ("/{x}" and "/{y}").
  - evidence: /shared/etcd-grove-sweep/Proof/net/http/Boundary.lean:891-896 (Handle_spec) and :884-887 (NewServeMux from True). Plan section 2 names only http.{Serve_ok,register,reserve,respWriteHeader_ok}. Reach: 6 `_safe` roots, 26 roots in all.
  - fix: Add it as a Batch 1 target (S, Go): `m := http.NewServeMux(); m.Handle("", nil)`. Fix: add a premise that the pattern is well formed and does not conflict with `regs`, and that h is not nil.

- **major**: The axioms gated by ETCD_VERIFY are missing from the plan. ValidateCalledOutSideApply, ValidateCalledInsideApply, ValidateCalledInsideUnittest and VerifyBackendConsistency all return unconditionally in their specs. In Go they panic, or call lg.Fatal, when ETCD_VERIFY=lock or all and the call stack does or does not contain `.applyEntries` (or `_test.go`). VerifyBackendConsistency also takes any Backend b, so under ETCD_VERIFY=all a user Backend whose BatchTx panics refutes it. The docstrings admit this is 'a deployment assumption', but no closed theorem states it.
  - evidence: /shared/etcd-grove/.lake/go-src/etcd/server/storage/backend/verify.go:31-95. /shared/etcd-grove-sweep/Spec/go_etcd_io/etcd/server/v3/storage/backend/ValidateCalledOutSideApply.lean header and spec (`∀ lg, {{isPkgInit}} … {{RET #(); True}}`). Under the axiom skill, a Go test may set t.Setenv before the call. Reach: 17 of 23 closed theorems each for OutSideApply and VerifyBackendConsistency.
  - fix: Add an S target with a Go test: a function named applyEntries calls ValidateCalledOutSideApply under t.Setenv("ETCD_VERIFY","lock"). Preferred repair: an explicit startup premise such as envVerifyOff that the adequacy theorems take, as they take walDirsAbsent, so the assumption appears in the closed statements.

- **major**: The grpc axioms over ProtoMsg/GrpcMethod have the same flaw as B1-1, with higher reach, yet the plan lists them only as a 'follow-up'. ProtoMsg's send, recv, wireLen and M are fields the caller supplies (wireLen is called 'part of the instance's trusted wire model'). grpcInvokerOk quantifies over any `Req Rep : ProtoMsg` and requires only `Req.wireLen m < grpcMsgMax`. A counterexample program controls both the client and the server it registers, so it can pick bogus instances.
  - evidence: /shared/etcd-grove-sweep/Proof/google_golang_org/grpc/InvGrpc.lean:78-110 (structure ProtoMsg) and :1210-1225 (grpcInvokerOk). Plan :223-225 admits that no report tried a bogus instance. Reach: ClientConn.Invoke, grpc.serve, proto.Size and the rest each reach 17 of 23.
  - fix: Make it a Batch 2 target, designed together with B1-1's repair, because one instance discipline should cover both PbType and ProtoMsg. Attack (a), a full round trip: a bogus Req whose recv pins m=42 while the client sends 7; the handler panics when the value differs. Attack (b): wireLen := 0 on an oversized message. Estimate M-L, since it needs the server start and network axioms.

- **major**: B2-4 attacks a statement that is derivable. Perennial's isContext HErr already returns `isCtxErr err` for every non-nil Err, and HErrDone returns isTypedErr. isCtxErr is exactly ErrAny's disjunction (Canceled as an *errorString holding "context canceled", or DeadlineExceeded's type). So the suspected counterexample is excluded by the premise. ErrAny's header ('Perennial's isContext says only that a done context's error is typed') is out of date.
  - evidence: /shared/etcd-grove/.lake/packages/perennial/Perennial/Proof/context/Base.lean:212-217 (isCtxErr), :570-589 (HErr, HErrDone). /shared/etcd-grove-sweep/Spec/context/ErrAny.lean:38-57. ErrAny reaches 22 of 23 `_safe` roots, the highest reach in this list.
  - fix: Replace the attack with removing the axiom: prove context.ErrAny.spec (and ErrDone, Err) from HErr/HErrDone. That needs isTypedErr for the Canceled *errorString and a type-inequality fact. Estimate S-M, Lean only. It removes an axiom with reach 22.

- **major**: B2-2's planned observation does not work, and the target is larger than estimated. reqURL_ok's `↦□` returns an existential URL that is not linked to R.path, and a mux pattern "b" panics inside Handle, which refutes Handle_ok, not urlOf.
  - evidence: /shared/etcd-grove-sweep/Proof/net/http/Boundary.lean:955-958 (`∃ up u, … up ↦□ u`, with no link to R). On the server side, reqAt links URL.Path to R.path (:494-497).
  - fix: Rewrite B2-2 as a client-server round trip: the server's handler reads r.URL.Path, which reqAt links to R.path, and answers non-200 unless it equals "b"; the client panics on non-200. Re-estimate as L. Split the easy Handle_ok refutation out as its own target (listed above).

- **major**: proto.Marshal, proto.Unmarshal and proto.Size (all at 17 of 23) are excluded because getallleases and grpc-start-replies mention them. Those reports only run Go's protobuf on leasepb and on reply sizes. No review attacks these triples, which are the mvccpb.KeyValue and txn per-type specs. Marshal's precondition leaves x's unknownFields' and state' unconstrained while its post fixes the bytes to kvEncode kv.
  - evidence: /shared/etcd-grove-sweep/Spec/google_golang_org/protobuf/proto/Marshal.lean:29-41. getallleases.md:37,40. grpc-start-replies.md:233-234.
  - fix: Fold them into B2-3's protobuf edge-case probes: unknown fields reached through Unmarshal and re-Marshal, the 2 GiB size limit and errors, and nil versus empty. Medium risk: SetUnknown is not translated, so injecting unknown fields may need an Unmarshal round trip.

- **minor**: Downgraded from major: context.WithValue was never reviewed on its own. Its spec is careful: it is limited to empty-struct key types, its Values field `vs` is read by no predicate, and it says nothing of other values of the same key type. The B1-3 counterexample will print WithValue among its axioms anyway.
  - evidence: /shared/etcd-grove-sweep/Spec/context/WithValue.lean:29-70.
  - fix: Have B1-3 also check WithValue's claims (the Value wand and txnCtx transfer), instead of saying 'used unchanged'.

- **minor**: B1-3's written attack does not go through. `context.Background()` gives no isContext, so ValueStartTime's premise cannot be met.
  - evidence: Plan :273. Spec/context/WithValue.lean:57-58 gives isContext only from an isContext parent.
  - fix: Start from `ctx, cancel := context.WithCancel(context.Background())`, then apply WithValue with StartTimeKey{} and 42.

- **minor**: Downgraded from major: proto.UnmarshalUser's missing UTF-8 premise is a latent gap, not a live refutation. userEncode is opaque (Buckets.lean:77), only authWf supplies it, and the axiom reaches 0 of 23 closed theorems.
  - evidence: tcb.json: UnmarshalUser reaches 4 roots, none ending in `_safe`. /shared/etcd-grove-sweep/Proof/go_etcd_io/etcd/server/v3/auth/Buckets.lean:77.
  - fix: Add a valid-UTF-8 premise on roles when a writer of the users bucket is verified. Record it in section 5, not as a target.

- **minor**: Smaller gaps that do hold up: (a) the RaftWitness copies of the B2-3 axioms, initLb_of_spec and FormatUint must receive the same fixes; (b) IsCapabilityEnabled takes RLock with no reader token, which belongs in B4-2; (c) the uncovered rpctypes initializers (the '34' count is overstated); (d) the 'refuted, still open' entries (ownWTxG_fill, Bucket.Put_kv) should be shown apart from the survivors; (e) sort.Sort.wp_anyLess and the heap specs need a cheap fuzz probe; (f) walPurgeRight is never consumed.
  - evidence: As cited by the checkers. IsCapabilityEnabled reaches 17 of 23.
  - fix: Fold these into the existing batch items, or into section 5 as the checkers propose.


## Dropped
- UnmarshalUser as a major: userEncode is opaque, only authWf supplies it, and the axiom reaches 0 of 23 closed theorems (kept as a latent minor)
- context.WithValue as a major: its spec is restricted and careful, so it is now a minor joint check within B1-3
- No checker's confirmed point about B1-2, B1-4 or B2-1 was overturned. The B1-4 effort bump to S-M and B2-1's dependency on SizePb stand as minors.


## Recommended order
1. 1. B1-2 zap zero Logger: Warn, Error, Panic, Fatal, Check, plus Info (S, Go, 17/17)
2. 2. NEW errors.IsCtxErr: a typed error whose Unwrap panics (S, Go, 17/17)
3. 3. B1-3 ValueStartTime, from WithCancel(Background) and WithValue(StartTimeKey{}, 42), with WithValue's claims checked jointly (S, Go, 17/17)
4. 4. NEW ETCD_VERIFY family: ValidateCalledOutSide/InsideApply, InsideUnittest, VerifyBackendConsistency (S, Go with t.Setenv, 17/17), repaired by an explicit env premise
5. 5. NEW http.Handle_ok / NewServeMux_ok: Handle("", nil) (S, Go, 6 closed)
6. 6. B1-4 featureInit and checkerInit (S-M, Go under the k8s module, 4/4)
7. 7. B2-4 recast: prove context.ErrAny, ErrDone and Err from isContext's HErr/HErrDone, removing the axioms (S-M, Lean only, 22/23)
8. 8. NEW grpc ProtoMsg/GrpcMethod bogus-instance family, designed with B1-1's PbType repair (M-L, 17/17)
9. 9. B2-1 swMsgBound_phys via a shared *Entry and SizePb, redone after B1-1's fix (M, Go)
10. 10. B2-3 raft per-type protobuf specs plus proto.{Marshal,Unmarshal,Size} for KeyValue/txn, with fixes mirrored to the RaftWitness copies (M, Go); then B2-2 rewritten as a round trip (L), B4-2 with IsCapabilityEnabled added, and the minors
