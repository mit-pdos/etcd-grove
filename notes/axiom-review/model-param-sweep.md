# The "trusted model as a parameter" sweep: what was checked

**Reviewed:** 2026-11-07, `lean` at `158829a8b9`, axiom sweep (`notes/axiom-sweep-plan.md` on
branch `axiom-sweep`; this pass follows B1-1).

**The shape.** An axiom quantified over a record or class whose fields are the trusted model (a
wire relation, a decoding, a receive predicate), with nothing tying that record to the Go type.
A caller then builds a bogus record. Either the axiom proves `False`, or it proves a program safe
that panics in Go. `pbEnc_ok` was the first ([pbenc](pbenc.md)).

**The scan.** It covered about 895 `axiom` declarations, in `Proof/`, `Spec/`, `GooseLang/`,
`TrustedCode/`, `RaftWitness/` and `PorcupineDag/`. It also covered the `.spec` bodies of the 401
`wp_proof` axioms. Flagged: binders typed by a structure or a class, and predicate binders. Two
axioms name a model structure directly, `pbEnc_ok` and `v3rpc.codec_proto`. Through the spec
bodies, the scan found:

- the five `proto.*Pb` specs;
- `grpc.ClientConn.NewStream` (`StreamMsg`);
- `grpc.CustomCodec`;
- the bridge's `New`.

`ProtoMsg` reaches its axioms indirectly, through `grpcInvokerOk` and `grpcMethodOkMd`.

## Confirmed

| family | axioms | branch, commit | record |
|---|---|---|---|
| `PbType`, the encoding | `pbEnc_ok` | `axiom/pbenc-inconsistent` `f238daef0c` | [pbenc](pbenc.md): a closed `False` |
| `PbType`, the triples | `proto.{Marshal,Size,Clone,MarshalAppend,Unmarshal}Pb.wp_proof` | `axiom/pbtype-specs` `0f1f10d1d1` | [pbenc](pbenc.md): a program that panics in Go, proved safe |
| grpc `ProtoMsg` | `grpc.serve`, `grpc.ClientConn.Invoke.wp_proof` | `axiom/protomsg` `8d7ff9b9b4` | [grpc-msg](grpc-msg.md) |
| grpc `StreamMsg` | `grpc.ClientConn.NewStream.wp_proof`, `grpc.serveStream` | `axiom/streammsg` `f285e9d4aa` | [grpc-msg](grpc-msg.md) |

## Cleared: no bogus model can be supplied

| axiom | file | why it is cleared |
|---|---|---|
| `reflNew_pointsto` (`[ZeroVal V] [TypedPointsto V] [IntoValTyped V T]`) | `Proof/reflect/Values.lean:75` | `IntoValTyped` needs `TypeRepr T V`, which only the semantics' facts give. Its laws are `wp_alloc`, `wp_load` and `wp_store` against the real heap. A user's instance cannot change what `p ↦ zero_val V` means. |
| `initLb_of_spec` (`[IsPkgInit p] [GetIsPkgInitWf p]`) | `Proof/runtime/PkgInitExt.lean:98` (and its `RaftWitness/` copy) | The conclusion follows from the premise `Hstd`, under the same instances, plus the fact that the package map only grows, which holds for any instance. A bogus instance only makes `Hstd` harder to prove. |
| `stampAt_elim` (`[Persistent P]`) | `Proof/github_com/jonboulle/clockwork/Defs.lean:82` | `Persistent` is a class with a law, so it cannot be faked, and `stampAt` is only made at `□ P`. |
| `reserve`, `register`, `Serve_ok`, `mux_handlerOk_ok` (`H : HttpNet`, `Proto`) | `Proof/net/http/Axioms.lean:39-155` | `Proto` is a protocol spec, not a wire model. Client and server are tied to one `P` per address through `httpProtoAt`, which comes from the exclusive `httpProtoFree a`. |
| `sort.Sort.wp_anyLess` (`R : List E → IProp`) | `Proof/sort/SortAnyLess.lean:33` | An ordinary higher-order spec: the caller proves `Len`, `Less` and `Swap` against `R`. |
| the other higher-order specs: heap, binary `Read`, the snapshot's `WriteTo`, `verify.Verify`, `errors.AsLeaf`, credentials | | Same reason as `sort.Sort.wp_anyLess`. |
| `New.spec` over `ObjSpec`/`ObjCodec` | `Proof/k8s_io/apiserver/pkg/storage/etcd3/Contract.lean` | etcd3's `New` is proved, not an axiom, and `contractOk` is a premise checked against the real codec. The axiom `New.wp_proof` of that name is the bridge's (`third_party/bridge/New.lean:28`), and it takes no model. |
| `grpc.CustomCodec`, `v3rpc.codec_proto`, `grpcSrvOpt` (`SrvOptKind`, an inductive) | `InvGrpcServer.lean:96-102`, `InvGrpcStart.lean:287` | Opaque `Prop`s about values, with no model chosen by the caller. |
| `memberEnc_id_learner`, `memberKey_inj`, `membership.membersOf_decode`, `swMsgBound_phys`, `collectorName`, `counterOpts`, `reqsValid` | various | Facts about fixed definitions or opaque predicates, with no model binder. Cleared of this shape only; the sweep's other targets cover `swMsgBound_phys` (B2-1). |

## A different shape: the environment record (cleared)

`etcd_noRefusal` and `etcd_noOtherRefusal` (`Proof/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/
NoRefusal.lean:55,85`) take `E : apply.AEnv`. They are **cleared** (2026-11-07). Their premise
`E.authOn = false` is tied to the real server through its wait registry:

- `isServerReq s E ρ` needs `waitInv v.w ρ E`, and `s.w ↦□ v.w` pins the registry;
- `waitInv` contains `isWait v.w … (reqWaitR ρ E)`, whose predicate is chosen once at `wait.New`
  (a proved spec);
- an auth-on server's registry carries `reqWaitRM true` (`resultΨOn …`), which differs from the off
  one (`resultΨ …`);
- `isWait` has no monotonicity law: `Register` would need `□R_off ⊢ □R_on`, `Trigger` would need
  `waitTrig R_off ⊢ waitTrig R_on`, and neither holds;
- a fresh registry would need the list's exclusive state;
- the other parts that depend on `E` do not fix the mode, but they do not need to:
  `srvIndexInvs`, `srvAppliedBody` and `srvFloorFact` read only `E.γ.idx`, and `isReqAuth` reads
  only `E.RD`.

**Not checked, outside this pattern.** Mode off means "auth never enabled", and `dispatchOk false`
excludes `AuthEnable`. Whether a client's `AuthEnable` can reach an off-mode server's apply thread
through its Auth service is a separate question about the workload premise.
