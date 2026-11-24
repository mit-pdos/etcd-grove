# Phase 7: the end state and the work plan (the gRPC, net and net/http trust boundary retired)

2026-11-24, overnight (coordinator-E's request; the user unavailable). One plan for what remains of
phase 7, so that every proof from here on is written against the statements it ends with. It
supersedes `notes/phase7-plan.md` where the two differ (that note keeps the history: S0, S1, the S2
draft, the S5 draft). Sources, read against `lean` at `479344f1e5`:

- the S3 design (`plan-s3.md`: one call protocol for unary calls and streams, the two `NewStream`
  defects, S3.0-S3.5);
- the S2 end-state design (`plan-s2-endstate.md`: the dec-shaped run contract, F2, O4-O10, W0-W8);
- the inventory of the family's 148 axioms and 30 opaques (`plan-inventory.md`, `lean` at
  `6d5a98fb3d`);
- the review of the landed S2 interface switch (`notes/axiom-review/s2-interface.md` and its design);
- `bridge.New` consuming `netAddrLeft a` (`cf333b5be9`, `notes/axiom-review/bridge-addrleft.md`).

The four design notes live outside the repository (the coordinator's `plans/phase7-design/`); what
this note takes from them is restated here. Nothing below has been built. A Lean block is the
intended statement; **not elaborated** marks what may need adjusting when it is compiled.

Trusted changes (trust-boundary axioms, opaque trusted definitions, `TrustedCode`, the models'
claims, top-level premises) are made only on branches and land after the user's review. The work
plan marks each branch **trusted** or not. The decisions taken overnight are in §3, each marked
"Decided (overnight, revisit in the morning)".

## 1. The architecture

### 1.1 In one page

- **A service table per address, heap-free.** `GrpcSvc GF := GoString → Option (GrpcSvcEntry GF)`.
  An entry is `.unary e` (S2's `GrpcEntry`: the messages' wire parts and the spec) or `.stream e`
  (`GrpcStreamEntry`: the wire parts, the client's content `up`, the server's content `dn md γ` at the
  dispatched metadata, and the stream specification `spec md γ Dn`). The table is a Lean term fixed
  when the address's protocols are set (`grpc_addr_set`, from `addrUnset a`), the same term on every
  machine. It mentions ghost names the start allocates, never a heap.
- **Per-address protocols.** `grpcAddrAt a Svc := addrProto a (grpcCliPI Svc) (grpcSrvPI Svc) ∗
  depSlotsCtx`. Until `Invoke`, `NewStream` and `Serve` are all proved over the model, the protocols
  are the opaque `grpcCliPI`/`grpcSrvPI` (trusted text, no law: no program but grpc's transport can
  write or learn anything on a grpc connection). At the end they are the defined `grpcCliP`/`grpcSrvP`
  of §1.4, and grpc's address vocabulary is **sealed** (`etc/api/grpc.txt`, `@[no_expose]`), so that
  no proof outside grpc can dial, listen or accept at a grpc address (§3, decision A).
- **Registrations read the table.** `isGrpcRpcMd addr name Spec := grpcSvcAt addr name …` and
  `isGrpcStreamMd addr name Up Spec := grpcStreamSvcAt addr name …`: an entry of `addr`'s table at the
  messages' wire parts, which the caller's spec converts into. No heap, no `γ` of a server, no
  `grpcReach`. Every user statement (`isGrpcRpc*`, `isGrpcStream*`) keeps its text.
- **One call protocol for unary calls and streams** (S3's design, adopted over S2's per-data-frame
  slot, §1.5). A call is opened by its client with heap-free ghost state, `callInv γ P`: the up queue,
  the down queue, the up end, the dispatched metadata and the server's end, each message's content
  held in the invariant until its receiver takes it. The client's head on a connection carries, in that
  connection's deposit slot, the server's whole share of the call (its tokens and `callInv γ P`). A
  unary call is the instance whose single request carries the caller's deposit. The transport,
  `clientStream` and `processRPC` are proved once.
- **One run contract shape.** A unary handler gets its deposit only out of a successful `dec`
  (`grpcDecDepOk`, with the abstract right `D` and receipt `Got` that `Serve`'s proof chooses), because
  both grpc-go and the model start the handler on the head, before any data frame. A stream handler gets
  the raw server end (`srvRawStreamIs`, unchanged) whose `RecvMsg` hands out `up i m` per message. The
  unary contract is the stream contract at one message.
- **The server's right to serve.** One form: `grpcServeTok gs lis a Svc` is the server being built, the
  node's open listener at `a`, `a` serving `Svc` and `gs` serving `Svc` (`grpcServes`, with a clause per
  entry kind). No server name `γ`, no start token: `grpc.start`, `grpcAddrIsRaw`, `grpcSrvCfgRaw`,
  `grpcSrvLink`, `grpcAddrIs_agree` and `grpcSrvCfg_agree` are deleted, not proved.
- **The single-process start** fixes Go's table at the start (`grpc.start'` sets the stream entries
  from a list now, the unary entries from a list after W4), and may mention the server's heap: only
  across machines must the table be heap-free.
- **Bridges** (O5, S2's D4, corrected): the bridge's address serves its target's table. The caller sets
  `a`'s table to the target's `Svc` from what `Listen` left (`netAddrLeft a`, consumed since
  `cf333b5be9`), and `bridge.New` takes `grpcAddrAt a Svc ∗ grpcAddrAt addr Svc` at the same `Svc`.
  Registrations at `a` are read off `a`'s table, as at any address.

### 1.2 What lands now: the switch, in end-state shape

Two trusted branches restate the interim axioms in their end-state shape, so that proving them over
the model later changes no user statement (§4, SW1 and SW2). SW1 merges S3.0 with the parts of S2's
W0 that touch the same statements (the attempt's metadata, the table, `grpcServeTok`, the start, the
bridge); SW2 is S2's run-contract switch (D1), whose sites are disjoint but for one clause of
`grpcServes`. The exact Lean follows; `...` is unchanged text.

**The table** (`Proof/google_golang_org/grpc/InvGrpcWire.lean`, section `svc`; `StreamNames` moves
down to a new defs module `InvGrpcCall.lean`, imported by `InvGrpcWire`):

```lean
/-- A message type's wire part: its Go type, its model (countable: a call's queues are ghost lists of
models), its stored form. -/
structure ProtoWire where
  ty : go.GoType
  M : Type
  tree : M → VTree
  cnt : Pos.Countable M := by infer_instance       -- new (not elaborated: the anonymous constructors)

abbrev ProtoMsg.wire (T : ProtoMsg GF) : ProtoWire := ⟨T.ty, T.M, T.tree, T.cnt⟩   -- ProtoMsg gains `cnt`
abbrev StreamMsg.wire (T : StreamMsg GF) : ProtoWire := ⟨T.ty, T.M, T.tree, T.cnt⟩ -- StreamMsg gains `tree`

/-- A streaming method of a service (no heap): its messages' wire parts, the client's content of its
`i`-th request, the server's content of its `j`-th response at the metadata the stream was dispatched
with, and what a client learns of a stream (`spec md γ Dn`, persistent). -/
structure GrpcStreamEntry (GF : BundledGFunctors) [GooseExts] where
  Wq : ProtoWire
  Wp : ProtoWire
  up : Nat → Wq.M → IProp GF
  dn : GrpcMd → StreamNames → Nat → Wp.M → IProp GF
  spec : GrpcMd → StreamNames → (Nat → Wp.M → IProp GF) → IProp GF

/-- An entry of a service table. (`plan-s3.md` named it `GrpcMethod`, which is taken: the start's
list element `GrpcMethod GF` of `InvGrpc.lean`.) -/
inductive GrpcSvcEntry (GF : BundledGFunctors) [GooseExts] where
  | unary (e : GrpcEntry GF)
  | stream (e : GrpcStreamEntry GF)

abbrev GrpcSvc (GF : BundledGFunctors) [GooseExts] := GoString → Option (GrpcSvcEntry GF)
```

`StreamNames` gains `md : GName`, and two definitions come with it (`InvGrpcCall.lean`):

```lean
/-- The stream `γ` was dispatched with the metadata `md` (persistent). Set once by whoever dispatches
it: `NewStream`'s axiom until S3, `call_dispatch` after. -/
def streamMdIs (γ : StreamNames) (md : GrpcMd) : IProp GF := dghostVar γ.md .discard (some md)

theorem streamMdIs_agree (γ : StreamNames) (md md' : GrpcMd) :
    streamMdIs γ md ∗ streamMdIs γ md' ⊢ ⌜md = md'⌝
```

**The registrations** (`InvGrpcWire.lean`, section `protos`; `InvGrpc.lean`; `InvGrpcStream.lean`):

```lean
def grpcSvcAt (a name : GoString) (Wq Wp : ProtoWire) (Spec : GrpcMd → Wq.M → (Wp.M → IProp GF) →
    (GoString → IProp GF) → IProp GF) : IProp GF :=
  iprop(∃ (Svc : GrpcSvc GF) (Spec₀ : …), grpcAddrAt a Svc ∗
    ⌜Svc name = some (.unary ⟨Wq, Wp, Spec₀⟩)⌝ ∗ □ ∀ md m Φ Ψe, Spec md m Φ Ψe ==∗ Spec₀ md m Φ Ψe)

def grpcStreamSvcAt (a name : GoString) (Wq Wp : ProtoWire) (Up : Nat → Wq.M → IProp GF)
    (Spec : GrpcMd → StreamNames → (Nat → Wp.M → IProp GF) → IProp GF) : IProp GF :=
  iprop(∃ (Svc : GrpcSvc GF) (up₀ : Nat → Wq.M → IProp GF)
      (dn₀ : GrpcMd → StreamNames → Nat → Wp.M → IProp GF)
      (spec₀ : GrpcMd → StreamNames → (Nat → Wp.M → IProp GF) → IProp GF),
    grpcAddrAt a Svc ∗ ⌜Svc name = some (.stream ⟨Wq, Wp, up₀, dn₀, spec₀⟩)⌝ ∗
    (□ ∀ md γ, spec₀ md γ (dn₀ md γ)) ∗
    (□ ∀ i m, Up i m ==∗ up₀ i m) ∗ (□ ∀ md γ Dn, spec₀ md γ Dn -∗ Spec md γ Dn))

-- InvGrpc.lean: `grpcReach` is deleted (bridges: §1.1, decision C3).
def isGrpcRpcMd {Req Rep : ProtoMsg GF} (addr name : GoString) (Spec : GrpcSpecMd Req Rep) : IProp GF :=
  iprop(∃ (_ : HasExt netExt) (π : NetProtoGS) (σ : NetSlotGS),
    grpcSvcAt (Gg := hG.goose_globalGS) (π := π) (σ := σ) addr name Req.wire Rep.wire Spec)

-- InvGrpcStream.lean: was `∃ γ, grpcAddrIs addr γ ∗ isGrpcStreamAt γ name Up Spec`.
def isGrpcStreamMd {Req Rep : StreamMsg GF} (addr name : GoString) (Up : Nat → Req.M → IProp GF)
    (Spec : GrpcMd → StreamSpec Rep) : IProp GF :=
  iprop(∃ (_ : HasExt netExt) (π : NetProtoGS) (σ : NetSlotGS),
    grpcStreamSvcAt (Gg := hG.goose_globalGS) (π := π) (σ := σ) addr name Req.wire Rep.wire Up Spec)
-- isGrpcStream, isGrpcStreamsMd, isGrpcStreams: text unchanged.
-- isGrpcStreamAt, grpcStreamServerAt, grpc.serveStream: deleted.
```

**The attempt's metadata, over an `IProp`** (S2's D6; `InvGrpc.lean`). The opaque Prop `credsYield`
becomes an opaque `IProp`, persistent by construction, so that the attempt's proof over the model can
produce it from the credentials' ghost record (no axiom; the same trusted count):

```lean
opaque credsYieldRaw (conn : Loc) (cm : GrpcMd) : IProp GF
def credsYieldI (conn : Loc) (cm : GrpcMd) : IProp GF := iprop(□ credsYieldRaw conn cm)

def grpcAttemptMdI (conn : Loc) (om md : GrpcMd) : IProp GF :=
  iprop(∃ cm, credsYieldI conn cm ∗ ⌜(∀ k, ¬ grpcReservedKey k →
      metadata.mdVals md k = metadata.mdVals cm k ++ metadata.mdVals om k) ∧ ∀ k, mdGet md k ≠ some []⌝)
-- grpcInvokerOk's premise:  ▷ (∀ md, grpcAttemptMdI conn om md -∗ Spec md m Φ Ψe)
-- connCredsOk: the same three arms, over `credsYieldI conn cm -∗ …` in place of `⌜credsYield conn cm⌝ →`.
-- client/v3's clientAttemptMd (InvKVConn.lean:1566) becomes the IProp clientAttemptMdI.
-- NewClient's premise perRPCCredsOk gains credKeysOk (no metadata key starting with ':').
```

**The client end of a stream** (`InvGrpcStream.lean`). `cliStreamIs` takes the call's metadata family
`Md` and an `md`-indexed `Dn`; two arms of `RecvMsg` change (R2 and R1 of §2), the rest keeps its text:

```lean
def cliStreamIs (cs : GoInterface) (γ : StreamNames) (Req Rep : StreamMsg GF)
    (Up : Nat → Req.M → IProp GF) (Md : GrpcMd → IProp GF) (Dn : GrpcMd → Nat → Rep.M → IProp GF)
    (cd : context.ContextDesc (IProp GF)) (Ok : IProp GF → Prop) : IProp GF := …
  -- RecvMsg, nil:  ∃ md m, Md md ∗ streamMdIs γ md ∗ Rep.recv out m ∗ Dn md L.length m ∗
  --                  cliRecvTok γ (L ++ [m])
  -- RecvMsg, EOF:  eofIs err ∗ ⌜err ≠ GoInterface.nil⌝ ∗ cliRecvTok γ L ∗
  --                  (downClosed γ L ∨ ⌜L = []⌝) ∗ Rep.own out
-- cliBidiStreamIs: the same two arms; cliBidiStreamIs_of_raw re-proved.
```

**`NewStream`** (`Spec/google_golang_org/grpc/ClientConn__NewStream.lean`; the axiom restated). The
precondition keeps its text. The post fixes no `md`: the stream specification holds at every metadata
an attempt may deliver, at that metadata's content.

```lean
  {{ (cs err : GoInterface), RET (PairV #cs #err); R ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ (a : GoString) (γ : StreamNames)
          (Dn : GrpcMd → Nat → Rep.M → IProp GF) (cd' : context.ContextDesc (IProp GF)),
        ⌜a ∈ addrs⌝ ∗
        cliStreamIs cs γ Req.toStreamMsg Rep.toStreamMsg (Up a) (clientAttemptMdI conn om) Dn cd' Ok ∗
        cliSendTok (Req := Req.toStreamMsg) γ [] ∗ cliRecvTok (Rep := Rep.toStreamMsg) γ [] ∗
        □ (∀ md, clientAttemptMdI conn om md -∗ Spec a md γ (Dn md))) ∨
      (⌜cs = GoInterface.nil⌝ ∗ cliStreamErr err)) }}
```

**What a server serves** (`InvGrpcRun.lean`). A clause per kind: a unary entry names no stream (C3), a
stream entry names no unary method (C3's mirror: a `NewStream` of a unary method's name runs the wrapped
unary handler on a stream, model `server.go:778-785`). The server's own `Up`/`Spec`/`Dns` may mention
its heap; it converts to the table's when it pushes.

```lean
def grpcServes (Svc : GrpcSvc GF) (ics sics : List GoFunc)
    (regs sregs : List (GoString × GoFunc × GoInterface)) : IProp GF :=
  iprop(□ ∀ (name : GoString) (ent : GrpcSvcEntry GF), ⌜Svc name = some ent⌝ -∗
    match ent with
    | .unary e => ⌜name ∉ sregs.map Prod.fst⌝ ∗ ∀ (mh : GoFunc) (srv : GoInterface),
        ⌜(name, mh, srv) ∈ regs⌝ -∗
        ∃ (Req Rep : ProtoMsgT GF) (Spec : GrpcSpecMd Req.toProtoMsg Rep.toProtoMsg),
          ⌜grpcReqModelOf GF Req.ty = some Req ∧ grpcRepModelOf GF Rep.ty = some Rep ∧
            e = ⟨Req.toProtoMsg.wire, Rep.toProtoMsg.wire, Spec⟩⌝ ∗
          grpcRunOkMd #mh srv ics Spec                       -- SW2: `grpcRunOkMd … ∨ grpcRunPreOkMd …`
    | .stream e => ⌜name ∉ regs.map Prod.fst⌝ ∗ ∀ (mh : GoFunc) (srv : GoInterface),
        ⌜(name, mh, srv) ∈ sregs⌝ -∗
        ∃ (Req Rep : StreamMsgT GF) (up₀ : Nat → Req.M → IProp GF)
          (dn₀ : GrpcMd → StreamNames → Nat → Rep.M → IProp GF)
          (spec₀ : GrpcMd → StreamSpec Rep.toStreamMsg) (Up : Nat → Req.M → IProp GF)
          (Spec : GrpcMd → StreamSpec Rep.toStreamMsg) (Dns : GrpcMd → StreamNames → Nat → Rep.M → IProp GF),
          ⌜streamReqModelOf GF Req.ty = some Req ∧ streamRepModelOf GF Rep.ty = some Rep ∧
            e = ⟨Req.wire, Rep.wire, up₀, dn₀, spec₀⟩⌝ ∗
          (□ ∀ i m, up₀ i m -∗ Up i m) ∗ (□ ∀ md γ, Spec md γ (Dns md γ)) ∗
          (□ ∀ md γ j m, Dns md γ j m -∗ dn₀ md γ j m) ∗
          grpcStreamRunOk #mh srv sics Up Spec)

/-- The right to serve `gs` on `lis` at `a`, for the table `Svc` (one form; the started disjunct and
its server name `γ` are gone). -/
def grpcServeTok (gs : Loc) (lis : GoInterface) (a : GoString) (Svc : GrpcSvc GF) : IProp GF :=
  iprop(∃ (c : GrpcSrvCfg GF) (svcs : List GoString),
    grpcSrvNew gs c.ics c.sics svcs c.regs c.sregs ∗ netListenerOpen lis a ∗
    ⌜grpcSrvNodup c ∧ grpcRepliesFit⌝ ∗
    (∃ (_ : HasExt netExt) (π : NetProtoGS) (σ : NetSlotGS),
      grpcAddrAt (Gg := hG.goose_globalGS) (π := π) (σ := σ) a Svc) ∗
    grpcServes Svc c.ics c.sics c.regs c.sregs)
```

`grpcStreamRunOk` loses its first conjunct (`□ ∀ md, streamSpecOk (Spec md)`): the start's premise and
`grpcServes` carry the content family explicitly (`dn`, `Dns`), as a Lean function, which Iris cannot
extract from a `∀ ∃` (S3 proposed restating the conjunct as `∃ Dns, □ ∀ md γ, Spec md γ (Dns md γ)`;
it is then said twice, so it goes). `GrpcStreamMethod` gains `dn`. `Server.Serve.spec` keeps its text.

**The single-process start** (`InvGrpcRun.lean`; a theorem, no longer over `grpc.start`):

```lean
/-- Go's configuration as a table: the unary methods as today (`grpcGoSvc`), the streams `sms`. -/
def grpcStartSvc (ics : List GoFunc) (regs : List (GoString × GoFunc × GoInterface))
    (tys : GoString → Option (ProtoMsgT GF × ProtoMsgT GF)) (sms : List (GrpcStreamMethod GF)) :
    GrpcSvc GF := fun name =>
  match grpcGoSvc ics regs tys name with
  | some e => some (.unary e)
  | none => (sms.find? (·.name = name)).map fun m =>
      .stream ⟨m.Req.wire, m.Rep.wire, m.Up, m.dn, m.spec⟩

theorem grpc.start' (gs : Loc) (lis : GoInterface) (addr : GoString) (ics sics : List GoFunc)
    (svcs : List GoString) (regs sregs : List (GoString × GoFunc × GoInterface))
    (tys : GoString → Option (ProtoMsgT GF × ProtoMsgT GF)) (htys : …)
    (sms : List (GrpcStreamMethod GF)) (hsms : ∀ m ∈ sms, (m.name, m.handler, m.srv) ∈ sregs)
    (hsnd : (sms.map (·.name)).Nodup)
    (hfit : grpcRepliesFit) (hnd : ((regs ++ sregs).map Prod.fst).Nodup) :
    grpcSrvNew (GF := GF) gs ics sics svcs regs sregs ∗ netListenerAt lis addr ∗ netAddrLeft addr ∗
      □ ([∗list] m ∈ sms, grpcStreamRunOk #m.handler m.srv sics m.Up m.spec ∗
          □ ∀ md γ, m.spec md γ (m.dn md γ)) ⊢
    |={⊤}=> grpcServerAt addr ics regs tys sms ∗
      ([∗list] m ∈ sms, isGrpcStreamMd addr m.name m.Up m.spec) ∗
      grpcServeTok gs lis addr (grpcStartSvc ics regs tys sms)
```

`grpcServerAt` loses its `γ` and its `grpcAddrIs`/`grpcSrvCfg` conjuncts (`grpc.serve` never read them)
and gains `sms` (its table is `grpcStartSvc`). The callers that today run `grpc.start'` and then
`grpc.serveStream` pass the stream list to `grpc.start'` instead.

**The bridge** (`Spec/github_com/mit_pdos/etcd_grove/third_party/bridge/New.lean`):

```lean
abbrev New.spec : Prop :=
  ∀ (addr a : GoString) (l : GoInterface) (Svc : GrpcSvc GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.third_party.bridge ∗
      netListenerAt l a ∗
      (∃ (_ : HasExt netExt) (π : NetProtoGS) (σ : NetSlotGS),
        grpcAddrAt (Gg := hG.goose_globalGS) (π := π) (σ := σ) a Svc ∗
        grpcAddrAt (Gg := hG.goose_globalGS) (π := π) (σ := σ) addr Svc) }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.third_party.bridge.New)) (Val #addr)) (Val #l))
  {{ (br : GoInterface), RET #br; ownBridge br addr false ∗ ⌜noRefusalAt addr → noRefusalAt a⌝ }}
```

The caller spends `netAddrLeft a` to set `a`'s table (`grpc_addr_set`) to the target's term, so
`cf333b5be9`'s condition holds unchanged: whoever bridges `a` has spent what sets `a`'s protocols, and
it set them to the target's.

**SW2: the dec-shaped run contract** (`InvGrpcBase.lean`, replacing `:706-725` and `:1158-1170`; S2's
§1.2 text, adopted as written):

```lean
def grpcDecDepOk (dec : GoFunc) {Req Rep : ProtoMsg GF} (Spec : GrpcSpecMd Req Rep)
    (ci : GoInterfaceOk) (D : IProp GF)
    (Got : (Rep.M → IProp GF) → (GoString → IProp GF) → IProp GF) : IProp GF :=
  iprop(□ ∀ l : Loc, {{ D ∗ Req.blank l }}
      (App (Val #dec) (Val #(interface.mkOk (go.GoType.PointerType Req.ty) #l : GoInterface)))
    {{ (err : GoInterface), RET #err;
        (⌜err = GoInterface.nil⌝ ∗ ∃ (m : Req.M) (Φ : Rep.M → IProp GF) (Ψe : GoString → IProp GF),
            Req.recv l m ∗ Req.recvOwn l m ∗ grpcSpecAt Spec ci m Φ Ψe ∗ Got Φ Ψe) ∨
        (D ∗ notHandlerErr err ∗ go_etcd_io.etcd.cache.v3.statusErrOk err) }})

def grpcRunOut {Rep : ProtoMsg GF} (D : IProp GF)
    (Got : (Rep.M → IProp GF) → (GoString → IProp GF) → IProp GF) (resp err : GoInterface) : IProp GF :=
  iprop(go_etcd_io.etcd.cache.v3.srvErrOk err ∗
    ((D ∗ ⌜err ≠ GoInterface.nil⌝ ∗ notHandlerErr err) ∨
     ∃ (Φ : Rep.M → IProp GF) (Ψe : GoString → IProp GF), Got Φ Ψe ∗
       (⌜err = GoInterface.nil⌝ -∗ ∃ (l : Loc) (m' : Rep.M),
          ⌜resp = interface.mkOk (go.GoType.PointerType Rep.ty) #l⌝ ∗ Rep.send l m' ∗ Φ m') ∗
       handlerErrOut Ψe err))

def grpcMethodOkMd {Req Rep : ProtoMsg GF} (mh : val) (srv : GoInterface) (ics : List GoFunc)
    (S : IProp GF) (Spec : GrpcSpecMd Req Rep) : IProp GF :=
  iprop(∀ (D : IProp GF) (Got : …) (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
      (dec ui : GoFunc),
    {{ S ∗ context.isContext ci cd ∗ grpcRunCtx ci ∗ D ∗ grpcDecDepOk dec Spec ci D Got ∗
        grpcSrvChainAll ics ui }}
      (methodHandlerCall mh #srv #(GoInterface.ok ci) dec ui)
    {{ (resp err : GoInterface), RET (PairV #resp #err); S ∗ grpcRunOut D Got resp err }})

def grpcRunOkMd {Req Rep : ProtoMsg GF} (mh : val) (srv : GoInterface) (ics : List GoFunc)
    (Spec : GrpcSpecMd Req Rep) : IProp GF :=
  iprop(∀ (D : IProp GF) (Got : …) (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
      (dec ui : GoFunc),
    {{ threadTok ∗ £ 1 ∗ context.isContext ci cd ∗ grpcRunCtx ci ∗ D ∗
        grpcDecDepOk dec Spec ci D Got ∗ grpcSrvChainAll ics ui }}
      (methodHandlerCall mh #srv #(GoInterface.ok ci) dec ui)
    {{ (resp err : GoInterface), RET (PairV #resp #err); threadTok ∗ grpcRunOut D Got resp err }})

-- Today's text, renamed (the deposit at a fixed `m` in the precondition), for Go's single-process
-- table only, until W4: grpcRunPreOkMd. A law: grpcRunPreOkMd_of_run (the new contract implies it,
-- at D := grpcSpecAt Spec ci m Φ Ψe and Got Φ' Ψe' := ⌜Φ' = Φ ∧ Ψe' = Ψe⌝).
```

`grpcGoEntry`'s spec is stated over `grpcRunPreOkMd` (S2 §1.4: a spec chosen after `dec` returns has no
contract to run against, so Go's table cannot be served under the dec-shaped contract). `grpc.serve`
keeps its premise in the new shape and converts. The migration table of S2 §1.5 stands (15 generated
handler specs, `UnaryHandlerLemmas.lean`'s four lemmas, about 20 adapters at three lines each).

### 1.3 The interim axioms after the switch

| axiom | change | why sound (the review re-runs these) |
|---|---|---|
| `grpc.Server.Serve.wp_proof` | text unchanged; `grpcServeTok` one form, `grpcServes` per kind (SW1), unary clause `run ∨ Pre` (SW2) | `s2-interface.md`'s argument with streams added (S3 §2.7): opaque protocols, so no raw writer (C1, C2, C2'); one dispatch per call (transparent retry only of an unprocessed first attempt, no retry policy); the dispatched metadata is an attempt's and both ends agree on it (`streamMdIs`); messages in order, intact, once; a server `SendMsg` after the status may return `nil` undelivered (R3); C3 and its mirror blocked by the kind clauses; a head naming no entry is written only by `Invoke`/`NewStream`, which take an entry |
| `grpc.ClientConn.NewStream.wp_proof` | R1, R2 fixed; `isGrpcStreamsMd` heap-free; `Md` an `IProp` | as `Serve`'s; R1 and R2 make it true of grpc-go v1.84 and the model (§2) |
| `grpc.ClientConn.Invoke.wp_proof` | text unchanged; meaning through D4 (no `grpcReach`) and D6 (`grpcAttemptMdI`) | `s2-interface.md` |
| `grpc.NewClient.wp_proof` | `credKeysOk` premise; `connCredsOk` over `credsYieldI` | D6 |
| `bridge.New.wp_proof` | takes both addresses' tables at one `Svc` | the relay carries bytes, and both addresses run grpc's protocols for the same table; `bridge-addrleft.md`'s routes both need `a`'s set token, spent on the target's table |
| deleted | `grpc.start`, `grpcAddrIsRaw`, `grpcSrvCfgRaw`, `grpcSrvLink`, `grpcAddrIs_agree`, `grpcSrvCfg_agree` | nothing reads a server name |

A review file `notes/axiom-review/phase7-switch.md` (the `axiom` skill, on SW1 and SW2 together)
is part of the switch.

### 1.4 The end state, after the proofs (S3.1-S3.3; not elaborated)

The call library (`InvGrpcCall.lean`, S3.1). `Md` is an `IProp` family (D6), which changes S3's text in
three places (`callInv`, `callDeposit`, `unaryParams`).

```lean
structure CallParams (GF : BundledGFunctors) [GooseExts] where
  Wq : ProtoWire
  Wp : ProtoWire
  Md : GrpcMd → IProp GF                       -- persistent family: the attempts' metadata
  up : Nat → Wq.M → IProp GF
  dn : GrpcMd → Nat → Wp.M → IProp GF
  fin : GrpcMd → Option GoString → IProp GF

def unaryParams (e : GrpcEntry GF) (Md : GrpcMd → IProp GF) (Φ : e.Wp.M → IProp GF)
    (Ψe : GoString → IProp GF) : CallParams GF where
  Wq := e.Wq; Wp := e.Wp; Md := Md
  up := fun i m => if i = 0 then iprop(▷ ∀ md, Md md -∗ |==> e.spec md m Φ Ψe) else iprop(False)
  dn := fun _ j m' => if j = 0 then Φ m' else iprop(True)
  fin := fun _ o => match o with | some d => iprop(⌜d ∈ handlerDescs⌝ -∗ Ψe d) | none => iprop(True)

def streamParams (e : GrpcStreamEntry GF) (γ : StreamNames) (Md : GrpcMd → IProp GF) : CallParams GF where
  Wq := e.Wq; Wp := e.Wp; Md := Md; up := e.up; dn := fun md => e.dn md γ; fin := fun _ _ => iprop(True)

def callAdmits (ent : GrpcSvcEntry GF) (γ : StreamNames) (P : CallParams GF) : Prop :=
  match ent with
  | .unary e => ∃ Φ Ψe, P = unaryParams e P.Md Φ Ψe
  | .stream e => P = streamParams e γ P.Md

/-- The call's invariant (persistent; allocated by the client when it opens the call): the up queue
`U` and the server's received prefix; each request not yet received holds `P.up i m`; the up end; the
dispatched metadata (unset, or `streamMdIs γ md` with `P.Md md`); the down queue and the client's
received prefix, each response not yet received holding `P.dn md j m`; the server's end
`callEndIs γ n o` with `P.fin md o` until the client takes it (a response pushed after the end stays
unreceived: R3). -/
def callInv (γ : StreamNames) (P : CallParams GF) : IProp GF := inv (callN γ) (…)
-- Laws (proved): call_push_up, call_take_up, call_close_up, call_dispatch, call_push_dn, call_take_dn,
-- call_end, call_take_fin, streamMdIs_agree.

/-- What the server claims when it dispatches (exclusive). -/
def callDeposit (ent : GrpcSvcEntry GF) (fs : List (GoString × GoString)) (γ : StreamNames)
    (P : CallParams GF) : IProp GF :=
  iprop(srvRecvTok γ [] ∗ srvSendTok γ [] ∗ streamAuxTok γ ∗ callMdTok γ ∗ callEndTok γ ∗
    callInv γ P ∗ ⌜callAdmits ent γ P⌝ ∗ (□ ∀ md, ⌜grpcFieldsMd fs md⌝ -∗ P.Md md) ∗ callFacts ent γ P)
-- callFacts (.stream e) γ P := □ ∀ md, P.Md md -∗ e.spec md γ (e.dn md γ);  callFacts (.unary _) := True

/-- The client's head `fs` on `cn` opens the call `γ` of the entry `ent` (persistent). The slot is
keyed by the head and the call's names, so both ends agree on `γ`; `P` reaches the server only inside
the claimed deposit. -/
def callHeadIs (Svc : GrpcSvc GF) (cn : Nat) (fs : List (GoString × GoString)) (γ : StreamNames)
    (ent : GrpcSvcEntry GF) : IProp GF :=
  iprop(∃ (name : GoString) (σ : SlotNames) (P : CallParams GF),
    ⌜pathOf fs = some name ∧ Svc name = some ent⌝ ∗ depSlotOf cn σ ((fs, γ) : K) ∗
    depSlotInv cn σ (headReady fs) (callDeposit ent fs γ P) (fun _ : Unit => iprop(True)))

def grpcCliP (Svc : GrpcSvc GF) : Proto GF := fun cn W =>
  iprop(⌜W <+: clientPrefaceBytes⌝ ∨
    ∃ fs γ ent rest, ⌜W = clientPrefaceBytes ++ headFrame fs ++ rest ∧ headOk fs⌝ ∗
      callHeadIs Svc cn fs γ ent ∗ cliFramesOk γ (entWq ent) rest)
-- grpcSrvP: the preface, then frames whose facts are stated at their position j (S3 §2.4):
-- a data frame is downAt γ j m of an encoding; a trailer is callEndIs γ j o; a refusal is connRefused.
```

These replace the per-data-frame library on `lean` (`InvGrpcWire.lean`: `GrpcOut`, `GrpcKey`,
`msgReady`, `grpcDeposit`, `grpcSlotCont`, `grpcAttemptSlot`, `cliRest`, `streamConn`, `srvFrameOk`,
`cli_read_slot`, `srv_data_answered`, `srv_trailer_answered`), which no linked result uses. The slot
library (`GooseLang/Ext/Net/Slot.lean`: `depSlot_register`, `_claim`, `_withdraw`, `_takeRefused`,
`conn_refuse`) is used as it is; `StreamNames` needs a `Countable` instance for the key.

**Bridges against per-connection slots (the review of SW1, finding 3; a justification gap, no
exploit today).** `bridge.New`'s relay sits between two connections `cn0` (client to bridge) and `cn1`
(bridge to target). A deposit registered on `cn0` is claimed on the target's side of `cn1`; a
`REFUSED_STREAM` the target writes on `cn1` must become `connRefused cn0` for the client's
`_takeRefused`, but the deposit was claimed with `cn1`'s freshness (`connFresh cn1`), which the relay
spent. S3.1 must key the slot and its refusal by the call `γ` (not by the connection), or add a relay
law to `Slot.lean` (`depSlot_relay`), before the bridge's axiom is read against the defined protocols.

Over the model, `processRPC` is proved once against `callRunOk h srv sics P γ md`, with two lemmas:
`wrapUnary_callRunOk` (from the dec-shaped `grpcRunOkMd`, at `D := srvRecvTok γ []` and
`Got Φ Ψe := ⌜Φ = Φ₀ ∧ Ψe = Ψe₀⌝` for the call's `unaryParams e Md Φ₀ Ψe₀`) and
`streamRun_callRunOk` (from `grpcStreamRunOk` and `grpcServes`' conversions). `NewStream` becomes
interceptor-generic over grpc's streamer (`grpcStreamerOk`, as SpecPlan's `streamerOk`), and the form
above becomes the theorem `etcdNewStream` in `client/v3`, once etcd's `retry_interceptor.go` stream path
is translated with its body (S3.4). Then `grpcAddrAt` points at `grpcCliP`/`grpcSrvP` and the opaques
are deleted (W5).

### 1.5 Where the notes disagreed, and what this plan takes

1. **S2's per-data-frame slot against S3's call protocol: S3's.** The model has one code path (`invoke`
   is `newClientStream`, `SendMsg`, `CloseSend`, two `RecvMsg`; `register` wraps unary methods as stream
   handlers), the handler starts on the head, and a stream needs per-message contents that survive a
   transparent retry, which bytes on one connection cannot carry. S2's slot would prove the transport
   twice (S3's estimate: 8-10 sessions more). I checked S3's design for a flaw and found one gap, not a
   reason to reject it: S3's unary `dec` contract (§3 of `plan-s3.md`) has no right `D`, so its triple,
   being persistent, would let a handler call `dec` twice for two deposits. S2's `grpcDecDepOk` has the
   `D`, and the instance is `D := srvRecvTok γ []`. This plan takes S2's text for the contract and S3's
   protocol for the wire.
2. **`grpcRunPreOkMd`: kept as S2 proposes**, interim, for Go's single-process unary table, deleted at
   W4 (before the protocols become definitions, where the `Pre` arm is C1-unsound).
3. **`grpcServeTok`'s one form: S3's, not S2's D7.** D7 allocated a server name `γ` and a start token at
   `grpc_addr_set` to make `grpc.start` a theorem, because S2 kept the stream half on `γ`. Once streams
   are table entries (SW1), nothing reads a server name: `grpc.start` and its five companions are deleted,
   not proved, and O10 (a stream head at a server with no `γ`) disappears with them.
4. **S3.0 and W0: merged where they touch the same statements.** D6 goes into SW1, because `NewStream`'s
   post names the attempt's metadata; D7 is superseded by SW1; D1 stays a separate branch (SW2): its sites
   (the 15 generated handlers, `UnaryHandlerLemmas`, the adapters) are disjoint from SW1's but for the
   unary clause of `grpcServes`, and its rebuild of `InvGrpcBase`'s 7700 importers would hold back S3.
5. **Bridges: S2's D4, corrected; S3's `bridgeReach` rejected.** S3's opaque `bridgeReach a a₀` keeps
   registration-level forwarding but gives `Invoke`'s model proof no protocol at the dialed address, so it
   would be redone at W5. D4 gives the bridge's address the target's table. Correction: S2 claimed
   `isGrpcRpcMd_forwards` follows "by `grpcSvcAt`'s agreement on `b` (from `addr_proto_agree`)". There is
   no such law in `GooseLang/Ext/Net`, and with opaque protocols `grpcCliPI Svc = grpcCliPI Svc'` gives
   nothing about `Svc`. So `forwards` is replaced, not re-proved: a bridge's start sets `a`'s table to the
   member's table term, and the registrations at `a` are read off it (`grpc.serve` at `a`, through
   `grpcServerAt a …`), as at the member's address. `cluster3`'s bundles carry the table term
   (`cluster3/Defs.lean` `forwards`, `isGrpcRpcMd_forwards`, `isGrpcStream_forwards`; `k8s/etcd3/
   StartLemmas.lean`'s `watchRegAt_forwards`; `partition/MainWatch.lean`).
6. **The name `GrpcMethod`** (S3 §2.2) is taken by the start's list element; the entry type is
   `GrpcSvcEntry`.
7. **`grpcStreamRunOk`'s first conjunct**: S3 restates it; this plan drops it (said twice otherwise).
8. **`StreamMsg` gains `tree`** (S3 left the choice open: `tree` into `StreamMsg`, or the predicates
   over `StreamMsgT`): the former, as S2's O3 did for `ProtoMsg`; four stream models change.
9. **D6's size.** S2 counted 5 files for `grpcAttemptMd`'s users. Its etcd form `clientAttemptMd`
   (`InvKVConn.lean:1566`) is used in 21 files, which change from `⌜clientAttemptMd …⌝` to the `IProp`.
   Mechanical, but SW1 is larger than S2's estimate for D6.
10. **What is already on `lean`.** S3 read the per-data-frame library as `phase7-s2-core`'s; it is on
   `lean` (`InvGrpcWire.lean:432-757`), unlinked. S3.1 replaces it there.
11. **The inventory's "S2c and S2d before S3"** (coupling order) is reversed for S3's interim: SW1
   (S3.0) needs no S2 proof. The proofs still share one core (S3.2), which is S2's remaining core done
   once.
12. **The S2 review's F2 ("S2 cannot retire D7's wire half")** stands; S2 §2's sealing is how it is
   enforced (decision A).

13. **SW1 as built (2026-11-24, branch `phase7-switch`), where the text of §1.2 had to change.**
   - **`streamMdIs` became `streamDispIs γ a md`** (the review of SW1, finding 2): a transparent retry
     before the stream is committed re-picks the transport (`getTransportConn`, the model's
     `modelChooseAddr`, `model_clientconn.go:322`), so the address, like the metadata, is learned with
     the responses. `NewStream` takes one client content `Up` for every address (the registration at
     `fun _ => Up`), its post is `□ ∀ a md, ⌜a ∈ addrs⌝ -∗ clientAttemptMdI conn om md -∗ Spec a md γ
     (Dn a md)`, and `cliStreamIs`' family `Md a md` and content `Dn a md` are indexed by the dispatch.
     `cliStreamIs`' `io.EOF` arm keeps `downClosed γ L` (finding 5, §2).
   - **No-refusal bound to the server (the review's finding 1, unsound on `lean` before SW1).**
     `noRefusalAt addr` is a fact about the address string, and `etcd_noRefusal` gave back
     `grpcSrvNew gs … ∗ netListenerAt lis addr` separately: a program could serve another server on
     `lis` under the certificate. Interim fix: the axioms (`etcd_noRefusal`, `etcd_noOtherRefusal`)
     return `grpcSrvAtLis gs lis addr …` (a new axiomatized exclusive predicate), which only
     `grpc.startBound` takes and `grpcServeTok` holds as its other form of the server at the listener.
     The end state is decision E's table form (no-refusal a property of the unary entries, checked by
     `grpcServes`, read by `grpcInvokerOk` from `grpcSvcAt`), which retires `grpcSrvAtLis`.
   - **`http.register` consumes `netAddrLeft a`** (the review's finding 4): an address served over HTTP
     never gets a grpc table.
   - **`credsYieldRaw`** carries `hG` (`include hG`), which its definition over `grpcConn` will need;
     **`ProtoMsg.cnt` is not a global instance** (the review's finding 6).
   - **`streamMdIs` stores a finite code of the metadata.** A ghost variable (`dghostVar`) holds a
     countable value, and `GrpcMd` (a function of the key) is not countable. `InvGrpcCall.lean`
     stores `c : GrpcMdCode := Option (List (GoString × List GoString))` and states
     `streamMdIs γ md := ∃ c, ⌜c.md = md⌝ ∗ dghostVar γ.md DFrac.discard (some c)`; `streamMdIs_agree`
     keeps its statement. A dispatched metadata is always such a code's (the server makes it from the
     head's finitely many fields). The ghost variable holds `Option GrpcMdCode`, so that `call_dispatch`
     (S3.1) can set it from `none`.
   - **`ProtoMsg.cnt` needs a `Pos.Countable` instance for every unary message model.** None existed;
     SW1 adds them where the `ProtoMsg` instances are (`client/v3/InvKVConn.lean`, `InvLease.lean`,
     `InvLeaseRead.lean`, `InvAuthConn.lean`, named `*.msgCountable`, since leaf files have their own
     instances of `HdrM` and `EtcdKv`), the nested `OpRespM` and `TxnOp` through Perennial's `GenTree`.
   - **`StreamMsg.tree`**: the four stream models' trees move from `PerTypeWatch.lean` and
     `PerTypeLeaseKeepAlive.lean` into `InvWatchStream.lean` and `LeaseKeepAliveMsg.lean`; the
     `StreamMsgT`s are `{ … with }`.
   - **The laws** of commit (2) are `grpcStreamSvcAt_of_addr` and `grpcStreamSvcAt_mono` (over the
     entry's components, not an `e`); `isGrpcStreamMd_of_addr` and `isGrpcStreamMd_mono` come with (3).
   - **`grpcServes`** is `□ ∀ name ent, ⌜Svc name = some ent⌝ -∗ grpcServesEnt … name ent`, the
     per-kind clause a separate definition by `match` (the text of §1.2, unchanged in content).
   - **`grpcGoSvc` returns `.unary` entries** (it is a `GrpcSvc`), so `grpcStartSvc`'s first arm is
     `some e => some e`.
   - **`grpcServerAt` and `grpc.serve` move to `InvGrpcRun.lean`**: they name `GrpcStreamMethod`
     (`InvGrpcStream.lean`), which imports `InvGrpc.lean`. A user of `grpc.serve` imports `InvGrpcRun`.
   - **`grpcStreamMethodOk` keeps its first conjunct** (`□ ∀ md, streamSpecOk (Spec md)`); only the run
     contract `grpcStreamRunOk` drops it (`grpcStreamRunOk_of_pools` discards it). The handlers' proofs
     are unchanged; the start's callers give the content family `dn` explicitly.
   - **`credKeysOk cm`** is `∀ k vs, mdGet cm k = some vs → k.head? ≠ some ':'`, a conjunct of
     `perRPCCredsOk`'s success post (`∃ cm, credsMapIs mp cm ∗ ⌜credKeysOk cm⌝ ∗ □ Q cm`).
   - **`grpc.start'`** takes `netListenerAt` (as before) and drops its `addrClaim`; the token holds
     `netListenerOpen`.
   - Between commits (2) and (6), `grpcServes` refuses stream entries (a `False` clause), so the
     interim `Serve` axiom says nothing new about them before their clause exists.

## 2. The two `NewStream` defects

Both are overclaims of a trust-boundary axiom: false of grpc-go v1.84 and of the model, which keeps
`stream.go` verbatim. SpecPlan's grpc API has both. Ledger entries (decision pending) are in
`notes/specs-only/ledger.md`, 2026-11-24.

**R1: a clean end with no handler run** (a defect of SpecPlan's text only; the review of SW1, finding
5: `cliStreamIs`' third arm, `cliStreamErr err`, admits `io.EOF`, a client error, so the Lean text never
claimed `downClosed` of a bare `io.EOF`; SW1 leaves its `io.EOF` arm as it was). A stream's first attempt refused (`REFUSED_STREAM`) is retried
transparently; if the replay's write fails, `retryLocked` returns the bare `io.EOF`
(`stream.go`, `retryLocked`/`shouldRetry`; `nonissues/grpc-transparent-retry-spurious-eof.md`,
grpc/grpc-go#9443, #9447). The client's next `RecvMsg` returns `io.EOF` before any message, with no
handler run. Today's `cliStreamIs` (`InvGrpcStream.lean:638-639`) and `cliBidiStreamIs` (`:679-680`)
give `downClosed γ L` at `io.EOF`, which says the handler returned after `L`; SpecPlan's `cliRecv_recv`
(`SpecPlan/Spec/google_golang_org/grpc/Api.lean:691-699`) gives `S.fin g md n none`. **Fix (SpecPlan):** `S.fin g md n none ∨ ⌜n = 0⌝`. No
user is affected: `serveWatchClient` and `recvKeepAliveLoop` already drop `downClosed`.

**R2: the stream's metadata is the dispatched attempt's.** A transparent retry recomputes the head
(`createHeaderFields` again, the per-RPC credentials called again: `model_transport.go:239-245`, from
`stream.go:482-505`), and etcd's token can be refreshed in between. Today's post fixes one `md` with
`clientAttemptMd conn om md` when `NewStream` returns and gives `Spec a md γ Dn`
(`ClientConn__NewStream.lean`, "once for the stream's life (grpc sends the headers once)"), while the
handler may run at another attempt's `md'` with the same `Dn`; for the watch's token-indexed spec that
equates `watchDn tok` and `watchDn tok'`. SpecPlan's `streamerOk_call` (`Api.lean:657-667`) fixes `md`
the same way. **Fix:** §1.2's post (the spec at every attempt metadata, at `Dn md`), with
`streamMdIs γ md` returned by every received message, so the client learns the dispatched `md` with the
first response and agrees on it after (`streamMdIs_agree`). SpecPlan: `cliSend`/`cliRecv` lose the `md`
index, and `cliRecv_recv`'s message arm gives `mdIs g md ∗ ⌜mdSeen (mdc ++ md0) md⌝` beside
`S.dn g md n c`. The one real user change is the watch client (decision C).

## 3. Decisions

Each was "for the user" in a design note. The rules applied: function contracts at the trust boundary
are per-function axioms (`Proof/<pkg>/<fn>.lean`, deployment restrictions as their preconditions), not
Iris premises of top-level theorems; a pure premise of a top-level theorem is eliminated into the Go
program where it can be; one collection of library models and specs serves etcd and dsverify.

**A. F2: sealing, and the model's claim narrowed.** Decided (overnight, revisit in the morning): seal
grpc's address vocabulary (`etc/api/grpc.txt` listing grpc's API modules; `grpcAddrAt`, `grpcSvcAt`,
`grpcStreamSvcAt`, `isGrpcRpcMd`, `isGrpcStreamMd`, `grpcCliP`, `grpcSrvP` and the call protocol
`@[no_expose]`; exported laws: `grpc_addr_set`, `grpcSvcAt_of_addr`, `grpcSvcAt_mono_upd`,
`isGrpcRpcMd_*`, `isGrpcStreamMd_*`, and `grpc_listen_au : grpcAddrAt a Svc ⊢ |={⊤,∅}=> netLisTok NG a ∗
(netLisTok NG a ={∅,⊤}=∗ True)` for the member's own `net.Listen`), and add to `models/README.md`'s grpc
section: "The model behaves as grpc-go does, as the program observes it, for programs whose code other
than grpc's transport and the trusted byte relays (`bridge.New`) neither dials, listens at, nor accepts
or reads a connection to an address a grpc server of the program serves." Why: once the protocols are
defined, raw code could write the model's frames with a proof and then talk model frames to real HTTP/2
(the review's C2). Sealing adds no Lean premise and no axiom, and every program here meets the claim
(etcd's clients go through `clientv3`, its member hands its listener to `gs.Serve`, the bridges relay
bytes without parsing them). Alternatives: (a) a premise over the program's syntax in each top-level
theorem (rejected: addresses are runtime strings, and the property is about which code calls `Dial`);
(b) opaque protocols forever (then `Invoke`/`Serve` stay axioms: an opaque has no equation for the proof
to use, and an equation axiom republishes it); (c) a non-duplicable grpc-only capability (not achievable:
`Invoke` must dial, so the client's fact holds an `addrProto`). Trusted (a claim change). The sealing
can land early (a refactor that changes no statement); the claim lands with W5.

**B. O7, the codec: per-function axioms now, the verified codec later.** Decided (overnight, revisit in
the morning): two trust-boundary specs of grpc's default codec, `encoding/proto`'s `codecV2.Marshal` and
`Unmarshal` as the model calls them, over the opaque `protoEncodes` (each an axiom in its own
`Proof/google_golang_org/grpc/encoding/proto/<fn>.lean`):

```lean
-- not elaborated: the model's codec signatures (mem.BufferSlice), the registered-model premise
Marshal:   {{ T.send l m }} codec.Marshal(l) {{ bs, RET …; T.send l m ∗ data ↦* bs ∗
             ⌜protoEncodes T.ty (T.tree m) bs⌝ }}
Unmarshal: {{ data ↦*{q} bs ∗ T.blank l ∗ ⌜protoEncodes T.ty t bs⌝ }} codec.Unmarshal(data, l)
           {{ RET nil; data ↦*{q} bs ∗ ∃ m, ⌜T.tree m = t⌝ ∗ T.recv l m ∗ T.recvOwn l m }}
```

and `ProtoMsgT.ReqSat`/`RepSat` (`InvGrpcBase.lean:987-1001`) restated without the sender's `T.send`
(it is on the other machine). Phase 5's `models_lab.pbcodec` later proves the same two statements.
Why: per-function axioms are the rule; installing `PbCodec` as grpc's default codec first would put
phase 5 on S3.2's critical path. Alternative: `PbCodec` first (no axiom, later start). Risk recorded in
§6: `Unmarshal` claims decoding is a function of the bytes into normalized trees. Trusted.

**C. The `NewStream` metadata fix (R2): the watch learns its token from its first response.**
Decided (overnight, revisit in the morning): §1.2's `md`-indexed post, and the watch client's epoch token
`tok = auth.mdTokenOf md` taken from `streamMdIs γ md` at the first response (`watchGRPCStream__run.lean`
`:152, 740, 2682`; `WatchRun.lean:543`; `serveWatchClient`; `WatchEpoch`), its later responses agreeing
by `streamMdIs_agree`. S3 estimated 300-600 lines touched. Why: with per-RPC credentials (etcd with auth
on) the metadata is not known when `NewStream` returns, and a fixed `md` is false. Alternatives: a
premise of no per-RPC credentials (false of the auth workloads); a derived lemma recovering today's form
for credential-free connections (needs `createHeaderFields`' post as a function of the head; extra work,
not needed by any user). Trusted (the axiom's text).

**D. `grpcRepliesFit`.** Decided (overnight, revisit in the morning): it stays a named premise
(visible today in the single-process statements as `Hrf`) until S3.2. There, `Serve`'s proof needs only
"each reply the handler returns encodes below `grpcReplyMax`", so the obligation moves from the opaque
`Prop` carried by `grpcServeTok` into the unary run contract's reply arm (beside `Φ m'`, a bound on the
reply's encoded size below `grpcReplyMax`; not elaborated: `wireLen`'s default for replies is no bound) and
the stream's `SendMsg`. etcd's handlers then take it as a deployment restriction, a
precondition of v3rpc's handler specs, false of etcd under nested keys-only transactions
(`issues/etcd-txn-keysonly-reply-alloc-panic.md`); eliminating it into the program (the workloads'
bounds in `Deployment.WellFormed` bounding the store) is a later item of the etcd lead. Why: the rule
puts deployment restrictions in per-function preconditions; an opaque nobody can discharge says less.
Alternative: keep the opaque, a premise of every top-level theorem forever. Trusted (premise placement).

**E. `etcd_noRefusal`'s voter assumption.** Decided (overnight, revisit in the morning): split the
axiom when it is retired (`server-no-refusal`, Wave 3): the refusal part proved from the server's errors
by identity (`notes/read-retry-plan.md` R1), and the voter fact a precondition `memberVoter` of the
per-function spec that needs it, discharged in the distributed `etcd_safe` from the program: the members
boot as voters (`BootFacts`) and no workload issues a membership change. Why: the axiom's docstring says
the voter fact rests on it, and `ccLogOk` does not exclude a re-add as a learner. Alternative: a premise
"no conf change makes a member a learner" on the top-level statement (rejected by the rule: it is
provable from the programs). Trusted until proved.

**F. One call protocol (S3's decision 0.1, for S2's owner on #24).** Decided (overnight, revisit in the
morning): adopted (§1.5, item 1). dsverify-net owns both S2 and S3, so no second session's work is
discarded; the S2 core branch's §0a library is replaced by S3.1.

**G. Environment-dependent initializers** (`go_etcd_io.etcd.client.v3.initFuncsOk`: `ETCD_CLIENT_DEBUG`;
`net.http.initFuncsOk`: `GODEBUG=httpmuxgo121`). Decided (overnight, revisit in the morning): each is
proved over its body under an environment clause of the machine's start state (`ClientStart`/
`ServerStart` in the distributed statement, beside the existing `verifyEnvOff`), not a separate premise.
Why: an initializer runs before `main`, so the program cannot clear the variable; the start state is
where `etcd_robust.spec` already states the environment. Trusted (a top-level premise's content).

**H. The stats-handler model's narrowed claim** (one `ConnBegin`/`ConnEnd` pair per stream; pending
since 2026-11-22). Decided (overnight, revisit in the morning): keep it as landed; it constrains only
programs whose behavior depends on how many connections carry their calls, and otelgrpc's connection
hooks do nothing.

**I. S5's vocabulary (S5 draft's Q1) and net/rpc over HTTP (Q4).** Decided (overnight, revisit in the
morning): SpecPlan's vocabulary for S5 (the convergence rule), with `Boundary.lean`'s opaques defined
over it; `conn.serve`'s proof also gives net/rpc's `RpcHttpServe` instance, so dsverify's kits and etcd
share one net/http server proof.

**J. The distributed `etcd_safe`'s `TrustBoundary` and putget's `S2Draft` hypothesis.** Decided
(overnight, revisit in the morning): both go; their contents become the per-function axioms of SW1/SW2
(`Serve`, `Invoke`, `NewStream`, `bridge.New`) and the proved start laws (`grpc_addr_set` from the
deployment's `addrUnset`). etcd-dist's interim `Serve_dist` and `etcdAddr_set` (on
`dist-putget-interim/2026-11-24`) are derived from them: `grpcServes (etcdSvc γE mid)` from the handlers'
run contracts, through `Serve`'s axiom. Why: function contracts are per-function axioms, not Iris
premises of top-level theorems.

## 4. The work plan

Owners: **dsverify-net** (the net extension, the models, S2 and S3), **zeldovich-proving-2** (S5, JSON,
leaves), **etcd lead** (coordinator-E's etcd-dist session: S4, the top-level statements, the start),
**dsverify-lab** (kaashoek: the kits), **zeldovich-coordinator** (pin bumps, the land queue). A session
may run several branches through agents in their own worktrees. Estimates are sessions (an agent's
working day), excluding build-queue time.

**Serialization** (from the inventory):
- **The grpc translation queue.** Every branch that edits `Code/google_golang_org/grpc*.toml`, the
  regenerated `Code/`/`GeneratedProof/` of grpc, or `models/grpc` lands in this order, each rebased and
  regenerated after the previous one, never hand-merged: `phase7-inits`, `phase7-s2-core-merge`,
  `phase7-s2a`, `status-bodies`, `grpclog-bodies`, `grpc-health`, then S3.2's translations.
- **`InvGrpcServer.lean`** is split (`InvGrpcHealth`, `InvGrpcProm`, `InvGrpcStats`) as the first commit
  of `phase7-s2a`, before health, prom-mw and otel edit it.
- **grpc's core statements** (`InvGrpcBase`, `InvGrpcWire`, `InvGrpcRun`, `InvGrpcStream`, `InvGrpc`):
  SW1, then SW2, then S3.1; one at a time.
- **`Net/Proof/net/http`, `Net/Proof/net/rpc`**: `net-rpc-rerr` lands before S5's `conn.serve` batch;
  dsverify-lab does not edit them during S5's batches.
- **`Proof/runtime/Start.lean` and the top-level statements**: the etcd lead only.
- A rebuild of `InvGrpcBase`'s importers is about 7700 modules (`phase7-s2-core`'s build was killed for
  low memory): SW1 and SW2 build on the VM (`vm-build:`).

### Wave 0: now, in parallel

| branch | owner | scope | prereq | files (for serialization) | est. | trusted |
|---|---|---|---|---|---|---|
| `phase7-switch` (SW1) | dsverify-net | §1.2 except the run contract: the table kinds, `StreamNames.md`, `streamMdIs`, `grpcStreamSvcAt`, `isGrpcStreamMd`/`isGrpcRpcMd` heap-free without `grpcReach`, `credsYieldI`/`grpcAttemptMdI`/`clientAttemptMdI`, `credKeysOk`, `cliStreamIs` (R1, R2), `NewStream`, `grpcServes` per kind, `grpcServeTok` one form, `grpc.start'` with `sms`, `grpcServerAt` without `γ`, `bridge.New` (D4), `ProtoWire.cnt`, `StreamMsg.tree`; the six axioms deleted; users (watch client, lease client, `GenericClientStream` proofs, `streamSpecOk_watchSpec`, the start chain: `etcd_watch_served`, `client.etcd_kv_started`, `etcdstart`, `cluster3`, `watch/Served`, `auth/MainServe`, `cache/v3/Results`, the 21 `clientAttemptMd` files); `notes/axiom-review/phase7-switch.md`; tcb baseline and collections | none | grpc's core statements; `Spec/.../grpc/{ClientConn__NewStream,NewClient}.lean`; bridge `New.lean`; client/v3 watch and lease; v3rpc `InvWatch`, `Results`; `etcdstart`; `cluster3`; `k8s/etcd3/StartLemmas`; `partition/MainWatch` | 3-5 | yes |
| `phase7-switch-dec` (SW2) | dsverify-net (second agent) | D1: §1.2's SW2 block; `grpcRunPreOkMd` and `grpcRunPreOkMd_of_run`; `grpcGoEntry` over it; S2 §1.5's sites | developed beside SW1, lands after it | `InvGrpcBase`, `InvGrpc`, `InvGrpcRun` (one clause), the 15 `_*_Handler` specs, `UnaryHandlerLemmas`, the adapters in `client/v3`, `v3rpc`, `AuthnServedOn`, `LeaseReadServed`, `LeaseGrantServed` | 1.5-2 | yes (`Serve`'s clause) |
| `phase7-inits` | zeldovich-proving-2 (dsverify-net reviews the model edit) | `grpc/internal`'s hooks, `grpclog.Component` and the three `logger`s, otel's `NewEncoderID`, `grpc_health_v1`'s no-op `init` (`TrustedCode`, etcdserverpb's precedent), the model's unmodelled hook stores dropped, the unused trusted `Server.Serve.impl` deleted: **−9 axioms** | none | grpc queue (first) | 1-1.5 | yes (model edit, `TrustedCode`) |
| `pin-bump` | zeldovich-coordinator | Perennial pin to the tip with `strings.Cut`/`TrimLeft`/`IndexByte`/`LastIndex` and the real `fmt` (the inventory's `ed1955557`; check what the pin already has) | none | `lake-manifest.json`, the generated tables | 0.5 | no |
| Perennial `context-withvalue`, `io-writestring`, `strings-tolower-index-count` | zeldovich-proving-2 proposes; Perennial's workflow | general changes, each on its own (`notes/perennial-changes.md`) | none | Perennial | 1-2 | no |
| `status-bodies` | zeldovich-proving-2 | the status slice (`status`, `internal/status`, genproto's `Status` via pbgen): `status.Error`/`FromError`/`Code`/`Errorf`/`Status.Code`, `statusAtRaw`, then `errors.IsStatusErr`, `toGRPCErrorMap_init`: **−7** | pbgen | grpc queue | 1.5-2 | no |
| `mvccfull-noaddr` | etcd lead | a start corollary for programs with no addresses (`goose_adequacy_start` at `As = []`), dropping `addrClaim`, `addrUnclaimed`, `httpProtoFree` from mvccfull and mvccrand | none | `Proof/runtime/Start.lean`, `examples/mvccfull/Adequacy.lean` | 0.5 | yes (a top-level statement loses premises) |
| `net-rpc-rerr` | its current owner | land as it is | none | `Net/Proof/net/rpc` | - | no |
| S5 server batches (`prove-ps2-s5srv`) | zeldovich-proving-2 | as planned (`phase7-plan.md`, S5 draft) | `net-rpc-rerr`, `WithValue` for `Serve`/`conn.serve` | `Net/Proof/net/http` | in flight | no |

**What S3's first branch is, exactly:** `phase7-switch` (SW1), off `lean`, in this commit order:
(1) `InvGrpcCall.lean` with `StreamNames` (moved, `md` added, `Countable`), `streamMdIs`,
`streamMdIs_agree`; (2) `ProtoWire.cnt`, `ProtoMsg.cnt`, `StreamMsg.tree`, `StreamMsg.wire`,
`GrpcStreamEntry`, `GrpcSvcEntry`, `GrpcSvc`, `grpcSvcAt`'s `.unary`, `grpcStreamSvcAt` with
`isGrpcStreamMd_of_addr`, `_mono`; (3) `isGrpcRpcMd`/`isGrpcStreamMd` redefined, `grpcReach` deleted;
(4) `credsYieldI`, `grpcAttemptMdI`, `connCredsOk`, `credKeysOk`, `clientAttemptMdI`; (5) `cliStreamIs`,
`cliBidiStreamIs`, `NewStream`; (6) `grpcServes`, `grpcServeTok`, `grpcStartSvc`, `grpc.start'`,
`grpcServerAt`, `GrpcStreamMethod.dn`, `grpcStreamRunOk`; the six axioms deleted; (7) `bridge.New`;
(8) the users, by group (agents in parallel: watch client; lease client; start chain and `cluster3`;
D6's files); (9) ledger entries applied, the review file, `tcb-report --check --update`, the
collections, `etc/gen-interface.py` where an API moved. The watch client's R2 change (8) is the one
non-mechanical part and the estimate's risk.

### Wave 1: after SW1

| branch | owner | scope | prereq | files | est. | trusted |
|---|---|---|---|---|---|---|
| `phase7-s3-dist-entries` (S3.5) | etcd lead | heap-free stream entries for a distributed start: the watch's `dn` without `srvTLSId s` (`v3rpc/InvWatchStream.lean:332, 349`), the server keeping its heapful `watchDn` as `Dns`; the lease keep-alive's `up` over the published view; `etcdPubStream γE` (`up₀ := ∀ ν, envAt γE ν -∗ Up ν`, `dn₀ md γ := ∃ ν, envAt γE ν ∗ Dn ν md γ`); R8: `LeaseKeepAlive`'s handler returns `srvErrOk` and its thread token while its loop still sends, and the lease stream is registered, which retires the premise `leaseKAStreamOk` | SW1; S2's `EnvPub` (etcd-dist) | `v3rpc/InvWatch*`, `InvLeaseKeepAlive`, `LeaseServer__LeaseKeepAlive`, `client/v3/InvLessor`, etcd-dist | 2-3 | no |
| `phase7-s3-calllib` (S3.1) | dsverify-net | §1.4's library: `CallParams`, `callInv` and its laws, `callDeposit`, `callHeadIs`, `grpcCliP`/`grpcSrvP` over frame sequences with the parse laws; the per-data-frame library deleted | SW1 | `InvGrpcCall`, `InvGrpcWire` | 2-3 | no |
| `phase7-seal` | dsverify-net | decision A's sealing: `etc/api/grpc.txt`, `@[no_expose]`, `grpc_listen_au`, `etc/api-check.py` clean, interfaces generated | SW1 | grpc's API modules, `etc/api/`, `interface/` | 1 | no (the claim lands with W5) |
| `phase7-s2-core-merge` (W1) | dsverify-net | S2 §5's W1: `phase7-s2-core` merged (take `lean`'s `InvGrpcWire`; hand-merge `etc/gen-init.py`, `etc/goose.py`; regenerate grpc), the `outRawIs_of_outMD` re-check, the batched `grpcInit` change, the reused proved leaves (`createHeaderFields` and the frame writers) | SW2 (to share the rebuild) | grpc queue | 1.5-2 | yes (the F1 model fix) |
| `phase7-codec` (W3) | zeldovich-proving-2 | decision B: the two codec axioms; `ReqSat`/`RepSat` without `send` (about 30 instances in `client/v3/PerType*.lean`) | SW1 | `InvGrpcBase`, `client/v3/PerType*`, new `encoding/proto` files | 1-2 | yes |
| `phase7-s3-interceptor` (S3.4) | zeldovich-proving-2 | `retry_interceptor.go`'s stream path translated with its body, proved against `grpcStreamerOk`; `etcdStreamInterceptor` defined; `etcdNewStream`; the two stubs switched; `Client.streamClientInterceptor.wp_proof` retired | SW1 | etcd's `client/v3` goose config, `InvDial` | 1-2 | no |
| `phase7-s2a` | dsverify-net | `InvGrpcServer.lean` split; `Server`/`ClientConn` translated structs (`a12d44ed4f`); `NewServer`, `RegisterService`, `grpcSrvNew` defined; `StatsHandler` under `h ≠ nil` | `phase7-inits` | grpc queue, `InvGrpcServer` | 2 | no |
| `grpclog-bodies`, `grpc-ctx-leaves` | zeldovich-proving-2 | inventory wave 1 (G-log with decision G's start clause; the metadata trio, `WithRequireLeader`, `withVersion`, `streamKeyFromCtx` with its missing premise) | `phase7-inits`; the Perennial changes and pin | grpc queue; client/v3 | 1 + 1-1.5 | G: yes |

### Wave 2

| branch | owner | scope | prereq | est. | trusted |
|---|---|---|---|---|---|
| `phase7-starttables` (W4) | zeldovich-proving-2 | the unary entries fixed at the start (`grpc.start'` takes the unary methods with their specs); `grpc.serve` read off; `grpcGoEntry`, `grpcRunPreOkMd` and the `Pre` arm deleted; the `grpcServerAt` users (S2 §5's list) | SW2 | 3-5 | yes, shrinking (`Serve`'s clause loses an arm) |
| `phase7-s3-core` (S3.2) | dsverify-net, split by function across agents: (a) the client transport stream and its reader; (b) `clientStream` (`withRetry`, the replay buffer, commit, `SendMsg`/`RecvMsg`/`CloseSend`, `csAttempt.*`); (c) the server transport (`HandleStreams`, `operateHeaders`, refusal, `WriteStatus`, `Write`); (d) `Serve` → `handleRawConn` → `serveStreams` → `handleStream` → `processRPC` with `callRunOk`, `wrapUnary_callRunOk`; (e) `invoke` = `Invoke` | S3.1, W1, W3; decision D's run-contract arm | 12-16 | no (proofs; the trusted text shrinks) |
| `grpc-health`, `grpc-prom-mw`, `prove-ps2-s5cli` | zeldovich-proving-2 | inventory wave 2 | `phase7-s2a`, `status-bodies`, prometheus vec constructors; `io.WriteString` and `net/url` for S5's client | 1 + 1.5-2 + 4-6 | no |

### Wave 3

| branch | owner | scope | prereq | est. | trusted |
|---|---|---|---|---|---|
| `phase7-s3-tops` (S3.3) | dsverify-net | `newClientStream`'s watcher goroutine, `cs.Context()` (needs `context.WithValue`), `NewStream` over the streamer, `processRPC`'s stream branch with the stream chain, `streamRun_callRunOk`; the prometheus `StreamServerInterceptor` fixed (latent-false, `notes/audit.md:394`) | S3.2, S3.4 | 2-3 | no |
| `phase7-defined` (W5) | dsverify-net | `grpcAddrAt` over `grpcCliP`/`grpcSrvP`, the opaques deleted; `Serve`, `Invoke`, `NewStream` theorems; decision A's claim in `models/README.md` | S3.3, W4, `phase7-seal` | 2 | yes (the claim) |
| `phase7-s2d-rest` | dsverify-net, zeldovich-proving-2 | `NewClient`, `grpcConn` defined, `credsYieldI` defined, `grpcResolverAt`, `etcdResolver_grpc`, `ClientConn.Target`, the `pb*_reg` registries out; client leaves (`Endpoints`, `GetRequestMetadata`, `Client.Close`, `RequiresCredentials`, `peer.String`, `logUnaryRequestStats`) | S3.2 | 3-4 | no |
| `etcd-dist-s4` | etcd lead | the deployment statement (one machine per member, decided 2026-11-22); `addrClaim`, `addrUnclaimed`, `httpProtoFree`, `reserve`/`register` gone; `etcd_safe` over SW1/SW2's axioms (decision J) | SW1, S3.5, S5's vocabulary | 3-5 | yes (top-level) |
| `phase7-retire` (W8) | etcd lead, dsverify-net | `Serve_dist` derived; baselines and collections; `grpcSrvNew`, `grpcWrotePeer` out | W5 | 2-3 | no |
| `server-no-refusal`, `grpc-otel-stats`, `bridge-net` | etcd lead; zeldovich-proving-2 | decision E; otel over its noop global (or kept trusted); the bridge over the net extension, or kept trusted (D26) | status-bodies, S3.2; S4 | 2 + 2 + 2 | E: yes |

dsverify-lab: no axiom of this family is in a kit's collection. Its touch points are S5's `conn.serve`
(decision I) and `NetStart`/`ServerStart` (the etcd lead's statement). It owns none of the branches
above.

### The critical paths

- **`etcd_safe` stated and proved modulo the switch's axioms** (the etcd lead's priority): SW1 (3-5) →
  S3.5 (2-3) → `etcd-dist-s4` (3-5), with SW2 beside SW1. About 8-13 sessions. No proof of the transport
  is on it.
- **The family retired from `etcd_safe`**: SW1 → S3.1 (2-3) → S3.2 (12-16, needing W1 and W3 by then) →
  S3.3 (2-3) → W5 (2, needing W4 and the sealing) → W8 (2-3). About 23-32 sessions on one line, with W4,
  S5, the leaves and S4 beside it.

**What runs in parallel now:** SW1 and SW2 (dsverify-net, two agents); `phase7-inits` then
`status-bodies` on the grpc queue, the Perennial proposals and the S5 server batches
(zeldovich-proving-2); the pin bump (zeldovich-coordinator); `mvccfull-noaddr` and the distributed
statement's preparation (etcd lead). **The cheap wins first:** `phase7-inits` (−9), the unused
`Server.Serve.impl` (in it), `mvccfull-noaddr` (−3 from mvccfull), `grpclog.SetLoggerV2` and
`status.Status.Code` (K only), `grpc.StatsHandler` under `h ≠ nil` (in `phase7-s2a`).

### What "done" means, and two items no stage retired (2026-11-24)

gRPC is done when it contributes no axiom, no `sorry` and no premise to any top-level robustness
theorem, and no trusted opaque definition either; what stays trusted is the `models/grpc` Go model
and the net extension's semantics. The collection `etc/tcb-collections/grpc.txt` (branch
`grpc-tcb-collection`: 142 axioms, no `sorry`, each mapped to the stage above that retires it) is
the measure; landings shrink its baseline until it is empty. Two items had no stage:

- **`DialWithBalancerBody`** (an instance premise of the single-process etcd, k8s and leaseexpiryN
  theorems, putget and etcd_robust): the hypothesis class that replaced the inconsistent
  `Client.dialWithBalancer.unfold`/`.builderType` axioms (notes/audit.md, B1), because client/v3's
  `Client.dialWithBalancer` is translated names-only. Stage **G-dial** (dsverify-net): translate it
  with its body; where goose refuses it, fix the translator gap in Perennial's goose as a general
  change (Perennial's own workflow), not a local stand-in; then prove it over the dial-side specs
  (`InvDial.lean`) and delete the class. After `phase7-switch` (it touches the dial options'
  vocabulary); about 1 session if goose takes it, 2-3 with a translator change.
- **Trusted opaque definitions** are not axioms, so the collection's axiom count does not see them:
  `grpcCliPI`/`grpcSrvPI`, `protoEncodes`, `credsYieldRaw`, the 17 opaques of
  `Proof/net/http/Boundary.lean`, `grpcRepliesFit`. Stage **T-opaques** (dsverify-net, tooling,
  untrusted): `etc/tcb-report.py` reports, for a collection, the `opaque` constants its roots'
  statements and axioms reach (an `opaque` line per constant in the baseline, checked as the axioms
  are), so that they too must drop to zero. The opaques retire with their stages (W5 the protocols,
  W3 the codec, S5 net/http's).
- **`grpcRepliesFit`** stays a premise of the theorems that have it until W3/W5 (it is false of
  etcd under one workload: `issues/etcd-txn-keysonly-reply-alloc-panic.md`); no new statement takes
  it: the library drivers (`notes/library-drivers.md`) send only messages the program bounds in Go.

## 5. What each top-level theorem still rests on

(2026-11-24) `etc/tcb-collections/grpc.txt` makes the family's part mechanical: its roots are every etcd
and Kubernetes example's result and every top-level robustness theorem, its `axioms` lines restrict the
baseline to the family (`etc/tcb-report.py --help`). Baseline at `2fac29cd4f`: 142 axioms, no `sorry`.
"gRPC is done" is that baseline empty and the grpc-specific premises gone from the statements
(`grpcRepliesFit`, `addrsUnclaimed`, `DialWithBalancerBody`'s resolver type; the opaques of the family
are not axioms and the report does not see them).

From the inventory (strict family counts, the adjacent prometheus and zap axioms in parentheses), with
this plan's order:

- **`etcd_safe_single_process`** (E, restored over the net extension, `notes/single-process-restore.md`):
  140 (152). SW1 removes 4 (`grpc.start`, `grpcAddrIsRaw`, `grpcSrvCfgRaw`, `grpcSrvLink`); the inits 9;
  the status slice 7. It needs every slice (G-log, the context leaves, S2a, S3.2-S3.3, S2d's rest, S5 both
  halves, health, prom-mw, otel, the bridge, `etcd_noRefusal`) and S4's addresses: the last to clear,
  after W8 and S5's client.
- **`k8s_safe_single_process`** (K): 124 (136). The same set less the auth and lease-grant
  registrations, plus `grpclog.SetLoggerV2`, `grpclog.initFuncsOk`, `status.Status.Code` (cheap). Clears
  with E.
- **`etcd_leaseexpiryN_safe_single_process`** (L): 117 (129). No `NewStream`, watch registries, bridge or
  `etcd_noRefusal`; its stream-half axioms go with SW1. It clears with the inits, G-log, status, the
  context leaves, S2a, S3.2 (its unary half), S2d's rest, S5, health, prom-mw, otel and S4: the first of
  the three.
- **mvccfull** (F): 12 (17): the inits (6), the client/v3 `init` (G-log, decision G), `status.Error`/
  `FromError`, and the three address axioms (`mvccfull-noaddr`). About 4 sessions: **the first top-level
  theorem free of the family**, after `phase7-inits`, `mvccfull-noaddr`, `status-bodies` and G-log.
- **cache**: 2 (`status.Error`, `FromError`): free after `status-bodies`.
- **`etcd_safe`/`etcd_robust`** (the distributed statement, a draft; `putget_safe` first, a theorem on
  `dist-putget-interim/2026-11-24` over `S2Draft`'s interim axioms): after SW1/SW2 and decision J, it
  rests on the switch's axioms (`Serve`, `Invoke`, `NewStream`, `NewClient`), the opaques `grpcCliPI`/
  `grpcSrvPI`/`protoEncodes`/`credsYieldRaw`, the codec axioms (W3), and the leaves E has. It is free of
  the family when E is (W8, S5, S4), less the single-process start. A collection for `putget_safe` is to
  be added when it lands.
- **mvcc, mvcc-compaction, the dsverify kits, kvnet, net, models-net, remote-counter**: none.

The lower collections to update with each branch (`--check --update`): cli 67, v3r 47, k8s 41, srv 38,
cache-client 30, lsrv 29, k8s-compactor 24, slice 20, snap 18, lease 16, wat 15, recipes 15.

## 6. Risks and open questions

- **Nothing is elaborated.** In particular: `ProtoWire.cnt`'s autoParam with the anonymous constructors
  (`⟨…⟩` may not fill it: write `cnt :=` in the models); a `Countable` instance for every message model's
  `M` and for `StreamNames`; the universe of `GrpcSvcEntry` (it holds `IProp`, as `GrpcEntry` does);
  `grpcStartSvc`'s `find?` against `grpcGoSvc`'s definitional unfolding in `grpc.serve`.
- **The watch client under R2** (decision C): its epoch's token is used before the first response in
  places to be found; S3's estimate (300-600 lines) is the switch's main risk.
- **`cluster3` without registration forwarding** (§1.5, item 5): the size of carrying the table term in
  the member and bridge bundles is unknown.
- **The codec's determinism** (decision B): `Unmarshal` claims that bytes decode to one normalized tree;
  the review must check the trees against protobuf's normal forms (unknown fields, `-0.0`, NaN payloads,
  proto2 presence, map order).
- **`Invoke` and R1's unary form** (grpc/grpc-go#9443): `Invoke` returns a bare `io.EOF` after the same
  failed replay; check that `Invoke`'s error arm (`clientErrTys`) admits it.
- **R3** (a server `SendMsg` after the status returns `nil` undelivered): stated in `models/README.md`'s
  grpc claim with S3.0, with R1's retry, the handler starting on the head, and one trailer per stream.
- **`context.WithValue`** (R6) blocks `cs.Context()` and the server run's context in S3.3 and S5's
  `Serve`; it waits on Perennial.
- **Latent-false axioms** to fix when proved: `streamKeyFromCtx` (`notes/audit.md:403`), prometheus's
  `StreamServerInterceptor` (`:394`).
- **R9**: etcd's `serverStreamingRetryingStream` can run a handler twice; it stays excluded by
  `ClientStreams = true`, so `Maintenance.Snapshot` is not covered.
- **Wildcard listeners** (O6, `net-wildcard-listen`): `grpcServeTok` would need the table at every
  accepted address.
- **Rebuild memory**: SW1, SW2 and W1 each rebuild about 7700 modules; build them on the VM.
- **The bridge in the end state** stays trusted (D26) unless `bridge-net` proves the relay
  (`depSlot_relay`, a slot claimed on one connection and re-registered on the other).
- **Open, for the user in the morning:** every "Decided (overnight)" of §3, and the trusted branches'
  reviews (SW1, SW2, `phase7-inits`, W1's model fix, W3, `mvccfull-noaddr`, G, W5's claim, S4).
