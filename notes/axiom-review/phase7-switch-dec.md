# Review: phase 7's switch, SW2 (the dec-shaped run contract, decision D1) (2026-11-25)

**Target.** Branch `phase7-switch-dec/2026-11-25` (off `lean` `820a287c3a`), the plan
`notes/phase7-endstate.md` §1.2 ("SW2: the dec-shaped run contract", adopted as written from S2's design
§1.2), §1.3 (`Serve`'s row) and §1.5 decision 2 (`grpcRunPreOkMd` kept, interim, for Go's single-process
table until W4). The one axiom whose meaning changes: `grpc.Server.Serve.wp_proof`
(`Proof/google_golang_org/grpc/Server__Serve.lean`), through `grpcServeTok` → `grpcServes` →
`grpcServesEnt`'s unary clause. Its spec text (`Spec/google_golang_org/grpc/Server__Serve.lean`) and the
text of `grpcServeTok` and `grpcServes` are unchanged. No other axiom, opaque or top-level statement
reaches the changed definitions (grep of every `axiom` file and every `TopLevel*.lean`; `Serve_dist`'s
statement names no run contract, only its docstring mentions one).

## The trusted text, old → new

All in `Proof/google_golang_org/grpc/InvGrpcBase.lean` (section `run` and the method contracts) and
`InvGrpcRun.lean`.

### 1. `grpcServesEnt`'s unary clause (`InvGrpcRun.lean`)

Old:

```lean
  | .unary e => iprop(⌜name ∉ sregs.map Prod.fst⌝ ∗ ∀ (mh : GoFunc) (srv : GoInterface),
      ⌜(name, mh, srv) ∈ regs⌝ -∗
      ∃ (Req Rep : ProtoMsgT GF) (Spec : GrpcSpecMd Req.toProtoMsg Rep.toProtoMsg),
        ⌜grpcReqModelOf GF Req.ty = some Req ∧ grpcRepModelOf GF Rep.ty = some Rep ∧
          e = ⟨Req.toProtoMsg.wire, Rep.toProtoMsg.wire, Spec⟩⌝ ∗
        grpcRunOkMd #mh srv ics Spec)
```

New (the last line only):

```lean
        (grpcRunOkMd #mh srv ics Spec ∨ grpcRunPreOkMd #mh srv ics Spec))
```

### 2. `grpcRunOkMd` (redefined) and `grpcRunPreOkMd` (the old text, renamed)

Old `grpcRunOkMd` = new `grpcRunPreOkMd`, word for word (only the name changes):

```lean
def grpcRunPreOkMd {Req Rep : ProtoMsg GF} (mh : val) (srv : GoInterface) (ics : List GoFunc)
    (Spec : GrpcSpecMd Req Rep) : IProp GF :=
  iprop(∀ (m : Req.M) (Φ : Rep.M → IProp GF) (Ψe : GoString → IProp GF) (ci : GoInterfaceOk)
      (cd : context.ContextDesc (IProp GF)) (dec ui : GoFunc),
    {{ threadTok ∗ £ 1 ∗ context.isContext ci cd ∗ grpcRunCtx ci ∗ grpcDecOk dec Req m ∗
        grpcSrvChainAll ics ui ∗ grpcSpecAt Spec ci m Φ Ψe }}
      (methodHandlerCall mh #srv #(GoInterface.ok ci) dec ui)
    {{ (resp err : GoInterface), RET (PairV #resp #err); threadTok ∗
        (⌜err = GoInterface.nil⌝ -∗ ∃ (l : Loc) (m' : Rep.M),
          ⌜resp = interface.mkOk (go.GoType.PointerType Rep.ty) #l⌝ ∗ Rep.send l m' ∗ Φ m') ∗
        handlerErrOut Ψe err ∗ go_etcd_io.etcd.cache.v3.srvErrOk err }})
```

New `grpcRunOkMd` (§1.2's text):

```lean
def grpcRunOkMd {Req Rep : ProtoMsg GF} (mh : val) (srv : GoInterface) (ics : List GoFunc)
    (Spec : GrpcSpecMd Req Rep) : IProp GF :=
  iprop(∀ (D : IProp GF) (Got : (Rep.M → IProp GF) → (GoString → IProp GF) → IProp GF)
      (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (dec ui : GoFunc),
    {{ threadTok ∗ £ 1 ∗ context.isContext ci cd ∗ grpcRunCtx ci ∗ D ∗
        grpcDecDepOk dec Spec ci D Got ∗ grpcSrvChainAll ics ui }}
      (methodHandlerCall mh #srv #(GoInterface.ok ci) dec ui)
    {{ (resp err : GoInterface), RET (PairV #resp #err); threadTok ∗ grpcRunOut D Got resp err }})
```

### 3. New: `grpcDecDepOk`, `grpcRunOut` (§1.2's text)

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
    (Got : (Rep.M → IProp GF) → (GoString → IProp GF) → IProp GF) (resp err : GoInterface) :
    IProp GF :=
  iprop(go_etcd_io.etcd.cache.v3.srvErrOk err ∗
    ((D ∗ ⌜err ≠ GoInterface.nil⌝ ∗ notHandlerErr err) ∨
     ∃ (Φ : Rep.M → IProp GF) (Ψe : GoString → IProp GF), Got Φ Ψe ∗
       (⌜err = GoInterface.nil⌝ -∗ ∃ (l : Loc) (m' : Rep.M),
          ⌜resp = interface.mkOk (go.GoType.PointerType Rep.ty) #l⌝ ∗ Rep.send l m' ∗ Φ m') ∗
       handlerErrOut Ψe err))
```

`grpcDecOk`'s text is unchanged (it is now reached only through `grpcRunPreOkMd`); its docstring gains a
sentence saying so.

### 4. Docstrings only

`Server.Serve.wp_proof`'s docstring: "runs Go's handler for it (`grpcServes`) on the request the call's
deposit holds, with the deposit `e.spec md m Φ Ψe` at the run's incoming metadata" becomes "runs Go's handler
for it (`grpcServes`) as one of the two run contracts the handler meets: dec-shaped (`grpcRunOkMd`), its
`dec` decodes the request the call's deposit holds and delivers the deposit `e.spec md m Φ Ψe` at the run's
incoming metadata with a receipt for `Φ`/`Ψe`, or fails with the run's right to the request given back, and
the run answers the receipt; or, interim for Go's single-process table, deposit-at-start
(`grpcRunPreOkMd`), the deposit given with the run". `grpc.CustomCodec.wp_proof`'s docstring names
`grpcDecDepOk` where it named `grpcDecOk` (what a run is given). The file headers of `InvGrpcBase.lean` and
`InvGrpcRun.lean` say the same.

## Why `Serve`'s axiom stays sound

**The new clause is equivalent to the old one.** The law `grpcRunPreOkMd_of_run` (`InvGrpcBase.lean`,
proved) gives `grpcRunOkMd mh srv ics Spec ⊢ grpcRunPreOkMd mh srv ics Spec`: run the dec-shaped contract
at `D := grpcSpecAt Spec ci m Φ Ψe` (the deposit, held from the start) and
`Got Φ' Ψe' := ⌜Φ' = Φ ∧ Ψe' = Ψe⌝`; `grpcDecOk dec Req m` gives `grpcDecDepOk` at those (on success the
held deposit and the trivial receipt, on failure `D` back); on `grpcRunOut`'s `D` arm the error is no
handler's (`handlerErrOut_not`) and not `nil`, on its receipt arm `Φ'`/`Ψe'` are the call's. So
`grpcRunOkMd ∨ grpcRunPreOkMd ⊣⊢ grpcRunPreOkMd`, and `grpcRunPreOkMd` is the old `grpcRunOkMd` word for
word: the new `grpcServesEnt` is equivalent to the old one at every entry, hence the new `grpcServes` and
`grpcServeTok` to the old. `Serve`'s axiom takes `grpcServeTok` in its precondition, so the new axiom
follows from the old one (and conversely). Its soundness is exactly the old axiom's, reviewed in
`notes/axiom-review/s2-interface.md` and, with streams and SW1's per-kind clauses, in
`notes/axiom-review/phase7-switch.md`: opaque protocols, so no raw writer or reader (C1, C2, C2'); one
dispatch per call; the dispatched metadata is an attempt's; C3 and its mirror blocked by the kind clauses.
No attack there depended on which run contract the clause names beyond its strength, and the strength is
unchanged.

**The dec-shaped arm on its own (what W4 leaves).** After W4 deletes the `Pre` arm, the clause is the
dec-shaped contract alone, which is weaker for `Serve`'s proof to rely on and stronger for a handler to
meet. It holds of grpc-go v1.84 and of the model: a handler receives its context and grpc's `dec` closure;
the caller's deposit reaches the handler only through a successful `dec`, which decodes the request the
call's attempt sent (`wrapUnaryHandler`'s `dec` is the stream's `RecvMsg`, `models/grpc/server.go`; real
grpc-go's `processUnaryRPC` decodes the received message in `df`), and its metadata is the run context's
(`grpcSpecAt`'s `ctxInMD`). `D` (exclusive, abstract) is the stream's unclaimed right to its one message,
so a second `dec` cannot produce a second deposit; a `dec` failure returns an error no handler makes
(`statusErrOk`, the same claim `grpcDecOk` made, `notes/axiom-review/hs6.md`). `Got` is abstract: the
handler never looks inside it and must return it with its answer, so the answer goes to the call whose
deposit it decoded. This is the contract C1's second paragraph (`s2-interface.md`) asked for: a handler
that relies on a deposit fact before calling `dec` (a metadata check) can no longer be proved against it.

**What a client sees.** Nothing: `Invoke`'s and `NewStream`'s texts, `isGrpcRpcMd` and the table are
untouched. Proofs that build `grpcServes` choose the arm; the program's servers (etcd's handlers through
the adapters, the gRPC driver's) use the dec-shaped arm, Go's single-process table (`grpcStartSvc` through
`grpcGoEntry`) the `Pre` arm (`grpcRunPreOkMd_goEntry`, and `grpc.serve` converts the handlers' contracts by
`grpcRunPreOkMd_of_run`).

## Deviations from §1.2

None in the trusted text: `grpcDecDepOk`, `grpcRunOut`, `grpcMethodOkMd`, `grpcRunOkMd` are §1.2's text
(binder `Got`'s type written out where §1.2 abbreviates it `…`), `grpcRunPreOkMd` is today's text renamed,
and the clause is `grpcRunOkMd … ∨ grpcRunPreOkMd …`. Untrusted choices the plan left open:

- The plain `grpcMethodOk` takes the same shape, at `GrpcSpec.md Spec` (S2 design §1.2's note), so
  `grpcMethodOk_md` is an equality of unfoldings.
- `grpcDecOk_ty` is replaced by `grpcDecDepOk_ty` (its one user, `UnaryHandlerLemmas`, now calls the
  dec-shaped `dec`); `grpcDecDepOk_mono_upd` is new (the mono laws of the contracts go through it).
- The handler specs' interceptor fact is `□ ∀ l m, Req.recv l m -∗ Q …` (the request's model is known only
  after `dec`), as S2 §1.5 says.
- `etcd_compactMethodOk` (client/v3 `Results.lean`) is generalized over its plain spec: with auth on, the
  `Compact` spec is vacuous, which the old proof read off the deposit in the run's precondition; now the
  deposit comes out of `dec`, so the proof runs the generated handler over a vacuous service-method
  contract.
