/-
**grpc's server: the right to serve and the start** (Lean-first, no Rocq counterpart; history:
`notes/phase7-endstate.md`).

**The service table** (one table of both kinds). A registration is heap-free: `isGrpcRpcMd addr name Spec`
(`InvGrpc.lean`) and `isGrpcStreamMd addr name Up Spec` (`InvGrpcStream.lean`) say that `addr`'s table
`Svc`, set once with its protocols (`grpcAddrAt`, `InvGrpcWire.lean`), has an entry for `name` that a
caller meets (`grpcSvcAt`, `grpcStreamSvcAt`). What makes this sound is `Server.Serve`'s axiom, which
takes `grpcServeTok gs lis a Svc`: Go's configuration being built (`grpcSrvNew`) with the node's open
listener at `a`, `a` serving `Svc`, and `grpcServes Svc`: a clause per entry kind (`grpcServesEnt`), a
unary entry naming no stream (C3) and met by the handler `gs` registers under its name as a run
(`grpcRunOkMd`, the run contract: a run is given the fork's thread token and one later credit, returns
the token), a stream entry naming no unary method (C3's mirror) and met by the stream `gs` registers
under its name as a run (`grpcStreamRunOk`), through the conversions between the entry's content and
the handler's own. `Serve`'s post is `True`; its axiom says the server meets `Svc` on every connection
to `a`, as the opaque protocols `grpcCliPI Svc`/`grpcSrvPI Svc` state it: no program but grpc's
transport writes or reads such a connection meaningfully (`notes/axiom-review/s2-interface.md`, C1 and
C2). There is no server name.

**One process.** The single-process start (`grpc.start'`, a theorem) sets the address's table to Go's
configuration (`grpcStartSvc ics regs tys sms`: an entry for each registered unary method `tys` gives
registered models, whose spec is some spec its handler's run contract meets, `grpcGoSvc`; and the
streams `sms`, each at its content family `dn`) from what `Listen` left (`netAddrLeft`), allocating the
net library's registry and slot map in the same ghost step, and proves `grpcServes` of it
(`grpcServes_start`) and the streams' registrations; `grpc.serve` (a theorem) then registers each unary
method at the spec it is proved at.

**Streams** share one call protocol with unary calls in the end state (S3); until S3 the stream's
transport is `ClientConn.NewStream`'s axiom, paired with `Serve`'s: both ends share the stream's names
`γ` and the persistent stream specification; the client learns the dispatch `(a, md)` with each
response (`streamDispIs`), the handler is given `md` through its context.

**The pair's argument, as `Serve`'s and `Invoke`'s axioms rest on it.** One deposit, one run: grpc's
transparent retry resends only a stream the server never processed (`stream.go`, `shouldRetry`'s
unprocessed case); the program's clients have no retry policy, no hedging and no
`healthCheckConfig` (every client is made by the `NewClient` spec under `grpcResolverAt` and
`dialOptsAt`; without it grpc resends a processed trailers-only attempt, `stream.go:803-858`, test
T8b); and grpc makes no calls of its own (no client-side health checks, no ORCA out-of-band
streams). The message models are the client's registered ones (model-param, option C'): `Invoke`'s
invoker contract (`grpcInvokerOk`) takes `grpcReqModelOf GF Req.ty = some Req` and
`grpcRepModelOf GF Rep.ty = some Rep` before the deposit, and a table's entry is at the registered
models' wire parts (`grpcServes`). Go facts, not pair facts: `(name, mh, srv) ∈ c.regs` (Go's
dispatch), `grpcSrvChainAll c.ics`, `grpcSrvStreamChainAll c.sics`, `grpcDecOk`, `grpcRunCtx`.
-/
module

public import Proof.google_golang_org.grpc.InvGrpcServer
public import TrustedCode.google_golang_org.grpc
public import Perennial.Proof.ThreadPool

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode Net

/-! ## Pure facts -/

section pure
variable [GooseExts]

theorem grpc_inj_of_nodup_map {α : Type _} {β : Type _} (f : α → β) :
    ∀ (l : List α), (l.map f).Nodup → ∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y
  | [], _, x, hx, _, _, _ => by simp at hx
  | a :: l, h, x, hx, y, hy, hxy => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at h
    rcases List.mem_cons.mp hx with rfl | hx' <;> rcases List.mem_cons.mp hy with rfl | hy'
    · rfl
    · exact absurd hxy.symm (h.1 y hy')
    · exact absurd hxy (h.1 x hx')
    · exact grpc_inj_of_nodup_map f l h.2 x hx' y hy' hxy

/-- Under the joint `Nodup`, two unary entries of one name are one entry. -/
theorem grpc_regs_unique (regs sregs : List (GoString × GoFunc × GoInterface)) (name : GoString)
    (mh mh' : GoFunc) (srv srv' : GoInterface)
    (Hnd : ((regs ++ sregs).map Prod.fst).Nodup)
    (H1 : (name, mh, srv) ∈ regs) (H2 : (name, mh', srv') ∈ regs) : mh = mh' ∧ srv = srv' := by
  have Hnd' : (regs.map Prod.fst).Nodup := by
    rw [List.map_append] at Hnd; exact (List.nodup_append.mp Hnd).1
  have := grpc_inj_of_nodup_map Prod.fst regs Hnd' _ H1 _ H2 rfl
  simp only [Prod.mk.injEq, true_and] at this
  exact this

/-- Under the joint `Nodup`, two stream entries of one name are one entry. -/
theorem grpc_sregs_unique (regs sregs : List (GoString × GoFunc × GoInterface)) (name : GoString)
    (mh mh' : GoFunc) (srv srv' : GoInterface)
    (Hnd : ((regs ++ sregs).map Prod.fst).Nodup)
    (H1 : (name, mh, srv) ∈ sregs) (H2 : (name, mh', srv') ∈ sregs) : mh = mh' ∧ srv = srv' := by
  have Hnd' : (sregs.map Prod.fst).Nodup := by
    rw [List.map_append] at Hnd; exact (List.nodup_append.mp Hnd).2.1
  have := grpc_inj_of_nodup_map Prod.fst sregs Hnd' _ H1 _ H2 rfl
  simp only [Prod.mk.injEq, true_and] at this
  exact this

end pure

/-! ## The registration and the accepted call -/

section reg
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The composed stream interceptor grpc calls, for the chain `sics`, with the resource `R`**
(persistent; as `grpcSrvChain` for streams: grpc's `chainStreamServerInterceptors`,
`server.go:1243-1276`: `nil` for no interceptor, the one interceptor, or grpc's closure, whose calls,
given `R`, are the chain's at `R`). The handler `h` is a function value (a `StreamDesc.Handler`), as
in the unary `grpcSrvChain`: a panic value there would unwind the call while the chain's
interceptors never see it. -/
def grpcSrvStreamChain (R : IProp GF) (sics : List GoFunc) (si : GoFunc) : IProp GF :=
  match sics with
  | [] => iprop(⌜si = func.nil⌝)
  | _ :: _ => iprop(⌜si ≠ func.nil⌝ ∗ □ ∀ (srv st info : val) (h : GoFunc) (Ψ : val → IProp GF),
      srvStreamChainWP R info sics #h srv st Ψ -∗
      R -∗ WP (App (App (App (App (Val #si) (Val srv)) (Val st)) (Val info)) (Val #h))
        {{ v, R ∗ Ψ v }})

instance grpcSrvStreamChain_persistent (R : IProp GF) (sics : List GoFunc) (si : GoFunc) :
    Persistent (grpcSrvStreamChain (GF := GF) R sics si) := by
  unfold grpcSrvStreamChain; cases sics <;> infer_instance

/-- **grpc's composed stream interceptor at every resource** (persistent; the Go fact a stream run is
given, `grpcAccepted`): as `grpcSrvChainAll`, true of grpc-go v1.84 because `chainStreamInterceptors`
and `getChainStreamHandler`'s closures are grpc's code, calling the next interceptor (or the
handler) synchronously on the run's goroutine and touching no resource of the program's. -/
def grpcSrvStreamChainAll (sics : List GoFunc) (si : GoFunc) : IProp GF :=
  iprop(□ ∀ R : IProp GF, grpcSrvStreamChain R sics si)

instance grpcSrvStreamChainAll_persistent (sics : List GoFunc) (si : GoFunc) :
    Persistent (grpcSrvStreamChainAll (GF := GF) sics si) := by
  unfold grpcSrvStreamChainAll; infer_instance

/-- **What `gs` serves for the entry `ent` of the name `name`**: a clause per kind.
* A unary entry names no stream (C3 of `notes/axiom-review/s2-interface.md`: a unary call of a
  stream's name would run the stream's handler), and a unary method `gs` registers under its name has
  that entry, at its registered message models, met by its handler as a run (`grpcRunOkMd`).
* A stream entry names no unary method (C3's mirror: a `NewStream` of a unary method's name runs the
  wrapped unary handler on a stream, the model's `server.go:778-785`), and a stream `gs` registers
  under its name has that entry, at its registered message models: the entry's request content gives
  the handler's `Up`, the handler's specification holds at its own response content `Dns`, which gives
  the entry's `dn₀`, and the handler meets `Spec` as a run (`grpcStreamRunOk`). The server's own `Up`,
  `Spec` and `Dns` may mention its heap; the entry's do not.
An entry `gs` does not register gets grpc's `Unimplemented` (no handler's description). -/
def grpcServesEnt (ics sics : List GoFunc) (regs sregs : List (GoString × GoFunc × GoInterface))
    (name : GoString) : GrpcSvcEntry GF → IProp GF
  | .unary e => iprop(⌜name ∉ sregs.map Prod.fst⌝ ∗ ∀ (mh : GoFunc) (srv : GoInterface),
      ⌜(name, mh, srv) ∈ regs⌝ -∗
      ∃ (Req Rep : ProtoMsgT GF) (Spec : GrpcSpecMd Req.toProtoMsg Rep.toProtoMsg),
        ⌜grpcReqModelOf GF Req.ty = some Req ∧ grpcRepModelOf GF Rep.ty = some Rep ∧
          e = ⟨Req.toProtoMsg.wire, Rep.toProtoMsg.wire, Spec⟩⌝ ∗
        grpcRunOkMd #mh srv ics Spec)
  | .stream e => iprop(⌜name ∉ regs.map Prod.fst⌝ ∗ ∀ (mh : GoFunc) (srv : GoInterface),
      ⌜(name, mh, srv) ∈ sregs⌝ -∗
      ∃ (Req Rep : StreamMsgT GF) (up₀ : Nat → Req.M → IProp GF)
        (dn₀ : GrpcMd → StreamNames → Nat → Rep.M → IProp GF)
        (spec₀ : GrpcMd → StreamSpec Rep.toStreamMsg) (Up : Nat → Req.M → IProp GF)
        (Spec : GrpcMd → StreamSpec Rep.toStreamMsg)
        (Dns : GrpcMd → StreamNames → Nat → Rep.M → IProp GF),
        ⌜streamReqModelOf GF Req.ty = some Req ∧ streamRepModelOf GF Rep.ty = some Rep ∧
          e = ⟨Req.wire, Rep.wire, up₀, dn₀, spec₀⟩⌝ ∗
        (□ ∀ i m, up₀ i m -∗ Up i m) ∗ (□ ∀ md γ, Spec md γ (Dns md γ)) ∗
        (□ ∀ md γ j m, Dns md γ j m -∗ dn₀ md γ j m) ∗
        grpcStreamRunOk #mh srv sics Up Spec)

/-- **`gs` serves the table `Svc` with Go's chains `ics`, `sics`, methods `regs` and streams `sregs`**
(persistent; a clause per entry kind, `grpcServesEnt`). -/
def grpcServes (Svc : GrpcSvc GF) (ics sics : List GoFunc)
    (regs sregs : List (GoString × GoFunc × GoInterface)) : IProp GF :=
  iprop(□ ∀ (name : GoString) (ent : GrpcSvcEntry GF), ⌜Svc name = some ent⌝ -∗
    grpcServesEnt ics sics regs sregs name ent)

instance grpcServes_persistent (Svc : GrpcSvc GF) (ics sics : List GoFunc)
    (regs sregs : List (GoString × GoFunc × GoInterface)) :
    Persistent (grpcServes Svc ics sics regs sregs) := by
  unfold grpcServes; infer_instance

/-- **Every reply the table `Svc` lets a handler send marshals** (persistent; grpc-trusted-T, T9,
2026-11-24; interim, retired by phase 7 decision B's W3, the codec's proof, which makes the bound the
codec's own): for each entry, the reply model registered for its reply's Go type (`grpcRepModelOf`,
`streamRepModelOf`: the one the entry's handler sends through, `grpcServes`) bounds the encoding of
every reply it sends (`Rep.send l m`) below `grpcReplyMax`, so grpc's marshalling of it allocates no
more than Go's `maxAlloc` (`InvGrpcServer.lean`, `grpcReplyMax`). The other way to the size premise
of `Serve`'s trusted model than the workload premise `grpcRepliesFit`: a property of the registered
models, which a program with bounded replies proves (the gRPC driver's `StringValue`). -/
def grpcRepliesBounded (Svc : GrpcSvc GF) : IProp GF :=
  iprop(□ ∀ (name : GoString) (ent : GrpcSvcEntry GF), ⌜Svc name = some ent⌝ -∗
    match ent with
    | .unary e => ∀ Rep : ProtoMsgT GF, ⌜grpcRepModelOf GF e.Wp.ty = some Rep⌝ -∗
        □ ∀ (l : Loc) (m : Rep.M), Rep.send l m -∗ ⌜Rep.wireLen m < grpcReplyMax⌝
    | .stream e => ∀ Rep : StreamMsgT GF, ⌜streamRepModelOf GF e.Wp.ty = some Rep⌝ -∗
        □ ∀ (l : Loc) (m : Rep.M), Rep.send l m -∗ ⌜Rep.wireLen m < grpcReplyMax⌝)

instance grpcRepliesBounded_persistent (Svc : GrpcSvc GF) :
    Persistent (grpcRepliesBounded Svc) := by
  unfold grpcRepliesBounded; infer_instance

/-- **The right to serve `gs` on `lis` at `a`, for the table `Svc`** (what `gs.Serve(lis)` takes):
Go's configuration `c` of `gs`, being built (`grpcSrvNew`), with the node's open listener at `a`, or
both bound together by a no-refusal certificate (`grpcSrvAtLis`); full names jointly distinct; the replies' size premise, or (since
grpc-trusted-T, T9) the table's registered reply models bounding every reply (`grpcRepliesBounded`);
`a` serving `Svc` (`grpcAddrAt`); `gs` serving `Svc` (`grpcServes`). -/
def grpcServeTok (gs : Loc) (lis : GoInterface) (a : GoString) (Svc : GrpcSvc GF) : IProp GF :=
  iprop(∃ (c : GrpcSrvCfg GF) (svcs : List GoString),
    ((grpcSrvNew gs c.ics c.sics svcs c.regs c.sregs ∗ netListenerOpen lis a) ∨
      grpcSrvAtLis gs lis a c.ics c.sics svcs c.regs c.sregs) ∗
    ⌜grpcSrvNodup c⌝ ∗ (⌜grpcRepliesFit⌝ ∨ grpcRepliesBounded Svc) ∗
    (∃ (_ : HasExt netExt) (π : NetProtoGS) (σ : NetSlotGS),
      grpcAddrAt (Gg := hG.goose_globalGS) (π := π) (σ := σ) a Svc) ∗
    grpcServes Svc c.ics c.sics c.regs c.sregs)

/-- **Go's configuration's entry for a registered method is met by its handler** (one process): under
distinct full names, the handler `gs` registers under `name` meets `grpcGoEntry`'s spec, whose
caller's run contract is the registered handler's (`grpc_regs_unique`). -/
theorem grpcRunOkMd_goEntry (ics : List GoFunc) (regs sregs : List (GoString × GoFunc × GoInterface))
    (name : GoString) (mh : GoFunc) (srv : GoInterface) (Req Rep : ProtoMsgT GF)
    (hnd : ((regs ++ sregs).map Prod.fst).Nodup) (hin : (name, mh, srv) ∈ regs) :
    ⊢ grpcRunOkMd (Req := Req.toProtoMsg) (Rep := Rep.toProtoMsg) #mh srv ics
      (grpcGoEntry ics regs name Req Rep).spec := by
  unfold grpcRunOkMd
  iintro %m %Φ %Ψe %ci %cd %dec %ui !> %Ψ ⟨HT, Hlc, Hctx, Hrc, Hd, Hch, HSpec⟩ HΨ
  iunfold grpcSpecAt at HSpec
  icases HSpec with ⟨%md, Hmd, HS⟩
  unfold grpcGoEntry
  icases HS with ⟨%mh', %srv', %S, %hin', #Hrun, HS⟩
  obtain ⟨rfl, rfl⟩ := grpc_regs_unique regs sregs name mh mh' srv srv' hnd hin hin'
  iunfold grpcRunOkMd at Hrun
  iapply Hrun $$ %m %Φ %Ψe %ci %cd %dec %ui [HT Hlc Hctx Hrc Hd Hch Hmd HS] HΨ
  iframe
  unfold grpcSpecAt
  iexists md
  iframe

/-- **Go's configuration as a table** (one process): the unary
methods as `grpcGoSvc` has them (an entry for each registered method `tys` gives models for), then the
streams `sms` (the first of a name), each at its registered models, its content and specification,
and its response content `dn`. The single-process start sets the address's table to it
(`grpc.start'`). -/
def grpcStartSvc (ics : List GoFunc) (regs : List (GoString × GoFunc × GoInterface))
    (tys : GoString → Option (ProtoMsgT GF × ProtoMsgT GF)) (sms : List (GrpcStreamMethod GF)) :
    GrpcSvc GF := fun name =>
  match grpcGoSvc ics regs tys name with
  | some e => some e
  | none => (sms.find? (fun m => decide (m.name = name))).map fun m =>
      .stream ⟨m.Req.wire, m.Rep.wire, m.Up, m.dn, m.spec⟩

theorem grpcStartSvc_go (ics : List GoFunc) (regs : List (GoString × GoFunc × GoInterface))
    (tys : GoString → Option (ProtoMsgT GF × ProtoMsgT GF)) (sms : List (GrpcStreamMethod GF))
    (name : GoString) (e : GrpcSvcEntry GF) (h : grpcGoSvc ics regs tys name = some e) :
    grpcStartSvc ics regs tys sms name = some e := by
  simp only [grpcStartSvc, h]

theorem grpcGoSvc_none (ics : List GoFunc) (regs : List (GoString × GoFunc × GoInterface))
    (tys : GoString → Option (ProtoMsgT GF × ProtoMsgT GF)) (name : GoString)
    (h : name ∉ regs.map Prod.fst) : grpcGoSvc ics regs tys name = none := by
  simp [grpcGoSvc, h]

/-- An entry of `grpcGoSvc` is a registered unary method's, at the models `tys` gives. -/
theorem grpcGoSvc_inv (ics : List GoFunc) (regs : List (GoString × GoFunc × GoInterface))
    (tys : GoString → Option (ProtoMsgT GF × ProtoMsgT GF)) (name : GoString)
    (ent : GrpcSvcEntry GF) (h : grpcGoSvc ics regs tys name = some ent) :
    name ∈ regs.map Prod.fst ∧ ∃ Req Rep, tys name = some (Req, Rep) ∧
      ent = .unary (grpcGoEntry ics regs name Req Rep) := by
  unfold grpcGoSvc at h
  by_cases hm : name ∈ regs.map Prod.fst
  · simp only [hm, if_true, Option.map_eq_some_iff] at h
    obtain ⟨⟨Req, Rep⟩, hty, rfl⟩ := h
    exact ⟨hm, Req, Rep, hty, rfl⟩
  · simp [hm] at h

/-- A stream of `sms`, registered, whose name no other stream of `sms` has, is `grpcStartSvc`'s
entry for its name. -/
theorem grpcStartSvc_stream (ics : List GoFunc) (regs sregs : List (GoString × GoFunc × GoInterface))
    (tys : GoString → Option (ProtoMsgT GF × ProtoMsgT GF)) (sms : List (GrpcStreamMethod GF))
    (hsms : ∀ m ∈ sms, (m.name, m.handler, m.srv) ∈ sregs) (hsnd : (sms.map (·.name)).Nodup)
    (hnd : ((regs ++ sregs).map Prod.fst).Nodup) (m : GrpcStreamMethod GF) (hm : m ∈ sms) :
    grpcStartSvc ics regs tys sms m.name = some (.stream ⟨m.Req.wire, m.Rep.wire, m.Up, m.dn, m.spec⟩) := by
  have hnr : m.name ∉ regs.map Prod.fst := by
    intro hr
    rw [List.map_append] at hnd
    exact (List.nodup_append.mp hnd).2.2 m.name hr m.name
      (List.mem_map.2 ⟨_, hsms m hm, rfl⟩) rfl
  have hfind : sms.find? (fun m' => decide (m'.name = m.name)) = some m := by
    cases hf : sms.find? (fun m' => decide (m'.name = m.name)) with
    | none =>
      rw [List.find?_eq_none] at hf
      exact absurd (by simp) (hf m hm)
    | some m' =>
      have h1 := List.find?_some hf
      have h2 := List.mem_of_find?_eq_some hf
      simp only [decide_eq_true_eq] at h1
      have h3 : m' = m := grpc_inj_of_nodup_map (fun x : GrpcStreamMethod GF => x.name) sms hsnd m' h2 m hm h1
      rw [h3]
  simp [grpcStartSvc, grpcGoSvc_none ics regs tys m.name hnr, hfind]

/-- An entry of `grpcStartSvc` is `grpcGoSvc`'s, or a stream of `sms`'s at its name. -/
theorem grpcStartSvc_inv (ics : List GoFunc) (regs : List (GoString × GoFunc × GoInterface))
    (tys : GoString → Option (ProtoMsgT GF × ProtoMsgT GF)) (sms : List (GrpcStreamMethod GF))
    (name : GoString) (ent : GrpcSvcEntry GF) (h : grpcStartSvc ics regs tys sms name = some ent) :
    grpcGoSvc ics regs tys name = some ent ∨
      ∃ m ∈ sms, m.name = name ∧ ent = .stream ⟨m.Req.wire, m.Rep.wire, m.Up, m.dn, m.spec⟩ := by
  unfold grpcStartSvc at h
  cases hg : grpcGoSvc ics regs tys name with
  | some e =>
    simp only [hg] at h
    left
    exact h
  | none =>
    simp only [hg, Option.map_eq_some_iff] at h
    right
    obtain ⟨m, hf, rfl⟩ := h
    have h1 := List.find?_some hf
    simp only [decide_eq_true_eq] at h1
    exact ⟨m, List.mem_of_find?_eq_some hf, h1, rfl⟩

/-- **Go's configuration serves its table** (one process): a unary entry of `grpcStartSvc` is a
registered unary method's, so it names no stream (distinct full names), at the models `tys` gives
(registered, `htys`), met by its handler (`grpcRunOkMd_goEntry`); a stream entry is a registered
stream's of `sms`, so it names no unary method, at its registered models, with the identity
conversions, met by its handler (the premise). -/
theorem grpcServes_start (ics sics : List GoFunc) (regs sregs : List (GoString × GoFunc × GoInterface))
    (tys : GoString → Option (ProtoMsgT GF × ProtoMsgT GF))
    (htys : ∀ n Req Rep, tys n = some (Req, Rep) →
      grpcReqModelOf GF Req.ty = some Req ∧ grpcRepModelOf GF Rep.ty = some Rep)
    (sms : List (GrpcStreamMethod GF)) (hsms : ∀ m ∈ sms, (m.name, m.handler, m.srv) ∈ sregs)
    (hnd : ((regs ++ sregs).map Prod.fst).Nodup) :
    □ ([∗list] m ∈ sms, grpcStreamRunOk #m.handler m.srv sics m.Up m.spec ∗
        □ ∀ md γ, m.spec md γ (m.dn md γ)) ⊢
    grpcServes (grpcStartSvc ics regs tys sms) ics sics regs sregs := by
  iintro #Hms
  unfold grpcServes
  iintro !> %name %ent %he
  rcases grpcStartSvc_inv ics regs tys sms name ent he with hg | ⟨m, hm, rfl, rfl⟩
  · obtain ⟨hmem, Req, Rep, hty, rfl⟩ := grpcGoSvc_inv ics regs tys name ent hg
    simp only [grpcServesEnt]
    isplitr
    · ipureintro
      intro hs
      rw [List.map_append] at hnd
      exact (List.nodup_append.mp hnd).2.2 name hmem name hs rfl
    iintro %mh %srv %hin
    iexists Req, Rep, (grpcGoEntry ics regs name Req Rep).spec
    isplitr
    · ipureintro
      exact ⟨(htys name Req Rep hty).1, (htys name Req Rep hty).2, rfl⟩
    iapply grpcRunOkMd_goEntry ics regs sregs name mh srv Req Rep hnd hin
  · simp only [grpcServesEnt]
    isplitr
    · ipureintro
      intro hr
      rw [List.map_append] at hnd
      exact (List.nodup_append.mp hnd).2.2 m.name hr m.name
        (List.mem_map.2 ⟨_, hsms m hm, rfl⟩) rfl
    iintro %mh %srv %hin
    obtain ⟨rfl, rfl⟩ := grpc_sregs_unique regs sregs m.name m.handler mh m.srv srv hnd (hsms m hm) hin
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hm
    ihave #Hm := BigSepL.bigSepL_lookup (Φ := fun _ (m : GrpcStreamMethod GF) =>
      iprop(grpcStreamRunOk #m.handler m.srv sics m.Up m.spec ∗ □ ∀ md γ, m.spec md γ (m.dn md γ)))
      hi $$ Hms
    icases Hm with ⟨#Hrun, #Hsp⟩
    iexists m.Req, m.Rep, m.Up, m.dn, m.spec, m.Up, m.spec, m.dn
    isplitr
    · ipureintro
      exact ⟨m.reqReg, m.repReg, rfl⟩
    isplitr
    · imodintro
      iintro %i %x Hx
      iexact Hx
    isplitr
    · iexact Hsp
    isplitr
    · imodintro
      iintro %md %γ %j %x Hx
      iexact Hx
    iexact Hrun

/-- **The server listening at `addr` serves Go's configuration, with the unary chain `ics`, the unary
methods `regs` at the models `tys`, and the streams `sms`** (persistent): `addr`'s table is `grpcStartSvc ics regs tys sms`. Made by `grpc.start'`. -/
def grpcServerAt (addr : GoString) (ics : List GoFunc)
    (regs : List (GoString × GoFunc × GoInterface))
    (tys : GoString → Option (ProtoMsgT GF × ProtoMsgT GF)) (sms : List (GrpcStreamMethod GF)) :
    IProp GF :=
  iprop(∃ (_ : HasExt netExt) (π : NetProtoGS) (σ : NetSlotGS),
    grpcAddrAt (Gg := hG.goose_globalGS) (π := π) (σ := σ) addr (grpcStartSvc ics regs tys sms))

instance grpcServerAt_persistent (addr : GoString) (ics : List GoFunc)
    (regs : List (GoString × GoFunc × GoInterface))
    (tys : GoString → Option (ProtoMsgT GF × ProtoMsgT GF)) (sms : List (GrpcStreamMethod GF)) :
    Persistent (grpcServerAt (GF := GF) addr ics regs tys sms) := by
  unfold grpcServerAt; infer_instance

/-- **Serving** (a theorem): the methods `ms` of the server at `addr` with the unary chain
`ics`, the registrations `regs` and the table's models `tys` (`grpcServerAt`, made by `grpc.start'`),
each registered with its handler and service, at its models, and meeting its run contract
(`grpcRunOkMd`), are registered at `addr` (`isGrpcRpcMd`): the table's entry is met by the method's
spec (`grpcSvcAt_of_addr`, `grpcSvcAt_mono_upd`). What runs the handlers is `Server.Serve` (its
trust-boundary axiom). -/
theorem grpc.serve (addr : GoString) (ics : List GoFunc)
    (regs : List (GoString × GoFunc × GoInterface))
    (tys : GoString → Option (ProtoMsgT GF × ProtoMsgT GF)) (sms : List (GrpcStreamMethod GF))
    (ms : List (GrpcMethod GF)) :
    (∀ m ∈ ms, (m.name, m.handler, m.srv) ∈ regs) →
    (∀ m ∈ ms, tys m.name = some (m.Req, m.Rep)) →
    grpcServerAt addr ics regs tys sms ∗
      □ ([∗list] m ∈ ms, grpcRunOkMd #m.handler m.srv ics m.spec) ⊢
    |={⊤}=> [∗list] m ∈ ms, isGrpcRpcMd addr m.name m.spec := by
  intro hreg hty
  iintro ⟨#Hs, #Hms⟩
  iunfold grpcServerAt at Hs
  icases Hs with ⟨%hX, %π, %σ, #Ha⟩
  imodintro
  have Hm : iprop(□ grpcAddrAt (Gg := hG.goose_globalGS) (π := π) (σ := σ) addr
      (grpcStartSvc ics regs tys sms)) ⊢
      [∗list] m ∈ ms, (grpcRunOkMd #m.handler m.srv ics m.spec -∗ isGrpcRpcMd addr m.name m.spec) :=
    BigSepL.bigSepL_intro (fun _ m hk => by
      have hm : m ∈ ms := List.mem_of_getElem? hk
      have he := grpcStartSvc_go ics regs tys sms m.name _
        (grpcGoSvc_some ics regs tys m.name m.handler m.srv m.Req m.Rep (hreg m hm) (hty m hm))
      have Hg' : grpcAddrAt (Gg := hG.goose_globalGS) (π := π) (σ := σ) addr
          (grpcStartSvc ics regs tys sms) ⊢
          grpcSvcAt (Gg := hG.goose_globalGS) (π := π) (σ := σ) addr m.name m.Req.toProtoMsg.wire
            m.Rep.toProtoMsg.wire (grpcGoEntry ics regs m.name m.Req m.Rep).spec :=
        grpcSvcAt_of_addr (Gg := hG.goose_globalGS) addr m.name (grpcStartSvc ics regs tys sms)
          (grpcGoEntry ics regs m.name m.Req m.Rep) he
      iintro #Ha #Hr
      ihave #Hg := Hg' $$ Ha
      unfold isGrpcRpcMd
      iexists hX, π, σ
      iapply (grpcSvcAt_mono_upd (Gg := hG.goose_globalGS) addr m.name m.Req.toProtoMsg.wire
        m.Rep.toProtoMsg.wire (grpcGoEntry ics regs m.name m.Req m.Rep).spec m.spec) $$ [] Hg
      imodintro
      iintro %md %x %Φ %Ψe HS
      imodintro
      unfold grpcGoEntry
      iexists m.handler, m.srv, m.spec
      isplitr
      · ipureintro; exact hreg m hm
      iframe HS
      iexact Hr)
  ihave Hw := Hm $$ []
  · imodintro; iexact Ha
  iapply BigSepL.bigSepL_wand $$ Hms Hw

/-- **The single-process start, over either form of the server at its listener** (`grpc.start'` and
`grpc.startBound` are its two instances; see `grpc.start'`). -/
theorem grpc.startCore (gs : Loc) (lis : GoInterface) (addr : GoString) (ics sics : List GoFunc)
    (svcs : List GoString) (regs sregs : List (GoString × GoFunc × GoInterface))
    (tys : GoString → Option (ProtoMsgT GF × ProtoMsgT GF))
    (htys : ∀ n Req Rep, tys n = some (Req, Rep) →
      grpcReqModelOf GF Req.ty = some Req ∧ grpcRepModelOf GF Rep.ty = some Rep)
    (sms : List (GrpcStreamMethod GF)) (hsms : ∀ m ∈ sms, (m.name, m.handler, m.srv) ∈ sregs)
    (hsnd : (sms.map (·.name)).Nodup)
    (hfit : grpcRepliesFit) (hnd : ((regs ++ sregs).map Prod.fst).Nodup) :
    ((grpcSrvNew (GF := GF) gs ics sics svcs regs sregs ∗ netListenerOpen lis addr) ∨
        grpcSrvAtLis gs lis addr ics sics svcs regs sregs) ∗ netAddrLeft addr ∗
      □ ([∗list] m ∈ sms, grpcStreamRunOk #m.handler m.srv sics m.Up m.spec ∗
          □ ∀ md γ, m.spec md γ (m.dn md γ)) ⊢
    |={⊤}=> grpcServerAt addr ics regs tys sms ∗
      ([∗list] m ∈ sms, isGrpcStreamMd addr m.name m.Up m.spec) ∗
      grpcServeTok gs lis addr (grpcStartSvc ics regs tys sms) := by
  iintro ⟨Hn, Hleft, #Hms⟩
  iunfold netAddrLeft at Hleft
  icases Hleft with ⟨%hX, Hp, #Hv, #Hti⟩
  imod netProto_alloc (Gg := hG.goose_globalGS) ⊤ with ⟨%π, #Hreg⟩
  imod depSlots_alloc (Gg := hG.goose_globalGS) ⊤ with ⟨%σ, #Hsl⟩
  imod addr_set_proto_tok (Gg := hG.goose_globalGS) ⊤ addr (grpcCliPI (grpcStartSvc ics regs tys sms))
    (grpcSrvPI (grpcStartSvc ics regs tys sms)) $$ Hreg Hp Hv Hti with #Hpr
  ihave #Ha : grpcAddrAt (Gg := hG.goose_globalGS) (π := π) (σ := σ) addr
      (grpcStartSvc ics regs tys sms) $$ []
  · unfold grpcAddrAt; iframe Hpr Hsl
  ihave #Hsv := (grpcServes_start ics sics regs sregs tys htys sms hsms hnd) $$ Hms
  imodintro
  isplitr [Hn]
  · unfold grpcServerAt
    iexists hX, π, σ
    iexact Ha
  isplitr [Hn]
  · have Hm : iprop(□ grpcAddrAt (Gg := hG.goose_globalGS) (π := π) (σ := σ) addr
        (grpcStartSvc ics regs tys sms)) ⊢
        [∗list] m ∈ sms, ((grpcStreamRunOk #m.handler m.srv sics m.Up m.spec ∗
          □ ∀ md γ, m.spec md γ (m.dn md γ)) -∗ isGrpcStreamMd addr m.name m.Up m.spec) :=
      BigSepL.bigSepL_intro (fun _ m hk => by
        have hm : m ∈ sms := List.mem_of_getElem? hk
        have he := grpcStartSvc_stream ics regs sregs tys sms hsms hsnd hnd m hm
        iintro #Ha ⟨-, #Hsp⟩
        iapply (isGrpcStreamMd_of_addr (Req := m.Req.toStreamMsg) (Rep := m.Rep.toStreamMsg)
          addr m.name (grpcStartSvc ics regs tys sms) m.Up m.dn m.spec he) $$ [Ha Hsp]
        iframe Ha Hsp)
    ihave Hw := Hm $$ []
    · imodintro; iexact Ha
    iapply BigSepL.bigSepL_wand $$ Hms Hw
  unfold grpcServeTok
  iexists ({ ics := ics, sics := sics, regs := regs, sregs := sregs } : GrpcSrvCfg GF), svcs
  isplitl [Hn]
  · iexact Hn
  isplitr
  · ipureintro
    exact hnd
  isplitr
  · ileft; ipureintro; exact hfit
  isplitr
  · iexists hX, π, σ
    iexact Ha
  iexact Hsv

/-- **The single-process start** (a theorem): the server being built and a listener bound at `addr`, with what `Listen`
left (`netAddrLeft`), set `addr`'s table to Go's configuration (`grpcStartSvc ics regs tys sms`: the
unary methods `tys` gives models for, and the streams `sms`), in one ghost step that allocates the net
library's registry and slot map (`netProto_alloc`, `depSlots_alloc`), and give: the server at `addr`
(`grpcServerAt`, for `grpc.serve`), the streams' registrations (`isGrpcStreamMd`), and the right to
serve it (`grpcServeTok`). Each stream of `sms` is registered (`hsms`), of a name no other has
(`hsnd`), met by its handler as a run, its specification holding at its content `dn`. -/
theorem grpc.start' (gs : Loc) (lis : GoInterface) (addr : GoString) (ics sics : List GoFunc)
    (svcs : List GoString) (regs sregs : List (GoString × GoFunc × GoInterface))
    (tys : GoString → Option (ProtoMsgT GF × ProtoMsgT GF))
    (htys : ∀ n Req Rep, tys n = some (Req, Rep) →
      grpcReqModelOf GF Req.ty = some Req ∧ grpcRepModelOf GF Rep.ty = some Rep)
    (sms : List (GrpcStreamMethod GF)) (hsms : ∀ m ∈ sms, (m.name, m.handler, m.srv) ∈ sregs)
    (hsnd : (sms.map (·.name)).Nodup)
    (hfit : grpcRepliesFit) (hnd : ((regs ++ sregs).map Prod.fst).Nodup) :
    grpcSrvNew (GF := GF) gs ics sics svcs regs sregs ∗ netListenerAt lis addr ∗ netAddrLeft addr ∗
      □ ([∗list] m ∈ sms, grpcStreamRunOk #m.handler m.srv sics m.Up m.spec ∗
          □ ∀ md γ, m.spec md γ (m.dn md γ)) ⊢
    |={⊤}=> grpcServerAt addr ics regs tys sms ∗
      ([∗list] m ∈ sms, isGrpcStreamMd addr m.name m.Up m.spec) ∗
      grpcServeTok gs lis addr (grpcStartSvc ics regs tys sms) := by
  iintro ⟨Hn, Hl, Hleft, #Hms⟩
  iunfold netListenerAt at Hl
  icases Hl with ⟨-, Hl⟩
  iapply (grpc.startCore gs lis addr ics sics svcs regs sregs tys htys sms hsms hsnd hfit hnd)
  iframe Hleft Hms
  ileft
  iframe

/-- **The single-process start of a server certified at its listener** (`grpcSrvAtLis`): as
`grpc.start'`. -/
theorem grpc.startBound (gs : Loc) (lis : GoInterface) (addr : GoString) (ics sics : List GoFunc)
    (svcs : List GoString) (regs sregs : List (GoString × GoFunc × GoInterface))
    (tys : GoString → Option (ProtoMsgT GF × ProtoMsgT GF))
    (htys : ∀ n Req Rep, tys n = some (Req, Rep) →
      grpcReqModelOf GF Req.ty = some Req ∧ grpcRepModelOf GF Rep.ty = some Rep)
    (sms : List (GrpcStreamMethod GF)) (hsms : ∀ m ∈ sms, (m.name, m.handler, m.srv) ∈ sregs)
    (hsnd : (sms.map (·.name)).Nodup)
    (hfit : grpcRepliesFit) (hnd : ((regs ++ sregs).map Prod.fst).Nodup) :
    grpcSrvAtLis (GF := GF) gs lis addr ics sics svcs regs sregs ∗ netAddrLeft addr ∗
      □ ([∗list] m ∈ sms, grpcStreamRunOk #m.handler m.srv sics m.Up m.spec ∗
          □ ∀ md γ, m.spec md γ (m.dn md γ)) ⊢
    |={⊤}=> grpcServerAt addr ics regs tys sms ∗
      ([∗list] m ∈ sms, isGrpcStreamMd addr m.name m.Up m.spec) ∗
      grpcServeTok gs lis addr (grpcStartSvc ics regs tys sms) := by
  iintro ⟨Hn, Hleft, #Hms⟩
  iapply (grpc.startCore gs lis addr ics sics svcs regs sregs tys htys sms hsms hsnd hfit hnd)
  iframe Hleft Hms
  iright
  iexact Hn

end reg

/-! ## The adapters: a handler's bundle from leveled pools -/

section adapt
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- Levels 0 to 3 of a thread token, and the rest. -/
theorem threadTok_levels0123 (HT : 4 ≤ threadBound GF) :
    threadTok (GF := GF) ⊣⊢ levelTok 0 ∗ levelTok 1 ∗ levelTok 2 ∗ levelTok 3 ∗ threadTokFrom 4 := by
  constructor
  · iintro H
    icases (threadTok_level0 (GF := GF)).1 $$ H with ⟨H0, H⟩
    icases (threadTokFrom_succ (GF := GF) 1 (by omega)).1 $$ H with ⟨H1, H⟩
    icases (threadTokFrom_succ (GF := GF) 2 (by omega)).1 $$ H with ⟨H2, H⟩
    icases (threadTokFrom_succ (GF := GF) 3 (by omega)).1 $$ H with ⟨H3, H⟩
    iframe
  · iintro ⟨H0, H1, H2, H3, H4⟩
    iapply (threadTok_level0 (GF := GF)).2
    iframe H0
    iapply (threadTokFrom_succ (GF := GF) 1 (by omega)).2
    iframe H1
    iapply (threadTokFrom_succ (GF := GF) 2 (by omega)).2
    iframe H2
    iapply (threadTokFrom_succ (GF := GF) 3 (by omega)).2
    iframe

/-- **The unary adapter** (Scope r5 §3.4, A4-MAJ-3): a handler proved against `grpcMethodOkMd` at
a bundle `levelTok 0 ∗ R₁ ∗ R₂ ∗ R₃` (the run's own level 0, per-type stage B3: the lease handlers'
level-0 pools, and three leveled pools, levels 1, 2, 3; abstract `IProp`s, not known timeless) meets
the run contract: the run borrows each pool with its token's level (each loan gives
`▷ Rᵢ`), strips the joined later with the run's one credit, runs the handler, and gives the loans
back. Generic in the pools: B2/B3 instantiate it with `raftPool`, `I` and the run pool. -/
theorem grpcRunOkMd_of_pools {Req Rep : ProtoMsg GF} (mh : val) (srv : GoInterface)
    (ics : List GoFunc) (Spec : GrpcSpecMd Req Rep) (R₁ R₂ R₃ : IProp GF)
    (N₁ N₂ N₃ : Namespace) (γ₁ γ₂ γ₃ : GName) (HT : 4 ≤ threadBound GF) :
    □ grpcMethodOkMd mh srv ics iprop(levelTok 0 ∗ R₁ ∗ R₂ ∗ R₃) Spec ∗
      threadPool.isThreadPoolL N₁ 1 γ₁ R₁ ∗ threadPool.isThreadPoolL N₂ 2 γ₂ R₂ ∗
      threadPool.isThreadPoolL N₃ 3 γ₃ R₃ ⊢
    grpcRunOkMd mh srv ics Spec := by
  iintro ⟨#Hm, #Hp1, #Hp2, #Hp3⟩
  iunfold grpcMethodOkMd at Hm
  unfold grpcRunOkMd
  iintro %m %Φ %Ψe %ci %cd %dec %ui !> %Ψ ⟨Htok, Hlc, Hctx, Hrc, Hd, Hch, HSpec⟩ HΨ
  icases (threadTok_levels0123 (GF := GF) HT).1 $$ Htok with ⟨H0, H1, H2, H3, H4⟩
  imod threadPool.borrowL N₁ 1 γ₁ R₁ ⊤ (fun _ _ => CoPset.mem_full) $$ [Hp1 H1] with ⟨HR1, Hl1⟩
  · iframe; iframe #
  imod threadPool.borrowL N₂ 2 γ₂ R₂ ⊤ (fun _ _ => CoPset.mem_full) $$ [Hp2 H2] with ⟨HR2, Hl2⟩
  · iframe; iframe #
  imod threadPool.borrowL N₃ 3 γ₃ R₃ ⊤ (fun _ _ => CoPset.mem_full) $$ [Hp3 H3] with ⟨HR3, Hl3⟩
  · iframe; iframe #
  ihave HR : iprop(▷ (R₁ ∗ R₂ ∗ R₃)) $$ [HR1 HR2 HR3]
  · inext; iframe
  imod lc_fupd_elim_later (E := ⊤) $$ Hlc HR with HR
  iapply wp_fupd
  iapply Hm $$ %m %Φ %Ψe %ci %cd %dec %ui [H0 HR Hctx Hrc Hd Hch HSpec]
  · iframe
  inext
  iintro %resp %err ⟨⟨H0, HB1, HB2, HB3⟩, Hok, Herr, Hsrv⟩
  imod threadPool.giveBackL N₁ 1 γ₁ R₁ ⊤ (fun _ _ => CoPset.mem_full) $$ [Hp1 Hl1 HB1] with H1
  · iframe; iframe #
  imod threadPool.giveBackL N₂ 2 γ₂ R₂ ⊤ (fun _ _ => CoPset.mem_full) $$ [Hp2 Hl2 HB2] with H2
  · iframe; iframe #
  imod threadPool.giveBackL N₃ 3 γ₃ R₃ ⊤ (fun _ _ => CoPset.mem_full) $$ [Hp3 Hl3 HB3] with H3
  · iframe; iframe #
  imodintro
  iapply HΨ
  iframe
  iapply (threadTok_levels0123 (GF := GF) HT).2
  iframe

/-- An update before a stream chain's call is absorbed (`fupd_wp` at the chain's first call). -/
theorem srvStreamChainWP_fupd (R : IProp GF) (info : val) (ics : List GoFunc) (h srv st : val)
    (Ψ : val → IProp GF) :
    (|={⊤}=> srvStreamChainWP R info ics h srv st Ψ) ⊢ srvStreamChainWP R info ics h srv st Ψ := by
  cases ics with
  | nil =>
    unfold srvStreamChainWP
    iintro H HR
    iapply fupd_wp
    imod H
    imodintro
    iapply H $$ HR
  | cons ic ics =>
    unfold srvStreamChainWP
    iintro H %h' #Hh' HR
    iapply fupd_wp
    imod H
    imodintro
    iapply H $$ %h' Hh' HR

/-- A stream chain's postcondition may be weakened, with an update (`Ψ` is only its first call's
postcondition). -/
theorem srvStreamChainWP_wand (R : IProp GF) (info : val) (ics : List GoFunc) (h srv st : val)
    (Ψ Ψ' : val → IProp GF) :
    srvStreamChainWP R info ics h srv st Ψ ∗ (∀ v, Ψ v -∗ |={⊤}=> Ψ' v) ⊢
      srvStreamChainWP R info ics h srv st Ψ' := by
  cases ics with
  | nil =>
    unfold srvStreamChainWP
    iintro ⟨H, Hw⟩ HR
    iapply wp_fupd
    iapply wp_wand $$ [H HR]
    · iapply H $$ HR
    iintro %v ⟨HR, HΨ⟩
    imod Hw $$ HΨ
    imodintro
    iframe
  | cons ic ics =>
    unfold srvStreamChainWP
    iintro ⟨H, Hw⟩ %h' #Hh' HR
    iapply wp_fupd
    iapply wp_wand $$ [H HR]
    · iapply H $$ %h' Hh' HR
    iintro %v ⟨HR, HΨ⟩
    imod Hw $$ HΨ
    imodintro
    iframe

/-- **The stream adapter** (Scope r5 §3.4; B1b): a stream handler proved against
`grpcStreamMethodOk` at a bundle `levelTok 0 ∗ levelTok 4 ∗ R₁ ∗ R₂ ∗ R₃` (the run's own level 0,
B3; its level 4, which the handler lends a weak context's `Err()`, k8s 7f-4, Freeze addendum T-f';
and three leveled pools, levels 1, 2, 3), which it returns, meets the stream run contract: the run
borrows each pool with its token's level, strips the joined later with the run's one credit, runs
the chain, and gives the loans back. Generic in the pools, as `grpcRunOkMd_of_pools`. -/
theorem grpcStreamRunOk_of_pools {Req Rep : StreamMsg GF} (mh : val) (srv : GoInterface)
    (sics : List GoFunc) (Up : Nat → Req.M → IProp GF) (Spec : GrpcMd → StreamSpec Rep)
    (R₁ R₂ R₃ : IProp GF) (N₁ N₂ N₃ : Namespace) (γ₁ γ₂ γ₃ : GName) (HT : 5 ≤ threadBound GF) :
    □ grpcStreamMethodOk mh srv sics iprop(levelTok 0 ∗ levelTok 4 ∗ R₁ ∗ R₂ ∗ R₃) Up Spec ∗
      threadPool.isThreadPoolL N₁ 1 γ₁ R₁ ∗ threadPool.isThreadPoolL N₂ 2 γ₂ R₂ ∗
      threadPool.isThreadPoolL N₃ 3 γ₃ R₃ ⊢
    grpcStreamRunOk mh srv sics Up Spec := by
  iintro ⟨#Hm, #Hp1, #Hp2, #Hp3⟩
  iunfold grpcStreamMethodOk at Hm
  icases Hm with ⟨-, #Hr⟩
  unfold grpcStreamRunOk
  iintro !> %γ %Dn %ci %cd %st %info HSp Htok Hlc Hraw HR HT' Ha Hi
  iapply srvStreamChainWP_fupd
  icases (threadTok_levels0123 (GF := GF) (by omega)).1 $$ Htok with ⟨H0, H1, H2, H3, H4⟩
  icases (threadTokFrom_succ (GF := GF) 4 (by omega)).1 $$ H4 with ⟨H4, H5⟩
  imod threadPool.borrowL N₁ 1 γ₁ R₁ ⊤ (fun _ _ => CoPset.mem_full) $$ [Hp1 H1] with ⟨HR1, Hl1⟩
  · iframe; iframe #
  imod threadPool.borrowL N₂ 2 γ₂ R₂ ⊤ (fun _ _ => CoPset.mem_full) $$ [Hp2 H2] with ⟨HR2, Hl2⟩
  · iframe; iframe #
  imod threadPool.borrowL N₃ 3 γ₃ R₃ ⊤ (fun _ _ => CoPset.mem_full) $$ [Hp3 H3] with ⟨HR3, Hl3⟩
  · iframe; iframe #
  ihave HRs : iprop(▷ (R₁ ∗ R₂ ∗ R₃)) $$ [HR1 HR2 HR3]
  · inext; iframe
  imod lc_fupd_elim_later (E := ⊤) $$ Hlc HRs with HRs
  imodintro
  iapply srvStreamChainWP_wand
  ihave HRs : iprop(levelTok 0 ∗ levelTok 4 ∗ R₁ ∗ R₂ ∗ R₃) $$ [H0 H4 HRs]
  · iframe
  isplitl [HSp HRs Hraw HR HT' Ha Hi]
  · iapply Hr $$ HSp HRs Hraw HR HT' Ha Hi
  iintro %v ⟨%err, %Hv, #Hse, ⟨H0, H4, HB1, HB2, HB3⟩⟩
  imod threadPool.giveBackL N₁ 1 γ₁ R₁ ⊤ (fun _ _ => CoPset.mem_full) $$ [Hp1 Hl1 HB1] with H1
  · iframe; iframe #
  imod threadPool.giveBackL N₂ 2 γ₂ R₂ ⊤ (fun _ _ => CoPset.mem_full) $$ [Hp2 Hl2 HB2] with H2
  · iframe; iframe #
  imod threadPool.giveBackL N₃ 3 γ₃ R₃ ⊤ (fun _ _ => CoPset.mem_full) $$ [Hp3 Hl3 HB3] with H3
  · iframe; iframe #
  imodintro
  iexists err
  isplitr
  · ipureintro; exact Hv
  iframe Hse
  iapply (threadTok_levels0123 (GF := GF) (by omega)).2
  iframe
  iapply (threadTokFrom_succ (GF := GF) 4 (by omega)).2
  iframe

end adapt


end EtcdGrove
end Perennial
