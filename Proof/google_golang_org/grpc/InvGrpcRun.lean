/-
**grpc's server: the right to serve and the start** (per-type stage B, B1a, 2026-11-11; Scope r5
§2.1-2.2; restated at phase 7 S2's interface, 2026-11-24; Lean-first, no Rocq counterpart).

**Go's configuration as a trusted fact.** `grpc.start` (`InvGrpcServer.lean`) emits, from the server
being built (`grpcSrvNew gs ics sics svcs regs sregs`), a persistent `grpcSrvCfg γ c`: the chains and
registrations Go's server holds (`GrpcSrvCfg`), fixed from `Serve` on (grpc's `RegisterService`
after `Serve` is fatal), beside `grpcAddrIs addr γ` (the server listening at `addr` is `γ`) and the
exclusive `grpcSrvLink gs lis γ`. A proof cannot choose `c`: it is made only by `grpc.start`, from
`grpcSrvNew`, and is unique per `γ` (`grpcSrvCfg_agree`); `γ` is unique per address
(`grpcAddrIs_agree`).

**The service table** (S2's interface). A unary registration is heap-free: `isGrpcRpcMd addr name
Spec` (`InvGrpc.lean`) says dialing `addr` reaches an address `a₀` whose table `Svc`, set once with
its protocols (`grpcAddrAt`, `InvGrpcWire.lean`), has an entry for `name` that `Spec`'s callers meet.
What makes this sound is `Server.Serve`'s axiom, which takes `grpcServeTok gs lis a Svc`: Go's
configuration (started, or being built with the node's open listener), `a` serving `Svc`, and
`grpcServes Svc`: every entry names no stream (C3) and, for each unary method `gs` registers under
its name, is met by Go's handler as a run (`grpcRunOkMd`, the run contract: a run is given the
fork's thread token and one later credit, returns the token), at the registered message models.
`Serve`'s post is `True`; its axiom says the server meets `Svc` on every connection to `a`, as the
opaque protocols `grpcCliPI Svc`/`grpcSrvPI Svc` state it: no program but grpc's transport writes
or reads such a connection meaningfully (`notes/axiom-review/s2-interface.md`, C1 and C2).

**One process.** The single-process start (`grpc.start'`) sets the address's table to Go's
configuration (`grpcGoSvc ics regs tys`, `InvGrpc.lean`: an entry for each registered unary method
`tys` gives registered models, whose spec is some spec its handler's run contract meets) from what
`Listen` left (`netAddrLeft`), allocating the net library's registry and slot map in the same ghost
step, and proves `grpcServes` of it (`grpcServes_go`); `grpc.serve` (a theorem) then registers each
method at the spec it is proved at.

**Streams** stay on the pair until S3: `NewStream`'s post and the server end share the stream's names
`γs`, `Dn` and the persistent `Spec md γs Dn`; the stream registration (`isGrpcStreamAt γ`, a WP of
the handler at the server's heap) is of a started server (`grpcServeTok`'s first disjunct), and
`Serve`'s axiom runs a stream as `ClientConn.NewStream`'s post pairs it (`InvGrpcStream.lean`).

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
dispatch), `grpcSrvChainAll c.ics`, `grpcSrvStreamChainAll c.sics`, `grpcDecOk`, `grpcRunCtx`. Until
S2's interface the server half was the trusted model `Serve` (`Server.Serve.impl := model.Serve`)
and its leaves' axioms (`acceptRun`, `acceptRunConns`, `respond`, `finishStream`, with
`grpcAccepted`, `grpcReplyTo`, `grpcConnsLink`), now retired.
-/
module

public import Proof.google_golang_org.grpc.InvGrpcServer
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

theorem grpc_inj_of_nodup_map {α β : Type} (f : α → β) :
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

/-- **`gs` serves the table `Svc` with Go's chain `ics`, methods `regs` and streams `sregs`**
(persistent; phase 7 S2's interface, 2026-11-24): every entry of `Svc` names no stream (C3 of
`notes/axiom-review/s2-interface.md`: a unary call of a stream's name would run the stream's
handler), and a unary method `gs` registers under its name has that entry, at its registered message
models, met by its handler as a run (`grpcRunOkMd`). An entry `gs` does not register gets grpc's
`Unimplemented` (no handler's description). -/
def grpcServes (Svc : GrpcSvc GF) (ics : List GoFunc)
    (regs sregs : List (GoString × GoFunc × GoInterface)) : IProp GF :=
  iprop(□ ∀ (name : GoString) (e : GrpcEntry GF), ⌜Svc name = some e⌝ -∗
    ⌜name ∉ sregs.map Prod.fst⌝ ∗
    ∀ (mh : GoFunc) (srv : GoInterface), ⌜(name, mh, srv) ∈ regs⌝ -∗
      ∃ (Req Rep : ProtoMsgT GF) (Spec : GrpcSpecMd Req.toProtoMsg Rep.toProtoMsg),
        ⌜grpcReqModelOf GF Req.ty = some Req ∧ grpcRepModelOf GF Rep.ty = some Rep ∧
          e = ⟨Req.toProtoMsg.wire, Rep.toProtoMsg.wire, Spec⟩⌝ ∗
        grpcRunOkMd #mh srv ics Spec)

instance grpcServes_persistent (Svc : GrpcSvc GF) (ics : List GoFunc)
    (regs sregs : List (GoString × GoFunc × GoInterface)) :
    Persistent (grpcServes Svc ics regs sregs) := by
  unfold grpcServes; infer_instance

/-- **The right to serve `gs` on `lis` at `a`, for the table `Svc`** (what `gs.Serve(lis)` takes;
phase 7 S2's interface, 2026-11-24: it was `grpcServeTok gs lis γ`, the link and Go's configuration):
Go's configuration `c`, either started (`grpc.start`: `gs` and `lis` linked to the server `γ`
listening at `a`; what the stream registrations `isGrpcStreamAt γ` are about) or not (`gs` being
built, with the node's open listener at `a`: no stream registration names it); full names jointly
distinct; the replies' size premise; `a` serving `Svc` (`grpcAddrAt`); `gs` serving `Svc`
(`grpcServes`). -/
def grpcServeTok (gs : Loc) (lis : GoInterface) (a : GoString) (Svc : GrpcSvc GF) : IProp GF :=
  iprop(∃ c : GrpcSrvCfg GF,
    ((∃ γ : GName, grpcSrvLink gs lis γ ∗ grpcAddrIs a γ ∗ grpcSrvCfg γ c) ∨
     (∃ svcs : List GoString,
        grpcSrvNew gs c.ics c.sics svcs c.regs c.sregs ∗ netListenerOpen lis a)) ∗
    ⌜grpcSrvNodup c ∧ grpcRepliesFit⌝ ∗
    (∃ (_ : HasExt netExt) (π : NetProtoGS) (σ : NetSlotGS),
      grpcAddrAt (Gg := hG.goose_globalGS) (π := π) (σ := σ) a Svc) ∗
    grpcServes Svc c.ics c.regs c.sregs)

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

/-- **Go's configuration serves its table** (one process): an entry of `grpcGoSvc` is a registered
unary method's, so it names no stream (distinct full names), at the models `tys` gives (registered,
`htys`), met by its handler (`grpcRunOkMd_goEntry`). -/
theorem grpcServes_go (ics : List GoFunc) (regs sregs : List (GoString × GoFunc × GoInterface))
    (tys : GoString → Option (ProtoMsgT GF × ProtoMsgT GF))
    (htys : ∀ n Req Rep, tys n = some (Req, Rep) →
      grpcReqModelOf GF Req.ty = some Req ∧ grpcRepModelOf GF Rep.ty = some Rep)
    (hnd : ((regs ++ sregs).map Prod.fst).Nodup) :
    ⊢ grpcServes (grpcGoSvc ics regs tys) ics regs sregs := by
  unfold grpcServes
  iintro !> %name %e %he
  have hm : name ∈ regs.map Prod.fst := by
    unfold grpcGoSvc at he
    by_cases h : name ∈ regs.map Prod.fst
    · exact h
    · simp [h] at he
  obtain ⟨⟨Req, Rep⟩, hty, rfl⟩ : ∃ p, tys name = some p ∧ grpcGoEntry ics regs name p.1 p.2 = e := by
    unfold grpcGoSvc at he
    simp only [hm, if_true, Option.map_eq_some_iff] at he
    exact he
  isplitr
  · ipureintro
    intro hs
    rw [List.map_append] at hnd
    exact (List.nodup_append.mp hnd).2.2 name hm name hs rfl
  iintro %mh %srv %hin
  iexists Req, Rep, (grpcGoEntry ics regs name Req Rep).spec
  isplitr
  · ipureintro
    exact ⟨(htys name Req Rep hty).1, (htys name Req Rep hty).2, rfl⟩
  iapply grpcRunOkMd_goEntry ics regs sregs name mh srv Req Rep hnd hin

/-- **The start, packaged** (proved from `grpc.start`; since phase 7 S2's interface it also sets the
address's table): the server listening at `addr`, as the facts `grpc.serve` and `grpc.serveStream` use
(`grpcServerAt`, at the table `grpcGoSvc ics regs tys`, `grpcStreamServerAt`), and the right to serve
it (`grpcServeTok`). The table is set from what `Listen` left (`netAddrLeft`), in one ghost step that
allocates the net library's registry and slot map (`netProto_alloc`, `depSlots_alloc`); `tys` gives
the program's unary methods their registered message models (`htys`). -/
theorem grpc.start' (gs : Loc) (lis : GoInterface) (addr : GoString) (ics sics : List GoFunc)
    (svcs : List GoString) (regs sregs : List (GoString × GoFunc × GoInterface))
    (tys : GoString → Option (ProtoMsgT GF × ProtoMsgT GF))
    (htys : ∀ n Req Rep, tys n = some (Req, Rep) →
      grpcReqModelOf GF Req.ty = some Req ∧ grpcRepModelOf GF Rep.ty = some Rep)
    (hfit : grpcRepliesFit) (hnd : ((regs ++ sregs).map Prod.fst).Nodup) :
    grpcSrvNew (GF := GF) gs ics sics svcs regs sregs ∗ netListenerAt lis addr ∗ netAddrLeft addr ⊢
    |={⊤}=> ∃ γ : GName, grpcServerAt addr ics regs tys γ ∗ grpcStreamServerAt addr sics sregs γ ∗
      grpcServeTok gs lis addr (grpcGoSvc ics regs tys) := by
  iintro ⟨Hn, Hl, Hleft⟩
  iunfold netAddrLeft at Hleft
  icases Hleft with ⟨%hX, Hp, #Hv, #Hti⟩
  imod netProto_alloc (Gg := hG.goose_globalGS) ⊤ with ⟨%π, #Hreg⟩
  imod depSlots_alloc (Gg := hG.goose_globalGS) ⊤ with ⟨%σ, #Hsl⟩
  imod addr_set_proto_tok (Gg := hG.goose_globalGS) ⊤ addr (grpcCliPI (grpcGoSvc ics regs tys))
    (grpcSrvPI (grpcGoSvc ics regs tys)) $$ Hreg Hp Hv Hti with #Hpr
  ihave #Ha : grpcAddrAt (Gg := hG.goose_globalGS) (π := π) (σ := σ) addr (grpcGoSvc ics regs tys) $$ []
  · unfold grpcAddrAt; iframe Hpr Hsl
  imod (grpc.start gs lis addr ics sics svcs regs sregs hfit hnd) $$ [Hn Hl] with ⟨%γ, #Hai, #Hc, Hk⟩
  · iframe
  ihave #Hsv := grpcServes_go ics regs sregs tys htys hnd
  imodintro
  iexists γ
  unfold grpcServerAt grpcStreamServerAt grpcServeTok
  isplitr [Hk]
  · iframe Hai
    isplitr
    · iexists sics, sregs
      iexact Hc
    iexists hX, π, σ
    iexact Ha
  isplitr [Hk]
  · iframe Hai
    iexists ics, regs
    iexact Hc
  iexists ({ ics := ics, sics := sics, regs := regs, sregs := sregs } : GrpcSrvCfg GF)
  isplitl [Hk]
  · ileft
    iexists γ
    iframe Hk Hai Hc
  isplitr
  · ipureintro
    exact ⟨hnd, hfit⟩
  isplitr
  · iexists hX, π, σ
    iexact Ha
  iexact Hsv

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
  icases Hm with ⟨#Hs, #Hr⟩
  unfold grpcStreamRunOk
  iframe Hs
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
