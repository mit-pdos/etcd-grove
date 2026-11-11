/-
**grpc's runs on real forks** (per-type stage B, B1a, 2026-11-11; Scope r5 §2.1-2.2,
`/shared/tmp/stageB/scope-r5.md`; Lean-first, no Rocq counterpart). The vocabulary of the trusted
`Serve` model (`TrustedCode/google_golang_org/grpc.lean`, `Server.Serve.impl`) and of its leaves'
axioms (`Spec/google_golang_org/grpc/model/`), which replace `grpc.serve`/`grpc.serveStream`'s
caller-chosen run resource and count (`axiom/grpc-serve-pool`, `1ad2cc63a0`). B1b moved the shared
vocabulary (`GrpcSrvCfg`, the trusted predicates and their laws, the run contracts, `isGrpcRpcAt`,
`isGrpcStreamAt`) to `InvGrpc.lean`/`InvGrpcStream.lean`, where the client side and `grpc.serve`
use it; this file keeps what only the model, its leaves and the start use (`grpcReplyTo`,
`grpcAccepted`, `grpcSrvStreamChain`, `grpcServeTok`, `grpc.start'`) and the adapters.

**Go's configuration as a trusted fact.** `grpc.start` (restated in B1b) emits, from the server
being built (`grpcSrvNew gs ics sics svcs regs sregs`), a persistent `grpcSrvCfg γ c`: the chains and
registrations Go's server holds (`GrpcSrvCfg`), fixed from `Serve` on (grpc's `RegisterService`
after `Serve` is fatal), beside `grpcAddrIs addr γ` (the server listening at `addr` is `γ`) and the
exclusive `grpcSrvLink gs lis γ` (the right to accept `γ`'s calls on `lis`). A proof cannot choose
`c`: it is made only by `grpc.start`, from `grpcSrvNew`, and is unique per `γ`
(`grpcSrvCfg_agree`); `γ` is unique per address (`grpcAddrIs_agree`).

**The registration** of a method at a server (`isGrpcRpcAt γ name Spec`): Go's configuration lists
`(name, mh, srv)` and the handler meets `Spec` under Go's chain, each run given the literal
`threadTok` and one later credit and returning the token (`grpcRunOkMd`, the run contract). No
caller-chosen resource, no count, no ghost registry, no saved predicate.

**The pair** (the soundness argument of the five trusted texts `ClientConn.Invoke`,
`ClientConn.NewStream`, `acceptRun`, `acceptRunConns`, `respond`, which are one channel per call):
- **Unary.** `Invoke`'s pre gives up the registration of the method at the address its attempt
  reaches (`grpcAddrIs a γ ∗ isGrpcRpcAt γ method Spec`) and `▷ Spec md m Φ Ψe` at the attempt's
  metadata. The server that accepts the attempt is the one listening at `a` (TCP; `bridge.New` maps
  a bridge's address to its target's `γ`), so it is `γ` (`grpcAddrIs_agree`), and the run's context
  carries the attempt's metadata. `acceptRun` hands exactly these to the run (the conjuncts of
  `grpcAccepted` marked "deposited") and a `grpcReplyTo` for `Φ`/`Ψe`. `respond` consumes `Φ m'`
  (or `Ψe d`) with the reply, and `Invoke`'s success post returns that `Φ m'` (its error post returns
  `Ψe d` only for a `handlerDescs` description, which only the handler makes).
- **One deposit, one run.** A deposit reaches at most one run: (a) grpc's transparent retry resends
  only a stream the server never processed (`stream.go`, `shouldRetry`'s unprocessed case); (b) the
  program's clients have no retry policy, no hedging and no `healthCheckConfig`: every client is
  made by the `NewClient` spec under `grpcResolverAt` (a service config without a retry policy) and
  `dialOptsAt`; without (b) grpc does resend a processed trailers-only attempt
  (`stream.go:803-858`; test T8b), which is why it is cited; (c) the world premise D7: every client
  connection to a served address is one the `NewClient` spec made (`grpcConn`), and grpc makes no
  calls of its own (no client-side health checks, no ORCA out-of-band streams). So each deposit is
  handed to at most one run, and `grpcReplyTo` (exclusive, no laws) is consumed once. An `Invoke`
  that returns an error early leaves its deposit with the run (grpc's handler runs asynchronously,
  test T2): nothing returns a deposit to a client.
- **Streams.** `NewStream`'s post and the server end share the stream's names `γs`, `Dn` and the
  persistent `Spec md γs Dn`; the server half is `acceptRun`'s stream arm, and the stream
  registration (`isGrpcStreamAt`) is deposited as in the unary case.
- **Go facts, not pair facts:** `(name, mh, srv) ∈ c.regs` (Go's dispatch), `grpcSrvChain c.ics`
  and `grpcSrvStreamChain c.sics` (Go's chains), `grpcDecOk` (grpc's codec), `grpcRunCtx` (no etcd
  keys in a run's context).

What the carrier (`Serve`'s proof) proves from this: `grpcSrvCfg_agree` makes the deposit's
configuration Go's `c`; the joint `Nodup` of `c.regs ++ c.sregs`' names (`grpc.start`'s premise,
carried by `grpcSrvNodup`) makes the deposit's handler Go's; the deposit's run contract then applies
to Go's handler with the carrier's own fork token and credit (`wp_fork_tok_upd`).
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

open Iris Iris.BI Iris.ProofMode

section axioms
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The reply channel of the accepted unary call `r`**, back to the client whose `Invoke`
deposited `Φ`, `Ψe` (exclusive; made only by `acceptRun`/`acceptRunConns`; its only use is
`respond`'s pre; no law). -/
axiom grpcReplyTo (r : val) (Rep : ProtoMsgT GF) (Φ : Rep.M → IProp GF)
  (Ψe : GoString → IProp GF) : IProp GF

end axioms


/-! ## The registration and the accepted call -/

section reg
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The composed stream interceptor grpc calls, for the chain `sics`** (persistent; as
`grpcSrvChain` for streams: grpc's `chainStreamServerInterceptors`, `server.go:1245-1262`: `nil` for
no interceptor, the one interceptor, or grpc's closure). The handler `h` is a function value (a
`StreamDesc.Handler`), as in the unary `grpcSrvChain`: a panic value there would unwind the call
while the chain's interceptors never see it. -/
def grpcSrvStreamChain (sics : List GoFunc) (si : GoFunc) : IProp GF :=
  match sics with
  | [] => iprop(⌜si = func.nil⌝)
  | _ :: _ => iprop(⌜si ≠ func.nil⌝ ∗ □ ∀ (srv st info : val) (h : GoFunc) (Ψ : val → IProp GF),
      srvStreamChainWP info sics #h srv st Ψ -∗
      WP (App (App (App (App (Val #si) (Val srv)) (Val st)) (Val info)) (Val #h)) {{ Ψ }})

instance grpcSrvStreamChain_persistent (sics : List GoFunc) (si : GoFunc) :
    Persistent (grpcSrvStreamChain (GF := GF) sics si) := by
  unfold grpcSrvStreamChain; cases sics <;> infer_instance

/-- **An accepted call** `r` of server `γ` with Go's configuration `c` (what `acceptRun` returns
with `runOk`). Unary: the run value of Go's handler `(name, mh, srv) ∈ c.regs` for the call's path;
the registration the client deposited (`isGrpcRpcAt γ name Spec`) and its request precondition
`▷ Spec md m Φ Ψe` at the metadata the run's context carries; grpc's context, decoder and chain
(Go facts); the reply channel `grpcReplyTo r Rep Φ Ψe`. Stream: the run value of Go's handler
`(name, mh, srv) ∈ c.sregs`; the deposited stream registration; Go's composed stream interceptor;
the stream's shared persistent `Spec md γs Dn` and its raw server end with both tokens at `[]`;
grpc's `info`. -/
def grpcAccepted (γ : GName) (c : GrpcSrvCfg GF) (r : val) : IProp GF :=
  iprop((∃ (name : GoString) (mh : GoFunc) (srv : GoInterface) (ci : GoInterfaceOk)
        (cd : context.ContextDesc (IProp GF)) (dec ui : GoFunc) (Req Rep : ProtoMsgT GF)
        (Spec : GrpcSpecMd Req.toProtoMsg Rep.toProtoMsg) (m : Req.M) (Φ : Rep.M → IProp GF)
        (Ψe : GoString → IProp GF),
      ⌜r = google_golang_org.grpc.model.runUnary mh srv ci dec ui⌝ ∗ ⌜(name, mh, srv) ∈ c.regs⌝ ∗
      isGrpcRpcAt γ name Spec ∗
      context.isContext ci cd ∗ grpcRunCtx ci ∗ grpcDecOk dec Req.toProtoMsg m ∗
      grpcSrvChain c.ics ui ∗
      ▷ Spec (metadata.incomingOf (GoInterface.ok ci)) m Φ Ψe ∗
      grpcReplyTo r Rep Φ Ψe) ∨
    (∃ (name : GoString) (mh : GoFunc) (srv : GoInterface) (ci : GoInterfaceOk)
        (cd : context.ContextDesc (IProp GF)) (st : GoInterface) (info : Loc) (si : GoFunc)
        (Req Rep : StreamMsgT GF) (Up : Nat → Req.M → IProp GF)
        (Spec : GrpcMd → StreamSpec Rep.toStreamMsg) (γs : StreamNames)
        (Dn : Nat → Rep.M → IProp GF),
      ⌜r = google_golang_org.grpc.model.runStream mh srv st info ci si⌝ ∗
      ⌜(name, mh, srv) ∈ c.sregs⌝ ∗
      isGrpcStreamAt γ name Up Spec ∗
      grpcSrvStreamChain c.sics si ∗
      □ Spec (metadata.incomingOf (GoInterface.ok ci)) γs Dn ∗
      srvRawStreamIs st γs Req.toStreamMsg Rep.toStreamMsg Up Dn ci cd ∗
      srvRecvTok (Req := Req.toStreamMsg) γs [] ∗ srvSendTok (Rep := Rep.toStreamMsg) γs [] ∗
      streamAuxTok γs ∗ srvStreamInfoIs info))

/-- **The right to serve `gs` on `lis` as server `γ`** (what `gs.Serve(lis)` takes; per-type stage B,
B1b: a definition, replacing the axiom of the same name): the link, Go's configuration with jointly
distinct full names, and the replies' size premise under which `grpc.start` made them. Made only by
`grpc.start'`. -/
def grpcServeTok (gs : Loc) (lis : GoInterface) (γ : GName) : IProp GF :=
  iprop(grpcSrvLink gs lis γ ∗ (∃ c : GrpcSrvCfg GF, grpcSrvCfg γ c ∗ ⌜grpcSrvNodup c⌝) ∗
    ⌜grpcRepliesFit⌝)

/-- **The start, packaged** (proved from `grpc.start`): the server listening at `addr`, as the facts
`grpc.serve` and `grpc.serveStream` use (`grpcServerAt`, `grpcStreamServerAt`), and the right to
serve it (`grpcServeTok`). -/
theorem grpc.start' (gs : Loc) (lis : GoInterface) (addr : GoString) (ics sics : List GoFunc)
    (svcs : List GoString) (regs sregs : List (GoString × GoFunc × GoInterface))
    (hfit : grpcRepliesFit) (hnd : ((regs ++ sregs).map Prod.fst).Nodup) :
    grpcSrvNew (GF := GF) gs ics sics svcs regs sregs ∗ netListenerAt lis addr ⊢
    |={⊤}=> ∃ γ : GName, grpcServerAt addr ics regs γ ∗ grpcStreamServerAt addr sics sregs γ ∗
      grpcServeTok gs lis γ := by
  iintro H
  imod (grpc.start gs lis addr ics sics svcs regs sregs hfit hnd) $$ H with ⟨%γ, #Ha, #Hc, Hl⟩
  imodintro
  iexists γ
  unfold grpcServerAt grpcStreamServerAt grpcServeTok
  isplitr [Hl]
  · iframe Ha
    iexists sics, sregs
    iexact Hc
  isplitr [Hl]
  · iframe Ha
    iexists ics, regs
    iexact Hc
  iframe Hl
  isplitr
  · iexists ({ ics := ics, sics := sics, regs := regs, sregs := sregs } : GrpcSrvCfg GF)
    iframe Hc
    ipureintro
    exact hnd
  ipureintro
  exact hfit

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
a bundle `R₁ ∗ R₂ ∗ R₃` of three leveled pools (levels 1, 2, 3; abstract `IProp`s, not known
timeless) meets the run contract: the run borrows each pool with its token's level (each loan gives
`▷ Rᵢ`), strips the joined later with the run's one credit, runs the handler, and gives the loans
back. Generic in the pools: B2/B3 instantiate it with `raftPool`, `I` and the run pool. -/
theorem grpcRunOkMd_of_pools {Req Rep : ProtoMsg GF} (mh : val) (srv : GoInterface)
    (ics : List GoFunc) (Spec : GrpcSpecMd Req Rep) (R₁ R₂ R₃ : IProp GF)
    (N₁ N₂ N₃ : Namespace) (γ₁ γ₂ γ₃ : GName) (HT : 4 ≤ threadBound GF) :
    □ grpcMethodOkMd mh srv ics iprop(R₁ ∗ R₂ ∗ R₃) Spec ∗
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
  iapply Hm $$ %m %Φ %Ψe %ci %cd %dec %ui [HR Hctx Hrc Hd Hch HSpec]
  · iframe
  inext
  iintro %resp %err ⟨⟨HB1, HB2, HB3⟩, Hok, Herr, Hsrv⟩
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
theorem srvStreamChainWP_fupd (info : val) (ics : List GoFunc) (h srv st : val)
    (Ψ : val → IProp GF) :
    (|={⊤}=> srvStreamChainWP info ics h srv st Ψ) ⊢ srvStreamChainWP info ics h srv st Ψ := by
  cases ics with
  | nil =>
    unfold srvStreamChainWP
    exact fupd_wp
  | cons ic ics =>
    unfold srvStreamChainWP
    iintro H %h' #Hh'
    iapply fupd_wp
    imod H
    imodintro
    iapply H $$ %h' Hh'

/-- A stream chain's postcondition may be weakened, with an update (`Ψ` is only its first call's
postcondition). -/
theorem srvStreamChainWP_wand (info : val) (ics : List GoFunc) (h srv st : val)
    (Ψ Ψ' : val → IProp GF) :
    srvStreamChainWP info ics h srv st Ψ ∗ (∀ v, Ψ v -∗ |={⊤}=> Ψ' v) ⊢
      srvStreamChainWP info ics h srv st Ψ' := by
  cases ics with
  | nil =>
    unfold srvStreamChainWP
    iintro ⟨H, Hw⟩
    iapply wp_fupd
    iapply wp_wand $$ H Hw
  | cons ic ics =>
    unfold srvStreamChainWP
    iintro ⟨H, Hw⟩ %h' #Hh'
    iapply wp_fupd
    iapply wp_wand $$ [H] Hw
    iapply H $$ %h' Hh'

/-- **The stream adapter** (Scope r5 §3.4; B1b): a stream handler proved against
`grpcStreamMethodOk` at a bundle `R₁ ∗ R₂ ∗ R₃` of three leveled pools (levels 1, 2, 3), which it
returns, meets the stream run contract: the run borrows each pool with its token's level, strips the
joined later with the run's one credit, runs the chain, and gives the loans back. Generic in the
pools, as `grpcRunOkMd_of_pools`. -/
theorem grpcStreamRunOk_of_pools {Req Rep : StreamMsg GF} (mh : val) (srv : GoInterface)
    (sics : List GoFunc) (Up : Nat → Req.M → IProp GF) (Spec : GrpcMd → StreamSpec Rep)
    (R₁ R₂ R₃ : IProp GF) (N₁ N₂ N₃ : Namespace) (γ₁ γ₂ γ₃ : GName) (HT : 4 ≤ threadBound GF) :
    □ grpcStreamMethodOk mh srv sics iprop(R₁ ∗ R₂ ∗ R₃) Up Spec ∗
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
  icases (threadTok_levels0123 (GF := GF) HT).1 $$ Htok with ⟨H0, H1, H2, H3, H4⟩
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
  isplitl [HSp HRs Hraw HR HT' Ha Hi]
  · iapply Hr $$ HSp HRs Hraw HR HT' Ha Hi
  iintro %v ⟨%err, %Hv, #Hse, ⟨HB1, HB2, HB3⟩⟩
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
  iapply (threadTok_levels0123 (GF := GF) HT).2
  iframe

end adapt

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

end EtcdGrove
end Perennial
