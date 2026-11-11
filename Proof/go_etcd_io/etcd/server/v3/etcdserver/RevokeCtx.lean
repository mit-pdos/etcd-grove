/-
**The revocation's thread resources** (revoke-open, 2026-11-06; `notes/revoke-open-plan.md`, Scope
Q1–Q7 and "Draft pass 1", C.0; `notes/decisions.md`, "The revocation's thread levels"). Lean-first.

`revokeExpiredLeases` (`run`'s expiry arm) `GoAttach`es an *outer* goroutine (`Logger()`,
`ensureLeadership()`, then a `GoAttach` per lease) whose *inner* goroutines `WithRoot` and
`LeaseRevoke`. Rounds overlap without bound, so the reader slots these goroutines hold come from
pools backed by thread tokens (`threadPool.isThreadPoolL`), borrowed with one level of a token each:

| level | what |
|---|---|
| 0 | a started goroutine's slot in `s.wg` (`goAttachInv`) |
| 1 | `wg.Add`'s pending token; `raftPool` (`lgMu`); the inner pool `I` (`leadTimeMu` ∗ `E.RD`) |
| 2 | the outer pool `B` (`wgMu` ∗ `read.mux`) |
| 3 | `ensureLeadership`'s token |

Levels 0–1 exist at every thread bound; levels 2–3 need `srvRevokeLevels` (`srvRevokeK` levels,
`RevokeLevels.lean`), which only the revocable run configuration carries (`lease.runCfg`,
`LeaseRun.lean`). Below `revokeExpiredLeases`'s spec, which names `srvRevokesLeases`,
`srvRevokeLevels` and `srvRevokeCtx` (`LeaseRun.lean` imports that spec, so they cannot live there).

(Review round 1, S1, 2026-11-06) The bundles and the pools are sealed, and the revocation's proof
takes from them only through narrow laws, one per use: the pools' borrows and give-backs
(`srvRevokeCtx_outerBorrow`/`srvRevokeOuterLoan_giveBack`, `srvRevokeCtx_innerBorrow`/
`srvRevokeInnerLoan_giveBack`), `raftPool` (`srvRevokeCtx_raftPool`), the bound `ensureLeadership`
takes (`srvRevokeCtx_bound`), the views (`srvRevokeCtx_views`), `WithRoot`'s premise
(`srvRevokeCtx_withRoot`), the credential (`srvRevokeCtx_cred`) and the context
(`srvRevokeCtx_ctx`).
-/
module

public import Proof.go_opentelemetry_io.otel.trace.Defs
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRunRes
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthGuard
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.RevokeLevels
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.AuthDerive
public import Proof.context.ReqKeys

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- **The cluster revokes leases** (moved from `LeaseRevoke.lean`, 2026-11-06, revoke-open: the
revocation's spec names it; see that file's header): two scope restrictions, the KV names' lease
mode `revocable` (the cluster's requests may revoke leases, `revokePropOk`) and auth off (the
auth-on apply row admits no revocation, `plainCover`). (Of `revokeExpiredLeases`' caller, the auth
half also follows from its slice of expired leases, whose grant guard says auth is off,
`srvGrantGuard`; `LeaseRevoke.spec` takes the pair.) -/
def srvRevokesLeases (E : apply.AEnv GF) (ρ : ReqNames) : Prop :=
  ρ.rd.kv.lm = .revocable ∧ E.authOn = false

/-- **The level bound the revocation's goroutines need** (revoke-open Q1 (a2), Q2 (ii)): levels
`0 … srvRevokeK - 1` of a thread token exist (see the file header). Only the revocable run
configuration carries it (`lease.runCfg`), so no other spec names the bound. -/
def srvRevokeLevels : Prop := srvRevokeK ≤ threadBound GF

/-- `srvRevokeLevels` at a thread bound `max m srvRevokeK` (the etcd examples' adequacy lemmas'). -/
theorem srvRevokeLevels_of_max {m : Nat} (h : threadBound GF = max m srvRevokeK) :
    srvRevokeLevels (GF := GF) := by
  unfold srvRevokeLevels; rw [h]; exact Nat.le_max_right _ _

/-- The copies in each of the revocation's pools: one fewer than the server's thread bound's limit
(`threadBound GF ≤ backend.rdPoolN`, `isServerBuilt`'s `%Hbound`), what `threadPool.initL` needs. -/
@[word_unfold] def srvRevokePoolN : Nat := backend.rdPoolN - 1

/-- The outer pool's namespace. -/
def srvRevokeOuterN : Namespace := nroot .@ "srvRevokeOuter"
/-- The inner pool's namespace. -/
def srvRevokeInnerN : Namespace := nroot .@ "srvRevokeInner"

/-- **The outer pool `B`** (revoke-open Q7; level 2; sealed): what the outer goroutine holds for
its loop, a reader slot of `wgMu` at `GoAttach`'s names `γg` (its `GoAttach`es) and one of the read
loop's lock (`ensureLeadership`'s `LinearizableReadNotify`). Carved by `start` from `srvStarted`'s
stocks (`srvRevokeOuterPool_intro`). -/
@[no_expose] def srvRevokeOuterPool (s : Loc) (γr : ReadNames) (γg : GoNames) : IProp GF :=
  iprop(∃ γ : GName, threadPool.isThreadPoolL srvRevokeOuterN 2 γ
    iprop(srvWgReaderAt s γg ∗ srvReadReader s γr))

instance srvRevokeOuterPool_persistent (s : Loc) (γr : ReadNames) (γg : GoNames) :
    Persistent (srvRevokeOuterPool (GF := GF) s γr γg) := by
  unfold srvRevokeOuterPool; infer_instance

/-- **A loan of the outer pool** (sealed; exclusive): what the borrower gives back with the slots
(`srvRevokeOuterLoan_giveBack`). -/
@[no_expose] def srvRevokeOuterLoan (s : Loc) (γr : ReadNames) (γg : GoNames) : IProp GF :=
  iprop(∃ γ : GName, threadPool.isThreadPoolL srvRevokeOuterN 2 γ
    iprop(srvWgReaderAt s γg ∗ srvReadReader s γr) ∗ threadPool.ownThreadLoan γ)

/-- **The inner pool `I`** (revoke-open Q7; level 1; sealed): what an inner goroutine holds for its
`WithRoot` and `LeaseRevoke`, a reader slot of `leadTimeMu` and the auth store's reader resource.
Built by `NewServer` from `leadTimeMu`'s rest and `E.RD`'s supply (Q6; `srvRevokeInnerPool_intro`). -/
@[no_expose] def srvRevokeInnerPool (s : Loc) (E : apply.AEnv GF) : IProp GF :=
  iprop(∃ γ : GName, threadPool.isThreadPoolL srvRevokeInnerN 1 γ
    iprop(srvLeadTimeReader s ∗ E.RD))

instance srvRevokeInnerPool_persistent (s : Loc) (E : apply.AEnv GF) :
    Persistent (srvRevokeInnerPool (GF := GF) s E) := by
  unfold srvRevokeInnerPool; infer_instance

/-- **A loan of the inner pool** (sealed; exclusive). -/
@[no_expose] def srvRevokeInnerLoan (s : Loc) (E : apply.AEnv GF) : IProp GF :=
  iprop(∃ γ : GName, threadPool.isThreadPoolL srvRevokeInnerN 1 γ
    iprop(srvLeadTimeReader s ∗ E.RD) ∗ threadPool.ownThreadLoan γ)

/-- **The outer pool, from a level-2 thread pool of its slots** (`start`). -/
theorem srvRevokeOuterPool_intro (s : Loc) (γr : ReadNames) (γg : GoNames) (γ : GName) :
    threadPool.isThreadPoolL srvRevokeOuterN 2 γ
        iprop(srvWgReaderAt (GF := GF) s γg ∗ srvReadReader s γr) ⊢
      srvRevokeOuterPool s γr γg := by
  unfold srvRevokeOuterPool
  iintro #H
  iexists γ
  iexact H

/-- **The inner pool, from a pool of `leadTimeMu`'s slots** (`NewServer`, which pairs the slots
in their own form: `srvLeadTimeReader` unfolded). (Moved from `NewServer.lean`, review round 1.) -/
theorem srvRevokeInnerPool_intro (s : Loc) (E : apply.AEnv GF) (γ : GName) :
    threadPool.isThreadPoolL srvRevokeInnerN 1 γ
        iprop(sync.ownRWMutex (srvLeadTimeMuAddr s) (leadTimeP s) ∗ E.RD) ⊢
      srvRevokeInnerPool s E := by
  unfold srvRevokeInnerPool srvLeadTimeReader
  iintro #H
  iexists γ
  iexact H

/-- **What `NewServer` builds for the revocation** (sealed; persistent): the inner pool, the
transport's pool of `lgMu` readers (`raftPool`, leveled at 1, Q3), the auth store's concrete
pointer (`WithRoot`'s receiver) and (revoke-open pass 2, 2026-11-06) the server's thread bound
within the backend's pool of readers (`NewServer`'s premise: what `ensureLeadership`'s bound
`threadBound GF ≤ 2 ^ 30 - 1` comes from in the revocation's outer goroutine). -/
@[no_expose] def srvRevokeBuilt (s : Loc) (E : apply.AEnv GF) : IProp GF :=
  iprop(srvRevokeInnerPool s E ∗ raftPool (srvLgReader s) ∗
    (∃ stl : Loc, srvAuthStoreAddr s ↦□ auth.authIface stl) ∗ ⌜threadBound GF ≤ backend.rdPoolN⌝)

instance srvRevokeBuilt_persistent (s : Loc) (E : apply.AEnv GF) :
    Persistent (srvRevokeBuilt (GF := GF) s E) := by
  unfold srvRevokeBuilt; infer_instance

/-- The transport's pool of `lgMu` readers, out of the revocation's built part (`start`'s
`GoAttach` protocol, `srvGoAttachOk`). -/
theorem srvRevokeBuilt_raftPool (s : Loc) (E : apply.AEnv GF) :
    srvRevokeBuilt (GF := GF) s E ⊢ raftPool (srvLgReader s) := by
  iintro #H
  iunfold srvRevokeBuilt at H
  icases H with ⟨-, #Hp, -, -⟩
  iexact Hp

/-- **The revocation's built part, from its pieces** (`NewServer`). -/
theorem srvRevokeBuilt_intro (s : Loc) (E : apply.AEnv GF) (stl : Loc) :
    srvRevokeInnerPool (GF := GF) s E ∗ raftPool (srvLgReader s) ∗
      srvAuthStoreAddr s ↦□ auth.authIface stl ∗ ⌜threadBound GF ≤ backend.rdPoolN⌝ ⊢
    srvRevokeBuilt s E := by
  iintro ⟨#HI, #Hp, #Ha, %Hb⟩
  iunfold srvRevokeBuilt
  iframe HI Hp
  isplitl
  · iexists stl; iexact Ha
  ipureintro; exact Hb

/-- **The revocation's persistent bundle** (sealed): `srvRevokeBuilt`, the outer pool at `start`'s
names, with auth off the request side's and the reader's views (from which `srvAuthAt`,
`srvAuthAt_of_views`, and `WithRoot`'s premise, `srvRevokeCtx_withRoot`), the request names'
credential, and the server context's contract (`s.ctx`, `WithRoot`'s argument and `LeaseRevoke`'s).
A conjunct of `isServerRunC` in both auth modes (the off-mode part guarded: with auth on the
revocation never runs, `srvRevokesLeases`). (Review round 1, NIT 3.3, 2026-11-06: until then also
`⌜E.authOn = false → E.authMode = .off⌝`, true of every `E`: `apply.AEnv.authMode_off_of_authOn`.) -/
@[no_expose] def srvRevokeCtx (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames)
    (γg : GoNames) : IProp GF :=
  iprop(srvRevokeBuilt s E ∗ srvRevokeOuterPool s γr γg ∗
    □ (⌜E.authOn = false⌝ → isServerReq s E ρ ∗ isServerRead s E γr) ∗
    □ (|==> idCred ρ.ids 1) ∗
    (∃ (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
      srvCtxAddr s ↦□ GoInterface.ok ctx ∗ context.isContext ctx cd ∗ context.libCtxOk ctx ∗
        trace.spanCtxOk ctx ∗ context.startTimeOk ctx))

instance srvRevokeCtx_persistent (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames)
    (γg : GoNames) : Persistent (srvRevokeCtx (GF := GF) s E ρ γr γg) := by
  unfold srvRevokeCtx; infer_instance

/-- **The revocation's bundle, from its pieces** (`start`). -/
theorem srvRevokeCtx_intro (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames)
    (γg : GoNames) :
    srvRevokeBuilt (GF := GF) s E ∗ srvRevokeOuterPool s γr γg ∗
      □ (⌜E.authOn = false⌝ → isServerReq s E ρ ∗ isServerRead s E γr) ∗
      □ (|==> idCred ρ.ids 1) ∗
      (∃ (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
        srvCtxAddr s ↦□ GoInterface.ok ctx ∗ context.isContext ctx cd ∗ context.libCtxOk ctx ∗
        trace.spanCtxOk ctx ∗ context.startTimeOk ctx) ⊢
    srvRevokeCtx s E ρ γr γg := by
  unfold srvRevokeCtx; exact .rfl

/-- **Borrow the outer pool's slots** with level 2 of a thread token (and a later credit): the
outer goroutine's for its loop, and its caller's for the round's `GoAttach`. -/
theorem srvRevokeCtx_outerBorrow (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames)
    (γg : GoNames) (Em : CoPset) (HN : ↑srvRevokeOuterN ⊆ Em) :
    £ 1 ∗ srvRevokeCtx (GF := GF) s E ρ γr γg ∗ levelTok 2 ⊢
      |={Em}=> (srvWgReaderAt s γg ∗ srvReadReader s γr) ∗ srvRevokeOuterLoan s γr γg := by
  iintro ⟨Hlc, #H, H2⟩
  iunfold srvRevokeCtx at H
  icases H with ⟨-, #HB, -, -, -⟩
  iunfold srvRevokeOuterPool at HB
  icases HB with ⟨%γ, #HB⟩
  imod threadPool.borrowL_lc srvRevokeOuterN 2 γ
      iprop(srvWgReaderAt s γg ∗ srvReadReader s γr) Em HN $$ [Hlc HB H2] with ⟨HR, Hl⟩
  · iframe Hlc H2; iexact HB
  imodintro
  iframe HR
  iunfold srvRevokeOuterLoan
  iexists γ
  iframe Hl
  iexact HB

/-- **Give the outer pool's slots back**, for level 2 of the token. -/
theorem srvRevokeOuterLoan_giveBack (s : Loc) (γr : ReadNames) (γg : GoNames) (Em : CoPset)
    (HN : ↑srvRevokeOuterN ⊆ Em) :
    srvRevokeOuterLoan (GF := GF) s γr γg ∗ srvWgReaderAt s γg ∗ srvReadReader s γr ⊢
      |={Em}=> levelTok 2 := by
  iintro ⟨Hl, Hwr, Hrd⟩
  iunfold srvRevokeOuterLoan at Hl
  icases Hl with ⟨%γ, #HB, Hl⟩
  iapply threadPool.giveBackL srvRevokeOuterN 2 γ
    iprop(srvWgReaderAt s γg ∗ srvReadReader s γr) Em HN
  iframe Hl Hwr Hrd
  iexact HB

/-- **Borrow the inner pool's slots** with level 1 of a thread token (and a later credit): an inner
goroutine's, for `WithRoot` and `LeaseRevoke`. -/
theorem srvRevokeCtx_innerBorrow (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames)
    (γg : GoNames) (Em : CoPset) (HN : ↑srvRevokeInnerN ⊆ Em) :
    £ 1 ∗ srvRevokeCtx (GF := GF) s E ρ γr γg ∗ levelTok 1 ⊢
      |={Em}=> (srvLeadTimeReader s ∗ E.RD) ∗ srvRevokeInnerLoan s E := by
  iintro ⟨Hlc, #H, H1⟩
  iunfold srvRevokeCtx at H
  icases H with ⟨#Hb, -, -, -, -⟩
  iunfold srvRevokeBuilt at Hb
  icases Hb with ⟨#HI, -, -, -⟩
  iunfold srvRevokeInnerPool at HI
  icases HI with ⟨%γ, #HI⟩
  imod threadPool.borrowL_lc srvRevokeInnerN 1 γ iprop(srvLeadTimeReader s ∗ E.RD) Em HN
    $$ [Hlc HI H1] with ⟨HR, Hl⟩
  · iframe Hlc H1; iexact HI
  imodintro
  iframe HR
  iunfold srvRevokeInnerLoan
  iexists γ
  iframe Hl
  iexact HI

/-- **Give the inner pool's slots back**, for level 1 of the token. -/
theorem srvRevokeInnerLoan_giveBack (s : Loc) (E : apply.AEnv GF) (Em : CoPset)
    (HN : ↑srvRevokeInnerN ⊆ Em) :
    srvRevokeInnerLoan (GF := GF) s E ∗ srvLeadTimeReader s ∗ E.RD ⊢ |={Em}=> levelTok 1 := by
  iintro ⟨Hl, Hlt, HRD⟩
  iunfold srvRevokeInnerLoan at Hl
  icases Hl with ⟨%γ, #HI, Hl⟩
  iapply threadPool.giveBackL srvRevokeInnerN 1 γ iprop(srvLeadTimeReader s ∗ E.RD) Em HN
  iframe Hl Hlt HRD
  iexact HI

/-- The transport's pool of `lgMu` readers (the outer goroutine's `Logger()`). -/
theorem srvRevokeCtx_raftPool (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames)
    (γg : GoNames) :
    srvRevokeCtx (GF := GF) s E ρ γr γg ⊢ raftPool (srvLgReader s) := by
  iintro #H
  iunfold srvRevokeCtx at H
  icases H with ⟨#Hb, -, -, -, -⟩
  iapply srvRevokeBuilt_raftPool $$ Hb

/-- The thread bound within Go's limit of an `RWMutex`'s readers (`ensureLeadership`'s premise). -/
theorem srvRevokeCtx_bound (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames)
    (γg : GoNames) :
    srvRevokeCtx (GF := GF) s E ρ γr γg ⊢ ⌜threadBound GF ≤ 2 ^ 30 - 1⌝ := by
  iintro #H
  iunfold srvRevokeCtx at H
  icases H with ⟨#Hb, -, -, -, -⟩
  iunfold srvRevokeBuilt at Hb
  icases Hb with ⟨-, -, -, %Hbnd⟩
  ipureintro
  word

/-- With auth off, the request side's and the reader's views. -/
theorem srvRevokeCtx_views (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames)
    (γg : GoNames) (h : E.authOn = false) :
    srvRevokeCtx (GF := GF) s E ρ γr γg ⊢ isServerReq s E ρ ∗ isServerRead s E γr := by
  iintro #H
  iunfold srvRevokeCtx at H
  icases H with ⟨-, -, #Hv, -, -⟩
  iapply Hv
  ipureintro; exact h

/-- **`WithRoot`'s premise** (review round 1, S3, 2026-11-06): with auth off, the auth store's
pointer and its `IsAuthEnabled` contract with the verdict of the mode `off`, at `E.RD` (the store's
contract, `srvAuthAt`, at the pointer `NewServer` recorded). (Review round 2, N1, 2026-11-06: until
then the verdict at `E.authMode`, which the caller equated with `.off`; the bridge,
`AuthMode.isOn_false_iff`, as in `apply.AEnv.authMode_off_of_authOn`, is now here, under this law's
gate `E.authOn = false`.) -/
theorem srvRevokeCtx_withRoot (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames)
    (γg : GoNames) (h : E.authOn = false) :
    srvRevokeCtx (GF := GF) s E ρ γr γg ⊢
      ∃ stl : Loc, srvAuthStoreAddr s ↦□ auth.authIface stl ∗
        □ ({{ E.RD }} (App (Val (stl @!! go.GoType.PointerType
            go_etcd_io.etcd.server.v3.auth.authStore.ty @!! go!"IsAuthEnabled")) (Val #()))
          {{ (b : Bool), RET #b; E.RD ∗ auth.enabledVerdict .off b }}) := by
  iintro #H
  ihave #Hvw := srvRevokeCtx_views s E ρ γr γg h $$ H
  ihave #Hauth := srvAuthAt_of_views s E ρ γr $$ Hvw
  iunfold srvRevokeCtx at H
  icases H with ⟨#Hb, -, -, -, -⟩
  iunfold srvRevokeBuilt at Hb
  icases Hb with ⟨-, -, ⟨%stl, #Hauf⟩, -⟩
  ihave ⟨%st, #Hst, #HAS⟩ := srvAuthAt_isAuthStore s E $$ Hauth
  icombine Hauf Hst gives %e0
  subst e0
  iexists stl
  iframe Hauf
  ihave #HEn := apply.isAuthStore_isAuthEnabled $$ HAS
  -- `apply.AEnv.authMode_off_of_authOn`'s content: that law carries `apply.Assumptions` (a section
  -- instance of `Chain.lean`), which this module does not have
  rw [(auth.AuthMode.isOn_false_iff E.authMode).1 h]
  iexact HEn

/-- The request names' credential (`LeaseRevoke`'s). -/
theorem srvRevokeCtx_cred (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames)
    (γg : GoNames) :
    srvRevokeCtx (GF := GF) s E ρ γr γg ⊢ □ (|==> idCred ρ.ids 1) := by
  iintro #H
  iunfold srvRevokeCtx at H
  icases H with ⟨-, -, -, #Hc, -⟩
  iexact Hc

/-- The server context's contract (`s.ctx`: `WithRoot`'s argument, `LeaseRevoke`'s). -/
theorem srvRevokeCtx_ctx (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames)
    (γg : GoNames) :
    srvRevokeCtx (GF := GF) s E ρ γr γg ⊢
      ∃ (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
        srvCtxAddr s ↦□ GoInterface.ok ctx ∗ context.isContext ctx cd ∗ context.libCtxOk ctx ∗
        trace.spanCtxOk ctx ∗ context.startTimeOk ctx := by
  iintro #H
  iunfold srvRevokeCtx at H
  icases H with ⟨-, -, -, -, Hc⟩
  iexact Hc

end defs

end EtcdGrove
end Perennial
