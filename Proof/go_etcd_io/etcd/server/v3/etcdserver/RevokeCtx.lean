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

Levels 0–1 exist at every thread bound; levels 2–3 need `srvRevokeLevels`, which only the revocable
run configuration carries (`lease.runCfg`, `LeaseRun.lean`). Below `revokeExpiredLeases`'s spec,
which names `srvRevokesLeases`, `srvRevokeLevels` and `srvRevokeCtx` (`LeaseRun.lean` imports that
spec, so they cannot live there).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRunRes
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthGuard

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
auth-on apply row admits no revocation, `plainCover`). -/
def srvRevokesLeases (E : apply.AEnv GF) (ρ : ReqNames) : Prop :=
  ρ.rd.kv.lm = .revocable ∧ E.authOn = false

/-- **The level bound the revocation's goroutines need** (revoke-open Q1 (a2), Q2 (ii)): levels 0–3
of a thread token exist (see the file header). Only the revocable run configuration carries it
(`lease.runCfg`), so no other spec names the bound. -/
def srvRevokeLevels : Prop := 4 ≤ threadBound GF

/-- The copies in each of the revocation's pools: one fewer than the server's thread bound's limit
(`threadBound GF ≤ backend.rdPoolN`, `isServerBuilt`'s `%Hbound`), what `threadPool.initL` needs. -/
@[word_unfold] def srvRevokePoolN : Nat := backend.rdPoolN - 1

/-- The outer pool's namespace. -/
def srvRevokeOuterN : Namespace := nroot .@ "srvRevokeOuter"
/-- The inner pool's namespace. -/
def srvRevokeInnerN : Namespace := nroot .@ "srvRevokeInner"

/-- **The outer pool `B`** (revoke-open Q7; level 2): what the outer goroutine holds for its loop,
a reader slot of `wgMu` at `GoAttach`'s names `γg` (its `GoAttach`es) and one of the read loop's lock
(`ensureLeadership`'s `LinearizableReadNotify`). Carved by `start` from `srvStarted`'s stocks. -/
def srvRevokeOuterPool (s : Loc) (γr : ReadNames) (γg : GoNames) : IProp GF :=
  iprop(∃ γ : GName, threadPool.isThreadPoolL srvRevokeOuterN 2 γ
    iprop(srvWgReaderAt s γg ∗ srvReadReader s γr))

instance srvRevokeOuterPool_persistent (s : Loc) (γr : ReadNames) (γg : GoNames) :
    Persistent (srvRevokeOuterPool (GF := GF) s γr γg) := by
  unfold srvRevokeOuterPool; infer_instance

/-- **The inner pool `I`** (revoke-open Q7; level 1): what an inner goroutine holds for its
`WithRoot` and `LeaseRevoke`, a reader slot of `leadTimeMu` and the auth store's reader resource.
Built by `NewServer` from `leadTimeMu`'s rest and `E.RD`'s supply (Q6). -/
def srvRevokeInnerPool (s : Loc) (E : apply.AEnv GF) : IProp GF :=
  iprop(∃ γ : GName, threadPool.isThreadPoolL srvRevokeInnerN 1 γ
    iprop(srvLeadTimeReader s ∗ E.RD))

instance srvRevokeInnerPool_persistent (s : Loc) (E : apply.AEnv GF) :
    Persistent (srvRevokeInnerPool (GF := GF) s E) := by
  unfold srvRevokeInnerPool; infer_instance

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

/-- **The revocation's built part, split** (`revokeExpiredLeases`). -/
theorem srvRevokeBuilt_parts (s : Loc) (E : apply.AEnv GF) :
    srvRevokeBuilt (GF := GF) s E ⊢
      srvRevokeInnerPool s E ∗ raftPool (srvLgReader s) ∗
      (∃ stl : Loc, srvAuthStoreAddr s ↦□ auth.authIface stl) ∗ ⌜threadBound GF ≤ backend.rdPoolN⌝ := by
  unfold srvRevokeBuilt; exact .rfl

/-- **The revocation's persistent bundle** (sealed): `srvRevokeBuilt`, the outer pool at `start`'s
names, with auth off the mode `off` (`WithRoot`'s premise, the `IsAuthEnabled` verdict) and the
request side's and the reader's views (from which `srvAuthAt`, `srvAuthAt_of_views`), the request
names' credential, and the server context's contract (`s.ctx`, `WithRoot`'s argument and
`LeaseRevoke`'s). A conjunct of `isServerRun*` in both auth modes (the off-mode parts guarded: with
auth on the revocation never runs, `srvRevokesLeases`). -/
@[no_expose] def srvRevokeCtx (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames)
    (γg : GoNames) : IProp GF :=
  iprop(srvRevokeBuilt s E ∗ srvRevokeOuterPool s γr γg ∗
    ⌜E.authOn = false → E.authMode = auth.AuthMode.off⌝ ∗
    □ (⌜E.authOn = false⌝ → isServerReq s E ρ ∗ isServerRead s E γr) ∗
    □ (|==> idCred ρ.ids 1) ∗
    (∃ (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
      srvCtxAddr s ↦□ GoInterface.ok ctx ∗ context.isContext ctx cd))

instance srvRevokeCtx_persistent (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames)
    (γg : GoNames) : Persistent (srvRevokeCtx (GF := GF) s E ρ γr γg) := by
  unfold srvRevokeCtx; infer_instance

/-- **The revocation's bundle, from its pieces** (`start`). -/
theorem srvRevokeCtx_intro (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames)
    (γg : GoNames) :
    srvRevokeBuilt (GF := GF) s E ∗ srvRevokeOuterPool s γr γg ∗
      ⌜E.authOn = false → E.authMode = auth.AuthMode.off⌝ ∗
      □ (⌜E.authOn = false⌝ → isServerReq s E ρ ∗ isServerRead s E γr) ∗
      □ (|==> idCred ρ.ids 1) ∗
      (∃ (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
        srvCtxAddr s ↦□ GoInterface.ok ctx ∗ context.isContext ctx cd) ⊢
    srvRevokeCtx s E ρ γr γg := by
  unfold srvRevokeCtx; exact .rfl

/-- **The revocation's bundle, split** (`revokeExpiredLeases`). -/
theorem srvRevokeCtx_parts (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames)
    (γg : GoNames) :
    srvRevokeCtx (GF := GF) s E ρ γr γg ⊢
      srvRevokeBuilt s E ∗ srvRevokeOuterPool s γr γg ∗
      ⌜E.authOn = false → E.authMode = auth.AuthMode.off⌝ ∗
      □ (⌜E.authOn = false⌝ → isServerReq s E ρ ∗ isServerRead s E γr) ∗
      □ (|==> idCred ρ.ids 1) ∗
      (∃ (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
        srvCtxAddr s ↦□ GoInterface.ok ctx ∗ context.isContext ctx cd) := by
  unfold srvRevokeCtx; exact .rfl

end defs

end EtcdGrove
end Perennial
