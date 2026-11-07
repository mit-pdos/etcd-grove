/-
`(*EtcdServer).applyEntries(ep, apply)` (server.go): the committed entries of a `toApply`,
from the next unapplied one. Lean-first (no Rocq counterpart); see `InvApplier.lean`,
`InvApply.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApplier
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvGoAttach
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApRes
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ApplyNormalOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ApplyRDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.cindex go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`s.applyEntries(ep, ap)` in the auth modes `P`, at a restart point** (R2d'a swap batch 3,
2026-11-06: until then `specBatch` was the first-start form, with the corollaries `ModeSpecs.lean`'s
`specOff`/`specOn`; the restart form was `ApplyAllR.lean`'s `specBatchRAt`, with the arms
`ApplyEntriesR.lean`'s `specBatchROff` and `ApplyEntriesROn.lean`'s `specBatchROnC`). `specBatch` is
`specBatchAt (· ≠ .any)`; the proof's two arms are `specBatchAt` at `.off` and at `on _`.

`apply.specAt` after `applyEntries`' cut of the batch at Go's index `ai` (`server.go:1215-1239` at the
pin `673da07c8`): Go's rows (`ep.appliedi`, `ep.appliedt`, `loopOk`) at Go's log `A`; the ghost rows
(the applied index `g`, the KV model, the view, `epCsAt`, `srvApRes`) at `ghostOf rp A`, the rest
buckets `srvRestR` and the batch `kvBatchR`. **A first start** (`rp = RestartPt.first`, `g = ai`) is
the old first-start text: `ghostOf_first`, `srvRestR_first`, `kvBatchR_first` (given `ai0 ≤ ciEff`, a
first start's `ai0 = 0`), and `uint.Z ai = ai0 + |A|` (`kvBatch`'s). In the environment's auth mode
(`E.authOn`): the server's view (`isServerM`), the committed log's shapes (`logShapeM`), the applier
state (`srvApplyKVM`), the apply thread's model (`kvAppliedM`); with auth on only, the lessor finding no
lease (`srvLessorNilM`), the receipts' bound and the token rights (`srvTokRights`, `True` off).

The contract (until swap batch 3, `ModeSpecs.lean`'s `applyEntries.specOff`'s account, at `A` for
the ghost log): `s.applyEntries(ep, ap)`, by the apply thread: the entries of `ap` (consecutive from
`f0`, with no gap after the applied index `ep.appliedi = ai`, as raft hands them over) from
`ai + 1` on are applied (`apply`), and `ep.appliedi`, `ep.appliedt` advance to the last; the
apply thread's relation `loopOk` (processed through the larger of `ci` and the applied
index) is kept. **The KV** (the apply package's unit 3): the apply thread's applier state goes
from `x` to `x'` by `entriesStep c (unapplied ai ms) x x'`, `c` the consistent index at the
start (`ciEff γ st.k`), under `logShape (unapplied ai ms)` (D19c's move; until then
`entriesOk c (unapplied ai ms) x`), and `batchWaitOk` of the
batch (unit 2 of the request path: the wait's premise, see `apply`). **The applied index** (the
request path's unit 4b): the apply thread's half of the ghost applied index (`srvAppliedOwn γr`)
at `ai`, with the log applied through `ai` the KV's (`appliedLogAt γr ai x.log`), goes to `ai'`, the
log applied through `ai'` the KV's after (`apply` deposits one per entry; 2026-10-14, unit C2a:
each entry committed, `batchCommittedIdx`). **The write budget**
(2026-10-13, unit 6): one write token of the store per entry applied (since D19b, 2026-10-18,
taken by `apply` from the budget `srvWTPool E` with a time receipt; until then
`txn.storeWTs E.γ (unapplied ai ms).length`, handed in and spent; D22 J5, 2026-10-26: the count of
tokens taken goes from `w` to `w` plus the entries applied, `srvWTTaken`, until then from `ai` to
`ai'`, `srvWTAt`: `apply.Apply` may open one store write transaction per entry, and over the real backend
every write transaction's `Unlock` may write back, costing one of the backend's write-back
tokens, `backend.wbTok`). **The KV model** (2026-10-14, unit T1): the apply thread at the committed
raft log `A` through `ai` (`kvApplied`), the entries above `ai` committed after it (`kvBatch`), at
`A` and those entries after. -/
abbrev EtcdServer.applyEntries.specBatchAt (P : auth.AuthMode → Prop) : Prop :=
  ∀ (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF) (E : apply.AEnv GF) (ρ : ReqNames)
    (b : GoInterface) (ep ap : Loc) (es : GoSlice) (ents : List Loc) (ms : List EntryModel) (f0 : w64)
    (rac : GoChan) (st : ApplyState) (ai at0 a t : w64) (cs : Loc)
    (x : apply.ApplyKV) (γr : ReadNames) (rp : RestartPt) (A : List EntryModel) (γp : WTNames)
    (dv : Option Loc) (w : Nat) (g : w64) (sa : auth.AuthState),
  P E.authMode → (E.authOn = true → receiptBound GF ≤ 2 ^ 48) →
  (ms = [] ∨ (entriesFrom f0 ms ∧ uint.Z f0 ≤ uint.Z ai + 1)) → uint.Z ai + 1 < 2 ^ 64 →
  loopOk γ st ai → logShapeM E.authOn E.lm (unapplied ai ms) →
  dvOk ρ.raft γr.kv.c0 dv (ciEff γ st.k) (g + 1) (unapplied ai ms) →
  uint.Z g = uint.Z γr.raft.ai0 + (ghostOf rp A).length →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerM E.authOn s γ ci TM E ρ γr ∗ srvLessorNilM E.authOn s ∗ batchWaitOk ρ E ms ∗
      taEntriesAddr ap ↦□ es ∗ taRaftAdvancedCAddr ap ↦□ rac ∗ es ↦*□ ents ∗ entriesAt ents ms ∗
      epAppliedIAddr ep ↦ ai ∗ epAppliedTAddr ep ↦ at0 ∗ epConfState ep cs ∗
      epCsAt ρ.raft (ghostOf rp A) cs ∗
      applyThread γ st ∗ applyBackend γ ci b ∗ ciApplying ci a t ∗ srvLgReader s ∗ srvGoRes s ∗
      srvApplyKVM E.authOn s E ρ.wait x sa ∗ srvAppliedOwn γr g ∗ appliedLogAt γr g x.log ∗
      batchCommittedIdx γr ms ∗ srvWTPool E γp ∗ srvWTTaken γp.cnt w ∗ srvFS s ∗
      kvAppliedM E.authOn γr.raft γr.kv srvAuthSt0 (ghostOf rp A) x sa ∗ srvRestR E γr rp A ∗
      kvBatchR γr (ciEff γ st.k) ai rp A (unapplied ai ms) ∗
      dvView ρ.raft dv (ghostOf rp A) ∗ dvRes s ρ.raft dv (A ++ unapplied ai ms) ∗ (match dv with | none => iprop(True) | some n => (letI := srvStor (GF := GF) ρ.raft.raft; nodeRunning n ρ.raft.raft.cl srvClusterN (1 : Qp).half)) ∗
      srvApRes s γr (ghostOf rp A) ∗ srvTokRights E (ciEff γ st.k) }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"applyEntries"))
      (Val #ep)) (Val #ap))
  {{ RET #(); srvFS s ∗ dvView ρ.raft dv (ghostOf rp (A ++ unapplied ai ms)) ∗ (match dv with | none => iprop(True) | some n => (letI := srvStor (GF := GF) ρ.raft.raft; nodeRunning n ρ.raft.raft.cl srvClusterN (1 : Qp).half)) ∗
      srvApRes s γr (ghostOf rp (A ++ unapplied ai ms)) ∗
      ∃ (st' : ApplyState) (ai' at' a' t' : w64) (cs' : Loc) (g' : w64),
        epAppliedIAddr ep ↦ ai' ∗ epAppliedTAddr ep ↦ at' ∗ epConfState ep cs' ∗
        epCsAt ρ.raft (ghostOf rp (A ++ unapplied ai ms)) cs' ∗
        applyThread γ st' ∗ srvTokRights E (ciEff γ st'.k) ∗ applyBackend γ ci b ∗
        ciApplying ci a' t' ∗ srvLgReader s ∗ srvGoRes s ∗
        srvAppliedOwn γr g' ∗ srvWTTaken γp.cnt (w + (unapplied ai ms).length) ∗
        (∃ (x' : apply.ApplyKV) (sa' : auth.AuthState), srvApplyKVM E.authOn s E ρ.wait x' sa' ∗
          ⌜entriesStep (ciEff γ st.k) (unapplied ai ms) x x'⌝ ∗ appliedLogAt γr g' x'.log ∗
          kvAppliedM E.authOn γr.raft γr.kv srvAuthSt0 (ghostOf rp (A ++ unapplied ai ms)) x' sa' ∗
          srvRestR E γr rp (A ++ unapplied ai ms)) ∗
        ⌜uint.Z g' = uint.Z γr.raft.ai0 + (ghostOf rp (A ++ unapplied ai ms)).length ∧
          loopOk γ st' ai' ∧
          uint.Z ai' = max (uint.Z ai) (((ms.getLast?).map (fun m => uint.Z m.index)).getD 0) ∧
          uint.Z ai' = uint.Z ai + (unapplied ai ms).length ∧
          ((unapplied ai ms = [] ∧ ciEff γ st'.k = ciEff γ st.k) ∨
            uint.Z (ciEff γ st'.k) = max (uint.Z (ciEff γ st.k)) (uint.Z ai')) ∧
          termAfter at0 (unapplied ai ms) at'⌝ }}

/-- **`s.applyEntries(…)`** in the environment's auth mode (`.any` excluded), at a restart point
(`specBatchAt`; R2d'a swap batch 3, 2026-11-06: the restart form, which replaces the first-start
form, its instance at `rp = RestartPt.first`, `g = ai`; stronger than it at every caller with
`ai0 ≤ ciEff`, which every existing caller has: `applyAll` supplies `ai ≤ ciEff`). -/
abbrev EtcdServer.applyEntries.specBatch : Prop :=
  EtcdServer.applyEntries.specBatchAt (GF := GF) (hG := hG) (· ≠ .any)

/-- (2026-11-01, J8a-5) **No entries** (a snapshot batch's, `rnApSnap`: raft hands out no committed
entries with a snapshot): `applyEntries` returns at once (its `len(apply.entries) == 0` check). -/
abbrev EtcdServer.applyEntries.specNil : Prop :=
  ∀ (s ep ap : Loc) (es : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      taEntriesAddr ap ↦□ es ∗ es ↦*□ ([] : List Loc) }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"applyEntries"))
      (Val #ep)) (Val #ap))
  {{ RET #(); True }}

/-- **`applyEntries`'s spec** (J8b, 2026-11-01): both cases, the batch (`specBatch`) and the empty batch (`specNil`), for the link. -/
abbrev EtcdServer.applyEntries.spec : Prop :=
  EtcdServer.applyEntries.specBatch (GF := GF) (hG := hG) ∧
    EtcdServer.applyEntries.specNil (GF := GF) (hG := hG)

end spec

end EtcdGrove
end Perennial
