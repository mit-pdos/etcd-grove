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

/-- `s.applyEntries(ep, ap)`, by the apply thread: the entries of `ap` (consecutive from
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
abbrev EtcdServer.applyEntries.spec : Prop :=
  ∀ (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF) (E : apply.AEnv GF) (ρ : ReqNames)
    (b : GoInterface) (ep ap : Loc) (es : GoSlice) (ents : List Loc) (ms : List EntryModel) (f0 : w64)
    (rac : GoChan) (st : ApplyState) (ai at0 a t : w64) (cs : Loc)
    (x : apply.ApplyKV) (γr : ReadNames) (A : List EntryModel) (γp : GName) (dv : Option Loc) (w : Nat),
  (ms = [] ∨ (entriesFrom f0 ms ∧ uint.Z f0 ≤ uint.Z ai + 1)) → uint.Z ai + 1 < 2 ^ 64 →
  loopOk γ st ai → logShape (unapplied ai ms) →
  -- (D43 M3, 2026-10-25) the driver's view, `apply`'s
  dvOk ρ.raft γr.kv.c0 dv (ciEff γ st.k) (ai + 1) (unapplied ai ms) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ isServer s γ ci TM E ρ γr ∗ batchWaitOk ρ E ms ∗ taEntriesAddr ap ↦□ es ∗ taRaftAdvancedCAddr ap ↦□ rac ∗
      es ↦*□ ents ∗ entriesAt ents ms ∗
      epAppliedIAddr ep ↦ ai ∗ epAppliedTAddr ep ↦ at0 ∗ epConfState ep cs ∗
      applyThread γ st ∗ applyBackend γ ci b ∗ ciApplying ci a t ∗ srvLgReader s ∗ srvGoRes s ∗
      srvApplyKV s E ρ.wait x ∗ srvAppliedOwn γr ai ∗ appliedLogAt γr ai x.log ∗
      batchCommittedIdx γr ms ∗ srvWTPool E γp ∗ srvWTTaken γp w ∗ srvFS s ∗
      kvApplied γr.raft γr.kv A x ∗ srvRest E γr A ∗ kvBatch γr (ciEff γ st.k) ai A (unapplied ai ms) ∗
      dvView ρ.raft dv A ∗ dvRes s ρ.raft dv (A ++ unapplied ai ms) ∗ srvApRes s γr A }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"applyEntries"))
      (Val #ep)) (Val #ap))
  {{ RET #(); srvFS s ∗ dvView ρ.raft dv (A ++ unapplied ai ms) ∗
      srvApRes s γr (A ++ unapplied ai ms) ∗
      ∃ (st' : ApplyState) (ai' at' a' t' : w64) (cs' : Loc),
        epAppliedIAddr ep ↦ ai' ∗ epAppliedTAddr ep ↦ at' ∗ epConfState ep cs' ∗
        applyThread γ st' ∗ applyBackend γ ci b ∗ ciApplying ci a' t' ∗ srvLgReader s ∗ srvGoRes s ∗
        srvAppliedOwn γr ai' ∗ srvWTTaken γp (w + (unapplied ai ms).length) ∗
        (∃ x' : apply.ApplyKV, srvApplyKV s E ρ.wait x' ∗
          ⌜entriesStep (ciEff γ st.k) (unapplied ai ms) x x'⌝ ∗ appliedLogAt γr ai' x'.log ∗
          kvApplied γr.raft γr.kv (A ++ unapplied ai ms) x' ∗ srvRest E γr (A ++ unapplied ai ms)) ∗
        ⌜loopOk γ st' ai' ∧
          uint.Z ai' = max (uint.Z ai) (((ms.getLast?).map (fun m => uint.Z m.index)).getD 0) ∧
          -- (D22 J5) one index per entry applied
          uint.Z ai' = uint.Z ai + (unapplied ai ms).length ∧
          (ciEff γ st'.k = ciEff γ st.k ∨
            uint.Z (ciEff γ st'.k) = max (uint.Z (ciEff γ st.k)) (uint.Z ai')) ∧
          -- (D22 S-h, 2026-10-20; S-0's amendment) the applied term: the last applied entry's
          termAfter at0 (unapplied ai ms) at'⌝ }}


/-- **`spec` in the auth mode `on`** (the auth plan's E3p, 2026-10-27): over `apply.specOn` (the
server with auth on, `logShapeOn`, the applier state with the auth row at the model's auth state
`sa`, the apply thread at the mode-`on` model; the lessor finding no lease, the receipts' bound),
after the batch at the model's state after `A ++ unapplied ai ms` (its auth state `sa'`). -/
abbrev EtcdServer.applyEntries.specOn : Prop :=
  ∀ (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF) (E : apply.AEnv GF) (ρ : ReqNames)
    (b : GoInterface) (ep ap : Loc) (es : GoSlice) (ents : List Loc) (ms : List EntryModel) (f0 : w64)
    (rac : GoChan) (st : ApplyState) (ai at0 a t : w64) (cs : Loc)
    (x : apply.ApplyKV) (γr : ReadNames) (A : List EntryModel) (γp : GName) (dv : Option NodeNames) (w : Nat)
    (γa : auth.AuthNames) (sa : auth.AuthState),
  E.authMode = .on γa → receiptBound GF ≤ 2 ^ 48 →
  (ms = [] ∨ (entriesFrom f0 ms ∧ uint.Z f0 ≤ uint.Z ai + 1)) → uint.Z ai + 1 < 2 ^ 64 →
  loopOk γ st ai → logShapeOn (unapplied ai ms) →
  -- (D43 M3, 2026-10-25) the driver's view, `apply`'s
  dvOk ρ.raft γr.kv.c0 dv (ciEff γ st.k) (ai + 1) (unapplied ai ms) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ isServerM true s γ ci TM E ρ γr ∗ srvLessorNil s ∗ batchWaitOk ρ E ms ∗ taEntriesAddr ap ↦□ es ∗ taRaftAdvancedCAddr ap ↦□ rac ∗
      es ↦*□ ents ∗ entriesAt ents ms ∗
      epAppliedIAddr ep ↦ ai ∗ epAppliedTAddr ep ↦ at0 ∗ epConfState ep cs ∗
      applyThread γ st ∗ applyBackend γ ci b ∗ ciApplying ci a t ∗ srvLgReader s ∗ srvGoRes s ∗
      srvApplyKVOn s E ρ.wait x sa ∗ srvAppliedOwn γr ai ∗ appliedLogAt γr ai x.log ∗
      batchCommittedIdx γr ms ∗ srvWTPool E γp ∗ srvWTTaken γp w ∗ srvFS s ∗
      kvAppliedOn γr.raft γr.kv srvAuthSt0 A x sa ∗ srvRest E γr A ∗ kvBatch γr (ciEff γ st.k) ai A (unapplied ai ms) ∗
      dvView ρ.raft dv A ∗ dvRes s ρ.raft dv (A ++ unapplied ai ms) ∗ srvApRes s γr A }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"applyEntries"))
      (Val #ep)) (Val #ap))
  {{ RET #(); srvFS s ∗ dvView ρ.raft dv (A ++ unapplied ai ms) ∗
      srvApRes s γr (A ++ unapplied ai ms) ∗
      ∃ (st' : ApplyState) (ai' at' a' t' : w64) (cs' : Loc),
        epAppliedIAddr ep ↦ ai' ∗ epAppliedTAddr ep ↦ at' ∗ epConfState ep cs' ∗
        applyThread γ st' ∗ applyBackend γ ci b ∗ ciApplying ci a' t' ∗ srvLgReader s ∗ srvGoRes s ∗
        srvAppliedOwn γr ai' ∗ srvWTTaken γp (w + (unapplied ai ms).length) ∗
        (∃ (x' : apply.ApplyKV) (sa' : auth.AuthState), srvApplyKVOn s E ρ.wait x' sa' ∗
          ⌜entriesStep (ciEff γ st.k) (unapplied ai ms) x x'⌝ ∗ appliedLogAt γr ai' x'.log ∗
          kvAppliedOn γr.raft γr.kv srvAuthSt0 (A ++ unapplied ai ms) x' sa' ∗ srvRest E γr (A ++ unapplied ai ms)) ∗
        ⌜loopOk γ st' ai' ∧
          uint.Z ai' = max (uint.Z ai) (((ms.getLast?).map (fun m => uint.Z m.index)).getD 0) ∧
          -- (D22 J5) one index per entry applied
          uint.Z ai' = uint.Z ai + (unapplied ai ms).length ∧
          (ciEff γ st'.k = ciEff γ st.k ∨
            uint.Z (ciEff γ st'.k) = max (uint.Z (ciEff γ st.k)) (uint.Z ai')) ∧
          -- (D22 S-h, 2026-10-20; S-0's amendment) the applied term: the last applied entry's
          termAfter at0 (unapplied ai ms) at'⌝ }}

end spec

end EtcdGrove
end Perennial
