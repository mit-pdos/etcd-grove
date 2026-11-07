/-
`(*EtcdServer).apply(es, ep, raftAdvancedC)` (server.go): the apply loop over a batch of
committed entries. Lean-first (no Rocq counterpart); see `InvApplier.lean`, `InvApply.lean`.
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

/-- **`s.apply(…)` in the auth modes `P`, at a restart point** (R2d'a swap batch 3, 2026-11-06:
until then `spec` was the first-start form, with the corollaries `ModeSpecs.lean`'s `specOff`/`specOn`;
the restart form was `ApplyR.lean`'s `specROff` and `ApplyROn.lean`'s `specROn`, now one statement
over the environment's mode). `spec` is `specAt (· ≠ .any)`; the proof's two arms are `specAt` at
`.off` and at `on _`.

Go's rows at Go's log `A` (the log raft handed this incarnation): the batch from `f0`, Go's index
`f0 - 1` (`kvBatchR`), `loopOk`, the returned index and term. The ghost rows at the ghost log
`ghostOf rp A` (`RestReplay.lean`): the applied index `g` and its log, the KV model, `ep.confState`'s
voters, the view, the membership resource; the rest buckets `srvRestR` (the replay arm inside the
window). At the pin `673da07c8` (`server.go:1922-1972`) the entries at or below the effective
consistent index are replayed v2-only (`shouldApplyV3` false): the ghost rows stay
(`setAppliedIndex`'s replay case), the rest buckets' image takes the attribute writes
(`restEntryV2`), and the replay closes on the model when Go's log reaches the backend's
(`restReplay_closeI`). The view's premise at the ghost index (`dvOk … (g + 1)`, Q19). **A first
start** (`rp = RestartPt.first`, `g = f0 - 1`) is the old first-start text: `ghostOf_first`,
`srvRestR_first`, `kvBatchR_first` (given `ai0 ≤ ciEff`, which a first start's `ai0 = 0` gives), and
the ghost index's equation `uint.Z (f0 - 1) = ai0 + |A|` (`kvBatch`'s).

The rows that differ by the mode, at `E.authOn`: the server's view (`isServerM`), the committed log's
shapes (`logShapeM`: with auth on, an admitted admin request too), the applier state (`srvApplyKVM`,
at the model's auth state `sa`, unconstrained off), the apply thread's model (`kvAppliedM`, from
`srvAuthSt0`). **With auth on** (only): the server's lessor finds no lease (`srvLessorNilM`), the
receipts' bound, and the rights to issue tokens at the consistent index (`srvTokRights`, `True` off),
at the new consistent index after. (2026-10-31, the snapshot track's S5) `ep.confState` reports the
voters once an entry is applied (`epCsAt`: the first is a validated conf change).

The contract (until swap batch 3, `ModeSpecs.lean`'s `apply.specOff`'s account, at `A` for the ghost
log): `s.apply(es, ep, rac)`, by the apply thread, on a non-empty batch of consecutive
committed entries from `f0` (`entriesFrom`), with the protocol's state `st` processed through
the larger of `ci` and `f0 - 1` (`loopOk`): each entry at or below `ci` is replayed with no
backend writes (`ApplyV2storeOnly`), each above is applied (`ApplyBoth`), and afterwards
`ci` and the processed-through index are both the larger of the old `ci` and the last index
`L`, which it returns with its term. So no entry's writes are applied twice, and none above
`ci` is skipped. **The KV** (the apply package's unit 3): the apply thread's applier state goes
from `x` to `x'` by `entriesStep c ms x x'` (`c` the consistent index the batch starts at: each
normal entry applied by `apply.Apply`, with `v3` iff above `c`), under `logShape ms` (each
normal entry's request meets its premise wherever the size clauses hold; the apply thread's log
is small, `srvApplyKV_small`, so they hold at the state each entry meets: D19c's move,
2026-10-18; until then `entriesOk c ms x`, the premise at every state the batch can reach). **The wait** (unit 2 of the
request path): `batchWaitOk` (each normal entry's id claimed for its data; each conf change's id,
`ccIdOf`, no KV request's registration), so every `Trigger` meets the registry's contract. **The
applied index** (the request path's unit 4b): the apply thread's half of the ghost applied index
(`srvAppliedOwn γr`) goes from `f0 - 1` to the last index, each `setAppliedIndex` depositing the KV
log after its entry, so the last index's log is `x'.log` (`appliedLogAt`); since 2026-10-14 (unit
C2a) from the log applied through `f0 - 1` the KV's (`appliedLogAt γr (f0 - 1) x.log`), with each
entry committed (`batchCommittedIdx`: raft's batches, `rnApP`), each entry's log deposited ahead
of its result (`applyEntryNormal`'s `srvAppliedPre`). **The KV model** (2026-10-14, unit T1): the
apply thread at the committed raft log `A` through `f0 - 1` (`kvApplied`), the batch committed after
it (`kvBatch`), at `A ++ ms` after. **The write budget**
(2026-10-13, unit 6): one write token of the store per entry, spent (a conf change's is wasted);
since D19b (2026-10-18) taken from the budget `srvWTPool E` with a time receipt of the entry's
iteration, until then handed in (`txn.storeWTs E.γ ms.length`); (D22 J5, 2026-10-26) the count of
tokens taken goes from `w` to `w + ms.length` (`srvWTTaken`; until J5 from `f0 - 1` to the last
index, `srvWTAt`). **The stop** (D19m, 2026-10-18): it
returns `shouldStop = false`, since `applyConfChange` removes no member (`ccApplyOk`), so the
caller's `stopWithDelay` is never reached. **The driver's view** (D43 M3, 2026-10-25; raft's
dynamic mode): with a view `dv` (`dvOk`: no replay, the node at the server's decoder), the view
after `A` goes to the view after `A ++ ms`, each conf entry applied through `applyConfChange`;
without, nothing (raft's static mode, or no conf entry in the batch). **The membership** (D43
M5e, 2026-10-26): the apply thread's membership resource (`srvApRes`: the fields and the cluster
and transport `applyConfChange` writes) from `A` to `A ++ ms`. -/
abbrev EtcdServer.apply.specAt (P : auth.AuthMode → Prop) : Prop :=
  ∀ (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF) (E : apply.AEnv GF) (ρ : ReqNames)
    (b : GoInterface) (es : GoSlice) (ents : List Loc) (ms : List EntryModel) (f0 : w64) (ep : Loc) (cs : Loc)
    (rac : GoChan) (st : ApplyState) (a at0 : w64) (x : apply.ApplyKV) (γr : ReadNames)
    (rp : RestartPt) (A : List EntryModel) (γp : WTNames) (dv : Option Loc) (w : Nat) (g : w64)
    (sa : auth.AuthState),
  P E.authMode → (E.authOn = true → receiptBound GF ≤ 2 ^ 48) →
  ms ≠ [] → entriesFrom f0 ms → loopOk γ st (f0 - 1) → logShapeM E.authOn E.lm ms →
  dvOk ρ.raft γr.kv.c0 dv (ciEff γ st.k) (g + 1) ms →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerM E.authOn s γ ci TM E ρ γr ∗ srvLessorNilM E.authOn s ∗ batchWaitOk ρ E ms ∗
      es ↦*□ ents ∗ entriesAt ents ms ∗
      applyThread γ st ∗ applyBackend γ ci b ∗ ciApplying ci a at0 ∗ epConfState ep cs ∗
      epCsAt ρ.raft (ghostOf rp A) cs ∗
      srvLgReader s ∗ srvGoRes s ∗ srvApplyKVM E.authOn s E ρ.wait x sa ∗ srvAppliedOwn γr g ∗
      appliedLogAt γr g x.log ∗ batchCommittedIdx γr ms ∗ srvWTPool E γp ∗
      srvWTTaken γp.cnt w ∗ srvFS s ∗
      kvAppliedM E.authOn γr.raft γr.kv srvAuthSt0 (ghostOf rp A) x sa ∗ srvRestR E γr rp A ∗
      kvBatchR γr (ciEff γ st.k) (f0 - 1) rp A ms ∗
      ⌜uint.Z g = uint.Z γr.raft.ai0 + (ghostOf rp A).length⌝ ∗
      dvView ρ.raft dv (ghostOf rp A) ∗ dvRes s ρ.raft dv (A ++ ms) ∗
      (match dv with | none => iprop(True) | some n => (letI := srvStor (GF := GF) ρ.raft.raft; nodeRunning n ρ.raft.raft.cl srvClusterN (1 : Qp).half)) ∗
      srvApRes s γr (ghostOf rp A) ∗
      -- (C1's A1, 2026-10-28) the rights to issue tokens at the consistent index
      srvTokRights E (ciEff γ st.k) }}
    (App (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"apply"))
      (Val #es)) (Val #ep)) (Val #rac))
  {{ (appliedt appliedi : w64) (shouldStop : Bool),
      RET (PairV (PairV #appliedt #appliedi) #shouldStop);
        srvFS s ∗ dvView ρ.raft dv (ghostOf rp (A ++ ms)) ∗
        (match dv with | none => iprop(True) | some n => (letI := srvStor (GF := GF) ρ.raft.raft; nodeRunning n ρ.raft.raft.cl srvClusterN (1 : Qp).half)) ∗
        srvApRes s γr (ghostOf rp (A ++ ms)) ∗
        (∃ (st' : ApplyState) (a' at' : w64) (csl : Loc) (g' : w64),
          applyThread γ st' ∗ srvTokRights E (ciEff γ st'.k) ∗ applyBackend γ ci b ∗
          ciApplying ci a' at' ∗
          epConfState ep csl ∗ epCsAt ρ.raft (ghostOf rp (A ++ ms)) csl ∗ srvLgReader s ∗
          srvGoRes s ∗ srvAppliedOwn γr g' ∗
          srvWTTaken γp.cnt (w + ms.length) ∗
          (∃ (x' : apply.ApplyKV) (sa' : auth.AuthState), srvApplyKVM E.authOn s E ρ.wait x' sa' ∗
            ⌜entriesStep (ciEff γ st.k) ms x x'⌝ ∗ appliedLogAt γr g' x'.log ∗
            kvAppliedM E.authOn γr.raft γr.kv srvAuthSt0 (ghostOf rp (A ++ ms)) x' sa' ∗
            srvRestR E γr rp (A ++ ms)) ∗
          ⌜uint.Z g' = uint.Z γr.raft.ai0 + (ghostOf rp (A ++ ms)).length ∧
            (ms.getLast?).map EntryModel.index = some appliedi ∧
            (ms.getLast?).map EntryModel.term = some appliedt ∧
            loopOk γ st' appliedi ∧
            uint.Z (ciEff γ st'.k) = max (uint.Z (ciEff γ st.k)) (uint.Z appliedi) ∧
            shouldStop = false⌝) }}

/-- **`s.apply(…)`**, the loop in the environment's auth mode (`.any` excluded), at a restart point
(`specAt`; R2d'a swap batch 3, 2026-11-06: the restart form, which replaces the first-start form,
its instance at `rp = RestartPt.first`, `g = f0 - 1`; stronger than it at every caller with
`ai0 ≤ ciEff`, which every existing caller has: `applyAll` supplies `ai ≤ ciEff`). -/
abbrev EtcdServer.apply.spec : Prop :=
  EtcdServer.apply.specAt (GF := GF) (hG := hG) (· ≠ .any)

end spec

end EtcdGrove
end Perennial
