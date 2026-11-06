/-
`(*EtcdServer).apply(es, ep, raftAdvancedC)` (server.go): the apply loop over a batch of
committed entries. Lean-first (no Rocq counterpart); see `InvApplier.lean`, `InvApply.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApplier
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvGoAttach
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApRes
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ApplyNormalOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ApplyWindow

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

/-- `s.apply(…)` in the environment's auth mode (`E.authOn`; step 3 of the auth-mode merge,
2026-10-30: one statement for both modes, `.any` excluded; until then `spec` (auth off) and `specOn`,
now `ModeSpecs.lean`'s `specOff`/`specOn`, corollaries `spec_off`/`spec_on`). As `specOff` (the
statement off, in `ModeSpecs.lean`, with the full account of every row), with the rows that
differ by the mode at `E.authOn`: the server's view (`isServerM`), the committed log's shapes
(`logShapeM`: with auth on, an admitted admin request too), the applier state (`srvApplyKVM`, at the
model's auth state `sa`, unconstrained off), the apply thread's model (`kvAppliedM`, from
`srvAuthSt0`). **With auth on** (only): the server's lessor finds no lease (`srvLessorNilM`), the
receipts' bound, and the rights to issue tokens at the consistent index (`srvTokRights`, `True` off),
at the new consistent index after. (2026-10-31, the snapshot track's S5) `ep.confState` reports
the voters once an entry is applied (`epCsAt`: the first is a validated conf change).

(R2d, Q13 (a), 2026-11-06; DRAFT, the window form, `ApplyWindow.lean`) **In a restarted member's
replay window**: the replays `W` pending and `D` done (`winOk`; no window `W = D = []`, where every
row is the one before, `apply.spec_noWin`). The batch starts with the pending replays, which `apply`
applies v2-only (their indices at most the consistent index, the premise F2 added: `entriesStep`'s
`v3` false); the
ghost applied index is `winGhost` of Go's (`f0 - 1` before, `appliedi` after; `setAppliedIndex`'s
replay case below it); the ghost log grows by the new entries only (`winNew W ms`); the rest
buckets' resources are the window's (`srvRestW`, the replays after `A`'s model; `srvRest`'s again at
the window's end, last writer wins). Go's own rows (`ep`'s fields, the consistent index, the write
tokens, one per entry, `entriesStep` over the whole batch) are as before. -/
abbrev EtcdServer.apply.spec : Prop :=
  ∀ (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF) (E : apply.AEnv GF) (ρ : ReqNames)
    (b : GoInterface) (es : GoSlice) (ents : List Loc) (ms : List EntryModel) (f0 : w64) (ep : Loc) (cs : Loc)
    (rac : GoChan) (st : ApplyState) (a at0 : w64) (x : apply.ApplyKV) (γr : ReadNames)
    (A : List EntryModel) (γp : WTNames) (dv : Option Loc) (w : Nat) (sa : auth.AuthState)
    (W D : List EntryModel),
  E.authMode ≠ .any → (E.authOn = true → receiptBound GF ≤ 2 ^ 48) →
  ms ≠ [] → entriesFrom f0 ms → loopOk γ st (f0 - 1) → logShapeM E.authOn E.lm ms →
  dvOk ρ.raft γr.kv.c0 dv (ciEff γ st.k) f0 ms →
  -- (R2d, DRAFT) the replay window
  winOk A D W ms →
  -- (R2d, Q17 F2) the pending replays at or below the consistent index (Go's `shouldApplyV3`,
  -- `server.go:1933-1937`)
  (∀ m ∈ W, uint.Z m.index ≤ uint.Z (ciEff γ st.k)) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerM E.authOn s γ ci TM E ρ γr ∗ srvLessorNilM E.authOn s ∗ batchWaitOk ρ E ms ∗ es ↦*□ ents ∗
      entriesAt ents ms ∗
      applyThread γ st ∗ applyBackend γ ci b ∗ ciApplying ci a at0 ∗ epConfState ep cs ∗ epCsAt ρ.raft A cs ∗
      srvLgReader s ∗ srvGoRes s ∗ srvApplyKVM E.authOn s E ρ.wait x sa ∗ srvAppliedOwn γr (winGhost (f0 - 1) W) ∗
      appliedLogAt γr (winGhost (f0 - 1) W) x.log ∗ batchCommittedIdx γr ms ∗ srvWTPool E γp ∗
      srvWTTaken γp.cnt w ∗ srvFS s ∗
      kvAppliedM E.authOn γr.raft γr.kv srvAuthSt0 A x sa ∗ srvRestW E γr A D ∗
      kvBatchW γr (ciEff γ st.k) (f0 - 1) W A ms ∗
      dvView ρ.raft dv A ∗ dvRes s ρ.raft dv (A ++ winNew W ms) ∗ (match dv with | none => iprop(True) | some n => (letI := srvStor (GF := GF) ρ.raft.raft; nodeRunning n ρ.raft.raft.cl srvClusterN (1 : Qp).half)) ∗ srvApRes s γr A ∗
      -- (C1's A1, 2026-10-28) the rights to issue tokens at the consistent index
      srvTokRights E (ciEff γ st.k) }}
    (App (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"apply"))
      (Val #es)) (Val #ep)) (Val #rac))
  {{ (appliedt appliedi : w64) (shouldStop : Bool),
      RET (PairV (PairV #appliedt #appliedi) #shouldStop); srvFS s ∗ dvView ρ.raft dv (A ++ winNew W ms) ∗ (match dv with | none => iprop(True) | some n => (letI := srvStor (GF := GF) ρ.raft.raft; nodeRunning n ρ.raft.raft.cl srvClusterN (1 : Qp).half)) ∗
      srvApRes s γr (A ++ winNew W ms) ∗
      ∃ (st' : ApplyState) (a' at' : w64) (csl : Loc),
        applyThread γ st' ∗ srvTokRights E (ciEff γ st'.k) ∗ applyBackend γ ci b ∗
        ciApplying ci a' at' ∗
        epConfState ep csl ∗ epCsAt ρ.raft (A ++ winNew W ms) csl ∗ srvLgReader s ∗ srvGoRes s ∗
        srvAppliedOwn γr (winGhost appliedi (winRest W ms)) ∗
        srvWTTaken γp.cnt (w + ms.length) ∗
        (∃ (x' : apply.ApplyKV) (sa' : auth.AuthState), srvApplyKVM E.authOn s E ρ.wait x' sa' ∗
          ⌜entriesStep (ciEff γ st.k) ms x x'⌝ ∗ appliedLogAt γr (winGhost appliedi (winRest W ms)) x'.log ∗
          kvAppliedM E.authOn γr.raft γr.kv srvAuthSt0 (A ++ winNew W ms) x' sa' ∗
            srvRestW E γr (A ++ winNew W ms) (winDone D W ms)) ∗
        ⌜(ms.getLast?).map EntryModel.index = some appliedi ∧
          (ms.getLast?).map EntryModel.term = some appliedt ∧
          loopOk γ st' appliedi ∧
          uint.Z (ciEff γ st'.k) = max (uint.Z (ciEff γ st.k)) (uint.Z appliedi) ∧
          shouldStop = false⌝ }}

end spec

end EtcdGrove
end Perennial
