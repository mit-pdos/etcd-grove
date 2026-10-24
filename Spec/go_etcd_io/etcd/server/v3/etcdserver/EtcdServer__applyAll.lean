/-
`s.applyAll(ep, ap)` (`server.go`): the apply loop's step. Lean-first (no Rocq counterpart); the request path's unit 4b
(2026-10-13).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApplyAll
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvGoAttach

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`s.applyAll(ep, ap)`**, the apply loop's step on one `toApply` from raft (`ap`: its entries
`ms`, consecutive from `f0` with no gap after the applied index `ai`, as `applyEntries` takes them;
no snapshot, `rnApP`; its `notifyc`, a unit bag channel raft signals once it persisted the batch),
by the apply thread: `applySnapshot` (nothing: no snapshot), `applyEntries` (the KV goes from `x`
to `x'` by `entriesStep` over the entries above `ai`, under their shapes, `logShape`; the
applied index to `ai'`,
the last entry's or `ai`; each `setAppliedIndex` deposits the KV log after its entry, so the log
applied through `ai'` is `x'.log`; 2026-10-14, unit C2a: each entry committed,
`batchCommittedIdx`, and its log deposited ahead of its result), the backend's verification (`VerifyBackendConsistency`, the
trust boundary), the `proposalsApplied` gauge, **`applyWait.Trigger(ai')`** (with `appliedAtLeast γr
ai'`: the read loop's `ApplyWait` waiters through `ai'` are released once the KV has applied through
`ai'`), `<-ap.notifyc`, the snapshot trigger (`snapshotIfNeededAndCompactRaftLog`, over the
`snapshot`/`compactRaftLog` contracts), and a pending merged-snapshot request on `msgSnapC`
(names-only contracts). The apply thread's resources come back at `ai'`, with `loopOk`. **The
write budget** (the backend's unit 6, merged 2026-10-13): `applyEntries`' one write token of the
store per entry above `ai`, from the budget `srvWTPool E` (D19b, 2026-10-18; until then
`txn.storeWTs E.γ (unapplied ai ms).length`, handed in). **The KV model**
(2026-10-14, unit T1): as `applyEntries` (`kvApplied`, `kvBatch`). (D22 S-h, 2026-10-20, S-0's
amendment) The applied term: `ep.appliedt` the last applied entry's term, unchanged with none
(`termAfter`), which the merged snapshot's metadata carries. (D22 S-h) The `msgSnapC` branch stays
dead (`isServerApplyAll`'s bag carries nothing); `SnapSendBranch.lean`'s `snapBranch_send` is its
two calls, proved for S-l. -/
abbrev EtcdServer.applyAll.spec : Prop :=
  ∀ (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF) (E : apply.AEnv GF)
    (ρ : ReqNames) (γr : ReadNames) (b : GoInterface) (ep ap : Loc) (es : GoSlice)
    (ents : List Loc) (ms : List EntryModel) (f0 : w64) (rac nc : GoChan) (st : ApplyState)
    (ai at0 a t : w64) (cs : Loc) (x : apply.ApplyKV) (A : List EntryModel)
    (mst : Loc) (γs : MemStorNames) (γp : GName),
  (ms = [] ∨ (entriesFrom f0 ms ∧ uint.Z f0 ≤ uint.Z ai + 1)) → uint.Z ai + 1 < 2 ^ 64 →
  loopOk γ st ai → logShape (unapplied ai ms) →
  -- (2026-10-19, D21 M3) the storage's cap at least `1` (`snapshotIfNeededAndCompactRaftLog`'s)
  1 ≤ γs.cap →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServer s γ ci TM E ρ γr ∗ isServerApplyAll s γr ∗ batchWaitOk ρ E ms ∗
      taEntriesAddr ap ↦□ es ∗ taRaftAdvancedCAddr ap ↦□ rac ∗
      -- (D19i part 1) closed once raft advanced past the batch: the storage's floor past it
      rnAdvChan rac (memFloorAtLeast mst γs
        (max (uint.Z ai) (((ms.getLast?).map (fun m => uint.Z m.index)).getD 0))) ∗ taSnapshotAddr ap ↦□ (null : Loc) ∗
      taNotifycAddr ap ↦□ nc ∗ isUnitBag nc ∗ es ↦*□ ents ∗ entriesAt ents ms ∗
      epAppliedIAddr ep ↦ ai ∗ epAppliedTAddr ep ↦ at0 ∗ epConfState ep cs ∗
      srvSnapState s ep mst γs ai (W64 0) ∗ applyThread γ st ∗ applyBackend γ ci b ∗ ciApplying ci a t ∗
      srvLgReader s ∗ srvGoRes s ∗ srvBemuReaderAt s E.γbe ∗ srvApplyKV s E ρ.wait x ∗ srvAppliedOwn γr ai ∗
      appliedLogAt γr ai x.log ∗ batchCommittedIdx γr ms ∗ srvWTPool E γp ∗ srvWTAt γp ai ∗
      kvApplied γr.raft γr.kv A x ∗ srvRest E γr A ∗ kvBatch γr (ciEff γ st.k) ai A (unapplied ai ms) }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"applyAll")) (Val #ep))
      (Val #ap))
  {{ RET #();
      -- (D22 receiver epochs, S7f, 2026-10-23) the apply thread's backend after the batch: the
      -- protocol's names `γ'` and the environment `E'` at some backend's (`beSucc`), with the
      -- server's view at them (`applySnapshot` moves the backend; without a snapshot they are
      -- `γ`, `TM`, `E`, `b`)
      ∃ (γ' : ApplyNames) (TM' : MetaCI → IProp GF) (E' : apply.AEnv GF) (b' : GoInterface)
        (st' : ApplyState) (ai' at' a' t' : w64) (cs' : Loc),
        ⌜beSucc γ E γ' E'⌝ ∗ isServer s γ' ci TM' E' ρ γr ∗
        epAppliedIAddr ep ↦ ai' ∗ epAppliedTAddr ep ↦ at' ∗ epConfState ep cs' ∗
        srvSnapState s ep mst γs ai' (W64 0) ∗ applyThread γ' st' ∗ applyBackend γ' ci b' ∗ ciApplying ci a' t' ∗
        srvLgReader s ∗ srvGoRes s ∗ srvBemuReaderAt s E.γbe ∗ srvAppliedOwn γr ai' ∗ appliedAtLeast γr ai' ∗
        srvWTAt γp ai' ∗
        (∃ x' : apply.ApplyKV, srvApplyKV s E' ρ.wait x' ∗
          ⌜entriesStep (ciEff γ st.k) (unapplied ai ms) x x'⌝ ∗ appliedLogAt γr ai' x'.log ∗
          kvApplied γr.raft γr.kv (A ++ unapplied ai ms) x' ∗ srvRest E' γr (A ++ unapplied ai ms)) ∗
        ⌜loopOk γ' st' ai' ∧
          uint.Z ai' = max (uint.Z ai) (((ms.getLast?).map (fun m => uint.Z m.index)).getD 0) ∧
          (ciEff γ' st'.k = ciEff γ st.k ∨
            uint.Z (ciEff γ' st'.k) = max (uint.Z (ciEff γ st.k)) (uint.Z ai')) ∧
          -- (D22 S-h, 2026-10-20; S-0's amendment) the applied term: the last applied entry's
          termAfter at0 (unapplied ai ms) at'⌝ }}

end spec

end EtcdGrove
end Perennial
