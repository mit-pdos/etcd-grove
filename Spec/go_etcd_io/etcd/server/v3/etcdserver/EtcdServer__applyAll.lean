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
to `x'` by `entriesStep` over the entries above `ai`, under `entriesOk`; the applied index to `ai'`,
the last entry's or `ai`; each `setAppliedIndex` deposits the KV log after its entry, so the log
applied through `ai'` is `x'.log`), the backend's verification (`VerifyBackendConsistency`, the
trust boundary), the `proposalsApplied` gauge, **`applyWait.Trigger(ai')`** (with `appliedAtLeast γr
ai'`: the read loop's `ApplyWait` waiters through `ai'` are released once the KV has applied through
`ai'`), `<-ap.notifyc`, the snapshot trigger (`snapshotIfNeededAndCompactRaftLog`, over the
`snapshot`/`compactRaftLog` contracts), and a pending merged-snapshot request on `msgSnapC`
(names-only contracts). The apply thread's resources come back at `ai'`, with `loopOk`. **The
write budget** (the backend's unit 6, merged 2026-10-13): `applyEntries`' one write token of the
store per entry above `ai` (`txn.storeWTs E.γ (unapplied ai ms).length`), spent. -/
abbrev EtcdServer.applyAll.spec : Prop :=
  ∀ (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF) (E : apply.AEnv GF)
    (ρ : ReqNames) (γr : ReadNames) (b : GoInterface) (ep ap : Loc) (es : GoSlice)
    (ents : List Loc) (ms : List EntryModel) (f0 : w64) (rac nc : GoChan) (st : ApplyState)
    (ai at0 a t : w64) (cs : Loc) (x : apply.ApplyKV),
  (ms = [] ∨ (entriesFrom f0 ms ∧ uint.Z f0 ≤ uint.Z ai + 1)) → uint.Z ai + 1 < 2 ^ 64 →
  loopOk γ st ai → entriesOk (ciEff γ st.k) (unapplied ai ms) x →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServer s γ ci TM E ρ γr ∗ isServerApplyAll s γr ∗ batchWaitOk ρ E ms ∗
      taEntriesAddr ap ↦□ es ∗ taRaftAdvancedCAddr ap ↦□ rac ∗ taSnapshotAddr ap ↦□ (null : Loc) ∗
      taNotifycAddr ap ↦□ nc ∗ isUnitBag nc ∗ es ↦*□ ents ∗ entriesAt ents ms ∗
      epAppliedIAddr ep ↦ ai ∗ epAppliedTAddr ep ↦ at0 ∗ epConfStateAddr ep ↦ cs ∗
      srvSnapState s ep ∗ applyThread γ st ∗ applyBackend γ ci b ∗ ciApplying ci a t ∗
      srvLgReader s ∗ srvGoRes s ∗ srvBemuReader s ∗ srvApplyKV s E ρ.wait x ∗ srvAppliedOwn γr ai ∗
      appliedLogAt γr ai x.log ∗ txn.storeWTs E.γ (unapplied ai ms).length }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"applyAll")) (Val #ep))
      (Val #ap))
  {{ RET #();
      ∃ (st' : ApplyState) (ai' at' a' t' : w64) (cs' : Loc),
        epAppliedIAddr ep ↦ ai' ∗ epAppliedTAddr ep ↦ at' ∗ epConfStateAddr ep ↦ cs' ∗
        srvSnapState s ep ∗ applyThread γ st' ∗ applyBackend γ ci b ∗ ciApplying ci a' t' ∗
        srvLgReader s ∗ srvGoRes s ∗ srvBemuReader s ∗ srvAppliedOwn γr ai' ∗ appliedAtLeast γr ai' ∗
        (∃ x' : apply.ApplyKV, srvApplyKV s E ρ.wait x' ∗
          ⌜entriesStep (ciEff γ st.k) (unapplied ai ms) x x'⌝ ∗ appliedLogAt γr ai' x'.log) ∗
        ⌜loopOk γ st' ai' ∧
          uint.Z ai' = max (uint.Z ai) (((ms.getLast?).map (fun m => uint.Z m.index)).getD 0) ∧
          (ciEff γ st'.k = ciEff γ st.k ∨
            uint.Z (ciEff γ st'.k) = max (uint.Z (ciEff γ st.k)) (uint.Z ai'))⌝ }}

end spec

end EtcdGrove
end Perennial
