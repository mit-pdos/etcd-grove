/-
**The server's mode variants of its merged specs** (the auth-mode merge,
`notes/auth-mode-merge-plan.md`, 2026-10-29): a merged spec is one statement for both auth modes,
the mode the environment's (`E.authOn`); for each, until its callers are merged too, the
statements of the two modes as they were (`specOff`, with the premise `E.authOn = false`, and
`specOn`, with `E.authOn = true`) and their corollaries `spec_off`/`spec_on` (no second proof:
`.claude/skills/spec/PRINCIPLES.md`, "One spec per function"). Each goes when no caller uses it.

The request path (step 5, 2026-10-29): `parseProposeCtxErr`, `processInternalRaftRequestOnce`,
`raftRequest`, `doSerialize`. Their proofs are over the mode `on` (`wp_proofM on`), so their
variants are `<F>.specM on` (the proposer's view `isServerReqM on` fixes `E.authOn = on`,
`isServerReqM_authOn`; `<F>.spec_M : <F>.spec → <F>.specM on`) and, for the mode-off proofs of
`Put`, `DeleteRange`, `Range` and `Txn` not merged yet, `<F>.specOff`, the mode-off statement before
the merge (over `isServerReq`, `reqPropOk`, the result at `kvModel`; `<F>.spec_off`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__snapshotIfNeededAndCompactRaftLog
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__parseProposeCtxErr
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__processInternalRaftRequestOnce
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__raftRequest
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__doSerialize
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Put
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__DeleteRange
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Range
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__applyEntryNormal

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section variants
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-! ## `snapshotIfNeededAndCompactRaftLog` -/

/-- **`spec` with auth off** (a corollary, `spec_off`): the off row (`srvApplyKV`). -/
abbrev EtcdServer.snapshotIfNeededAndCompactRaftLog.specOff : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (γw : GName) (γ : ApplyNames) (ci : Loc) (b : GoInterface) (γr : ReadNames)
    (ep : Loc) (st : ApplyState) (ai at' : w64) (cs : Loc) (a t : w64) (x : apply.ApplyKV)
    (ms : Loc) (γs : MemStorNames),
  E.authOn = false →
  loopOk γ st ai →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerApplyAll s γr ∗ srvSnapState s ep ms γs ai (W64 0) ∗
      epAppliedIAddr ep ↦ ai ∗ epAppliedTAddr ep ↦ at' ∗ epConfState ep cs ∗
      applyThread γ st ∗ applyBackend γ ci b ∗ ciApplying ci a t ∗ srvLgReader s ∗ srvApplyKV s E γw x }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"snapshotIfNeededAndCompactRaftLog"))
      (Val #ep))
  {{ RET #(); ∃ st' : ApplyState, srvSnapState s ep ms γs ai (W64 0) ∗
      epAppliedIAddr ep ↦ ai ∗ epAppliedTAddr ep ↦ at' ∗ epConfState ep cs ∗
      applyThread γ st' ∗ applyBackend γ ci b ∗ ciApplying ci a t ∗ srvLgReader s ∗ srvApplyKV s E γw x ∗ ⌜loopOk γ st' ai ∧ ciEff γ st'.k = ciEff γ st.k⌝ }}

/-- **`spec` with auth on** (a corollary, `spec_on`; the auth plan's E3p, 2026-10-27): the row with the
auth part at the model's auth state `sa` (`srvApplyKVOn`), kept. -/
abbrev EtcdServer.snapshotIfNeededAndCompactRaftLog.specOn : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (γw : GName) (γ : ApplyNames) (ci : Loc) (b : GoInterface) (γr : ReadNames)
    (ep : Loc) (st : ApplyState) (ai at' : w64) (cs : Loc) (a t : w64) (x : apply.ApplyKV)
    (ms : Loc) (γs : MemStorNames) (sa : auth.AuthState),
  E.authOn = true →
  loopOk γ st ai →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerApplyAll s γr ∗ srvSnapState s ep ms γs ai (W64 0) ∗
      epAppliedIAddr ep ↦ ai ∗ epAppliedTAddr ep ↦ at' ∗ epConfState ep cs ∗
      applyThread γ st ∗ applyBackend γ ci b ∗ ciApplying ci a t ∗ srvLgReader s ∗ srvApplyKVOn s E γw x sa }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"snapshotIfNeededAndCompactRaftLog"))
      (Val #ep))
  {{ RET #(); ∃ st' : ApplyState, srvSnapState s ep ms γs ai (W64 0) ∗
      epAppliedIAddr ep ↦ ai ∗ epAppliedTAddr ep ↦ at' ∗ epConfState ep cs ∗
      applyThread γ st' ∗ applyBackend γ ci b ∗ ciApplying ci a t ∗ srvLgReader s ∗ srvApplyKVOn s E γw x sa ∗ ⌜loopOk γ st' ai ∧ ciEff γ st'.k = ciEff γ st.k⌝ }}

/-- **`specOff`**, `spec` with auth off (the auth-mode merge's corollary). -/
theorem EtcdServer.snapshotIfNeededAndCompactRaftLog.spec_off
    (h : EtcdServer.snapshotIfNeededAndCompactRaftLog.spec (GF := GF) (hG := hG)) :
    EtcdServer.snapshotIfNeededAndCompactRaftLog.specOff (GF := GF) (hG := hG) := by
  intro s E γw γ ci b γr ep st ai at' cs a t x ms γs hoff
  have := h s E γw γ ci b γr ep st ai at' cs a t x ms γs srvAuthSt0
  rw [hoff] at this
  exact this

/-- **`specOn`**, `spec` with the mode-`on` row (the auth-mode merge's corollary). -/
theorem EtcdServer.snapshotIfNeededAndCompactRaftLog.spec_on
    (h : EtcdServer.snapshotIfNeededAndCompactRaftLog.spec (GF := GF) (hG := hG)) :
    EtcdServer.snapshotIfNeededAndCompactRaftLog.specOn (GF := GF) (hG := hG) := by
  intro s E γw γ ci b γr ep st ai at' cs a t x ms γs sa hon
  have := h s E γw γ ci b γr ep st ai at' cs a t x ms γs sa
  rw [hon] at this
  exact this

/-- **`specFull` with auth off** (a corollary, `spec_fullOff`; for the snapshot track): the off row (`srvApplyKV`). -/
abbrev EtcdServer.snapshotIfNeededAndCompactRaftLog.specFullOff : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (γw : GName) (γ : ApplyNames) (ci : Loc) (b : GoInterface) (γr : ReadNames)
    (ep : Loc) (st : ApplyState) (ai at' : w64) (cs : Loc) (a t : w64) (x : apply.ApplyKV)
    (ms : Loc) (γs : MemStorNames) (nid : w64) (γp : GName) (w : Nat)
    (TM : MetaCI → IProp GF) (ρ : ReqNames) (kv : GoInterface) (RC RC' : IProp GF),
  E.authOn = false →
  loopOk γ st ai →
  -- (D22 J5) the applied index at most the write tokens taken (no snapshot installed)
  uint.Z ai ≤ w →
  -- (2026-10-30, the repair: snapshots allowed) what `snapshot` takes (its spec, lean's
  -- `specFull`): the consistent index past `ai`, `Release` not failing
  uint.Z ai ≤ uint.Z (ciEff γ st.k) → storage.releaseOk →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerM false s γ ci TM E ρ γr ∗ srvSnapDisk s γr ∗ appliedAtLeast γr ai ∗
      srvKVAddr s ↦□ kv ∗ srvKVCommitOk kv RC RC' ∗ RC ∗ srvSnapStor ms γs γr nid ai at' ∗
      isServerApplyAll s γr ∗ srvWTPool E γp ∗ srvWTTaken γp w ∗ srvSnapState s ep ms γs ai (W64 0) ∗
      srvSnapFrozen γs (uint.nat ai) ∗
      -- (D19i part 1; 2026-10-30, the repair: in place of the storage's floor) the node `nid`'s
      -- applied index past the applied index (`raftAdvancedC`'s, `Compact`'s `J.B`)
      (letI := srvStor (GF := GF) γr.raft.raft; nodeAppliedLb γr.raft.raft.cl nid (uint.nat ai)) ∗
      epAppliedIAddr ep ↦ ai ∗ epAppliedTAddr ep ↦ at' ∗ epConfState ep cs ∗
      applyThread γ st ∗ applyBackend γ ci b ∗ ciApplying ci a t ∗ srvLgReader s ∗ srvApplyKV s E γw x }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"snapshotIfNeededAndCompactRaftLog"))
      (Val #ep))
  {{ RET #(); ∃ st' : ApplyState, (RC ∨ RC') ∗ srvSnapState s ep ms γs ai (W64 0) ∗ srvSnapFrozen γs (uint.nat ai) ∗
      epAppliedIAddr ep ↦ ai ∗ epAppliedTAddr ep ↦ at' ∗ epConfState ep cs ∗
      applyThread γ st' ∗ applyBackend γ ci b ∗ ciApplying ci a t ∗ srvLgReader s ∗ srvApplyKV s E γw x ∗ ⌜loopOk γ st' ai ∧ ciEff γ st'.k = ciEff γ st.k⌝ }}

/-- **`specFull` with auth on** (a corollary, `spec_fullOn`; for the snapshot track; the auth plan's E3p, 2026-10-27): the row with the
auth part at the model's auth state `sa` (`srvApplyKVOn`), kept (`snapshot` takes only the part both
rows share, `srvApplyKVCore`). -/
abbrev EtcdServer.snapshotIfNeededAndCompactRaftLog.specFullOn : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (γw : GName) (γ : ApplyNames) (ci : Loc) (b : GoInterface) (γr : ReadNames)
    (ep : Loc) (st : ApplyState) (ai at' : w64) (cs : Loc) (a t : w64) (x : apply.ApplyKV)
    (ms : Loc) (γs : MemStorNames) (nid : w64) (γp : GName) (w : Nat)
    (TM : MetaCI → IProp GF) (ρ : ReqNames) (kv : GoInterface) (RC RC' : IProp GF)
    (sa : auth.AuthState),
  E.authOn = true →
  loopOk γ st ai →
  -- (D22 J5) the applied index at most the write tokens taken (no snapshot installed)
  uint.Z ai ≤ w →
  -- (2026-10-30, the repair: snapshots allowed) what `snapshot` takes (its spec, lean's
  -- `specFull`): the consistent index past `ai`, `Release` not failing
  uint.Z ai ≤ uint.Z (ciEff γ st.k) → storage.releaseOk →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerM true s γ ci TM E ρ γr ∗ srvSnapDisk s γr ∗ appliedAtLeast γr ai ∗
      srvKVAddr s ↦□ kv ∗ srvKVCommitOk kv RC RC' ∗ RC ∗ srvSnapStor ms γs γr nid ai at' ∗
      isServerApplyAll s γr ∗ srvWTPool E γp ∗ srvWTTaken γp w ∗ srvSnapState s ep ms γs ai (W64 0) ∗
      srvSnapFrozen γs (uint.nat ai) ∗
      -- (D19i part 1; 2026-10-30, the repair: in place of the storage's floor) the node `nid`'s
      -- applied index past the applied index (`raftAdvancedC`'s, `Compact`'s `J.B`)
      (letI := srvStor (GF := GF) γr.raft.raft; nodeAppliedLb γr.raft.raft.cl nid (uint.nat ai)) ∗
      epAppliedIAddr ep ↦ ai ∗ epAppliedTAddr ep ↦ at' ∗ epConfState ep cs ∗
      applyThread γ st ∗ applyBackend γ ci b ∗ ciApplying ci a t ∗ srvLgReader s ∗ srvApplyKVOn s E γw x sa }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"snapshotIfNeededAndCompactRaftLog"))
      (Val #ep))
  {{ RET #(); ∃ st' : ApplyState, (RC ∨ RC') ∗ srvSnapState s ep ms γs ai (W64 0) ∗ srvSnapFrozen γs (uint.nat ai) ∗
      epAppliedIAddr ep ↦ ai ∗ epAppliedTAddr ep ↦ at' ∗ epConfState ep cs ∗
      applyThread γ st' ∗ applyBackend γ ci b ∗ ciApplying ci a t ∗ srvLgReader s ∗ srvApplyKVOn s E γw x sa ∗ ⌜loopOk γ st' ai ∧ ciEff γ st'.k = ciEff γ st.k⌝ }}

/-- **`specFullOff`**, `specFull` with auth off (the auth-mode merge's corollary). -/
theorem EtcdServer.snapshotIfNeededAndCompactRaftLog.spec_fullOff
    (h : EtcdServer.snapshotIfNeededAndCompactRaftLog.specFull (GF := GF) (hG := hG)) :
    EtcdServer.snapshotIfNeededAndCompactRaftLog.specFullOff (GF := GF) (hG := hG) := by
  intro s E γw γ ci b γr ep st ai at' cs a t x ms γs nid γp w TM ρ kv RC RC' hoff
  have := h s E γw γ ci b γr ep st ai at' cs a t x ms γs nid γp w TM ρ kv RC RC' srvAuthSt0
  rw [hoff] at this
  exact this

/-- **`specFullOn`**, `specFull` with the mode-`on` row (the auth-mode merge's corollary). -/
theorem EtcdServer.snapshotIfNeededAndCompactRaftLog.spec_fullOn
    (h : EtcdServer.snapshotIfNeededAndCompactRaftLog.specFull (GF := GF) (hG := hG)) :
    EtcdServer.snapshotIfNeededAndCompactRaftLog.specFullOn (GF := GF) (hG := hG) := by
  intro s E γw γ ci b γr ep st ai at' cs a t x ms γs nid γp w TM ρ kv RC RC' sa hon
  have := h s E γw γ ci b γr ep st ai at' cs a t x ms γs nid γp w TM ρ kv RC RC' sa
  rw [hon] at this
  exact this


/-! ## `applyEntryNormal` -/

/-- **`spec` with auth off** (a corollary, `spec_off`; until step 6 of the auth-mode merge,
2026-10-30, `spec` itself). `s.applyEntryNormal(e, v3)`, by the apply thread (protocol state `st`, out of flight).
With `v3` (`ApplyBoth`: the entry `i = p + 1`, above `ci`, whose index and term are the
applying index; the state loaded, `stLoaded γ st = st`, as `apply`'s `ConsistentIndex` left it,
which the applier's `ConsistentIndex` lends, `srvCiC`; S8d, 2026-10-26): the entry is applied (through `apply.Apply`, or not at all if it has no data)
and, after it, `ci` and the processed-through index are both `i` (the post-lock hook set `ci`
if the entry had writes; else the deferred update does, outside the lock). Without `v3` (an
entry at or below `ci`, replayed): nothing is written to the backend and the state is
unchanged. **The KV** (the apply package's unit 3): the apply thread's applier state
`srvApplyKV s E ρ.wait x`, with the entry's premise `entryOk x m` (its data decode to a request with an
id, neither a compaction nor empty, satisfying the txn package's premises at `x.log`), goes to
`x'` by `entryStep m v3 x x' out` (no data: nothing; else `apply.Apply`'s `applyStep`). **The wait** (the request path's unit 2,
2026-10-12): the server's wait is the registry (`waitInv`, in `isServer`, with the request path's
names `ρ`); the entry is normal (`m.typ = 0`) and its id was claimed for its data
(`entryWaitOk`), so the result handed to `Trigger(id, ar)` is the registered proposer's
expectation (`resultΨ`: this request's `applyStep`, `applyResultIs`, and the certificate of the
log after). It spends one write token of the store (`mvcc.storeWT E.γ`, `apply.Apply`'s;
2026-10-13, unit 6). **The delivery** (the request path's unit 4d): to a caller that knows the
entry's id was registered (`entryRegd ρ.wait m (some t)`), the entry is applied in full (its
outcome not waived for want of a waiter) unless that registration is gone (`entryDelivered`:
a `Trigger` took it out first); the apply loops know nothing (`none`). **The applied log**
(2026-10-14, unit C2a): at the applied index `v = m.index - 1` with its log the KV's
(`appliedLogAt γr v x.log`) and the entry committed (`committedAtLeast γr m.index`, raft's
`toApply` batches: `rnApP`), the KV log after the entry is deposited as the log applied through
`m.index` before the result goes to the waiter (`srvAppliedPre`, `applied_predeposit`; the
result's witness, `resultIsW`), for `apply`'s `setAppliedIndex(m.index)` to publish. **The KV
model** (2026-10-14, unit T1): the apply thread at the committed raft log `A` through `v`
(`kvApplied`), the entry committed after it, `v3` as the model's (above the start's consistent
index): the apply thread at `A ++ [m]` after, its log deposited as the model's (`kvLogAt`). -/
abbrev EtcdServer.applyEntryNormal.specOff : Prop :=
  ∀ (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF) (E : apply.AEnv GF) (ρ : ReqNames)
    (b : GoInterface) (e : Loc) (m : EntryModel) (st : ApplyState) (v3 : Bool) (x : apply.ApplyKV)
    (γr : ReadNames) (ot : Option GName) (v : w64) (A : List EntryModel),
  E.authOn = false →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ isServer s γ ci TM E ρ γr ∗ entryWaitOk ρ E m ∗ entryRegd ρ.wait ρ.ids.pfx m ot ∗ entryAt e m ∗ applyThread γ st ∗ applyBackend γ ci b ∗
      srvLgReader s ∗ srvGoRes s ∗ srvApplyKV s E ρ.wait x ∗ mvcc.storeWT E.γ ∗ srvFS s ∗
      srvAppliedOwn γr v ∗ appliedLogAt γr v x.log ∗ committedAtLeast γr m.index ∗
      kvApplied γr.raft γr.kv A x ∗ srvRest E γr A ∗ srvRLogLb γr.raft (A ++ [m]) ∗
      ⌜uint.Z v = uint.Z γr.raft.ai0 + A.length ∧ v3 = decide (uint.Z γr.kv.c0 < uint.Z m.index)⌝ ∗
      ⌜uint.Z m.index = uint.Z v + 1⌝ ∗
      ⌜st.pending = false ∧ entryOk x m ∧ m.typ = W32 0⌝ ∗
      (if v3 then iprop(ciApplying ci m.index m.term ∗
          ⌜m.index = st.p + 1 ∧ uint.Z st.p < uint.Z m.index ∧
            uint.Z (ciEff γ st.k) < uint.Z m.index ∧ stLoaded γ st = st⌝)
       else iprop(True)) }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"applyEntryNormal"))
      (Val #e)) (Val #v3))
  {{ RET #(); applyBackend γ ci b ∗ srvLgReader s ∗ srvGoRes s ∗ srvFS s ∗
      (∃ (x' : apply.ApplyKV) (out : apply.ApplyOut), srvApplyKV s E ρ.wait x' ∗
        ⌜entryStep m v3 x x' out⌝ ∗ entryDelivered ρ.wait m ot out ∗
        srvAppliedPre γr v m.index x'.log ∗ kvApplied γr.raft γr.kv (A ++ [m]) x' ∗ srvRest E γr (A ++ [m])) ∗
      (if v3 then iprop(ciApplying ci m.index m.term ∗
          ∃ eff : w64, applyThread γ ⟨m.index, m.index, eff, false⟩)
       else applyThread γ st) }}

/-- **`spec` in the auth mode `on`** (a corollary, `spec_on`) (the auth plan's E3o, 2026-10-27; `notes/decisions.md`, "E3o of
the auth plan"): the server as the apply thread sees it with auth on (`isServerM true`: the wait's
results `resultΨOn`, the applied logs the mode-`on` model's, `srvKVInvsOn`), the environment's
mode `on γa`; the applier state with the auth row at the model's auth state `sa`
(`srvApplyKVOn`), the apply thread at the mode-`on` model of `A` (`kvAppliedOn`, from the server's
start state `srvAuthSt0`); the entry's premise `entryOkOn` (an admitted admin request too); the
server's lessor finding no lease (`srvLessorNil`, `srv_uberKVL_on`'s named premise); one time
receipt (an admin step's cost, E2l) under the receipts' bound. After the entry, as `spec`'s, the
apply thread at the model's state after `A ++ [m]` (its auth state `sa'`), the log deposited as the
mode-`on` model's (`srvAppliedPre`, `kvLogAtM true`), and a registered proposer's result handed
over with the auth layer's verdict the model's (`resultΨOn`). -/
abbrev EtcdServer.applyEntryNormal.specOn : Prop :=
  ∀ (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF) (E : apply.AEnv GF) (ρ : ReqNames)
    (b : GoInterface) (e : Loc) (m : EntryModel) (st : ApplyState) (v3 : Bool) (x : apply.ApplyKV)
    (γr : ReadNames) (ot : Option GName) (v : w64) (A : List EntryModel) (γa : auth.AuthNames)
    (sa : auth.AuthState),
  E.authMode = .on γa →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerM true s γ ci TM E ρ γr ∗ srvLessorNil s ∗ entryWaitOk ρ E m ∗
      entryRegd ρ.wait ρ.ids.pfx m ot ∗ entryAt e m ∗ applyThread γ st ∗ applyBackend γ ci b ∗
      srvLgReader s ∗ srvGoRes s ∗ srvApplyKVOn s E ρ.wait x sa ∗ mvcc.storeWT E.γ ∗ srvFS s ∗
      ⧗ 1 ∗ srvAppliedOwn γr v ∗ appliedLogAt γr v x.log ∗ committedAtLeast γr m.index ∗
      kvAppliedOn γr.raft γr.kv srvAuthSt0 A x sa ∗ srvRest E γr A ∗ srvRLogLb γr.raft (A ++ [m]) ∗
      ⌜uint.Z v = uint.Z γr.raft.ai0 + A.length ∧ v3 = decide (uint.Z γr.kv.c0 < uint.Z m.index)⌝ ∗
      ⌜uint.Z m.index = uint.Z v + 1⌝ ∗
      ⌜st.pending = false ∧ entryOkOn x m ∧ m.typ = W32 0 ∧ receiptBound GF ≤ 2 ^ 48⌝ ∗
      (if v3 then iprop(ciApplying ci m.index m.term ∗
          ⌜m.index = st.p + 1 ∧ uint.Z st.p < uint.Z m.index ∧
            uint.Z (ciEff γ st.k) < uint.Z m.index ∧ stLoaded γ st = st⌝)
       else iprop(True)) ∗
      -- (C1's A1, 2026-10-28) the rights to issue tokens at the consistent index
      srvTokRights E (ciEff γ st.k) }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"applyEntryNormal"))
      (Val #e)) (Val #v3))
  {{ RET #(); applyBackend γ ci b ∗ srvLgReader s ∗ srvGoRes s ∗ srvFS s ∗
      (∃ (x' : apply.ApplyKV) (out : apply.ApplyOut) (sa' : auth.AuthState),
        srvApplyKVOn s E ρ.wait x' sa' ∗ ⌜entryStep m v3 x x' out⌝ ∗ entryDelivered ρ.wait m ot out ∗
        srvAppliedPre γr v m.index x'.log ∗
        kvAppliedOn γr.raft γr.kv srvAuthSt0 (A ++ [m]) x' sa' ∗ srvRest E γr (A ++ [m])) ∗
      (if v3 then iprop(ciApplying ci m.index m.term ∗
          ∃ eff : w64, applyThread γ ⟨m.index, m.index, eff, false⟩)
       else applyThread γ st) ∗
      (if v3 then srvTokRights E m.index else srvTokRights E (ciEff γ st.k)) }}

/-- **`specOff`**, `spec` with auth off (the auth-mode merge's corollary). -/
theorem EtcdServer.applyEntryNormal.spec_off
    (h : EtcdServer.applyEntryNormal.spec (GF := GF) (hG := hG)) :
    EtcdServer.applyEntryNormal.specOff (GF := GF) (hG := hG) := by
  intro s γ ci TM E ρ b e m st v3 x γr ot v A hoff
  have hm : E.authMode = .off := by
    rw [apply.AEnv.authOn_eq] at hoff
    cases h' : E.authMode <;> simp_all [auth.AuthMode.isOn]
  have hT : ∀ k, srvTokRights (GF := GF) E k = iprop(True) := by
    intro k; unfold srvTokRights; rw [hm]
  have := h s γ ci TM E ρ b e m st v3 x γr ot v A srvAuthSt0 (by rw [hm]; simp)
  rw [hoff] at this
  simp only [isServerM_false, srvLessorNilM_false, srvApplyKVM_false, kvAppliedM_false,
    entryOkM_false, hT, Bool.false_eq_true, ↓reduceIte] at this
  iintro %Φ ⟨#Hpkg, #Hsrv, #Hew, Hrg, He, Hst, Hbe, Hlr, Hgr, HKV, Hwt, Hfs, Hao, Hlog,
    #Hcm, Hka, HRS, #Hrl, %Hv, %Hidx, %Hpre, Hv3⟩ HΦ
  iapply this $$ [Hrg He Hst Hbe Hlr Hgr HKV Hwt Hfs Hao Hlog Hka HRS Hv3]
  · iframe Hpkg Hsrv Hew Hrg He Hst Hbe Hlr Hgr HKV Hwt Hfs Hao Hlog Hcm Hka HRS Hrl Hv3
    ipureintro; exact ⟨Hv, Hidx, Hpre.1, Hpre.2.1, Hpre.2.2, fun h => absurd h (by simp)⟩
  inext
  iintro ⟨Hbe, Hlr, Hgr, Hfs, ⟨%x', %out, %sa', HKV, %Hstep, Hdel, Hap, Hka, HRS⟩, Hst, -⟩
  iapply HΦ
  iframe Hbe Hlr Hgr Hfs Hst
  iexists x', out; iframe HKV Hdel Hap Hka HRS; ipureintro; exact Hstep

/-- **`specOn`**, `spec` in the mode `on` (the auth-mode merge's corollary). -/
theorem EtcdServer.applyEntryNormal.spec_on
    (h : EtcdServer.applyEntryNormal.spec (GF := GF) (hG := hG)) :
    EtcdServer.applyEntryNormal.specOn (GF := GF) (hG := hG) := by
  intro s γ ci TM E ρ b e m st v3 x γr ot v A γa sa hM
  have hon : E.authOn = true := by rw [apply.AEnv.authOn_eq, hM]; rfl
  have := h s γ ci TM E ρ b e m st v3 x γr ot v A sa (by rw [hM]; simp)
  rw [hon] at this
  simp only [srvLessorNilM_true, srvApplyKVM_true, kvAppliedM_true, entryOkM_true,
    ↓reduceIte] at this
  iintro %Φ ⟨#Hpkg, #Hsrv, #Hln, #Hew, Hrg, He, Hst, Hbe, Hlr, Hgr, HKV, Hwt, Hfs, Hr, Hao, Hlog,
    #Hcm, Hka, HRS, #Hrl, %Hv, %Hidx, %Hpre, Hv3, Htok⟩ HΦ
  iapply this $$ [Hrg He Hst Hbe Hlr Hgr HKV Hwt Hfs Hr Hao Hlog Hka HRS Hv3 Htok] HΦ
  iframe Hpkg Hsrv Hln Hew Hrg He Hst Hbe Hlr Hgr HKV Hwt Hfs Hr Hao Hlog Hcm Hka HRS Hrl Hv3 Htok
  ipureintro; exact ⟨Hv, Hidx, Hpre.1, Hpre.2.1, Hpre.2.2.1, fun _ => Hpre.2.2.2⟩

end variants

/-! ## The request path -/

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`spec` in either auth mode** (the auth plan's E3b, 2026-10-26): the server as a proposer sees
it in the auth mode `on` (`isServerReqM`; the function reads none of the mode's rows). At
`on = false` it is `spec` (by definition). -/
abbrev EtcdServer.parseProposeCtxErr.specM (on : Bool) : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (err : GoInterface) (start : time.Time),
  context.isTypedErr err →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerReqM on s E ρ ∗ srvLeadTimeReader s ∗
      (globalAddr context.Canceled ↦□ err ∨ globalAddr context.DeadlineExceeded ↦□ err) }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"parseProposeCtxErr"))
      (Val #err)) (Val #start))
  {{ (e : GoInterface), RET #e; srvLeadTimeReader s ∗ ⌜e ≠ GoInterface.nil⌝ ∗ applyErrIs e }}

/-- **The handoff in either auth mode** (the auth plan's E3b, 2026-10-26; `ReqOn.lean`): `spec`'s,
with the proposer's view of the server, the wait's results and the KV model of the mode
(`isServerReqM`; the applied result `resPostM`: in the mode `on` with the auth state the entry met
and the auth layer's verdict the model's grant there, `authTie`), and the proposal's permission at the header the server stamps
(`reqPropOkM`: in the mode `on` the check reads the request's principal, which the server fills in
from the context before it proposes; the result `Qh hm` is at that header `hm`, the one the post
names); (E3t, 2026-10-27) with auth on, the auth state after the entry published (`pubAfterM`);
(E3zb, 2026-10-28) with auth on, the stamped header's user bound to the context (`hdrBoundM`: the
store's `AuthInfoFromCtx` reads the context's token, `srvAuthBound` in `isServerReqM true`). At
`on = false` it is `spec` (`EtcdServer.processInternalRaftRequestOnce.wp_proof` is
derived from it, a constant `Qh`). -/
abbrev EtcdServer.processInternalRaftRequestOnce.specM (on : Bool) : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (p : Loc) (rq : apply.IRRModel)
    (Qh : apply.HeaderModel → List EntryModel → IProp GF) (F : mvcc.Log),
  rq.id = W64 0 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerReqM on s E ρ ∗ srvLeadTimeReader s ∗ E.RD ∗ idCred ρ.ids 1 ∗
      context.isContext ctx cd ∗ irrNoHdrIs p rq ∗ reqPropOkM on ρ.raft ρ.kv (hdrBoundM true s E (GoInterface.ok ctx)) rq Qh ∗
      (∃ h0 : Loc, structFieldRef etcdserverpb.InternalRaftRequest go!"Header" p ↦ h0) ∗
      mvcc.idxCert E.γ.idx F }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"processInternalRaftRequestOnce"))
      (Val #(GoInterface.ok ctx))) (Val #p))
  {{ (res : Loc) (err : GoInterface), RET (PairV #res #err); srvLeadTimeReader s ∗ E.RD ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ (hm : apply.HeaderModel) (rq' : apply.IRRModel),
          ⌜irrWireOf (apply.withHeader rq hm) rq'⌝ ∗ apply.resTrace res ∗
          ∃ L : List EntryModel, srvRLogLb ρ.raft L ∗ resPostM on E ρ rq' F res L ∗
            pubAfterM on E ρ rq' L ∗ □ Qh hm L ∗ hdrBoundM on s E (GoInterface.ok ctx) hm) ∨
       (⌜res = null ∧ err ≠ GoInterface.nil⌝ ∗ applyErrIs err ∗ srvMaybeDeposited ρ rq)) }}

/-- **The handoff.** `s.processInternalRaftRequestOnce(ctx, r)`, any goroutine, at a context, for
a request `r` holding `rq` but for its header (which it sets: the fresh id `Next` returns, the
auth info's user name and revision), with no `ID` (the server's requests have none; `Apply` takes
the header's), one id credit, a reader slot of `s.leadTimeMu` and (2026-10-14, unit A2) the auth store's reader
resource `E.RD` (`AuthInfoFromCtx`):
* success (`err = nil`): `res` is the apply thread's result of applying `rq'`, the request the
  proposed data decode to (`irrWireOf`: `rq` with its header, up to the model's `[0]` range ends):
  `resultIs E rq' res` (the apply package's `applyStep` and `applyResultIs` at the KV state the
  entry met, and mvcc's certificate of the log after; 2026-10-14, unit C2a: `resultIsW E ρ.rd`, with
  the witness that the log after is applied through an index of the committed log, `appliedWit`);
  and (2026-10-14, unit T1) the result `Qr` of the proposal's update at a committed log (`reqPropOk
  ρ.kv rq Qr`: the request has no KV write, `Qr` trivial; or, since 2026-10-15 (unit T2), it is a
  plain write, a put, a delete or a transaction, with its client's update over the whole state,
  `Qr L` the client's `□ Q` at the state of `L`'s model): `□ Qr L` of the committed log `L` before
  the entry the result is of, whose model is the log `lb` the entry met (unit W-M3: the result's
  `y.log`, so the update's state is the write's);
* failure: no result, an error the gRPC layer can take (`applyErrIs`: in an error tree, a safe map
  key, with a message; 2026-10-12, unit 3a), and the proposal, if made, deposited (`srvMaybeDeposited`: it may
  still be applied: the request limit, the auth store's error, the marshal's error, the size
  limit come before the proposal; `Propose`'s error, the context's (`parseProposeCtxErr`) and the
  server's stop (`ErrStopped`) after it). -/
abbrev EtcdServer.processInternalRaftRequestOnce.specOff : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (p : Loc) (rq : apply.IRRModel)
    (Qr : List EntryModel → IProp GF) (F : mvcc.Log),
  rq.id = W64 0 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerReq s E ρ ∗ srvLeadTimeReader s ∗ E.RD ∗ idCred ρ.ids 1 ∗ context.isContext ctx cd ∗
      irrNoHdrIs p rq ∗ reqPropOk ρ.kv rq Qr ∗
      (∃ h0 : Loc, structFieldRef etcdserverpb.InternalRaftRequest go!"Header" p ↦ h0) ∗
      mvcc.idxCert E.γ.idx F }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"processInternalRaftRequestOnce"))
      (Val #(GoInterface.ok ctx))) (Val #p))
  {{ (res : Loc) (err : GoInterface), RET (PairV #res #err); srvLeadTimeReader s ∗ E.RD ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ (hm : apply.HeaderModel) (rq' : apply.IRRModel),
          ⌜irrWireOf (apply.withHeader rq hm) rq'⌝ ∗ apply.resTrace res ∗
          ∃ lb : mvcc.Log, resultIsW E ρ.rd rq' F res lb ∗
            ∃ L : List EntryModel, srvRLogLb ρ.raft L ∗ ⌜kvModel ρ.kv L = lb⌝ ∗ □ Qr L) ∨
       (⌜res = null ∧ err ≠ GoInterface.nil⌝ ∗ applyErrIs err ∗ srvMaybeDeposited ρ rq)) }}

/-- **`spec` in either auth mode** (the auth plan's E3b, 2026-10-26; `ReqOn.lean`): over
`processInternalRaftRequestOnce.specM`; the success post at the committed prefix `L` before the
entry, with what the proposer learns of the model there (`appliedOkM`, `modelOutM`: in the mode `on`
the auth state the entry met and the auth layer's verdict the model's grant there). -/
abbrev EtcdServer.raftRequest.specM (on : Bool) : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (p : Loc) (rq : apply.IRRModel)
    (Qh : apply.HeaderModel → List EntryModel → IProp GF) (F : mvcc.Log),
  rq.id = W64 0 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerReqM on s E ρ ∗ srvLeadTimeReader s ∗ E.RD ∗ idCred ρ.ids 1 ∗
      context.isContext ctx cd ∗ irrNoHdrIs p rq ∗ reqPropOkM on ρ.raft ρ.kv (hdrBoundM true s E (GoInterface.ok ctx)) rq Qh ∗
      (∃ h0 : Loc, structFieldRef etcdserverpb.InternalRaftRequest go!"Header" p ↦ h0) ∗
      mvcc.idxCert E.γ.idx F }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"raftRequest"))
      (Val #(GoInterface.ok ctx))) (Val #p))
  {{ (resp err : GoInterface), RET (PairV #resp #err); srvLeadTimeReader s ∗ E.RD ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ (hm : apply.HeaderModel) (rq' : apply.IRRModel)
          (L : List EntryModel),
          ⌜irrWireOf (apply.withHeader rq hm) rq'⌝ ∗ srvRLogLb ρ.raft L ∗
          appliedOkM on E ρ rq' F resp L ∗ pubAfterM on E ρ rq' L ∗ □ Qh hm L ∗
          hdrBoundM on s E (GoInterface.ok ctx) hm) ∨
       (⌜resp = GoInterface.nil ∧ err ≠ GoInterface.nil⌝ ∗ applyErrIs err ∗
         ((∃ (hm : apply.HeaderModel) (rq' : apply.IRRModel),
            ⌜irrWireOf (apply.withHeader rq hm) rq'⌝ ∗ appliedErr E rq' F err ∗
            hdrBoundM on s E (GoInterface.ok ctx) hm) ∨
          srvMaybeDeposited ρ rq))) }}

/-- `s.raftRequest(ctx, r)` (as `processInternalRaftRequestOnce`): success, the apply thread's
answer to `rq'` (`appliedOk`: dispatched, the apply package's response, no error); failure, no
response and an error (2026-10-14, unit C2a: the success with the result's witness at `ρ.rd`,
`appliedWit`): the apply's (`appliedErr`), or `processInternalRaftRequestOnce`'s (the
proposal, if made, deposited). Unit W-M3: the update's committed log `L` is the raft prefix whose
model is the log `lb` the entry met (`appliedOk`'s `x.log`), and the log after is certified. -/
abbrev EtcdServer.raftRequest.specOff : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (p : Loc) (rq : apply.IRRModel)
    (Qr : List EntryModel → IProp GF) (F : mvcc.Log),
  rq.id = W64 0 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerReq s E ρ ∗ srvLeadTimeReader s ∗ E.RD ∗ idCred ρ.ids 1 ∗ context.isContext ctx cd ∗
      irrNoHdrIs p rq ∗ reqPropOk ρ.kv rq Qr ∗
      (∃ h0 : Loc, structFieldRef etcdserverpb.InternalRaftRequest go!"Header" p ↦ h0) ∗
      mvcc.idxCert E.γ.idx F }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"raftRequest"))
      (Val #(GoInterface.ok ctx))) (Val #p))
  {{ (resp err : GoInterface), RET (PairV #resp #err); srvLeadTimeReader s ∗ E.RD ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ (hm : apply.HeaderModel) (rq' : apply.IRRModel) (lb : mvcc.Log),
          ⌜irrWireOf (apply.withHeader rq hm) rq'⌝ ∗ appliedOk E ρ.rd rq' F resp lb ∗
          ∃ L : List EntryModel, srvRLogLb ρ.raft L ∗ ⌜kvModel ρ.kv L = lb⌝ ∗ □ Qr L) ∨
       (⌜resp = GoInterface.nil ∧ err ≠ GoInterface.nil⌝ ∗ applyErrIs err ∗
         ((∃ (hm : apply.HeaderModel) (rq' : apply.IRRModel),
            ⌜irrWireOf (apply.withHeader rq hm) rq'⌝ ∗ appliedErr E rq' F err) ∨
          srvMaybeDeposited ρ rq))) }}

/-- **`spec` in the auth mode `on`** (the auth plan's E3s, 2026-10-27): over the request and read
views in the mode (`isServerReqM on`, `isServerReadM on`; `spec` at `on = false`, by definition).
`doSerialize` reads only fields both modes share. With auth on (E3zb, 2026-10-28) the auth info
`chk` passed on is the caller's (`infoBoundM`: the empty one, or bound to the context's token),
given `AuthInfoFromCtx`'s binding with auth on (`AuthInfoFromCtx.spec`). -/
abbrev EtcdServer.doSerialize.specM (on : Bool) : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (chk get : GoFunc) (G Q : IProp GF)
    (C : go_etcd_io.etcd.server.v3.auth.AuthInfo → IProp GF) (t : Loc) (e : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerReqM on s E ρ ∗ isServerReadM on s E γr ∗ mvcc.txnCtx ctx cd ∗
      traceutil.ctxTraceIs ctx (some t) ∗
      (∀ (a : Loc) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (dq : DFrac),
        {{ a ↦{dq} info ∗ E.RD }} (App (Val #chk) (Val #a))
        {{ (err : GoInterface), RET #err; a ↦{dq} info ∗ E.RD ∗ applyErrIs err ∗
            (∀ _ : err = GoInterface.nil, C info) }}) ∗
      {{ G ∗ traceutil.ownTrace t e }} (App (Val #get) (Val #())) {{ RET #(); Q }} ∗ G ∗
      traceutil.ownTrace t e ∗ E.RD }}
    (App (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"doSerialize"))
      (Val #(GoInterface.ok ctx))) (Val #chk)) (Val #get))
  {{ (err : GoInterface), RET #err; E.RD ∗
      ((⌜err = GoInterface.nil⌝ ∗ (∃ info, C info ∗ infoBoundM on s E (GoInterface.ok ctx) info) ∗ Q) ∨ (⌜err ≠ GoInterface.nil⌝ ∗ applyErrIs err ∗
        ((G ∗ traceutil.ownTrace t e) ∨ Q))) }}

/-- **`s.doSerialize(ctx, chk, get)`** at a context, with the permission check `chk` (a triple:
on any auth info, an error the gRPC layer can take) and the read `get` (`{G} get() {Q}`): the
request's auth info (`AuthInfoFromCtx`, or an empty one), `chk` of it, `get()`, then the
token's revision against the auth store's (`ErrAuthOldRevision`). Success: `get` ran (`Q`);
failure: an error the gRPC layer can take, and `get` ran or not (`G ∨ Q`). 2026-10-14 (unit A2):
the auth store's reader resource `E.RD`, which `AuthInfoFromCtx` and `chk` take and give back.
2026-10-23 (auth plan A1): `C info`, what a passed `chk` establishes of the auth info it saw (the
permission class of the request's keys, `apply.rangeClass`, `apply.txnClass`); success gives it
of some auth info (the context's, or the empty one). -/
abbrev EtcdServer.doSerialize.specOff : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (chk get : GoFunc) (G Q : IProp GF)
    (C : go_etcd_io.etcd.server.v3.auth.AuthInfo → IProp GF) (t : Loc) (e : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerReq s E ρ ∗ isServerRead s E γr ∗ mvcc.txnCtx ctx cd ∗
      traceutil.ctxTraceIs ctx (some t) ∗
      (∀ (a : Loc) (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (dq : DFrac),
        {{ a ↦{dq} info ∗ E.RD }} (App (Val #chk) (Val #a))
        {{ (err : GoInterface), RET #err; a ↦{dq} info ∗ E.RD ∗ applyErrIs err ∗
            (∀ _ : err = GoInterface.nil, C info) }}) ∗
      {{ G ∗ traceutil.ownTrace t e }} (App (Val #get) (Val #())) {{ RET #(); Q }} ∗ G ∗
      traceutil.ownTrace t e ∗ E.RD }}
    (App (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"doSerialize"))
      (Val #(GoInterface.ok ctx))) (Val #chk)) (Val #get))
  {{ (err : GoInterface), RET #err; E.RD ∗
      ((⌜err = GoInterface.nil⌝ ∗ (∃ info, C info) ∗ Q) ∨ (⌜err ≠ GoInterface.nil⌝ ∗ applyErrIs err ∗
        ((G ∗ traceutil.ownTrace t e) ∨ Q))) }}


/-! ## `Put` -/

/-- **`spec` with auth off, as it was before the merge** (a corollary, `spec_off`; for the
off `ServerKV` until step 4). **`s.Put(ctx, r)`**, any goroutine, at a context, for a put request `r` holding `op`, with
one id credit and a reader slot of `s.leadTimeMu`: success, the apply package's answer to the put
(`putOutcomeIs`, no error: applied, `putModel`'s, at the log `x.log` the entry met) of the request
with the header the server set (`hm`), dispatched at `x` to `x'` (`applyStep`), the response
header's id fields owned (`appliedHdr`: for the gRPC layer to fill), with mvcc's certificate of
the log after, the token of the revision it appended (`revMinted`, the vertical slice's unit
V1), and (2026-10-14, unit C2a) the log after applied through an index of the committed log
(`appliedWit ρ.rd x'.log`: a linearizable read at that index reads a log extending it); failure, no response and an error the gRPC layer can take (`applyErrIs`): the
apply's (`appliedErr`), or the proposal's (made or not; if made, deposited: it may still be
applied). 2026-10-15 (unit T2): the put's update is over the whole state (`putPermit`: the lease
`0`, the client's `kvOpAu (.put op)`), a success giving `□ Q` of the state it linearized at.
2026-10-19 (D21 M6, D20 (b)): the update is fired at most once (`kvOpAu1`), a success giving `Q` of
the state it fired at; on a failure it fired once or not at all. -/
abbrev EtcdServer.Put.specOff : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (r : Loc) (op : OpFull)
    (Q : KVState → IProp GF) (F : mvcc.Log),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerReq s E ρ ∗ srvLeadTimeReader s ∗ E.RD ∗ idCred ρ.ids 1 ∗ context.isContext ctx cd ∗
      txn.putRequestIs r op ∗ putPermit ρ.kv op Q ∗ mvcc.idxCert E.γ.idx F }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"Put"))
      (Val #(GoInterface.ok ctx))) (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); srvLeadTimeReader s ∗ E.RD ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ (hm : apply.HeaderModel) (x x' : apply.ApplyKV)
          (o : apply.Outcome) (skip : Bool),
          ⌜apply.applyStep (apply.withHeader (irrPut op) hm) true x x' (.dispatched o skip) ∧
            (∃ log', o = .applied log' false) ∧ F <+: x.log⌝ ∗
          apply.putOutcomeIs x.log op resp GoInterface.nil o ∗
          apply.appliedHdr x.log (structFieldRef etcdserverpb.PutResponse go!"Header" resp) ∗
          mvcc.idxCert E.γ.idx x'.log ∗ revMinted E x.log x'.log ∗ appliedWit ρ.rd x'.log ∗
          mvcc.certOk E.γ x'.log ∗ Q (kvStateOf x.log)) ∨
       (⌜resp = null ∧ err ≠ GoInterface.nil⌝ ∗ applyErrIs err ∗
         ((∃ hm : apply.HeaderModel, appliedErr E (apply.withHeader (irrPut op) hm) F err) ∨
          srvMaybeDeposited ρ (irrPut op)))) }}

/-- **`spec` with auth on, as it was before the merge** (a corollary, `spec_on`) (the auth plan's E3b, 2026-10-26; `ReqOn.lean`): the server
as a proposer sees it in the mode `on` (`isServerReqM true`) and the put's permission with a key
not empty (`putPermitOn`); the same post: a success is a put the auth state the entry met granted
(the apply thread's auth verdict is the model's, `authTie`), so its client's update fired there and
its result `Q` holds at the log the entry met; a refusal is an error (`appliedErr`: the auth layer's
rejection). (E3zb, 2026-10-28) A success names the grant, at the committed log `L` before the
entry (`grantedAt`); a success and an applied error, the header the server stamped, whose user is
bound to the context (`hdrBoundM`: its token was issued to that user). -/
abbrev EtcdServer.Put.specOn : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (r : Loc) (op : OpFull)
    (Q : KVState → IProp GF) (F : mvcc.Log),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerReqM true s E ρ ∗ srvLeadTimeReader s ∗ E.RD ∗ idCred ρ.ids 1 ∗ context.isContext ctx cd ∗
      txn.putRequestIs r op ∗ putPermitOn ρ.raft ρ.kv (hdrBoundM true s E (GoInterface.ok ctx)) op Q ∗ mvcc.idxCert E.γ.idx F }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"Put"))
      (Val #(GoInterface.ok ctx))) (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); srvLeadTimeReader s ∗ E.RD ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ (hm : apply.HeaderModel) (x x' : apply.ApplyKV)
          (o : apply.Outcome) (skip : Bool),
          ⌜apply.applyStep (apply.withHeader (irrPut op) hm) true x x' (.dispatched o skip) ∧
            (∃ log', o = .applied log' false) ∧ F <+: x.log⌝ ∗
          apply.putOutcomeIs x.log op resp GoInterface.nil o ∗
          apply.appliedHdr x.log (structFieldRef etcdserverpb.PutResponse go!"Header" resp) ∗
          mvcc.idxCert E.γ.idx x'.log ∗ revMinted E x.log x'.log ∗ appliedWit ρ.rd x'.log ∗
          mvcc.certOk E.γ x'.log ∗ Q (kvStateOf x.log) ∗
          hdrBoundM true s E (GoInterface.ok ctx) hm ∗
          ∃ L, ⌜grantedAt ρ.kv srvAuthSt0 (apply.withHeader (irrPut op) hm) L⌝ ∗
            pubAfterM true E ρ (apply.withHeader (irrPut op) hm) L) ∨
       (⌜resp = null ∧ err ≠ GoInterface.nil⌝ ∗ applyErrIs err ∗
         ((∃ hm : apply.HeaderModel, appliedErr E (apply.withHeader (irrPut op) hm) F err ∗
            hdrBoundM true s E (GoInterface.ok ctx) hm) ∨
          srvMaybeDeposited ρ (irrPut op)))) }}

/-! ## `DeleteRange` -/

/-- **`spec` with auth off, as it was before the merge** (a corollary, `spec_off`; for the
off `ServerKV` until step 4). **`s.DeleteRange(ctx, r)`** (as `Put`; 2026-10-15, unit T2: a delete's update is over the
whole state, `deletePermit`: its range end not `[0]`, the client's `kvOpAu (.deleteRange op)`; a
success gives `□ Q` of the state it linearized at): success, the apply package's answer to the delete
(`deleteOutcomeIs`, no error: applied; the response header's id fields owned, `appliedHdr`) of the request the proposed data decode to (`rq'`, whose delete is
`op'`: `op` itself unless the range end is `[0]`, the model's ambiguity, `irrWireOf`), at the log
the entry met, with mvcc's certificate of the log after. 2026-10-20 (linkv-txn stage A, as
`Put` since D21 M6): the update is fired at most once (`kvOpAu1`), a success giving `Q` of the
state it fired at; on a failure it fired once or not at all. -/
abbrev EtcdServer.DeleteRange.specOff : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (r : Loc) (op : OpFull) (Q : KVState → IProp GF)
    (F : mvcc.Log),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerReq s E ρ ∗ srvLeadTimeReader s ∗ E.RD ∗ idCred ρ.ids 1 ∗ context.isContext ctx cd ∗
      txn.deleteRangeRequestIs r op ∗ deletePermit ρ.kv op Q ∗ mvcc.idxCert E.γ.idx F }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"DeleteRange"))
      (Val #(GoInterface.ok ctx))) (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); srvLeadTimeReader s ∗ E.RD ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ (hm : apply.HeaderModel) (rq' : apply.IRRModel) (op' : OpFull)
          (x x' : apply.ApplyKV) (o : apply.Outcome) (skip : Bool),
          ⌜irrWireOf (apply.withHeader (irrDeleteRange op) hm) rq' ∧ rq'.deleteRange = some op' ∧
            (irrNoZeroEnd (irrDeleteRange op) → op' = op) ∧
            apply.applyStep rq' true x x' (.dispatched o skip) ∧ (∃ log', o = .applied log' false) ∧
            F <+: x.log⌝ ∗
          apply.deleteOutcomeIs x.log op' resp GoInterface.nil o ∗
          apply.appliedHdr x.log (structFieldRef etcdserverpb.DeleteRangeResponse go!"Header" resp) ∗
          mvcc.idxCert E.γ.idx x'.log ∗ revMinted E x.log x'.log ∗ appliedWit ρ.rd x'.log ∗
          mvcc.certOk E.γ x'.log ∗ Q (kvStateOf x.log)) ∨
       (⌜resp = null ∧ err ≠ GoInterface.nil⌝ ∗ applyErrIs err ∗
         ((∃ (hm : apply.HeaderModel) (rq' : apply.IRRModel),
            ⌜irrWireOf (apply.withHeader (irrDeleteRange op) hm) rq'⌝ ∗ appliedErr E rq' F err) ∨
          srvMaybeDeposited ρ (irrDeleteRange op)))) }}

/-- **`spec` with auth on, as it was before the merge** (a corollary, `spec_on`) (the auth plan's E3b, 2026-10-26; `Put.specOn`'s): a success
is a delete the auth state the entry met granted, its result `Q` at the log the entry met. -/
abbrev EtcdServer.DeleteRange.specOn : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (ctx : GoInterfaceOk)
    (cd : context.ContextDesc (IProp GF)) (r : Loc) (op : OpFull) (Q : KVState → IProp GF)
    (F : mvcc.Log),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerReqM true s E ρ ∗ srvLeadTimeReader s ∗ E.RD ∗ idCred ρ.ids 1 ∗ context.isContext ctx cd ∗
      txn.deleteRangeRequestIs r op ∗ deletePermitOn ρ.raft ρ.kv (hdrBoundM true s E (GoInterface.ok ctx)) op Q ∗ mvcc.idxCert E.γ.idx F }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"DeleteRange"))
      (Val #(GoInterface.ok ctx))) (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); srvLeadTimeReader s ∗ E.RD ∗
      ((⌜err = GoInterface.nil⌝ ∗ ∃ (hm : apply.HeaderModel) (rq' : apply.IRRModel) (op' : OpFull)
          (x x' : apply.ApplyKV) (o : apply.Outcome) (skip : Bool),
          ⌜irrWireOf (apply.withHeader (irrDeleteRange op) hm) rq' ∧ rq'.deleteRange = some op' ∧
            (irrNoZeroEnd (irrDeleteRange op) → op' = op) ∧
            apply.applyStep rq' true x x' (.dispatched o skip) ∧ (∃ log', o = .applied log' false) ∧
            F <+: x.log⌝ ∗
          apply.deleteOutcomeIs x.log op' resp GoInterface.nil o ∗
          apply.appliedHdr x.log (structFieldRef etcdserverpb.DeleteRangeResponse go!"Header" resp) ∗
          mvcc.idxCert E.γ.idx x'.log ∗ revMinted E x.log x'.log ∗ appliedWit ρ.rd x'.log ∗
          mvcc.certOk E.γ x'.log ∗ Q (kvStateOf x.log) ∗ hdrBoundM true s E (GoInterface.ok ctx) hm ∗
          ∃ L, ⌜grantedAt ρ.kv srvAuthSt0 rq' L⌝ ∗ pubAfterM true E ρ rq' L) ∨
       (⌜resp = null ∧ err ≠ GoInterface.nil⌝ ∗ applyErrIs err ∗
         ((∃ (hm : apply.HeaderModel) (rq' : apply.IRRModel),
            ⌜irrWireOf (apply.withHeader (irrDeleteRange op) hm) rq'⌝ ∗ appliedErr E rq' F err ∗
            hdrBoundM true s E (GoInterface.ok ctx) hm) ∨
          srvMaybeDeposited ρ (irrDeleteRange op)))) }}


/-! ## `Range` -/

/-- **`spec` with auth off, as it was before the merge** (a corollary, `spec_off`). **`s.Range(ctx, r)`**, any goroutine, at a context, for a range request `r` holding `o` with
a valid sort target, with a read call's resources (`srvRdCall`: the store's reader slots, the
logger's, the committed index `c` the caller knew of): success, the txn package's answer at a
certified log of at least two revisions, after the read index unless serializable, the header's
id fields owned (`rangeReadOk`); failure, no response and an error the gRPC layer can take (the
read loop's, the auth store's, mvcc's `ErrFutureRev`, or the context's: `fmt.Errorf`'s in
Perennial's model, `applyErrIs` by the server's package facts). 2026-10-14 (unit T1): with a read
deposit `kvDep γr.kv Q` (a client's `Get` update, or nothing), a linearizable success read the KV
model of a committed raft log `L` at which the deposit gave `□ Q L` (`rangeReadOk`). 2026-10-23
(auth plan A1): a success passed the auth store's `IsRangePermitted` for some auth info (the
context's token's, or the empty one): with auth on, that info's read permission class of the
request's range (`apply.rangeClass`). -/
abbrev EtcdServer.Range.specOff : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (c : w64)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (r : Loc) (o : OpFull)
    (ot : Option Loc) (te : Bool) (Q : List EntryModel → IProp GF) (F : mvcc.Log),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerReq s E ρ ∗ isServerRead s E γr ∗ srvRdCall s E γr c ∗ context.isContext ctx cd ∗
      traceutil.ctxTraceIs ctx ot ∗ traceutil.ownTraceOpt ot te ∗ txn.rangeRequestIs r o ∗ ⌜txn.validSortTarget o⌝ ∗
      kvDep γr.kv Q ∗ mvcc.idxCert E.γ.idx F }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"Range"))
      (Val #(GoInterface.ok ctx))) (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); srvRdCall s E γr c ∗
      ((⌜err = GoInterface.nil ∧ resp ≠ null⌝ ∗ (∃ info, apply.rangeClass E.authMode info o) ∗
          rangeReadOk E γr c F o resp Q) ∨
       (⌜resp = null ∧ err ≠ GoInterface.nil⌝ ∗ applyErrIs err)) }}

/-- **`spec` with auth on, as it was before the merge** (a corollary, `spec_on`) (the auth plan's E3s, 2026-10-27; `notes/decisions.md`, "E3s of the
auth plan"): in the mode `on γa`, over the request and read views with auth on (`isServerReqM
true`, `isServerReadM true`), the read deposit at the mode-`on` model's state (`kvDep γr.kv Q
(kvStM true γr.kv)`), and a lower bound `n` of the auth store's published index the reader holds
(`auth.authPubLbM`), with the server's range check at it (`srvAuthLb`). Success: the auth store's
`IsRangePermitted` passed for some auth info at states no older than some `m ≥ n`
(`apply.rangeClassFrom`: a state recorded at an index at least `m` permits the read of the
request's range) and, for a linearizable read, no older than the auth state the committed log
through the read index left (`authFloorAt`, E3u: the applied index's invariant has that state
published, and `Range` checks after waiting for the read index, so the reader needs no bound of its
own beyond `n`, which `auth.authPubLb γa 0` always gives), and the read
as `spec`'s, a linearizable one at the mode-`on` model of a committed raft log `L` at which the
deposit gave `□ Q L` (`rangeReadOkM true`); the auth info checked is the caller's
(`infoBoundM`, E3zb, 2026-10-28). -/
abbrev EtcdServer.Range.specOn : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (c : w64)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (r : Loc) (o : OpFull)
    (ot : Option Loc) (te : Bool) (Q : List EntryModel → IProp GF) (F : mvcc.Log) (n : Nat)
    (γa : auth.AuthNames),
  E.authMode = .on γa →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerReqM true s E ρ ∗ isServerReadM true s E γr ∗ srvAuthLb s E ∗
      auth.authPubLbM E.authMode n ∗ srvRdCall s E γr c ∗ context.isContext ctx cd ∗
      traceutil.ctxTraceIs ctx ot ∗ traceutil.ownTraceOpt ot te ∗ txn.rangeRequestIs r o ∗ ⌜txn.validSortTarget o⌝ ∗
      kvDep γr.kv Q (kvStM true γr.kv) ∗ mvcc.idxCert E.γ.idx F }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"Range"))
      (Val #(GoInterface.ok ctx))) (Val #r))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); srvRdCall s E γr c ∗
      ((⌜err = GoInterface.nil ∧ resp ≠ null⌝ ∗
          (∃ (info : go_etcd_io.etcd.server.v3.auth.AuthInfo) (m : Nat), ⌜n ≤ m⌝ ∗ apply.rangeClassFrom E.authMode m info o ∗
            infoBoundM true s E (GoInterface.ok ctx) info ∗
            (if o.base.serializable then iprop(True) else authFloorAt E.authMode γr c m)) ∗
          rangeReadOkM true E γr c F o resp Q) ∨
       (⌜resp = null ∧ err ≠ GoInterface.nil⌝ ∗ applyErrIs err)) }}

end specs

/-! ## The instances from the spec -/

section corollaries
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem EtcdServer.parseProposeCtxErr.spec_M
    (h : EtcdServer.parseProposeCtxErr.spec (GF := GF) (hG := hG)) (on : Bool) :
    EtcdServer.parseProposeCtxErr.specM (GF := GF) (hG := hG) on := by
  intro s E ρ err start Herr
  iintro %Φ ⟨#Hpkg, #Hsrv, Hrest⟩ HΦ
  ihave %hon := isServerReqM_authOn on s E ρ $$ Hsrv
  subst hon
  iapply (h s E ρ err start Herr) $$ [Hrest] HΦ
  iframe Hpkg Hsrv Hrest

theorem EtcdServer.processInternalRaftRequestOnce.spec_M
    (h : EtcdServer.processInternalRaftRequestOnce.spec (GF := GF) (hG := hG)) (on : Bool) :
    EtcdServer.processInternalRaftRequestOnce.specM (GF := GF) (hG := hG) on := by
  intro s E ρ ctx cd p rq Qh F Hid0
  iintro %Φ ⟨#Hpkg, #Hsrv, Hrest⟩ HΦ
  ihave %hon := isServerReqM_authOn on s E ρ $$ Hsrv
  subst hon
  iapply (h s E ρ ctx cd p rq Qh F Hid0) $$ [Hrest] HΦ
  iframe Hpkg Hsrv Hrest

theorem EtcdServer.raftRequest.spec_M
    (h : EtcdServer.raftRequest.spec (GF := GF) (hG := hG)) (on : Bool) :
    EtcdServer.raftRequest.specM (GF := GF) (hG := hG) on := by
  intro s E ρ ctx cd p rq Qh F Hid0
  iintro %Φ ⟨#Hpkg, #Hsrv, Hrest⟩ HΦ
  ihave %hon := isServerReqM_authOn on s E ρ $$ Hsrv
  subst hon
  iapply (h s E ρ ctx cd p rq Qh F Hid0) $$ [Hrest] HΦ
  iframe Hpkg Hsrv Hrest

theorem EtcdServer.doSerialize.spec_M
    (h : EtcdServer.doSerialize.spec (GF := GF) (hG := hG)) (on : Bool) :
    EtcdServer.doSerialize.specM (GF := GF) (hG := hG) on := by
  intro s E ρ γr ctx cd chk get G Q C t e
  iintro %Φ ⟨#Hpkg, #Hsrv, Hrest⟩ HΦ
  ihave %hon := isServerReqM_authOn on s E ρ $$ Hsrv
  subst hon
  iapply (h s E ρ γr ctx cd chk get G Q C t e) $$ [Hrest] HΦ
  iframe Hpkg Hsrv Hrest

/-- The mode-off handoff from the spec (a constant result; the success post's model fact
`kvModel L = y.log`). -/
theorem EtcdServer.processInternalRaftRequestOnce.spec_off
    (h : EtcdServer.processInternalRaftRequestOnce.spec (GF := GF) (hG := hG)) :
    EtcdServer.processInternalRaftRequestOnce.specOff (GF := GF) (hG := hG) := by
  have hM := EtcdServer.processInternalRaftRequestOnce.spec_M h false
  intro s E ρ ctx cd p rq Qr F Hid0
  iintro %Φ Hpre HΦ
  iapply (hM s E ρ ctx cd p rq (fun _ => Qr) F Hid0) $$ [Hpre] [HΦ]
  · icases Hpre with ⟨Ha, Hb, Hc, Hd, He, Hf, Hg, Hok, Hi, Hj⟩
    ihave Hok' := reqPropOkM_of_false ρ.raft ρ.kv _ rq Qr $$ Hok
    rw [isServerReqM_false]
    iframe Ha Hb Hc Hd He Hf Hg Hok' Hi Hj
  · iintro !> %res %err ⟨Hrd, Hard, Hpost⟩
    iapply HΦ
    iframe Hrd Hard
    icases Hpost with (⟨%He, %hm, %rq', %Hw, HTr, %L, #HL, Hp, -, #HQ, -⟩ | Herr)
    · ileft
      isplitr
      · ipureintro; exact He
      iexists hm, rq'
      iframe HTr
      isplitr
      · ipureintro; exact Hw
      iunfold resPostM at Hp
      icases Hp with ⟨%Hnn, %y, %y', %out, %Hst, Hr1, Hr2, Hr3, Hr4, Hr5, -⟩
      iexists y.log
      iunfold resultIsW
      isplitl [Hr1 Hr2 Hr3 Hr4 Hr5]
      · isplitr
        · ipureintro; exact Hnn
        iexists y, y', out
        iframe Hr1 Hr2 Hr3 Hr4 Hr5
        ipureintro; exact ⟨Hst.1, Hst.2.1, rfl, Hst.2.2.1⟩
      iexists L
      iframe HL HQ
      ipureintro; exact Hst.2.2.2
    · iright; iexact Herr

/-- The mode-off `raftRequest` from the spec. -/
theorem EtcdServer.raftRequest.spec_off
    (h : EtcdServer.raftRequest.spec (GF := GF) (hG := hG)) :
    EtcdServer.raftRequest.specOff (GF := GF) (hG := hG) := by
  have hM := EtcdServer.raftRequest.spec_M h false
  intro s E ρ ctx cd p rq Qr F Hid0
  iintro %Φ Hpre HΦ
  icases Hpre with ⟨Ha, Hb, Hc, Hd, He, Hf, Hg, Hok, Hi, Hj⟩
  ihave Hok' := reqPropOkM_of_false ρ.raft ρ.kv _ rq Qr $$ Hok
  rw [← isServerReqM_false]
  iapply (hM s E ρ ctx cd p rq (fun _ => Qr) F Hid0) $$ [Ha Hb Hc Hd He Hf Hg Hok' Hi Hj] [HΦ]
  · iframe Ha Hb Hc Hd He Hf Hg Hok' Hi Hj
  iintro !> %resp %err ⟨Hrd, Hard, Hpost⟩
  iapply HΦ
  iframe Hrd Hard
  icases Hpost with (⟨%He, %hm, %rq', %L, %Hw, #HL, Hok, -, #HQ, -⟩ | Herr)
  · ileft
    isplitr
    · ipureintro; exact He
    iunfold appliedOkM at Hok
    icases Hok with ⟨%x, %x', %o, %skip, %Hst, Ha1, Ha2, Ha3, Ha4, Ha5, -⟩
    iexists hm, rq', x.log
    isplitr
    · ipureintro; exact Hw
    isplitl [Ha1 Ha2 Ha3 Ha4 Ha5]
    · iunfold appliedOk
      iexists x, x', o, skip
      iframe Ha1 Ha2 Ha3 Ha4 Ha5
      ipureintro; exact ⟨Hst.1, Hst.2.1, rfl, Hst.2.2.1⟩
    iexists L
    iframe HL HQ
    ipureintro; exact Hst.2.2.2.1
  · iright
    icases Herr with ⟨%Hr, #HaE, (⟨%hm, %rq', %Hw, Ha, -⟩ | Hdep)⟩
    · iframe HaE
      isplitr
      · ipureintro; exact Hr
      ileft; iexists hm, rq'; iframe Ha; ipureintro; exact Hw
    · iframe HaE Hdep
      ipureintro; exact Hr

/-- The mode-off `doSerialize` from the spec (the auth info's binding dropped). -/
theorem EtcdServer.doSerialize.spec_off
    (h : EtcdServer.doSerialize.spec (GF := GF) (hG := hG)) :
    EtcdServer.doSerialize.specOff (GF := GF) (hG := hG) := by
  have hM := EtcdServer.doSerialize.spec_M h false
  intro s E ρ γr ctx cd chk get G Q C t e
  iintro %Φ Hpre HΦ
  iapply (hM s E ρ γr ctx cd chk get G Q C t e) $$ %Φ [Hpre]
  · rw [isServerReqM_false, isServerReadM_false]; iexact Hpre
  inext
  iintro %err ⟨Hrd, Hres⟩
  iapply HΦ
  iframe Hrd
  icases Hres with (⟨%He, ⟨%info, HC, -⟩, HQ⟩ | Hr)
  · ileft; iframe HQ; isplitr
    · ipureintro; exact He
    · iexists info; iexact HC
  · iright; iexact Hr


/-- The mode-off `Put` from the spec (the gated rows dropped). -/
theorem EtcdServer.Put.spec_off
    (h : EtcdServer.Put.spec (GF := GF) (hG := hG)) :
    EtcdServer.Put.specOff (GF := GF) (hG := hG) := by
  intro s E ρ ctx cd r op Q F
  iintro %Φ ⟨#Hpkg, #Hsrv, Hrest⟩ HΦ
  ihave %hon := isServerReq_authOff s E ρ $$ Hsrv
  have h' := h s E ρ ctx cd r op Q F
  rw [hon] at h'
  simp only [putPermitM] at h'
  rw [isServerReqM_false] at h'
  iapply h' $$ [Hrest] [HΦ]
  · iframe Hpkg Hsrv Hrest
  iintro !> %resp %err ⟨Hrd, Hard, Hres⟩
  iapply HΦ
  iframe Hrd Hard
  icases Hres with (⟨%He, %hm, %x, %x', %o, %skip, %Hst, H1, H2, H3, H4, H5, H6, HQ, -, -⟩ |
    ⟨%Hr, #HaE, (⟨%hm, Herr, -⟩ | Hdep)⟩)
  · ileft
    isplitr
    · ipureintro; exact He
    iexists hm, x, x', o, skip
    iframe H1 H2 H3 H4 H5 H6 HQ
    ipureintro; exact Hst
  · iright
    iframe HaE
    isplitr
    · ipureintro; exact Hr
    ileft; iexists hm; iexact Herr
  · iright
    iframe HaE Hdep
    ipureintro; exact Hr

/-- The mode-on `Put` from the spec (the gate discharged). -/
theorem EtcdServer.Put.spec_on
    (h : EtcdServer.Put.spec (GF := GF) (hG := hG)) :
    EtcdServer.Put.specOn (GF := GF) (hG := hG) := by
  intro s E ρ ctx cd r op Q F
  iintro %Φ ⟨#Hpkg, #Hsrv, Hrest⟩ HΦ
  ihave %hon := isServerReqM_authOn true s E ρ $$ Hsrv
  have h' := h s E ρ ctx cd r op Q F
  rw [hon] at h'
  simp only [putPermitM] at h'
  iapply h' $$ [Hrest] [HΦ]
  · iframe Hpkg Hsrv Hrest
  iintro !> %resp %err ⟨Hrd, Hard, Hres⟩
  iapply HΦ
  iframe Hrd Hard
  icases Hres with (⟨%He, %hm, %x, %x', %o, %skip, %Hst, H1, H2, H3, H4, H5, H6, HQ, Hhb, #Hg⟩ | Herr)
  · ileft
    isplitr
    · ipureintro; exact He
    iexists hm, x, x', o, skip
    iframe H1 H2 H3 H4 H5 H6 HQ Hhb
    isplitr
    · ipureintro; exact Hst
    iapply Hg; ipureintro; simp
  · iright; iexact Herr

/-- The mode-off `DeleteRange` from the spec. -/
theorem EtcdServer.DeleteRange.spec_off
    (h : EtcdServer.DeleteRange.spec (GF := GF) (hG := hG)) :
    EtcdServer.DeleteRange.specOff (GF := GF) (hG := hG) := by
  intro s E ρ ctx cd r op Q F
  iintro %Φ ⟨#Hpkg, #Hsrv, Hrest⟩ HΦ
  ihave %hon := isServerReq_authOff s E ρ $$ Hsrv
  have h' := h s E ρ ctx cd r op Q F
  rw [hon] at h'
  simp only [deletePermitM] at h'
  rw [isServerReqM_false] at h'
  iapply h' $$ [Hrest] [HΦ]
  · iframe Hpkg Hsrv Hrest
  iintro !> %resp %err ⟨Hrd, Hard, Hres⟩
  iapply HΦ
  iframe Hrd Hard
  icases Hres with (⟨%He, %hm, %rq', %op', %x, %x', %o, %skip, %Hst, H1, H2, H3, H4, H5, H6, HQ, -, -⟩ |
    ⟨%Hr, #HaE, (⟨%hm, %rq', %Hw, Herr, -⟩ | Hdep)⟩)
  · ileft
    isplitr
    · ipureintro; exact He
    iexists hm, rq', op', x, x', o, skip
    iframe H1 H2 H3 H4 H5 H6 HQ
    ipureintro; exact Hst
  · iright
    iframe HaE
    isplitr
    · ipureintro; exact Hr
    ileft; iexists hm, rq'; iframe Herr; ipureintro; exact Hw
  · iright
    iframe HaE Hdep
    ipureintro; exact Hr

/-- The mode-on `DeleteRange` from the spec. -/
theorem EtcdServer.DeleteRange.spec_on
    (h : EtcdServer.DeleteRange.spec (GF := GF) (hG := hG)) :
    EtcdServer.DeleteRange.specOn (GF := GF) (hG := hG) := by
  intro s E ρ ctx cd r op Q F
  iintro %Φ ⟨#Hpkg, #Hsrv, Hrest⟩ HΦ
  ihave %hon := isServerReqM_authOn true s E ρ $$ Hsrv
  have h' := h s E ρ ctx cd r op Q F
  rw [hon] at h'
  simp only [deletePermitM] at h'
  iapply h' $$ [Hrest] [HΦ]
  · iframe Hpkg Hsrv Hrest
  iintro !> %resp %err ⟨Hrd, Hard, Hres⟩
  iapply HΦ
  iframe Hrd Hard
  icases Hres with (⟨%He, %hm, %rq', %op', %x, %x', %o, %skip, %Hst, H1, H2, H3, H4, H5, H6, HQ, Hhb, #Hg⟩ | Herr)
  · ileft
    isplitr
    · ipureintro; exact He
    iexists hm, rq', op', x, x', o, skip
    iframe H1 H2 H3 H4 H5 H6 HQ Hhb
    isplitr
    · ipureintro; exact Hst
    iapply Hg; ipureintro; simp
  · iright; iexact Herr


/-- The mode-off `Range` from the spec (at the lower bound `0`; the class a pass). -/
theorem EtcdServer.Range.spec_off
    (h : EtcdServer.Range.spec (GF := GF) (hG := hG)) :
    EtcdServer.Range.specOff (GF := GF) (hG := hG) := by
  intro s E ρ γr c ctx cd r o ot te Q F
  iintro %Φ ⟨#Hpkg, #Hsrv, #Hrd, Hrest⟩ HΦ
  ihave %hon := isServerReq_authOff s E ρ $$ Hsrv
  ihave #HaLb := srvAuthLb_off s E ρ $$ Hsrv
  have hoff : E.authMode = .off := by
    unfold apply.AEnv.authOn at hon
    cases hM : E.authMode <;> simp_all [auth.AuthMode.isOn]
  have h' := h s E ρ γr c ctx cd r o ot te Q F 0 (by rw [hoff]; intro h; cases h)
  rw [hon] at h'
  rw [isServerReqM_false, isServerReadM_false, kvStM_false] at h'
  simp only [rangeReadOkM_false] at h'
  iapply h' $$ [Hrest] [HΦ]
  · iframe Hpkg Hsrv Hrd HaLb
    isplitr
    · rw [hoff]; unfold auth.authPubLbM; ipureintro; trivial
    iexact Hrest
  iintro !> %resp %err ⟨Hcall, Hres⟩
  iapply HΦ
  iframe Hcall
  icases Hres with (⟨%He, ⟨%info, %m, -, #Hcl, -, -⟩, Hok⟩ | Herr)
  · ileft
    iframe Hok
    isplitr
    · ipureintro; exact He
    iexists info
    rw [hoff] at *
    iapply apply.rangeClass_of_from_off m info o $$ Hcl
  · iright; iexact Herr

/-- The mode-on `Range` from the spec. -/
theorem EtcdServer.Range.spec_on
    (h : EtcdServer.Range.spec (GF := GF) (hG := hG)) :
    EtcdServer.Range.specOn (GF := GF) (hG := hG) := by
  intro s E ρ γr c ctx cd r o ot te Q F n γa hM
  iintro %Φ ⟨#Hpkg, #Hsrv, Hrest⟩ HΦ
  ihave %hon := isServerReqM_authOn true s E ρ $$ Hsrv
  have h' := h s E ρ γr c ctx cd r o ot te Q F n (by rw [hM]; intro h; cases h)
  rw [hon] at h'
  iapply h' $$ [Hrest] HΦ
  iframe Hpkg Hsrv Hrest

end corollaries

end EtcdGrove
end Perennial
