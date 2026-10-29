/-
**The server's mode variants of its merged specs** (the auth-mode merge,
`notes/auth-mode-merge-plan.md`, 2026-10-29): a merged spec is one statement for both auth modes,
the mode the environment's (`E.authOn`); for each, until its callers are merged too, the
statements of the two modes as they were (`specOff`, with the premise `E.authOn = false`, and
`specOn`, with `E.authOn = true`) and their corollaries `spec_off`/`spec_on` (no second proof:
`.claude/skills/spec/PRINCIPLES.md`, "One spec per function"). Each goes when no caller uses it.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__snapshotIfNeededAndCompactRaftLog

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

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
    (ms : Loc) (γs : MemStorNames) (γp : GName) (w : Nat),
  E.authOn = false →
  loopOk γ st ai →
  1 ≤ γs.cap →
  -- (D22 J5) the applied index at most the write tokens taken (no snapshot installed)
  uint.Z ai ≤ w →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerApplyAll s γr ∗ srvWTPool E γp ∗ srvWTTaken γp w ∗ srvSnapState s ep ms γs ai (W64 0) ∗
      -- (D19i part 1) the storage's floor past the applied index (`raftAdvancedC`'s)
      memFloorAtLeast ms γs (uint.Z ai) ∗
      epAppliedIAddr ep ↦ ai ∗ epAppliedTAddr ep ↦ at' ∗ epConfState ep cs ∗
      applyThread γ st ∗ applyBackend γ ci b ∗ ciApplying ci a t ∗ srvLgReader s ∗ srvApplyKV s E γw x }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"snapshotIfNeededAndCompactRaftLog"))
      (Val #ep))
  {{ RET #(); ∃ st' : ApplyState, srvSnapState s ep ms γs ai (W64 0) ∗
      epAppliedIAddr ep ↦ ai ∗ epAppliedTAddr ep ↦ at' ∗ epConfState ep cs ∗
      applyThread γ st' ∗ applyBackend γ ci b ∗ ciApplying ci a t ∗ srvLgReader s ∗ srvApplyKV s E γw x ∗ ⌜loopOk γ st' ai ∧ ciEff γ st'.k = ciEff γ st.k⌝ }}

/-- **`spec` with auth on** (a corollary, `spec_on`; the auth plan's E3p, 2026-10-27): the row with the
auth part at the model's auth state `sa` (`srvApplyKVOn`), kept (`snapshot` takes only the part both
rows share, `srvApplyKVCore`). -/
abbrev EtcdServer.snapshotIfNeededAndCompactRaftLog.specOn : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (γw : GName) (γ : ApplyNames) (ci : Loc) (b : GoInterface) (γr : ReadNames)
    (ep : Loc) (st : ApplyState) (ai at' : w64) (cs : Loc) (a t : w64) (x : apply.ApplyKV)
    (ms : Loc) (γs : MemStorNames) (γp : GName) (w : Nat)
    (sa : auth.AuthState),
  E.authOn = true →
  loopOk γ st ai →
  1 ≤ γs.cap →
  -- (D22 J5) the applied index at most the write tokens taken (no snapshot installed)
  uint.Z ai ≤ w →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerApplyAll s γr ∗ srvWTPool E γp ∗ srvWTTaken γp w ∗ srvSnapState s ep ms γs ai (W64 0) ∗
      -- (D19i part 1) the storage's floor past the applied index (`raftAdvancedC`'s)
      memFloorAtLeast ms γs (uint.Z ai) ∗
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
  intro s E γw γ ci b γr ep st ai at' cs a t x ms γs γp w hoff
  have := h s E γw γ ci b γr ep st ai at' cs a t x ms γs γp w srvAuthSt0
  rw [hoff] at this
  exact this

/-- **`specOn`**, `spec` with the mode-`on` row (the auth-mode merge's corollary). -/
theorem EtcdServer.snapshotIfNeededAndCompactRaftLog.spec_on
    (h : EtcdServer.snapshotIfNeededAndCompactRaftLog.spec (GF := GF) (hG := hG)) :
    EtcdServer.snapshotIfNeededAndCompactRaftLog.specOn (GF := GF) (hG := hG) := by
  intro s E γw γ ci b γr ep st ai at' cs a t x ms γs γp w sa hon
  have := h s E γw γ ci b γr ep st ai at' cs a t x ms γs γp w sa
  rw [hon] at this
  exact this


end variants

end EtcdGrove
end Perennial
