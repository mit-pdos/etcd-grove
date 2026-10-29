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
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__applyEntryNormal

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


/-! ## `applyEntryNormal` (the bridge until step 6 merges it) -/

/-- **`applyEntryNormal` in the environment's auth mode** (the plan's step 3 bridge): `spec` and
`specOn` as one statement, the mode `E.authOn` (`.any` excluded), so that a merged caller need not
wait for step 6; derived from the two proofs (`applyEntryNormal_specE`). Off it takes a receipt
and the rights to issue tokens (`True` off) it does not need. -/
abbrev EtcdServer.applyEntryNormal.specE : Prop :=
  ∀ (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF) (E : apply.AEnv GF) (ρ : ReqNames)
    (b : GoInterface) (e : Loc) (m : EntryModel) (st : ApplyState) (v3 : Bool) (x : apply.ApplyKV)
    (γr : ReadNames) (ot : Option GName) (v : w64) (A : List EntryModel) (sa : auth.AuthState),
  E.authMode ≠ .any →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isServerM E.authOn s γ ci TM E ρ γr ∗ srvLessorNilM E.authOn s ∗ entryWaitOk ρ E m ∗
      entryRegd ρ.wait ρ.ids.pfx m ot ∗ entryAt e m ∗ applyThread γ st ∗ applyBackend γ ci b ∗
      srvLgReader s ∗ srvGoRes s ∗ srvApplyKVM E.authOn s E ρ.wait x sa ∗ mvcc.storeWT E.γ ∗
      srvFS s ∗ ⧗ 1 ∗ srvAppliedOwn γr v ∗ appliedLogAt γr v x.log ∗ committedAtLeast γr m.index ∗
      kvAppliedM E.authOn γr.raft γr.kv srvAuthSt0 A x sa ∗ srvRest E γr A ∗
      srvRLogLb γr.raft (A ++ [m]) ∗
      ⌜uint.Z v = uint.Z γr.raft.ai0 + A.length ∧ v3 = decide (uint.Z γr.kv.c0 < uint.Z m.index)⌝ ∗
      ⌜uint.Z m.index = uint.Z v + 1⌝ ∗
      ⌜st.pending = false ∧ entryOkM E.authOn x m ∧ m.typ = W32 0 ∧
        (E.authOn = true → receiptBound GF ≤ 2 ^ 48)⌝ ∗
      (if v3 then iprop(ciApplying ci m.index m.term ∗
          ⌜m.index = st.p + 1 ∧ uint.Z st.p < uint.Z m.index ∧
            uint.Z (ciEff γ st.k) < uint.Z m.index ∧ stLoaded γ st = st⌝)
       else iprop(True)) ∗
      srvTokRights E (ciEff γ st.k) }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"applyEntryNormal"))
      (Val #e)) (Val #v3))
  {{ RET #(); applyBackend γ ci b ∗ srvLgReader s ∗ srvGoRes s ∗ srvFS s ∗
      (∃ (x' : apply.ApplyKV) (out : apply.ApplyOut) (sa' : auth.AuthState),
        srvApplyKVM E.authOn s E ρ.wait x' sa' ∗ ⌜entryStep m v3 x x' out⌝ ∗
        entryDelivered ρ.wait m ot out ∗ srvAppliedPre γr v m.index x'.log ∗
        kvAppliedM E.authOn γr.raft γr.kv srvAuthSt0 (A ++ [m]) x' sa' ∗ srvRest E γr (A ++ [m])) ∗
      (if v3 then iprop(ciApplying ci m.index m.term ∗
          ∃ eff : w64, applyThread γ ⟨m.index, m.index, eff, false⟩)
       else applyThread γ st) ∗
      (if v3 then srvTokRights E m.index else srvTokRights E (ciEff γ st.k)) }}

/-- `specE` from the two modes' proofs, by the environment's mode. -/
theorem EtcdServer.applyEntryNormal.specE_of
    (h : EtcdServer.applyEntryNormal.spec (GF := GF) (hG := hG))
    (hOn : EtcdServer.applyEntryNormal.specOn (GF := GF) (hG := hG)) :
    EtcdServer.applyEntryNormal.specE (GF := GF) (hG := hG) := by
  intro s γ ci TM E ρ b e m st v3 x γr ot v A sa hany
  cases hm : E.authMode with
  | any => exact absurd hm hany
  | off =>
    have hoff : E.authOn = false := by rw [apply.AEnv.authOn_eq, hm]; rfl
    have hT : ∀ k, srvTokRights (GF := GF) E k = iprop(True) := by
      intro k; unfold srvTokRights; rw [hm]
    rw [hoff]
    simp only [isServerM_false, srvLessorNilM_false, srvApplyKVM_false, kvAppliedM_false,
      entryOkM_false]
    iintro %Φ ⟨#Hpkg, #Hsrv, -, #Hew, Hrg, He, Hst, Hbe, Hlr, Hgr, HKV, Hwt, Hfs, -, Hao, Hlog,
      #Hcm, Hka, HRS, #Hrl, %Hv, %Hidx, %Hpre, Hv3, -⟩ HΦ
    iapply (h s γ ci TM E ρ b e m st v3 x γr ot v A) $$
      [Hrg He Hst Hbe Hlr Hgr HKV Hwt Hfs Hao Hlog Hka HRS Hv3]
    · iframe Hpkg Hsrv Hew Hrg He Hst Hbe Hlr Hgr HKV Hwt Hfs Hao Hlog Hcm Hka HRS Hrl Hv3
      ipureintro; exact ⟨Hv, Hidx, Hpre.1, Hpre.2.1, Hpre.2.2.1⟩
    inext
    iintro ⟨Hbe, Hlr, Hgr, Hfs, ⟨%x', %out, HKV, %Hstep, Hdel, Hap, Hka, HRS⟩, Hst⟩
    iapply HΦ
    iframe Hbe Hlr Hgr Hfs Hst
    isplitl [HKV Hdel Hap Hka HRS]
    · iexists x', out, sa; iframe HKV Hdel Hap Hka HRS; ipureintro; exact Hstep
    cases v3 <;> simp only [hT, ite_true, ite_false, Bool.false_eq_true] <;> itrivial
  | on γa =>
    have hon : E.authOn = true := by rw [apply.AEnv.authOn_eq, hm]; rfl
    rw [hon]
    simp only [srvLessorNilM_true, srvApplyKVM_true, kvAppliedM_true,
      entryOkM_true]
    iintro %Φ ⟨#Hpkg, #Hsrv, #Hln, #Hew, Hrg, He, Hst, Hbe, Hlr, Hgr, HKV, Hwt, Hfs, Hr, Hao, Hlog,
      #Hcm, Hka, HRS, #Hrl, %Hv, %Hidx, %Hpre, Hv3, Htok⟩ HΦ
    iapply (hOn s γ ci TM E ρ b e m st v3 x γr ot v A γa sa hm) $$
      [Hrg He Hst Hbe Hlr Hgr HKV Hwt Hfs Hr Hao Hlog Hka HRS Hv3 Htok] HΦ
    iframe Hpkg Hsrv Hln Hew Hrg He Hst Hbe Hlr Hgr HKV Hwt Hfs Hr Hao Hlog Hcm Hka HRS Hrl Hv3 Htok
    ipureintro; exact ⟨Hv, Hidx, Hpre.1, Hpre.2.1, Hpre.2.2.1, Hpre.2.2.2 trivial⟩

end variants

end EtcdGrove
end Perennial
