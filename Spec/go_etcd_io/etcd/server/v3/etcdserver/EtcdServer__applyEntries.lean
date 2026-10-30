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

/-- `s.applyEntries(…)` in the environment's auth mode (`E.authOn`; step 3 of the auth-mode merge,
2026-10-30: one statement for both modes, `.any` excluded; until then `spec` (auth off) and `specOn`,
now `ModeSpecs.lean`'s `specOff`/`specOn`, corollaries `spec_off`/`spec_on`). As `specOff` (the
statement off, in `ModeSpecs.lean`, with the full account of every row), with the rows that
differ by the mode at `E.authOn`: the server's view (`isServerM`), the committed log's shapes
(`logShapeM`: with auth on, an admitted admin request too), the applier state (`srvApplyKVM`, at the
model's auth state `sa`, unconstrained off), the apply thread's model (`kvAppliedM`, from
`srvAuthSt0`). **With auth on** (only): the server's lessor finds no lease (`srvLessorNilM`), the
receipts' bound, and the rights to issue tokens at the consistent index (`srvTokRights`, `True` off),
at the new consistent index after. -/
abbrev EtcdServer.applyEntries.spec : Prop :=
  ∀ (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF) (E : apply.AEnv GF) (ρ : ReqNames)
    (b : GoInterface) (ep ap : Loc) (es : GoSlice) (ents : List Loc) (ms : List EntryModel) (f0 : w64)
    (rac : GoChan) (st : ApplyState) (ai at0 a t : w64) (cs : Loc)
    (x : apply.ApplyKV) (γr : ReadNames) (A : List EntryModel) (γp : GName) (dv : Option Loc) (w : Nat) (sa : auth.AuthState),
  E.authMode ≠ .any → (E.authOn = true → receiptBound GF ≤ 2 ^ 48) →
  (ms = [] ∨ (entriesFrom f0 ms ∧ uint.Z f0 ≤ uint.Z ai + 1)) → uint.Z ai + 1 < 2 ^ 64 →
  loopOk γ st ai → logShapeM E.authOn (unapplied ai ms) →
  -- (D43 M3, 2026-10-25) the driver's view, `apply`'s
  dvOk ρ.raft γr.kv.c0 dv (ciEff γ st.k) (ai + 1) (unapplied ai ms) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ isServerM E.authOn s γ ci TM E ρ γr ∗ srvLessorNilM E.authOn s ∗ batchWaitOk ρ E ms ∗ taEntriesAddr ap ↦□ es ∗ taRaftAdvancedCAddr ap ↦□ rac ∗
      es ↦*□ ents ∗ entriesAt ents ms ∗
      epAppliedIAddr ep ↦ ai ∗ epAppliedTAddr ep ↦ at0 ∗ epConfState ep cs ∗
      applyThread γ st ∗ applyBackend γ ci b ∗ ciApplying ci a t ∗ srvLgReader s ∗ srvGoRes s ∗
      srvApplyKVM E.authOn s E ρ.wait x sa ∗ srvAppliedOwn γr ai ∗ appliedLogAt γr ai x.log ∗
      batchCommittedIdx γr ms ∗ srvWTPool E γp ∗ srvWTTaken γp w ∗ srvFS s ∗
      kvAppliedM E.authOn γr.raft γr.kv srvAuthSt0 A x sa ∗ srvRest E γr A ∗ kvBatch γr (ciEff γ st.k) ai A (unapplied ai ms) ∗
      dvView ρ.raft dv A ∗ dvRes s ρ.raft dv (A ++ unapplied ai ms) ∗ (match dv with | none => iprop(True) | some n => (letI := srvStor (GF := GF) ρ.raft.raft; nodeRunning n ρ.raft.raft.cl srvClusterN (1 : Qp).half)) ∗ srvApRes s γr A ∗
      -- (C1's A1, 2026-10-28) the rights to issue tokens at the consistent index
      srvTokRights E (ciEff γ st.k) }}
    (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"applyEntries"))
      (Val #ep)) (Val #ap))
  {{ RET #(); srvFS s ∗ dvView ρ.raft dv (A ++ unapplied ai ms) ∗ (match dv with | none => iprop(True) | some n => (letI := srvStor (GF := GF) ρ.raft.raft; nodeRunning n ρ.raft.raft.cl srvClusterN (1 : Qp).half)) ∗
      srvApRes s γr (A ++ unapplied ai ms) ∗
      ∃ (st' : ApplyState) (ai' at' a' t' : w64) (cs' : Loc),
        epAppliedIAddr ep ↦ ai' ∗ epAppliedTAddr ep ↦ at' ∗ epConfState ep cs' ∗
        applyThread γ st' ∗ srvTokRights E (ciEff γ st'.k) ∗ applyBackend γ ci b ∗
        ciApplying ci a' t' ∗ srvLgReader s ∗ srvGoRes s ∗
        srvAppliedOwn γr ai' ∗ srvWTTaken γp (w + (unapplied ai ms).length) ∗
        (∃ (x' : apply.ApplyKV) (sa' : auth.AuthState), srvApplyKVM E.authOn s E ρ.wait x' sa' ∗
          ⌜entriesStep (ciEff γ st.k) (unapplied ai ms) x x'⌝ ∗ appliedLogAt γr ai' x'.log ∗
          kvAppliedM E.authOn γr.raft γr.kv srvAuthSt0 (A ++ unapplied ai ms) x' sa' ∗ srvRest E γr (A ++ unapplied ai ms)) ∗
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
