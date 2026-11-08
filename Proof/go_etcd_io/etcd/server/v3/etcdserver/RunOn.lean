/-
**`run`'s resources in the auth mode `on`** (the auth plan's E3q, 2026-10-27; `notes/decisions.md`,
"E3q of the auth plan"): `InvRunRes.lean`'s chain and start resources with the
apply thread's mode-`on` rows.

- `kvRunAtOn`: the apply thread's KV ghost state at `A` over the mode-`on` model (`kvAppliedOn`
  from `srvAuthSt0`), at the auth state `sa` the applier row holds (`kvRun`'s; `StartOn`'s
  `kvRunOn` hides `sa`, which the loop must share with the row);
- `applyResOn`, `applyStartOn`: `applyRes` and `applyStart` with the server with auth on
  (`isServerM true`), the row `srvApplyKVOn` and `kvRunAtOn` at one auth state;
- (until 2026-11-07) `isServerRunOn`, `run`'s mode-on premise: deleted, with `InvRun.lean`'s
  `isServerRun`, once `isServerRunC` (`AuthCompRows.lean`) stopped using them (R2d'a swap batch 5;
  the hub owner's call).

**Additive.** Nothing mode-off changes.

Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRun
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ApplyNormalOn

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- The environment's auth mode, kept by `beSucc`. -/
theorem beSucc_authMode {γ γ' : ApplyNames} {E E' : apply.AEnv GF} (h : beSucc γ E γ' E') :
    E'.authMode = E.authMode := by
  obtain ⟨-, p, P, f, c, RO, RW, rfl⟩ := h; rfl

/-- **The apply thread's KV ghost state at `A` in the mode `on`**, at the auth state `sa`
(`kvRun`'s). -/
def kvRunAtOn (γr : ReadNames) (ai₀ c₀ : w64) (A : List EntryModel) (x : apply.ApplyKV)
    (sa : auth.AuthState) : IProp GF :=
  iprop(kvAppliedOn γr.raft γr.kv srvAuthSt0 A x sa ∗ ⌜γr.kv.c0 = c₀ ∧ γr.raft.ai0 = ai₀⌝)

/-- **The apply thread's resources at the log `A` in the mode `on`** (`applyRes`'s). -/
def applyResOn (C : ApplyCtx GF) (A : List EntryModel) : IProp GF :=
  iprop(∃ (B : ApplyBe GF) (st : ApplyState) (ai at' a t : w64) (cs : Loc) (x : apply.ApplyKV)
      (sa : auth.AuthState),
    ⌜beSucc C.γ C.E B.γ B.E⌝ ∗ isServerM true C.s B.γ C.ci B.TM B.E C.ρ C.γr ∗
    epAppliedIAddr C.ep ↦ ai ∗ epAppliedTAddr C.ep ↦ at' ∗ epConfState C.ep cs ∗ epCsAt C.ρ.raft A cs ∗
    srvSnapState C.s C.ep C.ms C.γs ai (W64 0) ∗ applyThread B.γ st ∗ applyBackend B.γ C.ci B.b ∗ ciApplying C.ci a t ∗
    srvLgReader C.s ∗ srvBemuReaderAt C.s C.E.γbe ∗ srvWgReader C.s ∗ mvcc.api.mvccReaders B.E.γ 1 ∗ srvApplyKVOn C.s B.E C.γw x sa ∗
    srvAppliedOwn C.γr ai ∗ appliedLogAt C.γr ai x.log ∗ kvRunAtOn C.γr C.ai₀ C.c₀ A x sa ∗
    srvRest B.E C.γr A ∗ srvApRes C.s C.γr A ∗
    (∃ kv : GoInterface, srvKVAddr C.s ↦□ kv ∗ □ mvcc.api.isMvcc kv B.E.γ ∗ ⌜kv = B.E.kv⌝) ∗
    rnWalTokA C.rn (srvRAddr C.s) (1 : Qp).half ∗
    (∃ w : Nat, srvWTTaken C.wt.cnt w) ∗ srvTokRights B.E (ciEff B.γ st.k) ∗
    -- (D22 J1b, 2026-10-31) `applyRes`'s snapshot resources
    srvSnapOwn C.s C.ci B.E C.γr B.γ ai ∗
    ⌜loopOk B.γ st ai ∧ uint.Z ai = uint.Z C.ai₀ + A.length ∧ ciJ (ciEff B.γ st.k) C.c₀ ai ∧
      uint.Z ai ≤ uint.Z (ciEff B.γ st.k) ∧
      lastTermIs A at'⌝)

/-- **The apply thread's resources when `run` starts, in the mode `on`** (`applyStart`'s; the
model's auth state at the start's, `srvAuthSt0`). -/
def applyStartOn (s : Loc) (γ : ApplyNames) (ci : Loc) (b : GoInterface) (E : apply.AEnv GF)
    (γr : ReadNames) (ai₀ c₀ : w64) (x₀ : apply.ApplyKV) (γw : GName) : IProp GF :=
  iprop(∃ (st₀ : ApplyState) (a t : w64) (f : Bool),
    applyThread γ st₀ ∗ ⌜loopOk γ st₀ ai₀ ∧ c₀ = ciEff γ st₀.k⌝ ∗ applyBackend γ ci b ∗
    ciApplying ci a t ∗ srvLgReader s ∗ srvBemuReaderAt s E.γbe ∗ srvWgReader s ∗ mvcc.api.mvccReaders E.γ 1 ∗
    srvApplyKVOn s E γw x₀ srvAuthSt0 ∗
    srvAppliedOwn γr ai₀ ∗ appliedLogAt γr ai₀ x₀.log ∗ kvRunAtOn γr ai₀ c₀ [] x₀ srvAuthSt0 ∗
    srvRest E γr [] ∗ srvApRes s γr [] ∗ srvForceSnapAddr s ↦ f ∗ srvTokRights E (ciEff γ st₀.k) ∗
    -- (D22 J1b, 2026-10-31) `applyStart`'s snapshot resources
    srvSnapOwn s ci E γr γ ai₀)

end defs

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/-- **At the empty log the model's auth state is the start's** (E3r): `StartOn`'s `kvRunOn []` hides
an auth state the model reaches, which at `[]` is `srvAuthSt0` (`kvRaftOfOn` of the empty log). -/
theorem kvRunOn_nil_at (γr : ReadNames) (ai₀ c₀ : w64) (x : apply.ApplyKV) :
    kvRunOn (GF := GF) γr ai₀ c₀ [] x ⊢ kvRunAtOn γr ai₀ c₀ [] x srvAuthSt0 := by
  unfold kvRunOn kvRunAtOn kvAppliedOn kvAppliedLOn
  iintro ⟨⟨%st, ⟨#HL, Hhi, #Hc, %hs⟩, %hch⟩, %h⟩
  have hst : st = srvAuthSt0 := by
    rw [kvRaftOfOn_nil] at hs
    exact (Prod.mk.inj hs).1
  subst hst
  iframe HL Hhi Hc
  ipureintro
  exact ⟨⟨hs, hch⟩, h⟩

end lemmas

end EtcdGrove
end Perennial
