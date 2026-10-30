/-
**`run`'s resources in the auth mode `on`** (the auth plan's E3q, 2026-10-27; `notes/decisions.md`,
"E3q of the auth plan"): `InvRun.lean`'s chain resource, start resource and premise with the
apply thread's mode-`on` rows.

- `kvRunAtOn`: the apply thread's KV ghost state at `A` over the mode-`on` model (`kvAppliedOn`
  from `srvAuthSt0`), at the auth state `sa` the applier row holds (`kvRun`'s; `StartOn`'s
  `kvRunOn` hides `sa`, which the loop must share with the row);
- `applyResOn`, `applyStartOn`: `applyRes` and `applyStart` with the server with auth on
  (`isServerM true`), the row `srvApplyKVOn` and `kvRunAtOn` at one auth state;
- `isServerRunOn`: `isServerRun` with those, the raft environment's `E.C` in the mode
  (`srvCM true`), and the server's lessor finding no lease (`srvLessorNil`, the named premise of
  the apply thread's latest-state triples).

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
    epAppliedIAddr C.ep ↦ ai ∗ epAppliedTAddr C.ep ↦ at' ∗ epConfState C.ep cs ∗
    srvSnapState C.s C.ep C.ms C.γs ai (W64 0) ∗ applyThread B.γ st ∗ applyBackend B.γ C.ci B.b ∗ ciApplying C.ci a t ∗
    srvLgReader C.s ∗ srvBemuReaderAt C.s C.E.γbe ∗ srvWgReader C.s ∗ srvApplyKVOn C.s B.E C.γw x sa ∗
    srvAppliedOwn C.γr ai ∗ appliedLogAt C.γr ai x.log ∗ kvRunAtOn C.γr C.ai₀ C.c₀ A x sa ∗
    srvRest B.E C.γr A ∗ srvApRes C.s C.γr A ∗
    (∃ w : Nat, srvWTTaken C.wt w ∗ ⌜uint.Z ai ≤ w⌝) ∗ srvTokRights B.E (ciEff B.γ st.k) ∗
    ⌜loopOk B.γ st ai ∧ uint.Z ai = uint.Z C.ai₀ + A.length ∧ ciJ (ciEff B.γ st.k) C.c₀ ai ∧
      entriesStep C.c₀ A C.x₀ x ∧ 1 ≤ C.γs.cap ∧ lastTermIs A at'⌝)

/-- **The apply thread's resources when `run` starts, in the mode `on`** (`applyStart`'s; the
model's auth state at the start's, `srvAuthSt0`). -/
def applyStartOn (s : Loc) (γ : ApplyNames) (ci : Loc) (b : GoInterface) (E : apply.AEnv GF)
    (γr : ReadNames) (ai₀ c₀ : w64) (x₀ : apply.ApplyKV) (γw : GName) : IProp GF :=
  iprop(∃ (st₀ : ApplyState) (a t : w64) (f : Bool),
    applyThread γ st₀ ∗ ⌜loopOk γ st₀ ai₀ ∧ c₀ = ciEff γ st₀.k⌝ ∗ applyBackend γ ci b ∗
    ciApplying ci a t ∗ srvLgReader s ∗ srvBemuReaderAt s E.γbe ∗ srvWgReader s ∗
    srvApplyKVOn s E γw x₀ srvAuthSt0 ∗
    srvAppliedOwn γr ai₀ ∗ appliedLogAt γr ai₀ x₀.log ∗ kvRunAtOn γr ai₀ c₀ [] x₀ srvAuthSt0 ∗
    srvRest E γr [] ∗ srvApRes s γr [] ∗ srvForceSnapAddr s ↦ f ∗ srvTokRights E (ciEff γ st₀.k))

/-- **What `run` needs in the mode `on`** (`isServerRun`'s, see the file header). -/
def isServerRunOn (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF)
    (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (Er : RNEnv GF) (γn : RNNames)
    (γg : GoNames) (γcx : context.ContextNames) (γd : ChanNames) (v : RunFields)
    (b : GoInterface) (ai₀ at₀ c₀ : w64) (x₀ : apply.ApplyKV) :
    IProp GF :=
  iprop("#Hsrv" ∷ isServerM true s γ ci TM E ρ γr ∗
    "#Hlnil" ∷ srvLessorNil s ∗
    "#Hsa" ∷ isServerApplyAll s γr ∗
    "#Hrn" ∷ isRaftNode Er γn (srvRAddr s) ∗
    "%HEr" ∷ ⌜Er.C = srvCM true ρ E ai₀ c₀ x₀ ∧ Er.γr = γr ∧
      (γn.node.dyn = true → uint.Z c₀ ≤ uint.Z ai₀ ∧ γn.pre = [] ∧ ai₀ = W64 0)⌝ ∗
    "#Hrf" ∷ srvRunFieldsAt s γr γg γcx v ∗
    "Hsnap" ∷ (∃ ms : Loc, rnRaftStorageAddr (srvRAddr s) ↦□ ms ∗ rnSnapOnce ms γn.γs ai₀ at₀) ∗
    "Hloop" ∷ rnLoopTok γn [] ∗ "Hsend" ∷ Er.S ∗ "Happly" ∷ rnApplyTok γn [] ∗ "Hrdone" ∷ rnDoneTok γn (srvRAddr s) ∗
    "Hcomm" ∷ (∃ c : w64, srvCommittedOwn γr c) ∗
    "Hdc" ∷ ownBroadcastChan v.done γd iprop(True) .Pending ∗
    "Hclose" ∷ token γg.close ∗
    "Hstart" ∷ applyStartOn s γ ci b E γr ai₀ c₀ x₀ ρ.wait ∗
    "Hlr" ∷ srvLgReader s ∗
    "#HWB" ∷ (∃ γp : GName, srvWTPool E γp ∗ srvWTAt γp ai₀))


/-- **What `run` needs in the mode `on`** (the auth-mode merge's step 1, 2026-10-29):
`isServerRun` off, `isServerRunOn` on. -/
def isServerRunM (on : Bool) (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF)
    (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (Er : RNEnv GF) (γn : RNNames)
    (γg : GoNames) (γcx : context.ContextNames) (γd : ChanNames) (v : RunFields)
    (b : GoInterface) (ai₀ at₀ c₀ : w64) (x₀ : apply.ApplyKV) : IProp GF :=
  match on with
  | false => isServerRun s γ ci TM E ρ γr Er γn γg γcx γd v b ai₀ at₀ c₀ x₀
  | true => isServerRunOn s γ ci TM E ρ γr Er γn γg γcx γd v b ai₀ at₀ c₀ x₀

theorem isServerRunM_false (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF)
    (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (Er : RNEnv GF) (γn : RNNames)
    (γg : GoNames) (γcx : context.ContextNames) (γd : ChanNames) (v : RunFields)
    (b : GoInterface) (ai₀ at₀ c₀ : w64) (x₀ : apply.ApplyKV) :
    isServerRunM (GF := GF) false s γ ci TM E ρ γr Er γn γg γcx γd v b ai₀ at₀ c₀ x₀ =
      isServerRun s γ ci TM E ρ γr Er γn γg γcx γd v b ai₀ at₀ c₀ x₀ := rfl

theorem isServerRunM_true (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF)
    (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (Er : RNEnv GF) (γn : RNNames)
    (γg : GoNames) (γcx : context.ContextNames) (γd : ChanNames) (v : RunFields)
    (b : GoInterface) (ai₀ at₀ c₀ : w64) (x₀ : apply.ApplyKV) :
    isServerRunM (GF := GF) true s γ ci TM E ρ γr Er γn γg γcx γd v b ai₀ at₀ c₀ x₀ =
      isServerRunOn s γ ci TM E ρ γr Er γn γg γcx γd v b ai₀ at₀ c₀ x₀ := rfl
end defs

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

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
