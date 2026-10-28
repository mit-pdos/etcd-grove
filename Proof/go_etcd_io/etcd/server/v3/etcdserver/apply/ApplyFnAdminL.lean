/-
**`apply.Apply(lg, e, uberApply, w, shouldApplyV3)` on an admitted admin request with the admin
check at the latest state** (the auth plan's E3c, 2026-10-27; `notes/decisions.md`, "E3c of the
auth plan"). Lean-first (no Rocq counterpart).

A third triple of `apply.Apply` (`apply.go`), beside its spec and E2o's admin triple
(`ApplyFnAdmin.lean`): the same code, with the call to the uber-applier through its latest-state
admin triple (`uberApplier.Apply.adminSpecL`, `ApplyAdminL.lean`). With no alarm set, the base
applier's latest-state `Apply` (`applierAdmL`) and the latest-state resource lent by the authority
family: a rejected entry's admin check refused at the latest state, a dispatched one's passed.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.ApplyFnAdmin
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.ApplyAdminL

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.apply go_etcd_io.etcd.api.v3

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The `UberApplier` `ua` with its base applier's admin triples and latest-state `Apply`**
(persistent): `uberAuthSteps`' with the base applier's `applierAdmL` for the latest-state family
`L`. -/
def apply.uberAuthStepsL (ua : GoInterface) (E : apply.AEnv GF) (W : IProp GF)
    (Own : auth.AuthNames → List auth.AuthState → IProp GF) (L : List auth.AuthState → IProp GF) :
    IProp GF :=
  iprop(∃ (p : Loc) (opts : go_etcd_io.etcd.server.v3.etcdserver.apply.ApplierOptions),
    ⌜ua = interface.mkOk (go.GoType.PointerType uberApplier.ty) #p⌝ ∗ apply.uberIs E p opts ∗
    ∃ base : GoInterface, structFieldRef uberApplier go!"applyV3base" p ↦□ base ∗
      apply.applierAdmin E (apply.baseChain E.authOn) base W Own ∗
      apply.applierAdmL E (apply.baseChain E.authOn) base L)

instance apply.uberAuthStepsL_persistent (ua : GoInterface) (E : apply.AEnv GF) (W : IProp GF)
    (Own : auth.AuthNames → List auth.AuthState → IProp GF) (L : List auth.AuthState → IProp GF) :
    Persistent (apply.uberAuthStepsL ua E W Own L) := by
  unfold apply.uberAuthStepsL; infer_instance

variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-- **`apply.Apply(lg, e, ua, w, shouldApplyV3)` on an admitted admin request with no alarm set,
the admin check at the latest state** (see the file header): `Apply.adminSpec`'s triple with
`uberAuthStepsL`, the current chain the base one and the authority family lending `L`
(`hsplit`); its postcondition but for `applyAuthRes`, with a rejected entry's check refused at the
latest state and a dispatched one's passed. -/
abbrev apply.Apply.adminSpecL : Prop :=
  ∀ (lg e : Loc) (m : EntryModel) (ua w : GoInterface) (v3 : Bool) (E : apply.AEnv GF)
    (Pre Q Post : IProp GF) (x : apply.ApplyKV) (rq : apply.IRRModel) (id : w64) (RD : IProp GF)
    (K G : Option GName → w64 → IProp GF) (ot : Option GName) (W : IProp GF)
    (γa : auth.AuthNames) (hs : List auth.AuthState) (Own : auth.AuthNames → List auth.AuthState → IProp GF)
    (L : List auth.AuthState → IProp GF),
  (∀ h, Own γa h ⊢ L h ∗ (L h -∗ Own γa h)) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
      apply.uberAuthStepsL ua E W Own L ∗ waitOk w RD K G ∗ RD ∗ K ot id ∗ ⌜lg ≠ null⌝ ∗ entryAt e m ∗
      (if v3 then iprop(□ ({{ E.P ∗ Pre }} (App (Val E.f) (Val #())) {{ RET #(); Q }}) ∗
          (Q ={⊤}=∗ E.P ∗ Post))
       else iprop(True)) ∗ Pre ∗
      apply.applyKV E ua x ∗
      ⌜apply.irrDecode m.data = some rq ∧ apply.irrId rq = some id ∧ apply.adminKindOk rq ∧
        apply.dispatchOk E.authOn rq ∧ E.authMode = .on γa ∧ receiptBound GF ≤ 2 ^ 48⌝ ∗
      ⌜x.chain = apply.baseChain E.authOn⌝ ∗
      Own γa hs ∗ ⧗ 1 ∗ W ∗ (if v3 then apply.adminExtra E γa rq Pre else iprop(True)) }}
    (App (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.apply.Apply))
      (Val #lg)) (Val #e)) (Val #ua)) (Val #w)) (Val #v3))
  {{ (ar : Loc) (id' : w64), RET (PairV #ar #id'); RD ∗
      (if v3 then iprop(Post ∨ Pre) else Pre) ∗ apply.resultErrOk ar ∗ apply.resTrace ar ∗
      ⌜id' = id⌝ ∗
      ∃ (x' : apply.ApplyKV) (out : apply.ApplyOut), apply.applyKV E ua x' ∗
        ⌜apply.applyStep rq v3 x x' out⌝ ∗
        ⌜(out = .rejected → apply.needAdminPermission rq = true ∧ apply.adminRejL E.authMode hs rq) ∧
          (∀ o s, out = .dispatched o s → apply.adminPassL E.authMode hs rq)⌝ ∗
        apply.applyResultIs rq v3 x.log ar out ∗
        (⌜out.waived = false⌝ ∨ G ot id) ∗ W ∗ apply.adminOut Own γa E.authMode hs rq v3 ar out ∗
        apply.adminRejErr ar out }}

end defs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

set_option hygiene false in
/-- The call `uberApply.Apply(wrapper, v3)` through its admin triple and the postcondition. -/
local macro "call_tail_adminL" : tactic => `(tactic| (
  wp_apply (hUA E p opts x «$r0_ptr» rq sk v3 Pre Q Post W γa hs Own L hsplit)
      $$ [Hown Hkv Hcs Ho Hrc HW] as %ar ⟨%x', %out, Hown, Hkv, HPP, %Hst, %Hlat, Htr, Hres, HW, Hdone, HRE⟩
  · iframe # Hown Hkv Hcs Ho Hrc HW
    isplitr
    · ipureintro; exact ⟨Hmode, Hadm, Hdk, Hrb⟩
    isplitr
    · ipureintro
      intro h
      rw [← hsk] at h
      simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at h
      cases ht : rq.txn with
      | none => exact absurd (Hlt.2 ht) h.2
      | some _ => rfl
    ipureintro; exact Hch
  ihave ⟨#Hok, Hres⟩ := apply.applyResultIs_resultErrOk rq v3 x.log ar out $$ Hres
  iapply HΦ
  iframe HRD
  isplitl [HPP]
  · iapply cPost_if; iexact HPP
  iframe Hok Htr
  isplitr
  · ipureintro; rfl
  iexists x', out
  iframe Hres HW Hdone HRE
  isplitl [Hown Hkv]
  · iunfold apply.applyKV; iexists p; iframe Hown Hkv; ipureintro; rfl
  isplitr
  · ipureintro; exact Hst.1
  isplitr
  · ipureintro
    refine ⟨Hlat.1, fun o s h => ?_⟩
    rcases Hst.2 with h' | ⟨o', h'⟩
    · rw [h'] at h; cases h
    · exact Hlat.2 o' h'
  icases Hwv with (%Hsk | HG)
  · ileft; ipureintro
    rcases Hst.2 with h | ⟨o, h⟩ <;> subst h <;> simp [apply.ApplyOut.waived, Hsk]
  · iright; iexact HG))

theorem apply.Apply.wp_adminL
    (hMU : pbutil.MustUnmarshalMessage.spec (GF := GF) (hG := hG))
    (hZS : zap.Stringer.spec (GF := GF) (hG := hG))
    (hDbg : zap.Logger.Debug.spec (GF := GF) (hG := hG))
    (hNSE : apply.noSideEffect.spec (GF := GF) (hG := hG))
    (hUA : apply.uberApplier.Apply.adminSpecL (GF := GF) (hG := hG)) :
    apply.Apply.adminSpecL (GF := GF) (hG := hG) := by
  -- (C1's A2) phase 1 of the spec-first stage: the proof (at 2040bccc8a) is redone in phase 2
  sorry

end proof

end EtcdGrove
end Perennial
