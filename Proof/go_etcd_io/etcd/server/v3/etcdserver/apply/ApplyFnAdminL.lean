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

/-- **The `UberApplier` `ua`'s admin contract at the latest state** (step 6 of the auth-mode
merge, 2026-10-30; persistent): `ua` is the uber-applier `p`, whose `Apply` method has
`uberApplier.Apply.adminSpecL`'s triple at the base applier's admin steps `W`/`Own` and its
latest-state family `L` (what `uberAuthStepsL` gives with that triple, `uberAdmC_of`); the
family's lending (`adminSpecL`'s premise) a pure premise of the triple. In the method form
`apply.Apply.spec` calls it in. -/
def apply.uberAdmC (ua : GoInterface) (E : apply.AEnv GF) (W : IProp GF)
    (Own : auth.AuthNames → List auth.AuthState → IProp GF) (L : List auth.AuthState → IProp GF) :
    IProp GF :=
  iprop(∃ p : Loc, ⌜ua = interface.mkOk (go.GoType.PointerType uberApplier.ty) #p⌝ ∗
    □ ∀ (x : apply.ApplyKV) (r : Loc) (rq : apply.IRRModel) (skip v3 : Bool)
      (Pre Q Post : IProp GF) (γa : auth.AuthNames) (hs : List auth.AuthState),
    {{ ⌜∀ h, Own γa h ⊢ L h ∗ (L h -∗ Own γa h)⌝ ∗
        apply.irrWrapperIs r rq skip ∗ apply.uberOwn E p x.chain ∗ apply.kvOwn E x.log ∗
        apply.cPre v3 E.P E.f Pre Q Post ∗
        ⌜E.authMode = .on γa ∧ apply.adminKindOk rq ∧ apply.dispatchOk E.authOn rq ∧
          receiptBound GF ≤ 2 ^ 48⌝ ∗ ⌜skip = true → rq.txn.isSome = true⌝ ∗
        ⌜x.chain = apply.baseChain E.authOn⌝ ∗
        Own γa hs ∗ ⧗ 1 ∗ W ∗ (if v3 then apply.adminExtraG E γa rq hs Pre else iprop(True)) }}
      (App (App (Val (p @!! go.GoType.PointerType uberApplier.ty @!! go!"Apply")) (Val #r)) (Val #v3))
    {{ (ar : Loc), RET #ar; ∃ (x' : apply.ApplyKV) (out : apply.ApplyOut),
        apply.uberOwn E p x'.chain ∗ apply.kvOwn E x'.log ∗ apply.cPost v3 Pre Post ∗
        ⌜apply.applyStep rq v3 x x' out ∧ (out = .rejected ∨ ∃ o, out = .dispatched o skip)⌝ ∗
        ⌜(out = .rejected → apply.needAdminPermission rq = true ∧ apply.adminRejL E.authMode hs rq) ∧
          (∀ o, out = .dispatched o skip → apply.adminPassL E.authMode hs rq)⌝ ∗
        apply.resTrace ar ∗ apply.applyResultIs rq v3 x.log ar out ∗ W ∗
        apply.adminOut Own γa E.authMode hs rq v3 ar out ∗ apply.adminRejErr ar out }})

instance apply.uberAdmC_persistent (ua : GoInterface) (E : apply.AEnv GF) (W : IProp GF)
    (Own : auth.AuthNames → List auth.AuthState → IProp GF) (L : List auth.AuthState → IProp GF) :
    Persistent (apply.uberAdmC ua E W Own L) := by
  unfold apply.uberAdmC; infer_instance

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
      apply.uberAdmC ua E W Own L ∗ waitOk w RD K G ∗ RD ∗ K ot id ∗ ⌜lg ≠ null⌝ ∗ entryAt e m ∗
      (if v3 then iprop(□ ({{ E.P ∗ Pre }} (App (Val E.f) (Val #())) {{ RET #(); Q }}) ∗
          (Q ={⊤}=∗ E.P ∗ Post))
       else iprop(True)) ∗ Pre ∗
      apply.applyKV E ua x ∗
      ⌜apply.irrDecode m.data = some rq ∧ apply.irrId rq = some id ∧ apply.adminKindOk rq ∧
        apply.dispatchOk E.authOn rq ∧ E.authMode = .on γa ∧ receiptBound GF ≤ 2 ^ 48⌝ ∗
      ⌜x.chain = apply.baseChain E.authOn⌝ ∗
      Own γa hs ∗ ⧗ 1 ∗ W ∗ (if v3 then apply.adminExtraG E γa rq hs Pre else iprop(True)) }}
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

/-- **`uberAuthStepsL` gives `uberAdmC`** with the uber-applier's `adminSpecL`. -/
theorem apply.uberAdmC_of (hUA : apply.uberApplier.Apply.adminSpecL (GF := GF) (hG := hG))
    (ua : GoInterface) (E : apply.AEnv GF) (W : IProp GF)
    (Own : auth.AuthNames → List auth.AuthState → IProp GF) (L : List auth.AuthState → IProp GF) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
      apply.uberAuthStepsL ua E W Own L ⊢ apply.uberAdmC ua E W Own L := by
  iintro ⟨#Hpkg, #H⟩
  iunfold apply.uberAuthStepsL at H
  icases H with ⟨%p, %opts, %Hua, #Hu, %base, #Hbf, #Hsteps, #HstepsL⟩
  iunfold apply.uberAdmC
  iexists p
  isplitr
  · ipureintro; exact Hua
  iintro !> %x %r %rq %skip %v3 %Pre %Q %Post %γa %hs
  wp_start_folded as ⟨%hsplit, #Hwr, Hown, Hkv, Hcs, %Hp1, %Hp2, %Hch, Ho, Hrc, HW, Hx⟩
  wp_apply (hUA E p opts x r rq skip v3 Pre Q Post W γa hs Own L hsplit)
      $$ [Hown Hkv Hcs Ho Hrc HW Hx] as %ar HQ
  · iframe # Hown Hkv Hcs Ho Hrc HW Hx
    isplitr
    · ipureintro; exact Hp1
    isplitr
    · ipureintro; exact Hp2
    ipureintro; exact Hch
  iapply HΦ; iexact HQ

/-- **`Apply.adminSpecL` from `Apply.spec`**: the method contract is `uberAdmC`'s. -/
theorem apply.Apply.wp_adminL (hA : apply.Apply.spec (GF := GF) (hG := hG)) :
    apply.Apply.adminSpecL (GF := GF) (hG := hG) := by
  intro lg e m ua w v3 E Pre Q Post x rq id RD K G ot W γa hs Own L hsplit
  wp_start_folded as ⟨#Hfor, #Hwok, HRD, HK, %Hlg, #He, Hhook, HPre, Hkv, %Hprem, %Hch, Ho, Hrc, HW, Hx⟩
  obtain ⟨Hdec, Hid, Hadm, Hdk, Hmode, Hrb⟩ := Hprem
  iunfold apply.uberAdmC at Hfor
  icases Hfor with ⟨%p, %Hua, #Htr⟩
  iunfold apply.applyKV at Hkv
  icases Hkv with ⟨%p', %Hua', Hown, Hkv⟩
  subst Hua
  have := apply.mkOk_ptr_inj _ _ _ Hua'
  subst this
  ihave Hcs : iprop(apply.cPre v3 E.P E.f Pre Q Post) $$ [Hhook HPre]
  · cases v3
    · simp only [apply.cPre, Bool.false_eq_true, ↓reduceIte]
      iexact HPre
    · simp only [apply.cPre, ↓reduceIte, mvcc.csContract]
      icases Hhook with ⟨#Htr, Hup⟩
      iframe HPre Hup
      imodintro
      iexact Htr
  wp_apply (hA lg e m (interface.mkOk (go.GoType.PointerType uberApplier.ty) #p) w v3 rq id RD K G ot
      iprop(apply.uberOwn E p x.chain ∗ apply.kvOwn E x.log ∗ apply.cPre v3 E.P E.f Pre Q Post ∗
        Own γa hs ∗ ⧗ 1 ∗ W ∗ (if v3 then apply.adminExtraG E γa rq hs Pre else iprop(True)))
      (fun sk ar => iprop(∃ (x' : apply.ApplyKV) (out : apply.ApplyOut),
        apply.uberOwn E p x'.chain ∗ apply.kvOwn E x'.log ∗ apply.cPost v3 Pre Post ∗
        ⌜apply.applyStep rq v3 x x' out ∧ (out = .rejected ∨ ∃ o, out = .dispatched o sk)⌝ ∗
        ⌜(out = .rejected → apply.needAdminPermission rq = true ∧ apply.adminRejL E.authMode hs rq) ∧
          (∀ o, out = .dispatched o sk → apply.adminPassL E.authMode hs rq)⌝ ∗
        apply.resTrace ar ∗ apply.applyResultIs rq v3 x.log ar out ∗ W ∗
        apply.adminOut Own γa E.authMode hs rq v3 ar out ∗ apply.adminRejErr ar out)))
      $$ [HRD HK Hown Hkv Hcs Ho Hrc HW Hx] as %ar %id' ⟨HRD, %Hid', Hout⟩
  · iframe # HRD HK Hown Hkv Hcs Ho Hrc HW Hx
    isplitr
    · ipureintro; exact Hlg
    isplitr
    · ipureintro; exact ⟨Hdec, Hid⟩
    iexists ⟨go.GoType.PointerType uberApplier.ty, #p⟩
    isplitr
    · ipureintro; rfl
    iintro !> %r %sk
    wp_start_folded as ⟨#Hwr, %Hskt, Hown, Hkv, Hcs, Ho, Hrc, HW, Hx⟩
    wp_apply Htr $$ %x %r %rq %sk %v3 %Pre %Q %Post %γa %hs
        [Hown Hkv Hcs Ho Hrc HW Hx] as %ar HQ
    · iframe # Hown Hkv Hcs Ho Hrc HW Hx
      isplitr
      · ipureintro; exact hsplit
      isplitr
      · ipureintro; exact ⟨Hmode, Hadm, Hdk, Hrb⟩
      isplitr
      · ipureintro; exact Hskt
      ipureintro; exact Hch
    iapply HΦ; iexact HQ
  subst Hid'
  icases Hout with (⟨%sk, ⟨%x', %out, Hown, Hkv, HPP, %Hst, %Hlat, Htr, Hres, HW, Hdone, HRE⟩, Hwv⟩ |
    ⟨%Hnil, HG, Hown, Hkv, Hcs, Ho, Hrc, HW, Hx⟩)
  · ihave ⟨#Hok, Hres⟩ := apply.applyResultIs_resultErrOk rq v3 x.log ar out $$ Hres
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
    · iright; iexact HG
  · obtain ⟨Har, hns⟩ := Hnil
    subst Har
    iapply HΦ
    iframe HRD
    isplitl [Hcs]
    · iapply cPost_if; iapply apply.cPost_of_pre; iapply apply.cPre_pre; iexact Hcs
    isplitr
    · iunfold apply.resultErrOk; ileft; ipureintro; rfl
    isplitr
    · iapply apply.resTrace_null
    isplitr
    · ipureintro; rfl
    iexists x, .skipped
    simp only [apply.applyResultIs, apply.adminOut, apply.adminRejErr]
    iframe HW Ho Hrc
    isplitl [Hown Hkv]
    · iunfold apply.applyKV; iexists p; iframe Hown Hkv; ipureintro; rfl
    isplitr
    · ipureintro; simp [apply.applyStep, hns]
    isplitr
    · ipureintro; exact ⟨fun h => (by cases h), fun _ _ h => (by cases h)⟩
    iright; iexact HG

end proof

end EtcdGrove
end Perennial
