/-
**`a.Apply(r, shouldApplyV3)` on a KV request with the verdict at the latest state** (the auth
plan's E2y, 2026-10-26; `notes/decisions.md`, "E2y of the auth plan"). Lean-first (no Rocq
counterpart).

A second triple of `apply.uberApplier.Apply` (`uber_applier.go`), beside its spec
(`Spec/.../apply/uberApplier__Apply.lean`) and the admin one (`ApplyAdmin.lean`), for the KV
requests (`isKVKind`) on the apply thread with no alarm set (the current chain the base one,
`baseChain`): the current applier's `Apply` (the chain's `applierTriples` clause, which takes any
`applyFunc` with a triple of its own) runs `dispatch` through its KV triple at the latest state
(`dispatch.kvSpecL`, `DispatchKVL.lean`), whose KV triples of the current applier are the base
applier's (`applierKVL_cur`: with no alarm the current applier is the base one). The principal
the auth applier hands `dispatch` is the request's (`principalOf rq`, from its header): so a
dispatched request's outcome is decided at the latest state for it (`kvOutL`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.uberApplier__Apply
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.DispatchKVL

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.apply go_etcd_io.etcd.api.v3

/-- No alarm is set exactly when `restoreAlarms`' chain is the base one. -/
theorem apply.alarmChain_eq_base (on ns cr : Bool) (h : apply.alarmChain on ns cr = apply.baseChain on) :
    ns = false ∧ cr = false := by
  cases ns <;> cases cr <;> simp_all [apply.alarmChain, apply.baseChain]

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-- **`a.Apply(r, shouldApplyV3)` on a KV request with no alarm set, the verdict at the latest
state** (see the file header): `Apply.spec`'s triple with the current chain the base one, the base
applier's KV triples at the latest state (`applierKVL`), the latest-state resource `L hs` and the
checked permissions' shape (`kvShapedL`); besides `Apply.spec`'s postcondition, `L hs` back and,
for a dispatched and applied request, its outcome decided at the latest state for its principal
(`kvOutL` at `principalOf rq`). (Strict M1, 2026-11-06: over `Apply.spec`'s restated resources,
`kvOwnPre` in place of `kvOwn ∗ storeWT ∗ cPre`, the floor `kvLogLb`, the thread's token in and
back with a reader token of the backend.) -/
abbrev apply.uberApplier.Apply.kvSpecL : Prop :=
  ∀ (E : apply.AEnv GF) (p : Loc) (opts : go_etcd_io.etcd.server.v3.etcdserver.apply.ApplierOptions)
    (x : apply.ApplyKV) (r : Loc) (rq : apply.IRRModel) (skip v3 : Bool) (F : mvcc.Log)
    (Pre Q Post : IProp GF) (rs : apply.RestM) (ci : apply.Chain)
    (L : List auth.AuthState → IProp GF) (hs : List auth.AuthState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗ apply.uberIs E p opts ∗
      apply.irrWrapperIs r rq skip ∗ apply.uberOwn E p x.chain ∗ apply.kvOwnPre v3 E x.log Pre Q Post ∗
      apply.certPreVW v3 E x.chain rq x.log
        (apply.kvOutL E.authMode hs (auth.authInfoM (apply.principalOf rq)) ci rq x.log) ∗
      ⌜apply.rqOk .none x.log rq ∧ apply.dispatchOk E.authOn rq⌝ ∗
      ⌜skip = true → rq.txn.isSome = true⌝ ∗ srvApi.kvLogLb E.γs F ∗ threadTok ∗
      E.FS ∗ (if v3 then apply.ciSplit E Pre else iprop(True)) ∗ E.RO rs ∗
      (∃ base : GoInterface, structFieldRef uberApplier go!"applyV3base" p ↦□ base ∗
        apply.applierKVL E (apply.baseChain E.authOn) ci base L) ∗ L hs ∗
      ⌜x.chain = apply.baseChain E.authOn ∧ apply.isKVKind (apply.dispatchKind rq) = true ∧
        apply.kvShapedL E.authMode hs rq⌝ }}
    (App (App (Val (p @!! go.GoType.PointerType uberApplier.ty @!! go!"Apply")) (Val #r)) (Val #v3))
  {{ (ar : Loc), RET #ar; threadTok ∗ apply.bkRTOf E ∗ E.FS ∗
    ∃ (x' : apply.ApplyKV) (out : apply.ApplyOut),
      apply.uberOwn E p x'.chain ∗ apply.kvOwn E x'.log ∗ apply.cPost v3 Pre Post ∗
      E.RO (apply.restOut rq v3 out rs) ∗
      ⌜apply.applyStep rq v3 x x' out ∧ (out = .rejected ∨ ∃ o, out = .dispatched o skip) ∧
        apply.applyFloorOk rq v3 F x.log out⌝ ∗
      apply.resTrace ar ∗ apply.applyResultIs rq v3 x.log ar out ∗
      apply.applyAuthRes E.authMode x.chain rq v3 out ∗ L hs ∗
      ⌜∀ o, out = .dispatched o skip → v3 = true →
        apply.kvOutL E.authMode hs (auth.authInfoM (apply.principalOf rq)) ci rq x.log o⌝ }}

end defs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-- **With no alarm set the current applier's KV triples are the base applier's**: its shape
(`uberShape`) at the base chain makes it the base applier. -/
theorem apply.applierKVL_cur (E : apply.AEnv GF) (p : Loc) (a : GoInterface) (ci : apply.Chain)
    (L : List auth.AuthState → IProp GF) :
    apply.uberShape E p (apply.baseChain E.authOn) a ∗
      (∃ base : GoInterface, structFieldRef uberApplier go!"applyV3base" p ↦□ base ∗
        apply.applierKVL E (apply.baseChain E.authOn) ci base L) ⊢
      apply.applierKVL E (apply.baseChain E.authOn) ci a L := by
  iintro ⟨#Hsh, %base, #Hb, #Hkv⟩
  iunfold apply.uberShape at Hsh
  icases Hsh with ⟨%base', %ns, %cr, %Hc, #Hb', #Has⟩
  obtain ⟨rfl, rfl⟩ := apply.alarmChain_eq_base _ _ _ Hc.symm
  icombine Hb Hb' gives %Hbb
  subst Hbb
  iunfold apply.alarmShape at Has
  icases Has with ⟨%a1, #H1, #H2⟩
  iunfold apply.cappedShape at H1
  icases H1 with %Ha1
  iunfold apply.corruptShape at H2
  icases H2 with %Ha
  subst Ha1 Ha
  iexact Hkv

theorem apply.uberApplier.Apply.wp_kvL
    (hD : apply.uberApplier.dispatch.kvSpecL (GF := GF) (hG := hG)) :
    apply.uberApplier.Apply.kvSpecL (GF := GF) (hG := hG) := by
  intro E p opts x r rq skip v3 F Pre Q Post rs ci L hs
  wp_start as ⟨#Hu, #Hw, Hown, Hkv, #Hcp, %Hok, %Hskip, #HF, Htt, HFS, HSp, HRO, #Hbase, HL, %Hx⟩
  obtain ⟨Hch, Hkk, Hsh⟩ := Hx
  iunfold apply.uberOwn at Hown
  icases Hown with ⟨%a, Ha, #Hs, %HcE, #Hsh⟩
  ihave #Hsh' : apply.uberShape E p (apply.baseChain E.authOn) a $$ []
  · rw [← Hch]; iexact Hsh
  ihave #HKV : apply.applierKVL E x.chain ci a L $$ []
  · rw [Hch]
    iapply apply.applierKVL_cur
    iframe Hsh' Hbase
  ihave #Hs' := Hs
  iunfold apply.applierSpec at Hs'
  icases Hs' with ⟨%ai, %Hai, #Ht⟩
  subst Hai
  iunfold apply.applierTriples at Ht
  icases Ht with ⟨-, -, -, -, -, -, -, -, -, -, #HApply, -⟩
  wp_auto
  iapply wp_fupd
  wp_apply HApply $$ %r %rq %skip %v3
      %(methods (go.GoType.PointerType uberApplier.ty) go!"dispatch" #p)
      %(iprop(structFieldRef uberApplier go!"applyV3" p ↦ (GoInterface.ok ai) ∗
        apply.kvOwnPre v3 E x.log Pre Q Post ∗ threadTok ∗ E.FS ∗
        (if v3 then apply.ciSplit E Pre else iprop(True)) ∗ E.RO rs ∗ L hs))
      %(fun ar => iprop(threadTok ∗ apply.bkRTOf E ∗ E.FS ∗ E.RO (apply.restAfter rq v3 rs) ∗ ∃ (a' : GoInterface) (c' : apply.Chain) (o : apply.Outcome),
        structFieldRef uberApplier go!"applyV3" p ↦ a' ∗ apply.applierSpec E c' a' ∗
        apply.kvOwn E (o.logAfter x.log) ∗ apply.cPost v3 Pre Post ∗
        ⌜apply.dispatchStep x.chain rq v3 x.log o ∧ apply.chainAfter rq v3 x.chain c' ∧
          apply.kvFloorOk rq v3 F x.log o ∧ a' = GoInterface.ok ai ∧ c' = x.chain⌝ ∗
        (∀ _ : v3 = true, apply.chainClass E.authMode (apply.principalOf rq) x.chain rq o) ∗
        apply.resTrace ar ∗ L hs ∗
        ⌜v3 = true → apply.kvOutL E.authMode hs (auth.authInfoM (apply.principalOf rq)) ci rq x.log o⌝ ∗
        apply.dispatchResult rq v3 x.log skip ar o))
      [Ha Hkv Htt HFS HSp HRO HL] as %ar Hpost
  · iframe Hw Ha Hkv Htt HFS HSp HRO HL
    isplitr
    · iapply apply.rdLend_kvOwnPre
    imodintro
    iintro %Φ' ⟨Hres, Ha, Hkv, Htt, HFS, HSp, HRO, HL⟩ HΦ'
    iapply (hD E p opts x.chain (.ok ai) r rq skip v3 x.log F Pre Q Post rs (apply.principalOf rq) ci L hs)
      $$ [Hres Ha Hkv Htt HFS HSp HRO HL]
    · iframe #
      iframe Hres Ha Hkv Htt HFS HSp HRO HL
      ipureintro; exact ⟨Hok, HcE, Hkk, Hsh⟩
    inext
    iintro %ar ⟨Htt, Hrt, Hres, HFS, HRO, HB⟩
    iapply HΦ'
    simp only []
    iframe Htt Hrt Hres HFS HRO
    iexact HB
  icases Hpost with (⟨⟨Htt, Hrt, HFS, HRO, %a', %c', %o, Ha', #Hs'', Hkv, HPP, %Hst, #Hcls, Htr, HL, %HXo, Hres⟩, #Hadm⟩ |
    ⟨%Hna, ⟨Ha, Hkv, Htt, HFS, -, HRO, HL⟩, Hrej⟩)
  · obtain ⟨-, -, -, ha, hc⟩ := id Hst
    subst ha hc
    imodintro
    iapply HΦ
    iframe Htt Hrt HFS
    iexists ⟨o.logAfter x.log, x.chain, x.crev⟩, (.dispatched o skip)
    simp only [apply.applyResultIs, apply.restOut, apply.applyAuthRes]
    iframe Hkv HPP Hres Htr HRO Hcls Hadm HL
    isplitl [Ha']
    · iunfold apply.uberOwn; iexists _; iframe Ha' Hs'' Hsh
      ipureintro; exact HcE
    isplitr
    · ipureintro
      exact ⟨⟨Hskip, Hst.1, rfl, Hst.2.1, (apply.dispatchCrev_nonCmp _ _ _ _
        (fun h => by simp [apply.isKVKind, h] at Hkk)).symm⟩, Or.inr ⟨o, rfl⟩, Hst.2.2.1⟩
    ipureintro
    intro o' ho' hv
    injection ho' with ho'
    subst ho'
    exact HXo hv
  · iunfold apply.rejectResultIs at Hrej
    icases Hrej with ⟨%Harn, %v, Hv, %Hvf, #HeI⟩
    ipersist Hv
    ihave ⟨Hkv, Hrt, HPre⟩ := apply.kvOwnPre_kvOwn v3 E x.log Pre Q Post $$ Hkv
    imodintro
    iapply HΦ
    iframe Htt Hrt HFS
    ihave HRO : iprop(E.RO (apply.restOut rq v3 .rejected rs)) $$ [HRO]
    · rw [show apply.restOut rq v3 .rejected rs = rs from rfl]; iexact HRO
    iexists x, .rejected
    iframe Hkv HRO HL
    isplitl [Ha]
    · iunfold apply.uberOwn; iexists _; iframe Ha Hs Hsh; ipureintro; exact HcE
    isplitl [HPre]
    · iapply apply.cPost_of_pre
      iexact HPre
    isplitr
    · ipureintro; exact ⟨⟨Hna, rfl⟩, Or.inl rfl, trivial⟩
    isplitl []
    · iapply apply.resTrace_err ar v Hvf.1 $$ Hv
    isplitr []
    · simp only [apply.applyResultIs]
      iunfold apply.rejectedResultIs
      isplitr
      · ipureintro; exact Harn
      iexists v
      iframe Hv HeI
      ipureintro; exact Hvf
    isplitr
    · simp only [apply.applyAuthRes]
      itrivial
    ipureintro
    intro o' ho'
    cases ho'

end proof

end EtcdGrove
end Perennial
