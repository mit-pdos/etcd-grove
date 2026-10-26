/-
**`a.Apply(r, shouldApplyV3)` on an admitted admin request in the mode `on`** (the auth plan's
E2o, 2026-10-26; `notes/decisions.md`, "E2o of the auth plan"). Lean-first (no Rocq counterpart).

A second triple of `apply.uberApplier.Apply` (`uber_applier.go`), beside its spec
(`Spec/.../apply/uberApplier__Apply.lean`), for the requests the mode `on` admits by their shape
(`adminKindOk`): the current applier's `Apply` (the chain's `applierTriples` clause, which takes
any `applyFunc` with a triple of its own) runs `dispatch` through its admin triple
(`dispatch.adminSpec`, `DispatchAdmin.lean`), whose admin triples of the current applier come from
the base applier's and the current applier's shape (`applierAdmin_cur`). The auth layer's admin
check either passes (the request's admin outcome, `adminDone`) or rejects the request (the
authority, its receipt and `W` back). The current chain is unchanged (`dispatch` keeps it).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.uberApplier__Apply
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.DispatchAdmin

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.apply go_etcd_io.etcd.api.v3

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The admin outcome of `Apply`'s result** `ar` for the outcome `out` (the auth plan's E2o):
a dispatched request's `adminDone` (its step or the model's refusal); a rejected or skipped one
ran nothing, and the authority with its fuel and the unspent receipt come back. -/
def apply.adminOut (γa : auth.AuthNames) (M : auth.AuthMode) (hs : List auth.AuthState)
    (rq : apply.IRRModel) (v3 : Bool) (ar : Loc) : apply.ApplyOut → IProp GF
  | .dispatched _ _ => apply.adminDone γa M hs rq v3 ar
  | _ => iprop(auth.authOwnFu γa hs ∗ ⧗ 1)

variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-- **`a.Apply(r, shouldApplyV3)` on an admitted admin request in the mode `on γa`** (see the
file header): `Apply.spec`'s precondition but for the KV floor, the store's write token, the rest
buckets and the certificates (which an admin request does not use), with `adminKindOk rq` in place
of `rqOk`, the auth store's admin step facts (`isAuthSteps`, for the base applier's admin triples),
the authority with its fuel, a time receipt (the admin step's cost) and the store's write
resource `W`; its postcondition is `Apply.spec`'s but for the rest buckets (which an admin request
leaves, `restAfter_other`), with `W` back and the admin outcome (`adminOut`). -/
abbrev apply.uberApplier.Apply.adminSpec : Prop :=
  ∀ (E : apply.AEnv GF) (p : Loc) (opts : go_etcd_io.etcd.server.v3.etcdserver.apply.ApplierOptions)
    (x : apply.ApplyKV) (r : Loc) (rq : apply.IRRModel) (skip v3 : Bool)
    (Pre Q Post : IProp GF) (W : IProp GF) (γa : auth.AuthNames) (hs : List auth.AuthState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗ apply.uberIs E p opts ∗
      apply.irrWrapperIs r rq skip ∗ apply.uberOwn E p x.chain ∗ apply.kvOwn E x.log ∗
      apply.cPre v3 E.P E.f Pre Q Post ∗
      apply.isAuthSteps opts.AuthStore' E.P E.f E.authMode W ∗
      ⌜E.authMode = .on γa ∧ apply.adminKindOk rq ∧ apply.dispatchOk E.authOn rq ∧
        receiptBound GF ≤ 2 ^ 48⌝ ∗ ⌜skip = true → rq.txn.isSome = true⌝ ∗
      auth.authOwnFu γa hs ∗ ⧗ 1 ∗ W }}
    (App (App (Val (p @!! go.GoType.PointerType uberApplier.ty @!! go!"Apply")) (Val #r)) (Val #v3))
  {{ (ar : Loc), RET #ar; ∃ (x' : apply.ApplyKV) (out : apply.ApplyOut),
      apply.uberOwn E p x'.chain ∗ apply.kvOwn E x'.log ∗ apply.cPost v3 Pre Post ∗
      ⌜apply.applyStep rq v3 x x' out ∧ (out = .rejected ∨ ∃ o, out = .dispatched o skip)⌝ ∗
      apply.resTrace ar ∗ apply.applyResultIs rq v3 x.log ar out ∗
      apply.applyAuthRes E.authMode x.chain rq v3 out ∗ W ∗
      apply.adminOut γa E.authMode hs rq v3 ar out }}

end defs

/-- An admitted admin request is not a KV request. -/
theorem apply.adminKindOk_nonKV (rq : apply.IRRModel) (h : apply.adminKindOk rq) :
    apply.isKVKind (apply.dispatchKind rq) = false := by
  unfold apply.adminKindOk at h
  split at h <;> simp_all [apply.isKVKind]

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

theorem apply.uberApplier.Apply.wp_admin
    (hD : apply.uberApplier.dispatch.adminSpec (GF := GF) (hG := hG))
    (hUA : apply.applierV3backend.UserAdd.fuelSpec (GF := GF) (hG := hG))
    (hRA : apply.applierV3backend.RoleAdd.fuelSpec (GF := GF) (hG := hG))
    (hUGR : apply.applierV3backend.UserGrantRole.fuelSpec (GF := GF) (hG := hG))
    (hRGP : apply.applierV3backend.RoleGrantPermission.fuelSpec (GF := GF) (hG := hG))
    (hAE : apply.applierV3backend.AuthEnable.fuelSpec (GF := GF) (hG := hG)) :
    apply.uberApplier.Apply.adminSpec (GF := GF) (hG := hG) := by
  intro E p opts x r rq skip v3 Pre Q Post W γa hs
  wp_start as ⟨#Hu, #Hw, Hown, Hkv, Hcs, #Hst, %Hok, %Hskip, Ho, Hrc, HW⟩
  ihave #Hpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply $$ []
  · iPkgInit
  iunfold apply.uberOwn at Hown
  icases Hown with ⟨%a, Ha, #Hs, %HcE, #Hsh⟩
  ihave #Had := apply.applierAdmin_cur hUA hRA hUGR hRGP hAE E W p opts x.chain a
    $$ [Hpkg Hu Hst Hsh]
  · iframe #
  ihave #Hs' := Hs
  iunfold apply.applierSpec at Hs'
  icases Hs' with ⟨%ai, %Hai, #Ht⟩
  subst Hai
  iunfold apply.applierTriples at Ht
  icases Ht with ⟨-, -, -, -, -, -, -, -, -, #HApply⟩
  wp_auto
  iapply wp_fupd
  wp_apply HApply $$ %r %rq %skip %v3
      %(methods (go.GoType.PointerType uberApplier.ty) go!"dispatch" #p)
      %(iprop(structFieldRef uberApplier go!"applyV3" p ↦ (GoInterface.ok ai) ∗ apply.kvOwn E x.log ∗
        apply.cPre v3 E.P E.f Pre Q Post ∗ auth.authOwnFu γa hs ∗ ⧗ 1 ∗ W))
      %(fun ar => iprop(structFieldRef uberApplier go!"applyV3" p ↦ (GoInterface.ok ai) ∗
        ∃ o : apply.Outcome, apply.kvOwn E (o.logAfter x.log) ∗ apply.cPost v3 Pre Post ∗
          ⌜apply.dispatchStep x.chain rq v3 x.log o⌝ ∗ apply.resTrace ar ∗
          apply.dispatchResult rq v3 x.log skip ar o ∗ W ∗ apply.adminDone γa E.authMode hs rq v3 ar))
      [Ha Hkv Hcs Ho Hrc HW] as %ar Hpost
  · iframe Hw Ha Hkv Hcs Ho Hrc HW
    imodintro
    iintro %Φ' ⟨Hres, Ha, Hkv, Hcs, Ho, Hrc, HW⟩ HΦ'
    iapply (hD E p opts x.chain (.ok ai) r rq skip v3 x.log Pre Q Post (apply.principalOf rq) W γa hs)
      $$ [Hres Ha Hkv Hcs Ho Hrc HW]
    · iframe #
      iframe Hres Ha Hkv Hcs Ho Hrc HW
      ipureintro; exact ⟨Hok, HcE⟩
    inext
    iintro %ar ⟨Hres, Ha, Hrest⟩
    iapply HΦ'
    simp only []
    iframe Hres Ha Hrest
  icases Hpost with (⟨⟨Ha', %o, Hkv, HPP, %Hst', Htr, Hres, HW, Hdone⟩, #Hadm⟩ |
    ⟨%Hna, ⟨Ha, Hkv, Hcs, Ho, Hrc, HW⟩, Hrej⟩)
  · imodintro
    iapply HΦ
    iexists ⟨o.logAfter x.log, x.chain⟩, (.dispatched o skip)
    simp only [apply.applyResultIs, apply.applyAuthRes, apply.adminOut]
    iframe Hkv HPP Htr Hres HW Hdone Hadm
    isplitl [Ha']
    · iunfold apply.uberOwn; iexists _; iframe Ha' Hs Hsh; ipureintro; exact HcE
    isplitr
    · ipureintro; exact ⟨⟨Hskip, Hst', rfl, Or.inl rfl⟩, Or.inr ⟨o, rfl⟩⟩
    iintro %_
    iapply (apply.chainClass_nonKV _ _ _ _ _ (apply.adminKindOk_nonKV rq Hok.2.1))
  · iunfold apply.rejectResultIs at Hrej
    icases Hrej with ⟨%Harn, %v, Hv, %Hvf, #HeI⟩
    ipersist Hv
    imodintro
    iapply HΦ
    iexists x, .rejected
    simp only [apply.applyResultIs, apply.applyAuthRes, apply.adminOut]
    iframe Hkv Ho Hrc HW
    isplitl [Ha]
    · iunfold apply.uberOwn; iexists _; iframe Ha Hs Hsh; ipureintro; exact HcE
    isplitl [Hcs]
    · iapply apply.cPost_of_pre
      iapply apply.cPre_pre
      iexact Hcs
    isplitr
    · ipureintro; exact ⟨⟨Hna, rfl⟩, by simp⟩
    isplitl []
    · iapply apply.resTrace_err ar v Hvf.1 $$ Hv
    iunfold apply.rejectedResultIs
    isplitr
    · ipureintro; exact Harn
    iexists v
    iframe Hv HeI
    ipureintro; exact Hvf

end proof

end EtcdGrove
end Perennial
