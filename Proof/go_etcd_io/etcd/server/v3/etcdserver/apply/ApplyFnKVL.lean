/-
**`apply.Apply(lg, e, uberApply, w, shouldApplyV3)` on a KV entry with the verdict at the latest
state** (the auth plan's E2y, 2026-10-26; `notes/decisions.md`, "E2y of the auth plan").
Lean-first (no Rocq counterpart).

A second triple of `apply.Apply` (`apply.go`), beside its spec (`Spec/.../apply/Apply.lean`) and
the admin one (`ApplyFnAdmin.lean`), for a KV entry (`isKVKind`) on the apply thread with no alarm
set: the same code as `Apply.wp_proof`'s (decode the entry, its ID, the waiter check, the wrapper),
with the call to the uber-applier through its KV triple at the latest state
(`uberApplier.Apply.kvSpecL`, `ApplyKVL.lean`). A dispatched and applied request's outcome is
decided at the latest state for the request's principal (`kvOutL` at `principalOf rq`), the
hypothesis of E2t's `kv_applied_out_on` through `outcomeOn_of_kvOutL` (`KVOutcomeOn.lean`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.Apply
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.uberApplier__Apply
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.UberLemmas
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Packaging
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Apply
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.ApplyKVL

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.apply go_etcd_io.etcd.api.v3

/-- A dispatched outcome's `skip` is the wrapper's. -/
theorem apply.dispatched_skip {out : apply.ApplyOut} {o : apply.Outcome} {b sk : Bool}
    (h : out = .rejected ∨ ∃ o', out = .dispatched o' sk) (hb : out = .dispatched o b) :
    out = .dispatched o sk := by
  rcases h with h | ⟨o', h⟩ <;> subst h <;> simp_all

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The `UberApplier` `ua` with its base applier's KV triples at the latest state** (the auth
plan's E2y; persistent): `applierFor`'s and the base applier's `applierKVL` for the resource
family `L` (of the auth applier, `applierKVL_auth`). -/
def apply.uberKVL (ua : GoInterface) (E : apply.AEnv GF) (ci : apply.Chain)
    (L : List auth.AuthState → IProp GF) : IProp GF :=
  iprop(∃ (p : Loc) (opts : go_etcd_io.etcd.server.v3.etcdserver.apply.ApplierOptions),
    ⌜ua = interface.mkOk (go.GoType.PointerType uberApplier.ty) #p⌝ ∗ apply.uberIs E p opts ∗
    ∃ base : GoInterface, structFieldRef uberApplier go!"applyV3base" p ↦□ base ∗
      apply.applierKVL E (apply.baseChain E.authOn) ci base L)

instance apply.uberKVL_persistent (ua : GoInterface) (E : apply.AEnv GF) (ci : apply.Chain)
    (L : List auth.AuthState → IProp GF) : Persistent (apply.uberKVL ua E ci L) := by
  unfold apply.uberKVL; infer_instance

variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-- **The `UberApplier` `ua`'s KV contract at the latest state** (step 6 of the auth-mode merge,
2026-10-30; persistent): `ua` is the uber-applier `p`, whose `Apply` method has
`uberApplier.Apply.kvSpecL`'s triple at the base chain's KV triples `ci` and the latest-state
family `L` (what `uberKVL` gives with that triple, `uberKVC_of`). In the method form
`apply.Apply.spec` calls it in. -/
def apply.uberKVC (ua : GoInterface) (E : apply.AEnv GF) (ci : apply.Chain)
    (L : List auth.AuthState → IProp GF) : IProp GF :=
  iprop(∃ p : Loc, ⌜ua = interface.mkOk (go.GoType.PointerType uberApplier.ty) #p⌝ ∗
    □ ∀ (x : apply.ApplyKV) (r : Loc) (rq : apply.IRRModel) (skip v3 : Bool) (F : mvcc.Log)
      (Pre Q Post : IProp GF) (rs : apply.RestM) (hs : List auth.AuthState),
    {{ apply.irrWrapperIs r rq skip ∗ apply.uberOwn E p x.chain ∗ apply.kvOwn E x.log ∗
        apply.certPreVW v3 E x.chain rq x.log
          (apply.kvOutL E.authMode hs (auth.authInfoM (apply.principalOf rq)) ci rq x.log) ∗
        mvcc.storeWT E.γ ∗ apply.cPre v3 E.P E.f Pre Q Post ∗
        ⌜apply.rqOk x.log rq ∧ apply.dispatchOk E.authOn rq⌝ ∗
        ⌜skip = true → rq.txn.isSome = true⌝ ∗ mvcc.idxCert E.γ.idx F ∗
        E.FS ∗ (if v3 then apply.ciSplit E Pre else iprop(True)) ∗ E.RO rs ∗ L hs ∗
        ⌜x.chain = apply.baseChain E.authOn ∧ apply.isKVKind (apply.dispatchKind rq) = true ∧
          apply.kvShapedL E.authMode hs rq⌝ }}
      (App (App (Val (p @!! go.GoType.PointerType uberApplier.ty @!! go!"Apply")) (Val #r)) (Val #v3))
    {{ (ar : Loc), RET #ar; E.FS ∗ ∃ (x' : apply.ApplyKV) (out : apply.ApplyOut),
        apply.uberOwn E p x'.chain ∗ apply.kvOwn E x'.log ∗ apply.cPost v3 Pre Post ∗
        E.RO (apply.restOut rq v3 out rs) ∗
        ⌜apply.applyStep rq v3 x x' out ∧ (out = .rejected ∨ ∃ o, out = .dispatched o skip) ∧
          apply.applyFloorOk rq v3 F x.log out⌝ ∗
        apply.resTrace ar ∗ apply.applyResultIs rq v3 x.log ar out ∗
        apply.applyAuthRes E.authMode x.chain rq v3 out ∗ L hs ∗
        ⌜∀ o, out = .dispatched o skip → v3 = true →
          apply.kvOutL E.authMode hs (auth.authInfoM (apply.principalOf rq)) ci rq x.log o⌝ }})

instance apply.uberKVC_persistent (ua : GoInterface) (E : apply.AEnv GF) (ci : apply.Chain)
    (L : List auth.AuthState → IProp GF) : Persistent (apply.uberKVC ua E ci L) := by
  unfold apply.uberKVC; infer_instance

/-- **`apply.Apply(lg, e, ua, w, shouldApplyV3)` on a KV entry with no alarm set, the verdict at
the latest state** (see the file header): `Apply.spec`'s triple with the uber-applier's base KV
triples at the latest state (`uberKVL`), the current chain the base one, the latest-state resource
`L hs` and the checked permissions' shape (`kvShapedL`); besides `Apply.spec`'s postcondition,
`L hs` back and, for a dispatched and applied request, its outcome decided at the latest state
for its principal (`kvOutL` at `principalOf rq`). -/
abbrev apply.Apply.kvSpecL : Prop :=
  ∀ (lg e : Loc) (m : EntryModel) (ua w : GoInterface) (v3 : Bool) (E : apply.AEnv GF)
    (Pre Q Post : IProp GF) (x : apply.ApplyKV) (rq : apply.IRRModel) (id : w64) (RD : IProp GF)
    (K G : Option GName → w64 → IProp GF) (ot : Option GName) (F : mvcc.Log) (rs : apply.RestM)
    (ci : apply.Chain) (L : List auth.AuthState → IProp GF) (hs : List auth.AuthState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
      apply.uberKVC ua E ci L ∗ waitOk w RD K G ∗ RD ∗ K ot id ∗ ⌜lg ≠ null⌝ ∗ entryAt e m ∗
      (if v3 then iprop(□ ({{ E.P ∗ Pre }} (App (Val E.f) (Val #())) {{ RET #(); Q }}) ∗
          (Q ={⊤}=∗ E.P ∗ Post))
       else iprop(True)) ∗ Pre ∗
      apply.applyKV E ua x ∗ mvcc.storeWT E.γ ∗
      apply.certPreVW v3 E x.chain rq x.log
        (apply.kvOutL E.authMode hs (auth.authInfoM (apply.principalOf rq)) ci rq x.log) ∗
      ⌜apply.irrDecode m.data = some rq ∧ apply.irrId rq = some id ∧ apply.rqOk x.log rq ∧
        apply.dispatchOk E.authOn rq⌝ ∗ mvcc.idxCert E.γ.idx F ∗
      E.FS ∗ (if v3 then apply.ciSplit E Pre else iprop(True)) ∗ E.RO rs ∗ L hs ∗
      ⌜x.chain = apply.baseChain E.authOn ∧ apply.isKVKind (apply.dispatchKind rq) = true ∧
        apply.kvShapedL E.authMode hs rq⌝ }}
    (App (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.apply.Apply))
      (Val #lg)) (Val #e)) (Val #ua)) (Val #w)) (Val #v3))
  {{ (ar : Loc) (id' : w64), RET (PairV #ar #id'); RD ∗ E.FS ∗
      (if v3 then iprop(Post ∨ Pre) else Pre) ∗ apply.resultErrOk ar ∗ apply.resTrace ar ∗
      ⌜id' = id⌝ ∗
      ∃ (x' : apply.ApplyKV) (out : apply.ApplyOut), apply.applyKV E ua x' ∗
        E.RO (apply.restOut rq v3 out rs) ∗
        ⌜apply.applyStep rq v3 x x' out ∧ apply.applyFloorOk rq v3 F x.log out⌝ ∗
        apply.applyResultIs rq v3 x.log ar out ∗ apply.applyAuthRes E.authMode x.chain rq v3 out ∗
        L hs ∗
        ⌜∀ o b, out = .dispatched o b → v3 = true →
          apply.kvOutL E.authMode hs (auth.authInfoM (apply.principalOf rq)) ci rq x.log o⌝ ∗
        (⌜out.waived = false⌝ ∨ G ot id) }}

end defs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-- **`uberKVL` gives `uberKVC`** with the uber-applier's `kvSpecL`. -/
theorem apply.uberKVC_of (hUA : apply.uberApplier.Apply.kvSpecL (GF := GF) (hG := hG))
    (ua : GoInterface) (E : apply.AEnv GF) (ci : apply.Chain) (L : List auth.AuthState → IProp GF) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
      apply.uberKVL ua E ci L ⊢ apply.uberKVC ua E ci L := by
  iintro ⟨#Hpkg, #H⟩
  iunfold apply.uberKVL at H
  icases H with ⟨%p, %opts, %Hua, #Hu, %base, #Hb, #Hbk⟩
  iunfold apply.uberKVC
  iexists p
  isplitr
  · ipureintro; exact Hua
  iintro !> %x %r %rq %skip %v3 %F %Pre %Q %Post %rs %hs
  wp_start_folded as ⟨#Hwr, Hown, Hkv, Hcp, Hwt, Hcs, %Hp1, %Hp2, HF, HFS, HSp, HRO, HL, %Hx⟩
  wp_apply (hUA E p opts x r rq skip v3 F Pre Q Post rs ci L hs)
      $$ [Hown Hkv Hcp Hwt Hcs HF HFS HSp HRO HL] as %ar HQ
  · iframe # Hown Hkv Hcp Hwt Hcs HF HFS HSp HRO HL
    isplitr
    · ipureintro; exact Hp1
    isplitr
    · ipureintro; exact Hp2
    ipureintro; exact Hx
  iapply HΦ; iexact HQ

/-- **`Apply.kvSpecL` from `Apply.spec`**: the method contract is `uberKVC`'s. -/
theorem apply.Apply.wp_kvL (hA : apply.Apply.spec (GF := GF) (hG := hG)) :
    apply.Apply.kvSpecL (GF := GF) (hG := hG) := by
  intro lg e m ua w v3 E Pre Q Post x rq id RD K G ot F rs ci L hh
  wp_start_folded as ⟨#Hfor, #Hwok, HRD, HK, %Hlg, #He, Hhook, HPre, Hkv, Hwt, #Hcp, %Hprem, #HF, HFS, HSp, HRO, HL, %Hx⟩
  obtain ⟨Hdec, Hid, Hrq, Hdk⟩ := Hprem
  iunfold apply.uberKVC at Hfor
  icases Hfor with ⟨%p, %Hua, #Htr⟩
  iunfold apply.applyKV at Hkv
  icases Hkv with ⟨%p', %Hua', Hown, Hkv, Hco⟩
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
      iprop(apply.uberOwn E p x.chain ∗ apply.kvOwn E x.log ∗ mvcc.storeWT E.γ ∗
        apply.cPre v3 E.P E.f Pre Q Post ∗ E.FS ∗
        (if v3 then apply.ciSplit E Pre else iprop(True)) ∗ E.RO rs ∗ L hh)
      (fun sk ar => iprop(E.FS ∗ ∃ (x' : apply.ApplyKV) (out : apply.ApplyOut),
        apply.uberOwn E p x'.chain ∗ apply.kvOwn E x'.log ∗ apply.cPost v3 Pre Post ∗
        E.RO (apply.restOut rq v3 out rs) ∗
        ⌜apply.applyStep rq v3 x x' out ∧ (out = .rejected ∨ ∃ o, out = .dispatched o sk) ∧
          apply.applyFloorOk rq v3 F x.log out⌝ ∗
        apply.resTrace ar ∗ apply.applyResultIs rq v3 x.log ar out ∗
        apply.applyAuthRes E.authMode x.chain rq v3 out ∗ L hh ∗
        ⌜∀ o, out = .dispatched o sk → v3 = true →
          apply.kvOutL E.authMode hh (auth.authInfoM (apply.principalOf rq)) ci rq x.log o⌝)))
      $$ [HRD HK Hown Hkv Hwt Hcs HFS HSp HRO HL] as %ar %id' ⟨HRD, %Hid', Hout⟩
  · iframe # HRD HK Hown Hkv Hwt Hcs HFS HSp HRO HL
    isplitr
    · ipureintro; exact Hlg
    isplitr
    · ipureintro; exact ⟨Hdec, Hid⟩
    iexists ⟨go.GoType.PointerType uberApplier.ty, #p⟩
    isplitr
    · ipureintro; rfl
    iintro !> %r %sk
    wp_start_folded as ⟨#Hwr, %Hskt, Hown, Hkv, Hwt, Hcs, HFS, HSp, HRO, HL⟩
    wp_apply Htr $$ %x %r %rq %sk %v3 %F %Pre %Q %Post %rs %hh
        [Hown Hkv Hwt Hcs HFS HSp HRO HL] as %ar HQ
    · iframe # Hown Hkv Hwt Hcs HFS HSp HRO HL
      ipureintro; exact ⟨⟨Hrq, Hdk⟩, Hskt, Hx⟩
    iapply HΦ; iexact HQ
  subst Hid'
  icases Hout with (⟨%sk, ⟨HFS, %x', %out, Hown, Hkv, HPP, HRO, %Hst, Htr, Hres, #Hauth, HL, %HXo⟩, Hwv⟩ |
    ⟨%Hnil, HG, Hown, Hkv, Hwt, Hcs, HFS, HSp, HRO, HL⟩)
  · ihave ⟨#Hok, Hres⟩ := apply.applyResultIs_resultErrOk rq v3 x.log ar out $$ Hres
    iapply HΦ
    iframe HRD HFS
    isplitl [HPP]
    · iapply cPost_if; iexact HPP
    iframe Hok Htr
    isplitr
    · ipureintro; rfl
    iexists x', out
    iframe Hres HRO Hauth
    isplitl [Hown Hkv Hco]
    · iunfold apply.applyKV; iexists p
      rw [apply.applyStep_crev_nonCmp rq v3 x x' out (fun h => by simp [apply.isKVKind, h] at Hx) Hst.1]
      iframe Hown Hkv Hco; ipureintro; rfl
    isplitr
    · ipureintro; exact ⟨Hst.1, Hst.2.2⟩
    iframe HL
    isplitr
    · ipureintro
      intro o b hb hv
      exact HXo o (apply.dispatched_skip Hst.2.1 hb) hv
    icases Hwv with (%Hsk | HG)
    · ileft; ipureintro
      rcases Hst.2.1 with h | ⟨o, h⟩ <;> subst h <;> simp [apply.ApplyOut.waived, Hsk]
    · iright; iexact HG
  · obtain ⟨Har, hns⟩ := Hnil
    subst Har
    iapply HΦ
    iframe HRD HFS
    isplitl [Hcs]
    · iapply cPost_if; iapply apply.cPost_of_pre; iapply apply.cPre_pre; iexact Hcs
    isplitr
    · iunfold apply.resultErrOk; ileft; ipureintro; rfl
    isplitr
    · iapply apply.resTrace_null
    isplitr
    · ipureintro; rfl
    iexists x, .skipped
    simp only [apply.applyResultIs, apply.restOut]
    iframe HRO
    isplitl [Hown Hkv Hco]
    · iunfold apply.applyKV; iexists p; iframe Hown Hkv Hco; ipureintro; rfl
    isplitr
    · ipureintro; simp [apply.applyStep, apply.applyFloorOk, hns]
    isplitr
    · itrivial
    isplitr
    · simp only [apply.applyAuthRes]; itrivial
    iframe HL
    isplitr
    · ipureintro; intro o b hb; cases hb
    iright; iexact HG

end proof

end EtcdGrove
end Perennial
