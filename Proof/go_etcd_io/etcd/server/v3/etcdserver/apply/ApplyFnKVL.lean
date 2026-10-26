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
public import Spec.go_etcd_io.etcd.pkg.v3.pbutil.MustUnmarshalMessage
public import Spec.go_uber_org.zap.Stringer
public import Spec.go_uber_org.zap.Logger__Debug
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.noSideEffect
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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
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
      apply.uberKVL ua E ci L ∗ waitOk w RD K G ∗ RD ∗ K ot id ∗ ⌜lg ≠ null⌝ ∗ entryAt e m ∗
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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

set_option hygiene false in
/-- The call `uberApply.Apply(wrapper, v3)` and the postcondition. -/
local macro "call_tailL" : tactic => `(tactic| (
  wp_apply (hUA E p opts x «$r0_ptr» rq sk v3 F Pre Q Post rs ci L hh)
      $$ [Hown Hkv Hwt Hcs HFS HSp HRO HL] as %ar ⟨HFS, %x', %out, Hown, Hkv, HPP, HRO, %Hst, Htr, Hres, #Hauth, HL, %HXo⟩
  · iframe # Hown Hkv Hwt Hcs HFS HSp HRO HL
    ipureintro
    refine ⟨⟨Hrq, Hdk⟩, fun h => ?_, Hx⟩
    rw [← hsk] at h
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at h
    cases ht : rq.txn with
    | none => exact absurd (Hlt.2 ht) h.2
    | some _ => rfl
  ihave ⟨#Hok, Hres⟩ := apply.applyResultIs_resultErrOk rq v3 x.log ar out $$ Hres
  iapply HΦ
  iframe HRD HFS
  isplitl [HPP]
  · iapply cPost_if; iexact HPP
  iframe Hok Htr
  isplitr
  · ipureintro; rfl
  iexists x', out
  iframe Hres HRO Hauth
  isplitl [Hown Hkv]
  · iunfold apply.applyKV; iexists p; iframe Hown Hkv; ipureintro; rfl
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
  · iright; iexact HG))

theorem apply.Apply.wp_kvL
    (hMU : pbutil.MustUnmarshalMessage.spec (GF := GF) (hG := hG))
    (hZS : zap.Stringer.spec (GF := GF) (hG := hG))
    (hDbg : zap.Logger.Debug.spec (GF := GF) (hG := hG))
    (hNSE : apply.noSideEffect.spec (GF := GF) (hG := hG))
    (hUA : apply.uberApplier.Apply.kvSpecL (GF := GF) (hG := hG)) :
    apply.Apply.kvSpecL (GF := GF) (hG := hG) := by
  intro lg e m ua w v3 E Pre Q Post x rq id RD K G ot F rs ci L hh
  wp_start as ⟨#Hfor, #Hwok, HRD, HK, %Hlg, #He, Hhook, HPre, Hkv, Hwt, #Hcp, %Hprem, #HF, HFS, HSp, HRO, HL, %Hx⟩
  obtain ⟨Hdec, Hid, Hrq, Hdk⟩ := Hprem
  ihave #Pzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  ihave #Ppb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.pbutil $$ []
  · iPkgInit
  ihave ⟨%Hen, %d, #Hfd, #Hds⟩ := entryAt_fields _ _ $$ He
  wp_auto
  wp_apply (hMU.2 raftReq_ptr _ d m.data DfracDiscarded rq) $$ [raftReq] as ⟨#Hirr, -⟩
  · iframe raftReq Hds
    ipureintro; exact Hdec
  wp_apply hZS as %f -
  wp_apply wp_slice_literal (l := [f])
  isplitr
  · ipureintro; rfl
  iintro %fsl -
  wp_auto
  wp_apply hDbg
  · ipureintro; exact Hlg
  ihave #Hirr' := Hirr
  iunfold apply.internalRaftRequestIs at Hirr'
  icases Hirr' with ⟨%Hpn, #HID, ⟨%lh, #FH, #Hh⟩, -, -, -, ⟨%lt, #FT, #Ht⟩, -⟩
  ihave #Ht := apply.optReqIs_txnW lt rq $$ Ht
  ihave %Hlt := apply.optReqIs_nil lt rq.txn _ apply.txnRequestIs_nn $$ Ht
  ihave %Hlh := apply.optReqIs_nil lh rq.header _ apply.headerIs_nn $$ Hh
  wp_auto
  wp_join iprop(id_ptr ↦ id) with [id] as id
  · -- `ID == 0`: the header's
    have Hid0 := Hid
    rw [apply.irrId_zero rq Hif] at Hid0
    wp_if_destruct
    · -- no header: `irrId rq = none`
      exfalso
      have hh : rq.header = none := Hlh.1 rfl
      simp [hh] at Hid0
    cases hhd : rq.header with
    | none => exact absurd (Hlh.2 hhd) Hif
    | some hm =>
      simp only [hhd, apply.optReqIs]
      iunfold apply.headerIs at Hh
      icases Hh with ⟨-, #HhID, -, -⟩
      wp_auto
      wp_join_done
      have : id = hm.id := by
        rw [hhd] at Hid0; exact (Option.some.inj Hid0).symm
      subst this
      iexact id
  · -- `ID != 0`: it
    have : id = rq.id := by
      rw [apply.irrId_nz rq Hif] at Hid; exact (Option.some.inj Hid).symm
    subst this
    iexact id
  iunfold waitOk at Hwok
  icases Hwok with ⟨%wi, %Hwi, #HIsReg⟩
  subst Hwi
  wp_apply HIsReg $$ [$HRD $HK] as %need ⟨HRD, Hneed⟩
  wp_join (Q := fun v => iprop(⌜v = #(!need && !decide (lt = null))⌝)) at (if: _ then _ else _)
  · cases need
    · wp_auto
      ipureintro; simp
    · wp_auto
      ipureintro; simp
  rename_i v
  iintro %Hv
  subst Hv
  wp_auto
  ihave ⟨Hw, %Hwn⟩ := typedPointsto_not_null_dup _ _ _ $$ «$r0»
  iStructNamed Hw
  ipersist InternalRaftRequest
  ipersist SkipRangeExecution
  ihave #Hwr : iprop(apply.irrWrapperIs «$r0_ptr» rq (!need && !decide (lt = null))) $$ []
  · iunfold apply.irrWrapperIs
    isplitr
    · ipureintro; exact Hwn
    iexists raftReq_ptr
    iframe #
  -- the uber-applier
  iunfold apply.uberKVL at Hfor
  icases Hfor with ⟨%p, %opts, %Hua, #Hu, %base, #Hb, #Hbk⟩
  ihave #Hbase : iprop(∃ base : GoInterface, structFieldRef uberApplier go!"applyV3base" p ↦□ base ∗
      apply.applierKVL E (apply.baseChain E.authOn) ci base L) $$ []
  · iexists base; iframe #
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
  generalize hsk : (!need && !decide (lt = null)) = sk
  cases need
  · -- no waiter: applied only with side effects
    icases Hneed with (%Hf | HG)
    · cases Hf
    wp_auto
    wp_apply (hNSE raftReq_ptr rq) $$ [] as %b %Hb
    · iframe #
    subst Hb
    cases hns : apply.noSideEffect rq
    · wp_auto
      ihave Hwv : iprop(⌜sk = false⌝ ∨ G ot id) $$ [HG]
      · iright; iexact HG
      call_tailL
    · wp_auto
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
      isplitl [Hown Hkv]
      · iunfold apply.applyKV; iexists p; iframe Hown Hkv; ipureintro; rfl
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
  · -- a waiter: applied
    ihave Hwv : iprop(⌜sk = false⌝ ∨ G ot id) $$ []
    · ileft; ipureintro; rw [← hsk]; simp
    iclear Hneed
    wp_auto
    call_tailL

end proof

end EtcdGrove
end Perennial
