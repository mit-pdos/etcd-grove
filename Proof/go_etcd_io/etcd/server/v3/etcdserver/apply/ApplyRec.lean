/-
`apply.Apply` at the uber-applier's recorded-state triple: `Apply.spec` (parametric in the
`UberApplier`'s `Apply` contract) instantiated with `uberApplier.Apply.spec`, through `applierFor`.
Lean-first (no Rocq counterpart). Step 6 of the auth-mode merge (2026-10-30;
`notes/decisions.md`, "Step 6: one `apply.Apply.spec`").
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.Apply
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.uberApplier__Apply
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.UberLemmas
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Packaging
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Apply

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
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-- **The backend's tokens and the critical section's contract, at whichever backend the tie
names** (strict M1, 2026-11-06): for a backend `B` of the tie, a write-back and a reader token of
`B` (`bkWT`, `bkRT`) and, with `v3`, the hook's run at `B`'s batch lock (`hookRun (E.Pk B) E.f`)
and the caller's update; the tie given back. What `specRec`'s caller adds to the applier state
for `uberApplier.Apply`'s `kvOwnPre` (the server: at its tie's backend `d`). -/
def apply.bkToks (v3 : Bool) (E : AEnv GF) (Pre Q Post : IProp GF) : IProp GF :=
  iprop(∀ B : mvcc.KBReal, E.BkTie B -∗ E.BkTie B ∗ apply.bkWT B ∗ apply.bkRT B ∗
    (if v3 then iprop(mvcc.api.hookRun (E.Pk B) E.f Pre Q ∗ (Q ={⊤}=∗ E.Pk B ∗ Post))
     else iprop(True)))

/-- **The applier's contract, with what an entry does to the KV** (`Apply.spec` at the
uber-applier's recorded-state triple, `uberApplier.Apply.spec`, through `applierFor`; until step 6
of the auth-mode merge, 2026-10-30, this was `Apply.spec` itself). `apply.Apply(lg, e, ua, w, v3)`
decodes the entry `e`'s request `rq` (the premise: its data decode, `irrDecode`), computes its id
(`irrId rq = some id`: an id, or a header's) and, if it must (a waiter, `w.IsRegistered(id)`, with
the reader's resource `RD` of the wait, `waitOk`, given back; or
side effects, `noSideEffect`); an outcome waived for want of a waiter (`ApplyOut.waived`: not
applied, or a transaction's ranges not run) comes with what `IsRegistered`'s `false` told the
caller about the id (`G ot id`: to one that knew the id registered, that the registration is
gone; the request path's unit 4d), applies it through the `UberApplier` `ua` (`applierFor ua E`).
* **The server's protocol** (as before unit 2): for `v3` (`ApplyBoth`) the entry's writes to the
  backend happen in **one** critical section of the batch lock of the tie's backend `B`
  (`LockInsideApply` ... `Unlock`), or not at all: in the first case the applier takes the lock
  (`E.Pk B`), runs the hook (`hookRun (E.Pk B) E.f Pre Q`, from the caller), writes (the caller's
  update `Q ={⊤}=∗ E.Pk B ∗ Post`) and unlocks; in the second it writes nothing, and the caller keeps
  `Pre`. Without `v3` (`ApplyV2storeOnly`) it writes nothing to the backend. The result is `nil` or
  has a readable `Err` (`resultErrOk`), the id is `rq`'s.
* **The KV** (unit 2): the apply thread's applier state `applyKV E ua x` goes to `x'` by
  `applyStep rq v3 x x' out`, the result `applyResultIs`. (Strict M1, 2026-11-06: the backend's
  tokens at the tie's backend, `bkToks`, in place of mvcc's `storeWT`; the reader token given back,
  `bkRTOf E`; the floor `kvLogLb E.γs F` in place of mvcc's `idxCert`; the thread's token taken and
  given back.) The caller certifies the logs the request may commit (`certPreV`). The applier
  state holds the apply thread's compaction resources at `x.crev` (`cmpOwn`), which `applyStep`
  moves. The rest state's premise `restReqOk`, `dispatch`'s. -/
abbrev apply.Apply.specRec : Prop :=
  ∀ (lg e : Loc) (m : EntryModel) (ua w : GoInterface) (v3 : Bool) (E : AEnv GF)
    (Pre Q Post : IProp GF) (x : apply.ApplyKV) (rq : IRRModel) (id : w64) (RD : IProp GF)
    (K G : Option GName → w64 → IProp GF) (ot : Option GName) (F : mvcc.Log) (rs : apply.RestM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
      apply.applierFor ua E ∗ waitOk w RD K G ∗ RD ∗ K ot id ∗ ⌜lg ≠ null⌝ ∗ entryAt e m ∗
      apply.bkToks v3 E Pre Q Post ∗ Pre ∗
      apply.applyKV E ua x ∗ apply.certPreV v3 E x.chain rq x.log ∗
      ⌜apply.irrDecode m.data = some rq ∧ apply.irrId rq = some id ∧ apply.rqOk x.log rq ∧
        apply.dispatchOk E.authOn rq ∧ apply.cmpAdmit x.log rq ∧ apply.restReqOk rq rs⌝ ∗
      apply.cmpPermRq E rq ∗ threadTok ∗
      srvApi.kvLogLb E.γs F ∗ E.FS ∗ (if v3 then apply.ciSplit E Pre else iprop(True)) ∗ E.RO rs }}
    (App (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.apply.Apply))
      (Val #lg)) (Val #e)) (Val #ua)) (Val #w)) (Val #v3))
  {{ (ar : Loc) (id' : w64), RET (PairV #ar #id'); RD ∗ E.FS ∗ threadTok ∗ apply.bkRTOf E ∗
      (if v3 then iprop(Post ∨ Pre) else Pre) ∗ apply.resultErrOk ar ∗ apply.resTrace ar ∗
      ⌜id' = id⌝ ∗
      ∃ (x' : apply.ApplyKV) (out : apply.ApplyOut), apply.applyKV E ua x' ∗
        E.RO (apply.restOut rq v3 out rs) ∗
        ⌜apply.applyStep rq v3 x x' out ∧ apply.applyFloorOk rq v3 F x.log out⌝ ∗
        apply.applyResultIs rq v3 x.log ar out ∗ apply.applyAuthRes E.authMode x.chain rq v3 out ∗
        (⌜out.waived = false⌝ ∨ G ot id) }}

end defs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-- **The applier state with the tie's backend's tokens is `uberApplier.Apply`'s** (`kvOwnPre`). -/
theorem apply.kvOwnPre_of_toks (v3 : Bool) (E : AEnv GF) (log : mvcc.Log) (Pre Q Post : IProp GF) :
    apply.kvOwn E log ∗ apply.bkToks v3 E Pre Q Post ∗ Pre ⊢ apply.kvOwnPre v3 E log Pre Q Post := by
  iintro ⟨Hk, Ht, HPre⟩
  iunfold apply.kvOwn at Hk
  icases Hk with ⟨Hw, Hbk, Hll, Hrd⟩
  iunfold apply.kvBk at Hbk
  icases Hbk with ⟨%B, Hmb, Hhk, Htie⟩
  iunfold apply.bkToks at Ht
  ihave ⟨Htie, Hwt, Hrt, Hc⟩ := Ht $$ %B Htie
  iunfold apply.kvOwnPre
  iframe Hw Hll Hrd
  iexists B
  iframe Hmb Hhk Htie Hwt Hrt
  cases v3
  · simp only [apply.cPre, Bool.false_eq_true, ↓reduceIte]
    iexact HPre
  · simp only [apply.cPre, ↓reduceIte, srvApi.csContractA]
    iframe HPre Hc

/-- **`Apply.specRec` from `Apply.spec`**: the method contract is `uberApplier.Apply.spec` at
`applierFor`'s pointer, its pre the applier state and the write's resources, its post
`uberApplier.Apply.spec`'s. -/
theorem apply.Apply.spec_rec (hA : apply.Apply.spec (GF := GF) (hG := hG))
    (hUA : apply.uberApplier.Apply.spec (GF := GF) (hG := hG)) :
    apply.Apply.specRec (GF := GF) (hG := hG) := by
  intro lg e m ua w v3 E Pre Q Post x rq id RD K G ot F rs
  wp_start_folded as ⟨#Hfor, #Hwok, HRD, HK, %Hlg, #He, Htoks, HPre, Hkv, #Hcp, %Hprem, #Hcpr, Htt,
    #HF, HFS, HSp, HRO⟩
  obtain ⟨Hdec, Hid, Hrq, Hdk, Hca, Hrr⟩ := Hprem
  ihave #Hpk : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply $$ []
  · iPkgInit
  iunfold apply.applierFor at Hfor
  icases Hfor with ⟨%p, %opts, %Hua, #Hu⟩
  iunfold apply.applyKV at Hkv
  icases Hkv with ⟨%p', %Hua', Hown, Hkv, Hco⟩
  subst Hua
  have := apply.mkOk_ptr_inj _ _ _ Hua'
  subst this
  ihave Hkp := apply.kvOwnPre_of_toks v3 E x.log Pre Q Post $$ [Hkv Htoks HPre]
  · iframe Hkv Htoks HPre
  wp_apply (hA lg e m (interface.mkOk (go.GoType.PointerType uberApplier.ty) #p) w v3 rq id RD K G ot
      iprop(apply.uberOwn E p x.chain ∗ apply.kvOwnPre v3 E x.log Pre Q Post ∗ threadTok ∗ E.FS ∗
        (if v3 then apply.ciSplit E Pre else iprop(True)) ∗ E.RO rs ∗ apply.cmpOwn E x.crev)
      (fun sk ar => iprop(threadTok ∗ apply.bkRTOf E ∗ E.FS ∗ ∃ (x' : apply.ApplyKV) (out : apply.ApplyOut),
        apply.uberOwn E p x'.chain ∗ apply.kvOwn E x'.log ∗ apply.cPost v3 Pre Post ∗
        E.RO (apply.restOut rq v3 out rs) ∗ apply.cmpOwn E x'.crev ∗
        ⌜apply.applyStep rq v3 x x' out ∧ (out = .rejected ∨ ∃ o, out = .dispatched o sk) ∧
          apply.applyFloorOk rq v3 F x.log out⌝ ∗
        apply.resTrace ar ∗ apply.applyResultIs rq v3 x.log ar out ∗
        apply.applyAuthRes E.authMode x.chain rq v3 out)))
      $$ [HRD HK Hown Hkp Htt HFS HSp HRO Hco] as %ar %id' ⟨HRD, %Hid', Hout⟩
  · iframe # HRD HK Hown Hkp Htt HFS HSp HRO Hco
    isplitr
    · ipureintro; exact Hlg
    isplitr
    · ipureintro; exact ⟨Hdec, Hid⟩
    iexists ⟨go.GoType.PointerType uberApplier.ty, #p⟩
    isplitr
    · ipureintro; rfl
    iintro !> %r %sk
    wp_start_folded as ⟨#Hwr, %Hskt, Hown, Hkp, Htt, HFS, HSp, HRO, Hco⟩
    wp_apply (hUA E p opts x r rq sk v3 F Pre Q Post rs)
        $$ [Hown Hkp Htt HFS HSp HRO Hco] as %ar HQ
    · iframe # Hown Hkp Htt HFS HSp HRO Hco
      isplitr
      · ipureintro; exact ⟨Hrq, Hdk, Hca⟩
      isplitr
      · ipureintro; exact Hskt
      ipureintro; exact Hrr
    iapply HΦ; iexact HQ
  subst Hid'
  icases Hout with (⟨%sk, ⟨Htt, Hrt, HFS, %x', %out, Hown, Hkv, HPP, HRO, Hco, %Hst, Htr, Hres, #Hauth⟩, Hwv⟩ |
    ⟨%Hnil, HG, Hown, Hkp, Htt, HFS, HSp, HRO, Hco⟩)
  · ihave ⟨#Hok, Hres⟩ := apply.applyResultIs_resultErrOk rq v3 x.log ar out $$ Hres
    iapply HΦ
    iframe HRD HFS Htt Hrt
    isplitl [HPP]
    · iapply cPost_if; iexact HPP
    iframe Hok Htr
    isplitr
    · ipureintro; rfl
    iexists x', out
    iframe Hres HRO Hauth
    isplitl [Hown Hkv Hco]
    · iunfold apply.applyKV; iexists p; iframe Hown Hkv Hco; ipureintro; rfl
    isplitr
    · ipureintro; exact ⟨Hst.1, Hst.2.2⟩
    icases Hwv with (%Hsk | HG)
    · ileft; ipureintro
      rcases Hst.2.1 with h | ⟨o, h⟩ <;> subst h <;> simp [apply.ApplyOut.waived, Hsk]
    · iright; iexact HG
  · obtain ⟨Har, hns⟩ := Hnil
    subst Har
    icases apply.kvOwnPre_kvOwn v3 E x.log Pre Q Post $$ Hkp with ⟨Hkv, Hrt, HPre⟩
    iapply HΦ
    iframe HRD HFS Htt Hrt
    isplitl [HPre]
    · iapply cPost_if; iapply apply.cPost_of_pre; iexact HPre
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
    iright; iexact HG

end proof

end EtcdGrove
end Perennial
