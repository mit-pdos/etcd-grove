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

/-- **The applier's contract, with what an entry does to the KV** (`Apply.spec` at the
uber-applier's recorded-state triple, `uberApplier.Apply.spec`, through `applierFor`; until step 6
of the auth-mode merge, 2026-10-30, this was `Apply.spec` itself). `apply.Apply(lg, e, ua, w, v3)`
decodes the entry `e`'s request `rq` (the premise: its data decode, `irrDecode`), computes its id
(`irrId rq = some id`: an id, or a header's) and, if it must (a waiter, `w.IsRegistered(id)`, with
the reader's resource `RD` of the wait, `waitOk`, given back; or
side effects, `noSideEffect`); an outcome waived for want of a waiter (`ApplyOut.waived`: not
applied, or a transaction's ranges not run) comes with what `IsRegistered`'s `false` told the
caller about the id (`G ot id`: to one that knew the id registered, that the registration is
gone; the request path's unit 4d), applies it through the `UberApplier` `ua` (`applierFor ua E`), whose
backend's batch lock has invariant `E.P` and runs the post-lock hook `E.f`.
* **The server's protocol** (as before unit 2): for `v3` (`ApplyBoth`) the entry's writes to the
  backend happen in **one** critical section of the batch lock (`LockInsideApply` ... `Unlock`),
  or not at all: in the first case the applier takes the lock (`E.P`), runs the hook (its triple,
  from the caller: `{E.P ∗ Pre} E.f() {Q}`), writes (the caller's update `Q ={⊤}=∗ E.P ∗ Post`,
  which models the writes) and unlocks; in the second it writes nothing, and the caller keeps
  `Pre`. Without `v3` (`ApplyV2storeOnly`: an entry already in the backend, replayed) it writes
  nothing to the backend. The result is `nil` or has a readable `Err` (`resultErrOk`), the id is
  `rq`'s.
* **The KV** (unit 2): the apply thread's applier state `applyKV E ua x` (the uber-applier's
  current chain, the KV's committed log), with the request's premises at `x.log` (`rqOk`: the txn
  package's for a KV request; `dispatchOk`: not empty; `cmpAdmit`: a compaction's facts), goes to
  `x'` by
  `applyStep rq v3 x x' out`: skipped or rejected by the admin check (`x' = x`), or dispatched
  (`dispatchStep`: a KV request as the chain's `chainStep backendStep`, the txn package's results;
  without `v3`, nothing), the result `applyResultIs`. It spends one write token of the store
  (`mvcc.storeWT E.γ`: a KV write or a revocation opens one store write transaction, whose
  `Unlock` over the real backend may cost a write-back; 2026-10-13, unit 6). The caller certifies
  the logs the request may commit (`certPre`: the store's `txnEndPre` asks it of every commit;
  2026-10-14, unit T1). The applier state holds the apply thread's compaction resources at
  `x.crev` (`cmpOwn`; M2's apply side, A1, 2026-10-31: item 21), which `applyStep` moves. -/
abbrev apply.Apply.specRec : Prop :=
  ∀ (lg e : Loc) (m : EntryModel) (ua w : GoInterface) (v3 : Bool) (E : AEnv GF)
    (Pre Q Post : IProp GF) (x : apply.ApplyKV) (rq : IRRModel) (id : w64) (RD : IProp GF)
    (K G : Option GName → w64 → IProp GF) (ot : Option GName) (F : mvcc.Log) (rs : apply.RestM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
      apply.applierFor ua E ∗ waitOk w RD K G ∗ RD ∗ K ot id ∗ ⌜lg ≠ null⌝ ∗ entryAt e m ∗
      (if v3 then iprop(□ ({{ E.P ∗ Pre }} (App (Val E.f) (Val #())) {{ RET #(); Q }}) ∗
          (Q ={⊤}=∗ E.P ∗ Post))
       else iprop(True)) ∗ Pre ∗
      apply.applyKV E ua x ∗ mvcc.storeWT E.γ ∗ apply.certPreV v3 E x.chain rq x.log ∗
      ⌜apply.irrDecode m.data = some rq ∧ apply.irrId rq = some id ∧ apply.rqOk x.log rq ∧
        apply.dispatchOk E.authOn rq ∧ apply.cmpAdmit E.γ.kb x.log rq⌝ ∗ mvcc.idxCert E.γ.idx F ∗
      E.FS ∗ (if v3 then apply.ciSplit E Pre else iprop(True)) ∗ E.RO rs }}
    (App (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.apply.Apply))
      (Val #lg)) (Val #e)) (Val #ua)) (Val #w)) (Val #v3))
  {{ (ar : Loc) (id' : w64), RET (PairV #ar #id'); RD ∗ E.FS ∗
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

/-- **`Apply.specRec` from `Apply.spec`**: the method contract is `uberApplier.Apply.spec` at
`applierFor`'s pointer, its pre the applier state and the write's resources, its post
`uberApplier.Apply.spec`'s. -/
theorem apply.Apply.spec_rec (hA : apply.Apply.spec (GF := GF) (hG := hG))
    (hUA : apply.uberApplier.Apply.spec (GF := GF) (hG := hG)) :
    apply.Apply.specRec (GF := GF) (hG := hG) := by
  intro lg e m ua w v3 E Pre Q Post x rq id RD K G ot F rs
  wp_start_folded as ⟨#Hfor, #Hwok, HRD, HK, %Hlg, #He, Hhook, HPre, Hkv, Hwt, #Hcp, %Hprem, #HF, HFS, HSp, HRO⟩
  obtain ⟨Hdec, Hid, Hrq, Hdk, Hca⟩ := Hprem
  ihave #Hpk : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply $$ []
  · iPkgInit
  iunfold apply.applierFor at Hfor
  icases Hfor with ⟨%p, %opts, %Hua, #Hu⟩
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
        (if v3 then apply.ciSplit E Pre else iprop(True)) ∗ E.RO rs ∗ apply.cmpOwn E x.crev)
      (fun sk ar => iprop(E.FS ∗ ∃ (x' : apply.ApplyKV) (out : apply.ApplyOut),
        apply.uberOwn E p x'.chain ∗ apply.kvOwn E x'.log ∗ apply.cPost v3 Pre Post ∗
        E.RO (apply.restOut rq v3 out rs) ∗ apply.cmpOwn E x'.crev ∗
        ⌜apply.applyStep rq v3 x x' out ∧ (out = .rejected ∨ ∃ o, out = .dispatched o sk) ∧
          apply.applyFloorOk rq v3 F x.log out⌝ ∗
        apply.resTrace ar ∗ apply.applyResultIs rq v3 x.log ar out ∗
        apply.applyAuthRes E.authMode x.chain rq v3 out)))
      $$ [HRD HK Hown Hkv Hwt Hcs HFS HSp HRO Hco] as %ar %id' ⟨HRD, %Hid', Hout⟩
  · iframe # HRD HK Hown Hkv Hwt Hcs HFS HSp HRO Hco
    isplitr
    · ipureintro; exact Hlg
    isplitr
    · ipureintro; exact ⟨Hdec, Hid⟩
    iexists ⟨go.GoType.PointerType uberApplier.ty, #p⟩
    isplitr
    · ipureintro; rfl
    iintro !> %r %sk
    wp_start_folded as ⟨#Hwr, %Hskt, Hown, Hkv, Hwt, Hcs, HFS, HSp, HRO, Hco⟩
    wp_apply (hUA E p opts x r rq sk v3 F Pre Q Post rs)
        $$ [Hown Hkv Hwt Hcs HFS HSp HRO Hco] as %ar HQ
    · iframe # Hown Hkv Hwt Hcs HFS HSp HRO Hco
      ipureintro; exact ⟨⟨Hrq, Hdk, Hca⟩, Hskt⟩
    iapply HΦ; iexact HQ
  subst Hid'
  icases Hout with (⟨%sk, ⟨HFS, %x', %out, Hown, Hkv, HPP, HRO, Hco, %Hst, Htr, Hres, #Hauth⟩, Hwv⟩ |
    ⟨%Hnil, HG, Hown, Hkv, Hwt, Hcs, HFS, HSp, HRO, Hco⟩)
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
    · iunfold apply.applyKV; iexists p; iframe Hown Hkv Hco; ipureintro; rfl
    isplitr
    · ipureintro; exact ⟨Hst.1, Hst.2.2⟩
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
    iright; iexact HG

end proof

end EtcdGrove
end Perennial
