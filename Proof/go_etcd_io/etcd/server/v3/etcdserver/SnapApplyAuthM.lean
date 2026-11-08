/-
**The install's auth step, by the server's auth mode** (`notes/snapshot-auth-on-plan.md`, P6.2,
2026-11-03): what makes `applySnapshot_walk` one walk over `E.authMode` (F9) rather than a twin.

* `kvAuthM`: the auth part of the apply thread's applier row (`srvApplyKVM`), by the mode, and
  `srvApplyKVM_open` (the row with that part named);
* `snapKeepS`: the new backend's buckets the install keeps after the auth store's `Recover` (all
  of them off; on, all but the auth ones, which the auth realization takes), and its split at the
  cluster's buckets (`rbOwnIn_keep_split`);
* `snapAuthImgR`: the image's auth facts at the buckets `Recover` reads (from `snapAuthImgM`);
* `wp_authRecoverM`: `ast.Recover(NewAuthBackend(lg, newbe))` in either mode: off,
  `authRecoverOk`; on, `authRecoverOn.spec` (the glue), the apply thread's open share of the new
  backend a quarter after it (`srvOpenQ`), the old backend's half back.

Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SnapAuthRecover
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AppliedOn

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section pure
variable [GooseExts]

/-- **The new backend's buckets the install keeps after the auth store's `Recover`**: every one
off; on, all but the auth store's, which its realization takes for good. -/
def snapKeepS (M : auth.AuthMode) (n : GoString) : Prop :=
  match M with
  | .on _ => ¬ auth.authBkts n
  | _ => True

theorem clusterBkts_not_auth (n : GoString) (hc : membership.clusterBkts n) : ¬ auth.authBkts n := by
  intro ha
  unfold membership.clusterBkts membership.memberBkts at hc
  unfold auth.authBkts at ha
  rcases hc with (h | h) | h <;> rcases ha with h' | h' | h' <;>
    (rw [h] at h'; exact absurd h' (by decide))

theorem snapKeepS_cluster (M : auth.AuthMode) (n : GoString) (hc : membership.clusterBkts n) :
    snapKeepS M n := by
  cases M <;> simp only [snapKeepS] <;> first | trivial | exact clusterBkts_not_auth n hc

/-- **The image's auth facts at the buckets `Recover` reads** (`snapAuthImgM`'s, at the image's
buckets with the lessor's and the alarm store's emptied): off, the boot's auth buckets; on, the
state after the image's log `A'`, below raft's bound (that it extends the applied `A` is
`specSnapM`'s `hAA'`: review r2 S2). -/
def snapAuthImgR (M : auth.AuthMode) (γr : ReadNames) (r : GMap GoString backend.BktData)
    (A A' : List EntryModel) : Prop :=
  match M with
  | .off => (r.lookup go!"auth").getD ∅ = authBoot ∧ (r.lookup go!"authUsers").getD ∅ = ∅ ∧
      (r.lookup go!"authRoles").getD ∅ = ∅
  | .on _ => authBucketsAt (srvAuthAtLog γr.kv srvAuthSt0 A') r ∧ A'.length < 2 ^ 61
  | .any => True

theorem snapAuthImgR_of (M : auth.AuthMode) (γr : ReadNames) (P : backend.BParams)
    (D : backend.Data) (A A' : List EntryModel) (h : snapAuthImgM M γr P D A A') :
    snapAuthImgR M γr (((backend.rbData P D).insert go!"lease" ∅).insert go!"alarm" ∅) A A' := by
  cases M with
  | off =>
    simp only [snapAuthImgM, snapAuthImgR] at h ⊢
    refine ⟨?_, ?_, ?_⟩ <;>
      rw [GMap.lookup_insert_ne _ _ (by decide), GMap.lookup_insert_ne _ _ (by decide)]
    · exact h.1
    · exact h.2.1
    · exact h.2.2
  | on γa =>
    simp only [snapAuthImgM, snapAuthImgR] at h ⊢
    refine ⟨?_, h.2.2⟩
    have e : authDataOf (((backend.rbData P D).insert go!"lease" ∅).insert go!"alarm" ∅) =
        authDataOf (backend.rbData P D) := by
      unfold authDataOf
      rw [GMap.lookup_insert_ne _ _ (by decide), GMap.lookup_insert_ne _ _ (by decide),
        GMap.lookup_insert_ne _ _ (by decide), GMap.lookup_insert_ne _ _ (by decide),
        GMap.lookup_insert_ne _ _ (by decide), GMap.lookup_insert_ne _ _ (by decide)]
    unfold authBucketsAt at h ⊢
    rw [e]; exact h.2.1
  | any => trivial

/-- **The rest model's buckets after the image's log at the ones the rest resource holds**
(`snapRestImgM`'s): the image's, at the cluster's buckets and the rest part's (`restSet`). -/
theorem snapRestImgM_bk (M : auth.AuthMode) (γr : ReadNames) (P : backend.BParams)
    (D : backend.Data) (A' : List EntryModel) (hany : M ≠ .any)
    (h : snapRestImgM M.isOn γr P D A') :
    ∀ n, membership.clusterBkts n ∨ restSet M n →
      (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A')).bk.lookup n =
      (<[go!"alarm" := ∅]> (<[go!"lease" := ∅]> (backend.rbData P D))).lookup n := by
  intro n hn
  cases M with
  | off => simp only [snapRestImgM, auth.AuthMode.isOn_off] at h; rw [h]
  | any => exact absurd rfl hany
  | on γa =>
    simp only [snapRestImgM, auth.AuthMode.isOn] at h
    refine h n ?_
    rcases hn with hc | hr
    · exact clusterBkts_not_auth n hc
    · simp only [restSet] at hr; exact hr.2

end pure

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **The auth part of the apply thread's applier row, by the mode** (`srvApplyKVM`'s): off, the
auth resource (`srvAuthApplyRes`); on, the base applier's auth layer (`srvUberBase`) and the auth
resource at the state `st` (`srvAuthApplyResB`). -/
def kvAuthM (on : Bool) (s : Loc) (E : apply.AEnv GF) (ua : GoInterface) (st : auth.AuthState) :
    IProp GF :=
  match on with
  | false => srvAuthApplyRes s E
  | true => iprop(srvUberBase s ua E ∗ srvAuthApplyResB s E st)

/-- **The applier row with its auth part named** (both directions). -/
theorem srvApplyKVM_open (on : Bool) (s : Loc) (E : apply.AEnv GF) (γw : GName)
    (x : apply.ApplyKV) (st : auth.AuthState) :
    srvApplyKVM (GF := GF) on s E γw x st ⊣⊢
      iprop(∃ ua : GoInterface, srvUberApplyAddr s ↦ ua ∗ apply.applierFor ua E ∗
        apply.applyKV E ua x ∗ srvBeOwn s E ∗ revAuth E x.log ∗ kvAuthM on s E ua st ∗
        (∃ (w : GoInterface) (RD : IProp GF), srvWAddr s ↦□ w ∗
          waitOk w RD (fun ot id => waitRegdOpt γw id ot) (fun ot id => waitGoneOpt γw id ot) ∗ RD) ∗
        (∃ rd : GoFunc, lease.rdOwn (mvcc.api.mvccLeases E.γ) rd ∗ mvcc.api.mvccDeleter rd E.γ)) := by
  cases on with
  | false => exact .rfl
  | true =>
    simp only [srvApplyKVM, srvApplyKVOn, kvAuthM]
    constructor
    · iintro ⟨%ua, Ha, #Hb, Hf, Hk, Hbe, Hr, Hres, Hw, Hrd⟩
      iexists ua
      iframe Ha Hf Hk Hbe Hr
      isplitl [Hres]
      · iframe Hres; iexact Hb
      isplitl [Hw]
      · iexact Hw
      iexact Hrd
    · iintro ⟨%ua, Ha, Hf, Hk, Hbe, Hr, ⟨#Hb, Hres⟩, Hw, Hrd⟩
      iexists ua
      iframe Ha Hf Hk Hbe Hr Hres
      isplitr
      · iexact Hb
      isplitl [Hw]
      · iexact Hw
      iexact Hrd

/-- **The install's auth row after `Recover`, by the mode**: off, the old auth resource (it does
not name the backend); on, the base applier's auth layer and the auth resource on the new backend
`dn` at the image's state. -/
def snapAuthRowM (M : auth.AuthMode) (s : Loc) (E : apply.AEnv GF) (ua : GoInterface) (ast : Loc)
    (γr : ReadNames) (A' : List EntryModel) (dn : mvcc.KBReal) (Pk : IProp GF) (f : GoFunc) :
    IProp GF :=
  match M with
  | .on γa => iprop(srvUberBase s ua E ∗
      authApplyResB (.on γa) ast (srvAuthAtLog γr.kv srvAuthSt0 A') dn Pk f E.RD)
  | _ => srvAuthApplyRes s E

end defs

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **The kept buckets are the cluster's and the rest resource's part** (`restSet`). -/
theorem rbOwnIn_keep_split (M : auth.AuthMode) (γB : backend.BNames)
    (r : GMap GoString backend.BktData) :
    backend.rbOwnIn (GF := GF) γB (snapKeepS M) r ⊣⊢
      iprop(backend.rbOwnIn γB membership.clusterBkts r ∗ backend.rbOwnIn γB (restSet M) r) := by
  refine (backend.rbOwnIn_set γB _ (fun n => membership.clusterBkts n ∨ restSet M n) r ?_).trans
    (backend.rbOwnIn_split γB _ _ r (fun n hc hr => restSet_ncl M n hr hc))
  intro n
  cases M <;> simp only [snapKeepS, restSet]
  · exact ⟨fun _ => Classical.em _, fun _ => trivial⟩
  · exact ⟨fun _ => Classical.em _, fun _ => trivial⟩
  · constructor
    · intro ha
      by_cases hc : membership.clusterBkts n
      · exact .inl hc
      · exact .inr ⟨hc, ha⟩
    · rintro (hc | ⟨-, ha⟩)
      · exact clusterBkts_not_auth n hc
      · exact ha

/-- **`ast.Recover(NewAuthBackend(lg, newbe))` at the install, in either mode** (F9): off,
`authRecoverOk`'s triple (the idle auth buckets come back, the install keeps every bucket); on,
`authRecoverOn.spec` (the glue): the apply thread's auth row on the old backend `d` at the applied
log `A`'s state goes to the store, which comes back on the new backend `dn` at the image's state
(`A'`'s), with the new backend's idle auth buckets, its auth reader slots and the realization's
quarter of its open token; the old backend's quarter comes back (its half whole again, for the
close goroutine). -/
theorem wp_authRecoverM
    (s ast abl lg : Loc) (E : apply.AEnv GF) (γr : ReadNames) (ua : GoInterface)
    (A A' : List EntryModel) (d dn : mvcc.KBReal) (W Pk : IProp GF) (f : GoFunc)
    (r : GMap GoString backend.BktData)
    (hkb : E.BkTie = srvBkTie d) (hany : E.authMode ≠ .any) (hr : snapAuthImgR E.authMode γr r A A') (hAA' : A <+: A')
    (hhas : dn.P.has mvcc.authBI ∧ dn.P.has mvcc.authUsersBI ∧ dn.P.has mvcc.authRolesBI)
    (hlg : lg ≠ null) (hf : f ≠ func.nil)
    -- (2026-11-03) the store's `Recover` with auth on only (the mode off's path rests on no glue)
    (hRecOn : E.authOn = true → authRecoverOn.spec (GF := GF) (hG := hG)) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗
        srvAtomicsM E.authOn s E γr ∗ srvAuthStoreAddr s ↦□ auth.authIface ast ∗
        snapAuthResM E.authMode s ast E.RD γr A' ∗ srvRLogLb γr.raft A' ∗
        authBeOn ast d.be ∗ kvAuthM E.authOn s E ua (srvAuthAtLog γr.kv srvAuthSt0 A) ∗
        ablOn abl dn.be lg ∗ backend.isBackend dn.γB dn.P W Pk dn.be ∗
        backend.plHookRO dn.γB f ∗
        backend.bOpen dn.γB (1 : Qp).half ∗ backend.bkRPool dn.γB dn.P dn.be ∗ threadTok ∗
        backend.rbOwnIn dn.γB (fun _ => True) r ∗ authRdSlots dn ∗
        backend.bOpen d.γB (srvOpenQ E.authMode) }}
      (App (Val (ast @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.auth.authStore.ty @!!
        go!"Recover")) (Val #(authBkIface abl)))
    {{ RET #(); authBeOn ast dn.be ∗ backend.bOpen dn.γB (srvOpenQ E.authMode) ∗
        backend.bkRPool dn.γB dn.P dn.be ∗ threadTok ∗
        backend.rbOwnIn dn.γB (snapKeepS E.authMode) r ∗ backend.bOpen d.γB (1 : Qp).half ∗
        snapAuthRowM E.authMode s E ua ast γr A' dn Pk f }} := by
  iintro %Φ ⟨#Hpkg, #Hat, #Hauf, HauR, #HA', Hbe, Hkv, #Habl, #HB, #Hhk, HnO, HnPl, HthT, HnRB, Hsl,
    HoO⟩ HΦ
  icases (backend.rbOwnIn_split_compl (GF := GF) dn.γB auth.authBkts r).1 $$ HnRB
    with ⟨HnRA, HnRB⟩
  cases hM : E.authMode with
  | any => exact absurd hM hany
  | off =>
    have hon : E.authOn = false := by simp [apply.AEnv.authOn, hM]
    rw [hM] at hr
    simp only [snapAuthImgR] at hr
    try rw [hM]
    try rw [hon]
    simp only [snapAuthResM]
    icases HauR with #HauR
    iunfold authRecoverOk at HauR
    iunfold ablOn at Habl
    icases Habl with ⟨#Hab1, #Hab2⟩
    ihave #HauR' := HauR $$ %d.be %abl %lg %dn %W %Pk %((1 : Qp).half) %r
    wp_apply HauR' $$ [Hbe HnO HnPl HthT HnRA] as ⟨Hbe, HnO, HnPl, HthT, HnRA⟩
    · iframe Hbe HnO HnPl HthT HnRA; iframe #
      ipureintro; exact ⟨hlg, ⟨hr.1, hr.2.1⟩, hhas⟩
    iapply HΦ
    simp only [srvOpenQ]
    iframe Hbe HnO HnPl HthT HoO
    simp only [snapAuthRowM, kvAuthM]
    iframe Hkv
    iapply (backend.rbOwnIn_set (GF := GF) dn.γB (snapKeepS .off) (fun _ => True) r
      (fun _ => Iff.rfl)).2
    iapply (backend.rbOwnIn_split_compl (GF := GF) dn.γB auth.authBkts r).2
    iframe HnRA HnRB
  | on γa =>
    have hon : E.authOn = true := by simp [apply.AEnv.authOn, hM, auth.AuthMode.isOn]
    rw [hM] at hr
    simp only [snapAuthImgR] at hr
    obtain ⟨hbk, hlen⟩ := hr
    have hpre := hAA'
    try rw [hM]
    try rw [hon]
    simp only [snapAuthResM]
    icases HauR with #Hsok
    iunfold srvAuthSnapOk at Hsok
    icases Hsok with ⟨%ast0, %R, #Hauf0, #Hinv, #Hsnap, %HRD⟩
    icombine Hauf Hauf0 gives %e0
    simp only [auth.authIface, interface_mkOk_inj] at e0
    have e0' : ast = ast0 := by
      simp only [intoVal_eq_iff, _root_.true_and, _root_.and_true] at e0; first | exact e0 | exact e0.symm
    subst e0'
    simp only [kvAuthM]
    icases Hkv with ⟨#Hub, Hres⟩
    iunfold srvAuthApplyResB at Hres
    icases Hres with ⟨%stl, %d0, %Pk0, %hkb0, #Hauf1, Hrow, -, -⟩
    icombine Hauf Hauf1 gives %e1
    simp only [auth.authIface, interface_mkOk_inj] at e1
    have e1' : ast = stl := by
      simp only [intoVal_eq_iff, _root_.true_and, _root_.and_true] at e1; first | exact e1 | exact e1.symm
    subst e1'
    have hd0 : d = d0 := srvBkTie_inj d d0 (hkb.symm.trans hkb0.1)
    subst hd0
    try rw [hM]
    iunfold srvAtomicsM at Hat
    icases Hat with ⟨-, -, #Hkvi⟩
    simp only [srvKVInvsM]
    icases Hkvi with ⟨#Hkvi, -⟩
    iunfold srvKVInvsOn at Hkvi
    icases Hkvi with ⟨#HkI, -, #HrI, #Htie, -, -⟩
    imod kv_log_plainOn γr.raft γr.kv srvAuthSt0 A' $$ HkI HrI HA' with %Hpl
    -- the new backend's half: the apply thread's quarter and the realization's
    icases (backend.bOpen_add (GF := GF) dn.γB (1 : Qp).half.half (1 : Qp).half.half).1 $$ [HnO]
      with ⟨HnO, HnOa⟩
    · rw [Qp.half_add_half]; iexact HnO
    iapply wp_fupd
    iapply (hRecOn (by simp [apply.AEnv.authOn, hM, auth.AuthMode.isOn]) ast abl lg d dn W Pk Pk0 f E.f r γa R E.RD E γr A A'
      (srvAuthAtLog γr.kv srvAuthSt0 A) hM) $$ %_ [Hbe Hrow HnRA Hsl HnOa]
    · iframe Hbe Hrow HnRA Hsl; iframe #
      isplitr
      · ipureintro; exact HRD
      isplitr
      · ipureintro; exact ⟨hpre, rfl, hlen, Hpl⟩
      isplitr
      · ipureintro; exact hlg
      isplitr
      · ipureintro; exact hhas
      isplitr
      · ipureintro; exact hf
      isplitl [HnOa]
      · unfold authOpenQ; iexact HnOa
      ipureintro; exact hbk
    iintro !> Hpost
    imod Hpost with ⟨Hbe, Hrow, HoOa⟩
    ihave HoO2 : backend.bOpen (GF := GF) d.γB (1 : Qp).half $$ [HoO HoOa]
    · rw [← Qp.half_add_half (1 : Qp).half]
      iapply (backend.bOpen_add (GF := GF) d.γB (1 : Qp).half.half (1 : Qp).half.half).2
      simp only [srvOpenQ, authOpenQ]; iframe HoO HoOa
    imodintro
    iapply HΦ
    simp only [srvOpenQ, snapAuthRowM]
    iframe Hbe HnO HnPl HthT HoO2 Hub Hrow
    iapply (backend.rbOwnIn_set (GF := GF) dn.γB (snapKeepS (.on γa)) (fun n => ¬ auth.authBkts n) r
      (fun _ => Iff.rfl)).2
    iexact HnRB

end lemmas

end EtcdGrove
end Perennial
