/-
**An admin entry's application by the apply thread, with auth on** (the auth plan's E3n,
2026-10-27). Lean-first (no Rocq counterpart).

`apply.Apply(lg, e, uberApply, w, v3)` on an admitted admin request (`adminKindOk`), from the
apply thread's resources in the mode `on γa`: its auth row at the server's hook (`authApplyResB`:
the authority with its fuel and tie at a history `hs` whose latest state is the model's `st`, the
write token, the provider's admin share, the write contract at every schema auth backend on `bel`,
the store's admin steps at `adminW`), the rest resource lending the store's half of `be`
(`roLendsAuthBe`, E3n), the uber-applier's latest-state admin triples (`uberAuthStepsL`,
`srv_uberAuthStepsL_on`) and one time receipt (the admin step's cost, E2l). The half of `be` is
borrowed from the rest for the call (blocker 1's row: `adminW_of_beOn`, `beOn_of_adminW`), the
latest-state resource lent by the authority (`ownFuT_lend`), and `apply.Apply.adminSpecL`'s outcome
read as the model's admin step (`adminOut_model`): the row comes back at the history after it,
whose latest state `st'` is a successor of the model's (`adminStateR rq st st'`), the rest at the
same value, the KV log and chain kept (`applyStep_admin_keep`).

E3o: any `v3` (a replayed entry, `v3` false, changes nothing: the authority comes back at the same
history), and with `v3` the result `nil` or its error not `ErrNoSpace`'s
(`applyResultIs_notNoSpaceAdmin`, read off the admin outcome before it is consumed), for
`applyEntryNormal`'s NOSPACE branch.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ApplyNormalOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.StoreLatest
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.ApplyFnAdminL
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.NoSpaceDeadAdminOn

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]
variable [errors_sem : _root_.Perennial.errors.Assumptions]

/-- **An admin entry's application with auth on** (see the file header): the triple. (C1's A2) An
`Authenticate` entry too (`adminKindOk`; it needs no admin permission): with `v3`, the right to
its token at the index `ConsistentIndex()` reads under what it borrows from `Pre`
(`apply.adminExtra`, H5: guarded by the check's verdict, `apply.adminExtraG`; an appending
step's cap permission at the history `hs`), giving back the response (`adminAuthnAr`). -/
abbrev adminEntryOn.spec : Prop :=
  ∀ (lg e : Loc) (m : EntryModel) (ua w : GoInterface) (v3 : Bool) (E : apply.AEnv GF)
    (Pre Q Post : IProp GF) (x : apply.ApplyKV) (rq : apply.IRRModel) (id : w64) (RD : IProp GF)
    (K G : Option GName → w64 → IProp GF) (ot : Option GName) (γa : auth.AuthNames)
    (stl bel : Loc) (T : IProp GF) (st : auth.AuthState) (rs : apply.RestM)
    (hs : List auth.AuthState),
    E.authMode = .on γa → apply.noSideEffect rq = false →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
        Perennial.EtcdGrove.apply.uberAuthStepsL ua E (adminW stl bel (.on γa) E.P E.f T)
          (fun γa' h => iprop(auth.authOwnFu γa' h ∗ auth.tieRes stl (.on γa) h))
          (auth.latestRes stl (.on γa)) ∗
        waitOk w RD K G ∗ RD ∗ K ot id ∗ ⌜lg ≠ null⌝ ∗ entryAt e m ∗
        (if v3 then iprop(□ ({{ E.P ∗ Pre }} (App (Val E.f) (Val #())) {{ RET #(); Q }}) ∗
            (Q ={⊤}=∗ E.P ∗ Post))
         else iprop(True)) ∗ Pre ∗
        apply.applyKV E ua x ∗
        ⌜apply.irrDecode m.data = some rq ∧ apply.irrId rq = some id ∧ apply.adminKindOk rq ∧
          apply.dispatchOk E.authOn rq ∧ receiptBound GF ≤ 2 ^ 48⌝ ∗
        ⌜x.chain = apply.baseChain E.authOn⌝ ∗
        (auth.authOwnFu γa hs ∗ auth.tieRes stl (.on γa) hs ∗ ⌜hs.getLast? = some st⌝) ∗
        T ∗ auth.tpAdmin stl (.on γa) ∗ authWBackendAt bel (.on γa) E.P E.f T ∗
        roLendsAuthBe E.RO stl bel ∗ E.RO rs ∗ ⧗ 1 ∗ (if v3 then apply.adminExtraG E γa rq hs Pre else iprop(True)) }}
      (App (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.apply.Apply))
        (Val #lg)) (Val #e)) (Val #ua)) (Val #w)) (Val #v3))
    {{ (ar : Loc) (id' : w64), RET (PairV #ar #id'); RD ∗
        (if v3 then iprop(Post ∨ Pre) else Pre) ∗
        apply.resultErrOk ar ∗ apply.resTrace ar ∗ ⌜id' = id⌝ ∗
        ∃ (x' : apply.ApplyKV) (out : apply.ApplyOut), apply.applyKV E ua x' ∗
          ⌜apply.applyStep rq v3 x x' out ∧ x'.log = x.log ∧ x'.chain = x.chain⌝ ∗
          apply.applyResultIs rq v3 x.log ar out ∗ (⌜out.waived = false⌝ ∨ G ot id) ∗
          apply.adminRejErr ar out ∗
          (if v3 then iprop(⌜ar = null⌝ ∨ ∃ err : GoInterface,
              structFieldRef go_etcd_io.etcd.server.v3.etcdserver.apply.Result go!"Err" ar ↦□ err ∗
              notNoSpaceErr err)
           else iprop(True)) ∗
          E.RO rs ∗ T ∗ auth.tpAdmin stl (.on γa) ∗
          ∃ (hs' : List auth.AuthState) (st' : auth.AuthState),
            auth.authOwnFu γa hs' ∗ auth.tieRes stl (.on γa) hs' ∗
            ⌜hs'.getLast? = some st' ∧ (if v3 then adminStateR rq st st' else st' = st)⌝ ∗
            (if v3 then adminTieAr ar rq st st' out else iprop(True)) ∗
          (if v3 then adminAuthnAr γa ar rq out else iprop(True)) }}

/-- **An `Authenticate` entry's outcome** (C1's A2): the authority as it was, and the response
(`adminAuthnAr`); it is rejected or dispatched. -/
theorem adminOut_authn (γa : auth.AuthNames) (Own : auth.AuthNames → List auth.AuthState → IProp GF)
    (hs : List auth.AuthState) (rq : apply.IRRModel) (ar : Loc) (out : apply.ApplyOut)
    (hk : apply.dispatchKind rq = .authenticate)
    (hout : out = .rejected ∨ ∃ o b, out = .dispatched o b) :
    apply.adminOut Own γa (.on γa) hs rq true ar out ⊢ Own γa hs ∗ adminAuthnAr γa ar rq out := by
  rcases hout with rfl | ⟨o, b, rfl⟩
  · simp only [apply.adminOut]
    iintro ⟨Ho, -⟩
    iframe Ho
    iunfold adminAuthnAr
    ileft
    ipureintro
    exact Or.inr (fun o b h => by cases h)
  · simp only [apply.adminOut, apply.adminDone, ↓reduceIte]
    iintro ⟨%v, %ad, %resp, ⟨%had, %hresp⟩, #Hv, Hres⟩
    unfold apply.adminReqOf at had
    rw [hk] at had
    cases hm : rq.authenticate with
    | none => simp [hm] at had
    | some am =>
      simp only [hm, Option.map_some, Option.some.injEq] at had
      subst had
      simp only [apply.AdminReq.result]
      icases Hres with ⟨Ho, Hout⟩
      iframe Ho
      iunfold adminAuthnAr
      iright
      iexists am, v, resp
      iframe Hv Hout
      ipureintro
      exact ⟨hm, hresp⟩

/-- `adminStateR` of a kind with no step (an `Authenticate`): the state as it was. -/
theorem adminStateR_authn (rq : apply.IRRModel) (st : auth.AuthState)
    (hk : apply.dispatchKind rq = .authenticate) : adminStateR rq st st := by
  unfold adminStateR
  rw [hk]
  split <;> rfl

/-- **An admin entry's application with auth on** (see the file header). -/
theorem apply_admin_entry_on
    (hAL : Perennial.EtcdGrove.apply.Apply.adminSpecL (GF := GF) (hG := hG)) :
    adminEntryOn.spec (GF := GF) (hG := hG) := by
  intro lg e m ua w v3 E Pre Q Post x rq id RD K G ot γa stl bel T st rs hs hM hns
  iintro %Φ ⟨#Hpkg, #Hsteps, #Hwok, HRD, HK, %Hlg, #He, Hhook, HPre, Hkv, %Hprem, %Hch,
    ⟨Hfu, Htie, %Hl⟩, HT, Htp, #Hwa, #Hro, HRO, Hrc, Hx⟩ HΦ
  obtain ⟨Hdec, Hid, Hadm, Hdk, Hrb⟩ := Hprem
  ihave #Pauth : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth $$ []
  · iPkgInit
  ihave Hai : (go_etcd_io.etcd.server.v3.etcdserver.apply.applyInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hai with ⟨-, -, #Hev⟩
  -- the store's half of `be` borrowed from the rest, as the admin steps' write resource
  iunfold roLendsAuthBe at Hro
  ihave ⟨Hbe, Hback⟩ := Hro $$ %rs HRO
  ihave HW : iprop(adminW stl bel (.on γa) E.P E.f T) $$ [Hbe HT Htp]
  · iunfold adminW
    iframe Htp
    iapply adminW_of_beOn stl bel (.on γa) E.P E.f T
    iframe Hbe Hwa HT
  iapply (hAL lg e m ua w v3 E Pre Q Post x rq id RD K G ot (adminW stl bel (.on γa) E.P E.f T) γa
      hs (fun γa' h => iprop(auth.authOwnFu γa' h ∗ auth.tieRes stl (.on γa) h))
      (auth.latestRes stl (.on γa)) (fun h => auth.ownFuT_lend stl γa h))
    $$ [HRD HK Hhook HPre Hkv Hfu Htie Hrc HW Hx]
  · iframe Hpkg Hsteps Hwok HRD HK He HPre Hkv Hrc HW Hhook Hx
    isplitr
    · ipureintro; exact Hlg
    isplitr
    · ipureintro; exact ⟨Hdec, Hid, Hadm, Hdk, hM, Hrb⟩
    isplitr
    · ipureintro; exact Hch
    iframe Hfu Htie
  iintro !> %ar %id' ⟨HRD, HPP, #Hok, Htr, %Hid', %x', %out, Hkv, %Hst, %Hlat, Hres, Hwv, HW, Hout,
    #HRE⟩
  have hout : out = .rejected ∨ ∃ o b, out = .dispatched o b := by
    cases out with
    | skipped =>
      obtain ⟨h, -⟩ := Hst
      rw [hns] at h; cases h
    | rejected => exact Or.inl rfl
    | dispatched o b => exact Or.inr ⟨o, b, rfl⟩
  have hOut : apply.adminOut (GF := GF)
      (fun γa' h => iprop(auth.authOwnFu (GF := GF) γa' h ∗ auth.tieRes stl (.on γa) h))
      γa E.authMode hs rq v3 ar out =
      apply.adminOut (GF := GF)
        (fun γa' h => iprop(auth.authOwnFu (GF := GF) γa' h ∗ auth.tieRes stl (.on γa) h))
        γa (.on γa) hs rq v3 ar out := by rw [hM]
  irevert Hout
  rw [hOut]
  iintro Hout
  -- the half of `be` back to the rest
  iunfold adminW at HW
  icases HW with ⟨⟨%be, HWbe⟩, Htp⟩
  ihave ⟨Hbe, HT⟩ := beOn_of_adminW stl bel (.on γa) E.P E.f T be $$ HWbe
  ihave HRO := Hback $$ Hbe
  have hk := applyStep_admin_keepV rq v3 x x' out Hadm Hst
  cases v3 with
  | false =>
    -- replayed: the authority back at the same history
    ihave Hown : iprop(auth.authOwnFu γa hs ∗ auth.tieRes stl (.on γa) hs) $$ [Hout]
    · rcases hout with rfl | ⟨o, b, rfl⟩
      · simp only [apply.adminOut]
        icases Hout with ⟨Ho, -⟩
        iexact Ho
      · simp only [apply.adminOut, apply.adminDone, Bool.false_eq_true, ↓reduceIte]
        iexact Hout
    icases Hown with ⟨Hfu, Htie⟩
    simp only [Bool.false_eq_true, ↓reduceIte] at *
    iapply HΦ
    iframe HRD HPP Hok Htr Hkv Hres Hwv HRE HRO HT Htp
    isplitr
    · ipureintro; exact Hid'
    isplitr
    · ipureintro; exact ⟨Hst, hk⟩
    iexists hs, st
    iframe Hfu Htie
    isplitr
    · ipureintro; exact ⟨Hl, rfl⟩
    isplitl <;> itrivial
  | true =>
    -- the result's error is not `ErrNoSpace`'s, read off the outcome before it is consumed
    ihave ⟨Hres, Hout, #Hnn⟩ := applyResultIs_notNoSpaceAdmin
      (fun γa' h => iprop(auth.authOwnFu γa' h ∗ auth.tieRes stl (.on γa) h)) γa (.on γa) hs rq
      x.log ar out $$ [] Hres Hout HRE
    · iframe Pauth Hev
    have hrj := Hlat.1
    have hps := Hlat.2
    rw [hM] at hrj hps
    by_cases hka : apply.dispatchKind rq = .authenticate
    · -- (C1's A2) an `Authenticate`: the authority as it was, its response
      ihave ⟨Hown, HAu⟩ := adminOut_authn γa
        (fun γa' h => iprop(auth.authOwnFu γa' h ∗ auth.tieRes stl (.on γa) h)) hs rq ar out hka
        hout $$ Hout
      have hna : apply.needAdminPermission rq = false := by
        have h := Hadm; unfold apply.adminKindOk at h; rw [hka] at h; exact h
      icases Hown with ⟨Hfu, Htie⟩
      simp only [↓reduceIte] at *
      iapply HΦ
      iframe HRD HPP Hok Htr Hkv Hres Hwv HRE HRO HT Htp Hnn
      isplitr
      · ipureintro; exact Hid'
      isplitr
      · ipureintro; exact ⟨Hst, hk⟩
      iexists hs, st
      iframe Hfu Htie HAu
      isplitr
      · ipureintro; exact ⟨Hl, adminStateR_authn rq st hka⟩
      iapply adminTieAr_nonAdmin ar rq st st out hna
    -- the outcome as the model's admin step
    have hn := adminKindOk_needAdmin rq Hadm hka
    ihave ⟨%hs', %st', %Hm, Hown, #HtA⟩ := adminOut_model γa
      (fun γa' h => iprop(auth.authOwnFu γa' h ∗ auth.tieRes stl (.on γa) h)) hs st rq ar out Hl
      hn Hadm hrj (fun o b h => hps o b h) hout $$ Hout
    icases Hown with ⟨Hfu, Htie⟩
    simp only [↓reduceIte] at *
    iapply HΦ
    iframe HRD HPP Hok Htr Hkv Hres Hwv HRE HRO HT Htp Hnn
    isplitr
    · ipureintro; exact Hid'
    isplitr
    · ipureintro; exact ⟨Hst, hk⟩
    iexists hs', st'
    iframe Hfu Htie HtA
    isplitr
    · ipureintro; exact Hm
    iunfold adminAuthnAr
    ileft
    ipureintro; exact Or.inl hka

end proof

end EtcdGrove
end Perennial

#print axioms Perennial.EtcdGrove.apply_admin_entry_on
