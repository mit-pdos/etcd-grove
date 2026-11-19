/-
**The auth realization's reserved reads** (auth-schema-srv A6, 2026-11-18): the admin side's reads
(`auth.authBackendReads`' `GetUser`, `GetRole`, `GetAllUsers`: schema's read transaction at the write token, no
ticket) over the per-backend invariant (`AuthRealInv.lean`): the real backend is schema's `authBE` for the
reserved pool (`real_BER`: the write token deposited while the read holds the slot, the admin side's authority
lent to `RLock`), and the held read observes the history's last state in every bucket (the deposited token
excludes a batch: `real_obsR`). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthRealInv
public import Proof.go_etcd_io.etcd.server.v3.auth.InvAuth
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.authBackend__GetUser
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.authBackend__GetRole
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.authBackend__GetAllUsers

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace authReal

open Iris Iris.BI Iris.ProofMode backend

section rsv
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]
variable [schema_sem : go_etcd_io.etcd.server.v3.storage.schema.Assumptions]

theorem wTok_excl (γc : auth.AuthBkNames) : auth.authWTok (GF := GF) γc ∗ auth.authWTok γc ⊢ False := by
  unfold auth.authWTok
  iintro ⟨H1, H2⟩
  iapply token_exclusive $$ H1 H2

/-- A deposited count of at least one holds the exclusive resource. -/
theorem tokIn_T (T : IProp GF) (hT : T ∗ T ⊢ False) (a : Nat) (h : 1 ≤ a) : tokIn T a ∗ T ⊢ False := by
  match a, h with
  | 0, h => exact absurd h (by omega)
  | 1, _ => simp only [tokIn]; exact hT
  | n + 2, _ => simp only [tokIn]; iintro ⟨H, -⟩; iexact H

/-- An acquiring reader of the reserved pool: the pool holds the token. -/
theorem poolSt_rcpt_T (γm γh : GName) (T : IProp GF) (hT : T ∗ T ⊢ False) (dep : Option Qp → IProp GF)
    (tok sh : IProp GF) (N k : Nat) (d : Option Qp) :
    poolSt γm γh (tokIn T) dep tok sh N ∗ ghostMapElem γm k (DFrac.own 1) d ∗ T ⊢ False := by
  iintro ⟨Hp, Hk, HT⟩
  iunfold poolSt at Hp
  icases Hp with ⟨%m, %nx, %kh, Hm, -, HRs, -, -, -, %Hb⟩
  ihave %Hl := ghost_map_lookup $$ Hm Hk
  have hpos : 0 < m.size := Nat.pos_of_ne_zero (map_size_ne_0_lookup_2 m Hl)
  iapply tokIn_T T hT (kh + m.size) (by omega) $$ [$HRs $HT]

/-- A holding reader of the reserved pool: the pool holds the token. -/
theorem poolSt_held_T (γm γh : GName) (T : IProp GF) (hT : T ∗ T ⊢ False) (dep : Option Qp → IProp GF)
    (tok sh : IProp GF) (N : Nat) :
    poolSt γm γh (tokIn T) dep tok sh N ∗ ownToks γh 1 ∗ T ⊢ False := by
  iintro ⟨Hp, Hr, HT⟩
  iunfold poolSt at Hp
  icases Hp with ⟨%m, %nx, %kh, -, -, HRs, Hh, -, -, %Hb⟩
  icombine Hh Hr gives %Hkh
  iapply tokIn_T T hT (kh + m.size) (by omega) $$ [$HRs $HT]

/-- **A reserved reader's receipt**: its deposit's entry, the share lent the slot's, its own `X` and the
admin side's authority lent to `RLock`. -/
def rcptR (γ : RNames) (s0 : Qp) (X : IProp GF) (hs : List auth.AuthState) (_ : Unit) (qo : Qp) : IProp GF :=
  iprop((∃ k : Nat, ghostMapElem γ.γm' k (DFrac.own 1) (none : Option Qp)) ∗ ⌜qo = s0⌝ ∗ X ∗
    auth.authOwn (.on γ.γa) hs)

/-- The buckets read hold the history's last state. -/
def viewL (d : mvcc.KBReal) (hs : List auth.AuthState) (rv : RView) : Prop :=
  ∃ st, hs.getLast? = some st ∧ viewAt (auth.BkView.uni st) (schema.rvAuth d.P rv)

/-- **A reserved reader's held receipt**: the held slot's, its own `X`, the view of the history's last. -/
def yR (γ : RNames) (d : mvcc.KBReal) (hs : List auth.AuthState) (X : IProp GF) (rv : RView) : IProp GF :=
  iprop(ownToks γ.γh' 1 ∗ X ∗ ⌜viewL d hs rv⌝)

/-- **`Racq` of the reserved pool**: the write token deposited for a slot. -/
theorem real_acqR (γ : RNames) (d : mvcc.KBReal) (s0 q0 : Qp) (X : IProp GF) (hs : List auth.AuthState) :
    realInv (GF := GF) γ d s0 q0 ∗ (auth.authWTok γ.γc ∗ X) ∗ auth.authOwn (.on γ.γa) hs ∗ £ 1 ⊢
      |={⊤}=> ∃ qo : Qp, rdTok d.γB d.P d.be ∗ bOpen d.γB qo ∗ rcptR γ s0 X hs () qo := by
  iintro ⟨#Hinv, ⟨HT, HX⟩, HL, Hlc⟩
  iunfold realInv at Hinv
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ ∖ ↑authRealN) (P := realSt γ d s0 q0) $$ Hlc Hi with Hi
  iunfold realSt at Hi
  icases Hi with ⟨%cs, %sa, %su, %sr, %ja, %ju, %jr, %p, Hc, Hl⟩
  icases Hl with (⟨Hs, Hr, Hp, Hb⟩ | ⟨Hpt, Hp, Hq, HT', Hbt⟩ | ⟨Hcur, Hr, Hpr, HT', Hbt⟩)
  · iunfold pools at Hp
    icases Hp with ⟨Hp1, Hp2⟩
    ihave Htt : iprop(True) $$ []
    · itrivial
    imod pool_acq _ γ.γm' γ.γh' (tokIn (auth.authWTok γ.γc)) (fun _ => iprop(True)) _ _ (auth.authWTok γ.γc) 1
      (fun a => tokIn_dep _ (wTok_excl γ.γc) a) none $$ [$Hp2 $HT $Htt] with ⟨Hp2, Htok, Hsh, %k, Hk⟩
    imod Hclose $$ [Hc Hs Hr Hp1 Hp2 Hb]
    · inext
      iunfold realSt
      iexists cs, sa, su, sr, ja, ju, jr, p
      iframe Hc
      ileft
      iframe Hs Hr Hb
      iunfold pools
      iframe Hp1 Hp2
    imodintro
    iexists s0
    iframe Htok Hsh
    iunfold rcptR
    iframe HX HL
    isplitl [Hk]
    · iexists k; iexact Hk
    ipureintro; rfl
  · iexfalso; iapply wTok_excl γ.γc $$ [$HT $HT']
  · iexfalso; iapply wTok_excl γ.γc $$ [$HT $HT']

/-- **`Robs` of the reserved pool**: the deposited token excludes a batch, so the buckets are idle at the
history's last (the lent authority agrees with the lock's share); the authority back, the held receipt. -/
theorem real_obsR (γ : RNames) (d : mvcc.KBReal) (s0 q0 : Qp) (X : IProp GF) (hs : List auth.AuthState)
    (x : Loc) (rv : RView) (qo : Qp) :
    realInv (GF := GF) γ d s0 q0 ∗ rtHeld d.γB d.P d.be x rv ∗ bOpen d.γB qo ∗ rcptR γ s0 X hs () qo ∗ £ 1 ⊢
      |={⊤}=> rtHeld d.γB d.P d.be x rv ∗ auth.authOwn (.on γ.γa) hs ∗ yR γ d hs X rv ∗
        ⌜schema.authWf (schema.rvAuth d.P rv)⌝ := by
  iintro ⟨#Hinv, Hh, Ho, Hrc, Hlc⟩
  iunfold rcptR at Hrc
  icases Hrc with ⟨⟨%k, Hk⟩, %hq, HX, HL⟩
  subst hq
  iunfold realInv at Hinv
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ ∖ ↑authRealN) (P := realSt γ d qo q0) $$ Hlc Hi with Hi
  iunfold realSt at Hi
  icases Hi with ⟨%cs, %sa, %su, %sr, %ja, %ju, %jr, %p, Hc, Hl⟩
  icases bkCommon_rv γ d cs sa su sr ja ju jr p x rv $$ [$Hc $Hh] with ⟨Hc, Hh, %Hcs⟩
  icases Hl with (⟨Hs, Hr, Hp, Hb⟩ | ⟨Hpt, Hp, Hq, HT', Hbt⟩ | ⟨Hcur, Hr, Hpr, HT', Hbt⟩)
  · iunfold pools at Hp
    icases Hp with ⟨Hp1, Hp2⟩
    icases Hb with (Hid | Hbb)
    · iunfold bkIdle at Hid
      icases Hid with ⟨%hs', %rc, %w, Hlq, Hro, Hbt, Hsw, Hq, %Hid⟩
      simp only [auth.authOwn]
      icases HL with ⟨Hhh, HcurH⟩
      ihave %Heq := auth.authHistHalf_lockQ_agree γ.γa hs hs' $$ Hhh Hlq
      subst Heq
      obtain ⟨hl, hu, hr, -, -, -, -⟩ := id Hid
      iunfold bkCommon at Hc
      icases Hc with ⟨Ha, Hu, Hr', #Hsa, #Hsu, #Hsr, %Hv⟩
      imod pool_obs _ γ.γm' γ.γh' (tokIn (auth.authWTok γ.γc)) (fun _ => iprop(True)) _ _ 1 k none
        $$ [$Hp2 $Hk $Ho] with ⟨Hp2, -, Hy⟩
      imod Hclose $$ [Ha Hu Hr' Hs Hr Hp1 Hp2 Hq Hlq Hro Hbt Hsw]
      · inext
        iunfold realSt
        iexists cs, sa, su, sr, ja, ju, jr, p
        isplitl [Ha Hu Hr']
        · iunfold bkCommon; iframe Ha Hu Hr'; iframe #; ipureintro; exact Hv
        ileft
        iframe Hs Hr
        isplitl [Hp1 Hp2]
        · iunfold pools; iframe Hp1 Hp2
        ileft
        iunfold bkIdle
        iexists hs, rc, w
        iframe Hlq Hro Hbt Hsw Hq
        ipureintro; exact Hid
      have hv : viewAt (auth.BkView.uni sa) (schema.rvAuth d.P rv) := by
        rw [Hcs]
        have h := Hv.1
        rw [hu, hr] at h
        exact h
      imodintro
      iframe Hh Hhh HcurH
      isplitl [Hy HX]
      · iunfold yR; iframe Hy HX; ipureintro; exact ⟨sa, hl, hv⟩
      ipureintro; exact viewAt_wf hv
    · iunfold bkBatch at Hbb
      icases Hbb with ⟨HT', -⟩
      iexfalso
      iapply poolSt_rcpt_T γ.γm' γ.γh' _ (wTok_excl γ.γc) _ _ _ 1 k none $$ [$Hp2 $Hk $HT']
  · iunfold pools at Hp
    icases Hp with ⟨-, Hp2⟩
    iexfalso
    iapply poolSt_rcpt_T γ.γm' γ.γh' _ (wTok_excl γ.γc) _ _ _ 1 k none $$ [$Hp2 $Hk $HT']
  · iunfold poolsRel at Hpr
    icases Hpr with ⟨-, Hpr2⟩
    iexfalso
    iapply poolRel_noRcpt γ.γm' γ.γh' _ k none $$ [$Hpr2 $Hk]

/-- **`Rrel` of the reserved pool**: the slot and the held receipt back for the write token. -/
theorem real_relR (γ : RNames) (d : mvcc.KBReal) (s0 q0 : Qp) (X : IProp GF) (hs : List auth.AuthState)
    (rv : RView) :
    realInv (GF := GF) γ d s0 q0 ∗ rdTok d.γB d.P d.be ∗ yR γ d hs X rv ∗ £ 1 ⊢
      |={⊤}=> auth.authWTok γ.γc ∗ X := by
  iintro ⟨#Hinv, Htok, Hy, Hlc⟩
  iunfold yR at Hy
  icases Hy with ⟨Hy, HX, -⟩
  iunfold realInv at Hinv
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := ⊤ ∖ ↑authRealN) (P := realSt γ d s0 q0) $$ Hlc Hi with Hi
  iunfold realSt at Hi
  icases Hi with ⟨%cs, %sa, %su, %sr, %ja, %ju, %jr, %p, Hc, Hl⟩
  icases Hl with (⟨Hs, Hr, Hp, Hb⟩ | ⟨Hpt, Hp, Hq, HT', Hbt⟩ | ⟨Hcur, Hr, Hpr, HT', Hbt⟩)
  · iunfold pools at Hp
    icases Hp with ⟨Hp1, Hp2⟩
    imod pool_rel _ γ.γm' γ.γh' (tokIn (auth.authWTok γ.γc)) (fun _ => iprop(True)) _ _ (auth.authWTok γ.γc) 1
      (fun a => tokIn_wd _ a) $$ [$Hp2 $Hy $Htok] with ⟨Hp2, HT⟩
    imod Hclose $$ [Hc Hs Hr Hp1 Hp2 Hb]
    · inext
      iunfold realSt
      iexists cs, sa, su, sr, ja, ju, jr, p
      iframe Hc
      ileft
      iframe Hs Hr Hb
      iunfold pools
      iframe Hp1 Hp2
    imodintro
    iframe HT HX
  · iunfold pools at Hp
    icases Hp with ⟨-, Hp2⟩
    iexfalso
    iapply poolSt_held_T γ.γm' γ.γh' _ (wTok_excl γ.γc) _ _ _ 1 $$ [$Hp2 $Hy $HT']
  · iunfold poolsRel at Hpr
    icases Hpr with ⟨-, Hpr2⟩
    imod poolRel_rel _ γ.γm' γ.γh' (tokIn (auth.authWTok γ.γc)) (auth.authWTok γ.γc)
      (fun a => tokIn_wd _ a) $$ [$Hpr2 $Hy] with ⟨-, HT⟩
    iexfalso
    iapply wTok_excl γ.γc $$ [$HT $HT']

/-- **The real backend is schema's `authBE` for the reserved pool**, at the write token with any `X`, lending
the admin side's authority at `hs`. -/
theorem real_BER (hRT : backend.backend.ReadTx.spec (GF := GF) (hG := hG))
    (hRL : backend.readTx.RLock.spec (GF := GF) (hG := hG))
    (hRU : backend.readTx.RUnlock.spec (GF := GF) (hG := hG))
    (hUR : backend.readTx.UnsafeRange.spec (GF := GF) (hG := hG))
    (hFE : backend.readTx.UnsafeForEach.spec (GF := GF) (hG := hG))
    (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG))
    (γ : RNames) (d : mvcc.KBReal) (s0 q0 : Qp) (W Pk : IProp GF) (hP : schema.authHas d.P)
    (X : IProp GF) (hs : List auth.AuthState) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      isBackend d.γB d.P W Pk d.be ∗ realInv γ d s0 q0 ⊢
      schema.authBE (schema.beIface d.be) (iprop(auth.authWTok γ.γc ∗ X))
        (fun _ : Unit => auth.authOwn (.on γ.γa) hs) (schema.heldR d.γB d.P d.be (yR γ d hs X)) := by
  iintro ⟨#Hp1, #Hp2, #Hb, #Hinv⟩
  iapply schema.authBE_real hRT hRL hRU hUR hFE hID hName hSafe d.γB d.P W Pk d.be
    (iprop(auth.authWTok γ.γc ∗ X)) (fun _ : Unit => auth.authOwn (.on γ.γa) hs) (rcptR γ s0 X hs)
    (yR γ d hs X) hP
  iframe Hp1 Hp2 Hb
  isplitr
  · iintro !> %o ⟨HR, HL, Hlc⟩
    iapply real_acqR γ d s0 q0 X hs $$ [$Hinv $HR $HL $Hlc]
  isplitr
  · iintro !> %o %x %rv %qo ⟨Hh, Ho, HC, Hlc⟩
    iapply real_obsR γ d s0 q0 X hs x rv qo $$ [$Hinv $Hh $Ho $HC $Hlc]
  · iintro !> %rv ⟨Ht, Hy, Hlc⟩
    iapply real_relR γ d s0 q0 X hs rv $$ [$Hinv $Ht $Hy $Hlc]

/-! ## The three reads -/

/-- The buckets hold the history's last state. -/
def phiL (hs : List auth.AuthState) (D : schema.AuthData) : Prop :=
  ∃ st, hs.getLast? = some st ∧ viewAt (auth.BkView.uni st) D

/-- A held reserved read observes it. -/
theorem heldR_phiL (γ : RNames) (d : mvcc.KBReal) (hs : List auth.AuthState) (X : IProp GF) :
    ⊢ □ (∀ (x : Loc) (D : schema.AuthData), schema.heldR (GF := GF) d.γB d.P d.be (yR γ d hs X) x D -∗
      schema.heldR d.γB d.P d.be (yR γ d hs X) x D ∗ ⌜phiL hs D⌝) := by
  iintro !> %x %D H
  iunfold schema.heldR at H
  icases H with ⟨%rv, %Hrv, Hh, Hy⟩
  iunfold yR at Hy
  icases Hy with ⟨Hy, HX, %Hv⟩
  isplitl [Hh Hy HX]
  · iunfold schema.heldR; iexists rv; iframe Hh; isplitr
    · ipureintro; exact Hrv
    iunfold yR; iframe Hy HX; ipureintro; exact Hv
  ipureintro
  obtain ⟨st, hl, hv⟩ := Hv
  rw [Hrv.1] at hv
  exact ⟨st, hl, hv⟩

/-- The users' records of the history's last state (by choice). -/
def dUL (hs : List auth.AuthState) (D : schema.AuthData) : GoString → auth.UserRec :=
  Classical.epsilon (fun dU => ∃ st, hs.getLast? = some st ∧ schema.usersAt st D.users dU)

/-- The roles' records of the history's last state (by choice). -/
def dRL (hs : List auth.AuthState) (D : schema.AuthData) : GoString → auth.RoleRec :=
  Classical.epsilon (fun dR => ∃ st, hs.getLast? = some st ∧ schema.rolesAt st D.roles dR)

theorem dUL_at {hs : List auth.AuthState} {D : schema.AuthData} {st : auth.AuthState}
    (hl : hs.getLast? = some st) (h : viewAt (auth.BkView.uni st) D) : schema.usersAt st D.users (dUL hs D) := by
  obtain ⟨-, ⟨dU, hu⟩, -⟩ := h
  obtain ⟨st', hl', hu'⟩ := Classical.epsilon_spec (p := fun dU => ∃ st, hs.getLast? = some st ∧
    schema.usersAt st D.users dU) ⟨dU, st, hl, hu⟩
  rw [hl] at hl'
  cases hl'
  exact hu'

theorem dRL_at {hs : List auth.AuthState} {D : schema.AuthData} {st : auth.AuthState}
    (hl : hs.getLast? = some st) (h : viewAt (auth.BkView.uni st) D) : schema.rolesAt st D.roles (dRL hs D) := by
  obtain ⟨-, -, ⟨dR, hr⟩⟩ := h
  obtain ⟨st', hl', hr'⟩ := Classical.epsilon_spec (p := fun dR => ∃ st, hs.getLast? = some st ∧
    schema.rolesAt st D.roles dR) ⟨dR, st, hl, hr⟩
  rw [hl] at hl'
  cases hl'
  exact hr'

/-- The schema auth backend `abl` as an interface. -/
abbrev ablIface (abl : Loc) : GoInterfaceOk :=
  ⟨go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.schema.authBackend.ty, #abl⟩

/-- **The admin side's three read-transaction reads** (`authBackendReads`' first three clauses) at the write
token with any `X`, from the reserved pool. -/
theorem real_reads3 (hRT : backend.backend.ReadTx.spec (GF := GF) (hG := hG))
    (hRL : backend.readTx.RLock.spec (GF := GF) (hG := hG))
    (hRU : backend.readTx.RUnlock.spec (GF := GF) (hG := hG))
    (hUR : backend.readTx.UnsafeRange.spec (GF := GF) (hG := hG))
    (hFE : backend.readTx.UnsafeForEach.spec (GF := GF) (hG := hG))
    (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG))
    (hGU : schema.authBackend.GetUser.spec (GF := GF) (hG := hG))
    (hGR : schema.authBackend.GetRole.spec (GF := GF) (hG := hG))
    (hGA : schema.authBackend.GetAllUsers.spec (GF := GF) (hG := hG))
    (γ : RNames) (d : mvcc.KBReal) (s0 q0 : Qp) (W Pk : IProp GF) (hP : schema.authHas d.P)
    (X : IProp GF) (abl lg : Loc) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema ∗
      isBackend d.γB d.P W Pk d.be ∗ realInv γ d s0 q0 ∗ ablOn abl d.be lg ⊢
      □ (∀ (hs : List auth.AuthState) (name : GoString),
        {{ (auth.authWTok γ.γc ∗ X) ∗ auth.authOwn (.on γ.γa) hs }}
          (App (Val #(methods (ablIface abl).ty go!"GetUser" (ablIface abl).v)) (Val #name))
        {{ (u : Loc), RET #u; (auth.authWTok γ.γc ∗ X) ∗ auth.authOwn (.on γ.γa) hs ∗
            ∃ sta : auth.AuthState, ⌜auth.histLast (.on γ.γa) hs sta⌝ ∗ auth.userOut u sta name }}) ∗
      □ (∀ (hs : List auth.AuthState) (name : GoString),
        {{ (auth.authWTok γ.γc ∗ X) ∗ auth.authOwn (.on γ.γa) hs }}
          (App (Val #(methods (ablIface abl).ty go!"GetRole" (ablIface abl).v)) (Val #name))
        {{ (r : Loc), RET #r; (auth.authWTok γ.γc ∗ X) ∗ auth.authOwn (.on γ.γa) hs ∗
            ∃ sta : auth.AuthState, ⌜auth.histLast (.on γ.γa) hs sta⌝ ∗ auth.roleOut r sta name }}) ∗
      □ (∀ hs : List auth.AuthState,
        {{ (auth.authWTok γ.γc ∗ X) ∗ auth.authOwn (.on γ.γa) hs }}
          (App (Val #(methods (ablIface abl).ty go!"GetAllUsers" (ablIface abl).v)) (Val #()))
        {{ (s : GoSlice), RET #s; (auth.authWTok γ.γc ∗ X) ∗ auth.authOwn (.on γ.γa) hs ∗
            ∃ sta : auth.AuthState, ⌜auth.histLast (.on γ.γa) hs sta⌝ ∗ auth.usersOut s sta }}) := by
  iintro ⟨#Hp1, #Hp2, #Hb, #Hinv, #Habl⟩
  iunfold ablOn at Habl
  icases Habl with ⟨#Hbf, #Hlf⟩
  isplitr
  · iintro !> %hs %name !> %Φ ⟨HR, HL⟩ HΦ
    ihave #Hbe := real_BER hRT hRL hRU hUR hFE hID hName hSafe γ d s0 q0 W Pk hP X hs $$ [$Hp1 $Hp2 $Hb $Hinv]
    ihave #Hobs := heldR_phiL γ d hs X
    wp_apply (hGU abl (schema.beIface d.be) lg (iprop(auth.authWTok γ.γc ∗ X)) (schema.heldR d.γB d.P d.be (yR γ d hs X))
      (fun _ : Unit => auth.authOwn (.on γ.γa) hs) () (phiL hs) (dUL hs) name
      (fun D _ h => by obtain ⟨st, hl, hv⟩ := h; exact schema.usersAt_dec (dUL_at hl hv)))
      $$ [$Hp2 $Hbf $Hlf $Hbe $HR $HL $Hobs] as %u ⟨HR, HL, %D, %HD, Hu⟩
    obtain ⟨-, st, hl, hv⟩ := HD
    iapply HΦ
    iframe HR HL
    iexists st
    isplitr
    · ipureintro; simp only [auth.histLast]; exact hl
    iapply schema.userOutD_are st D.users u name (dUL hs D) (dUL_at hl hv) $$ Hu
  isplitr
  · iintro !> %hs %name !> %Φ ⟨HR, HL⟩ HΦ
    ihave #Hbe := real_BER hRT hRL hRU hUR hFE hID hName hSafe γ d s0 q0 W Pk hP X hs $$ [$Hp1 $Hp2 $Hb $Hinv]
    ihave #Hobs := heldR_phiL γ d hs X
    wp_apply (hGR abl (schema.beIface d.be) lg (iprop(auth.authWTok γ.γc ∗ X)) (schema.heldR d.γB d.P d.be (yR γ d hs X))
      (fun _ : Unit => auth.authOwn (.on γ.γa) hs) () (phiL hs) (dRL hs) name
      (fun D _ h => by obtain ⟨st, hl, hv⟩ := h; exact schema.rolesAt_dec (dRL_at hl hv)))
      $$ [$Hp2 $Hbf $Hlf $Hbe $HR $HL $Hobs] as %r ⟨HR, HL, %D, %HD, Hr⟩
    obtain ⟨-, st, hl, hv⟩ := HD
    iapply HΦ
    iframe HR HL
    iexists st
    isplitr
    · ipureintro; simp only [auth.histLast]; exact hl
    iapply schema.roleOutD_are st D.roles r name (dRL hs D) (dRL_at hl hv) $$ Hr
  · iintro !> %hs !> %Φ ⟨HR, HL⟩ HΦ
    ihave #Hbe := real_BER hRT hRL hRU hUR hFE hID hName hSafe γ d s0 q0 W Pk hP X hs $$ [$Hp1 $Hp2 $Hb $Hinv]
    ihave #Hobs := heldR_phiL γ d hs X
    wp_apply (hGA abl (schema.beIface d.be) lg (iprop(auth.authWTok γ.γc ∗ X)) (schema.heldR d.γB d.P d.be (yR γ d hs X))
      (fun _ : Unit => auth.authOwn (.on γ.γa) hs) () (phiL hs) (dUL hs)
      (fun D _ h => by obtain ⟨st, hl, hv⟩ := h; exact schema.usersAt_dec (dUL_at hl hv)))
      $$ [$Hp2 $Hbf $Hlf $Hbe $HR $HL $Hobs] as %s ⟨HR, HL, %D, %HD, Hs⟩
    obtain ⟨-, st, hl, hv⟩ := HD
    iapply HΦ
    iframe HR HL
    iexists st
    isplitr
    · ipureintro; simp only [auth.histLast]; exact hl
    iapply usersOutD_at st D.users (dUL hs D) s (dUL_at hl hv) $$ Hs

end rsv

end authReal
end EtcdGrove
end Perennial
