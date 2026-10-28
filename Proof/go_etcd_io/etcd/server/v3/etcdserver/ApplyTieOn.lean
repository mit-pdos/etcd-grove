/-
**The apply thread's auth state and the admin side's history, in the auth mode `on`** (the auth
plan's E3a, 2026-10-26; `notes/decisions.md`, "E3a of the auth plan"). Lean-first (no Rocq
counterpart).

The mode-`on` model of the committed log (`kvAppliedOn`, E2t) reaches an auth state `st`; the apply
thread's auth resource (`authApplyRes`, E2k) holds the admin side's authority at a history `hs`.
The apply thread's step on an entry is the model's (`kv_applied_out_on`) once its outcome is
`outcomeOn`'s, and both checks it makes, the KV one (E2y's `outcomeOn_of_kvOutL`) and the admin
one, are at the latest state of `hs`: so the apply loop keeps the two tied, `hs.getLast? = some st`.
Here, what keeps the tie across one entry:

- **A KV entry** (or one below the consistent index, or without data): its outcomes keep the auth
  state (`outcomeOn_auth_keep`), and it does not touch the history.
- **An admin entry** whose admin check passed at the latest state (`auth.adminOk`) and whose step
  ran: its result (`auth.adminOutX` without an extra error, `AdminReq.result` since E3a's
  `UserAdd`) gives the authority at the history after the outcome (`histAfter`), whose latest state
  is the outcome's (`histAfter_last`), and that state is a successor of the model's admin step
  (`adminStateR_of_step`), so `outcomeOn`'s (`outcomeOn_of_adminStateR`); one whose admin check
  failed keeps both (`adminStateR_refused`).

Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVApplyOn
public import Proof.go_etcd_io.etcd.server.v3.auth.TieRes
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.ApplyAdminL

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section pure
variable [GooseExts]

/-- **The history after an admin outcome**: `next` appends its state, a refusal and nothing to do
keep it (`auth.outResX`'s). -/
def histAfter (hs : List auth.AuthState) : auth.Outcome → List auth.AuthState
  | .next st' => hs ++ [st']
  | _ => hs

/-- The latest state of the history after an outcome is the outcome's state (`outState`). -/
theorem histAfter_last (hs : List auth.AuthState) (st : auth.AuthState) (o : auth.Outcome)
    (h : hs.getLast? = some st) : (histAfter hs o).getLast? = some (outState st o) := by
  cases o <;> simp [histAfter, outState, h]

/-- **A KV entry keeps the auth state**: every outcome `outcomeOn` allows for an entry that is not
an admin one above `c₀` (a KV request, a request of another kind, an entry without data or below
the consistent index) keeps the state's auth part. -/
theorem outcomeOn_auth_keep (c₀ : w64) (ch : apply.Chain) (s o : auth.AuthState × mvcc.Log)
    (m : EntryModel)
    (hna : ∀ rq, m.typ = W32 0 → m.data ≠ [] → apply.irrDecode m.data = some rq →
      ¬ (uint.Z c₀ < uint.Z m.index ∧ apply.needAdminPermission rq = true))
    (ho : outcomeOn c₀ ch s m o) : o.1 = s.1 := by
  unfold outcomeOn at ho
  split at ho
  · rename_i hm
    split at ho
    · rename_i rq hdec
      rw [if_neg (hna rq hm.1 hm.2 hdec)] at ho
      split at ho
      · rw [ho]
      · rw [ho]
    · rw [ho]
  · rw [ho]

/-- **An admin entry's model outcome from its admin step**: an admin entry above `c₀` reaches any
successor of its admin step (`adminStateR`), the log kept. -/
theorem outcomeOn_of_adminStateR (c₀ : w64) (ch : apply.Chain) (s : auth.AuthState × mvcc.Log)
    (m : EntryModel) (rq : apply.IRRModel) (st' : auth.AuthState) (ht : m.typ = W32 0)
    (hd : m.data ≠ []) (hdec : apply.irrDecode m.data = some rq) (hv : uint.Z c₀ < uint.Z m.index)
    (ha : apply.needAdminPermission rq = true) (hr : adminStateR rq s.1 st') :
    outcomeOn c₀ ch s m (st', s.2) := by
  unfold outcomeOn
  rw [if_pos ⟨ht, hd⟩, hdec]
  simp only
  rw [if_pos ⟨hv, ha⟩]
  exact ⟨hr, trivial⟩

/-- **The admin check failed at the latest state**: the admin step keeps the state. -/
theorem adminStateR_refused (rq : apply.IRRModel) (st : auth.AuthState)
    (ha : ¬ auth.adminOk st (some (auth.authInfoM (apply.principalOf rq)))) :
    adminStateR rq st st := by
  unfold adminStateR
  rw [if_neg ha]

/-- **The admin check passed at the latest state and the step ran**: the outcome's state is a
successor of the model's admin step, for `examples/authkv`'s `SetUp`'s requests but `AuthEnable`
(`UserAdd`, `RoleAdd`, `UserGrantRole`, `RoleGrantPermission`: the request model's own step,
`AdminReq.result`'s relation; `AuthEnable`'s relation is at the flag the store read, which
`AdminReq.result` gives at some recorded state only, `auth.enabledVerdict`). -/
theorem adminStateR_of_step (rq : apply.IRRModel) (st : auth.AuthState) (o : auth.Outcome)
    (ha : auth.adminOk st (some (auth.authInfoM (apply.principalOf rq))))
    (hR : (∃ m, apply.dispatchKind rq = .authUserAdd ∧ rq.authUserAdd = some m ∧
            auth.stepOf (auth.userAddF m.name) st o) ∨
          (∃ n, apply.dispatchKind rq = .authRoleAdd ∧ rq.authRoleAdd = some n ∧
            auth.stepOf (auth.roleAddF n) st o) ∨
          (∃ u r, apply.dispatchKind rq = .authUserGrantRole ∧ rq.authUserGrantRole = some (u, r) ∧
            auth.userGrantRoleR u r st o) ∨
          (∃ n w, apply.dispatchKind rq = .authRoleGrantPermission ∧
            rq.authRoleGrantPermission = some (n, w) ∧ auth.roleGrantPermissionR n w st o)) :
    adminStateR rq st (outState st o) := by
  unfold adminStateR
  rw [if_pos ha]
  rcases hR with ⟨m, hk, hm, h⟩ | ⟨n, hk, hn, h⟩ | ⟨u, r, hk, hu, h⟩ | ⟨n, w, hk, hn, h⟩
  · rw [hk]; simp only [hm]; exact Or.inr ⟨o, h, rfl⟩
  · rw [hk]; simp only [hn]; exact ⟨o, h, rfl⟩
  · rw [hk]; simp only [hu]; exact ⟨o, h, rfl⟩
  · rw [hk]; simp only [hn]; exact ⟨o, h, rfl⟩

/-- **`AuthEnable`'s step at the latest state's flag** (E3c: `AdminReq.result`'s `AuthEnable` at
`authEnableR`, the flag the store read the latest state's): with the admin check passed at the
latest state, the outcome's state is the model's admin step's successor. -/
theorem adminStateR_of_authEnable (γa : auth.AuthNames) (rq : apply.IRRModel) (st : auth.AuthState)
    (en : Bool) (o : auth.Outcome)
    (ha : auth.adminOk st (some (auth.authInfoM (apply.principalOf rq))))
    (hk : apply.dispatchKind rq = .authEnable) (h : apply.authEnableR (.on γa) en st o) :
    adminStateR rq st (outState st o) := by
  unfold adminStateR
  rw [if_pos ha, hk]
  exact ⟨o, apply.authEnableR_on γa en st o h, rfl⟩

/-- **An admin check refused at the latest state** (E3c's `adminRejL`, from `uberApplier.Apply`'s
latest-state admin triple): the admin step keeps the state. -/
theorem adminStateR_of_rejL (γa : auth.AuthNames) (hs : List auth.AuthState) (st : auth.AuthState)
    (rq : apply.IRRModel) (hl : hs.getLast? = some st)
    (h : apply.adminRejL (.on γa) hs rq) : adminStateR rq st st :=
  adminStateR_refused rq st (h st hl)

/-- **An admin check passed at the latest state** (E3c's `adminPassL`): the latest state admits
the request's principal, `adminStateR_of_step`'s premise. -/
theorem adminOk_of_passL (γa : auth.AuthNames) (hs : List auth.AuthState) (st : auth.AuthState)
    (rq : apply.IRRModel) (hl : hs.getLast? = some st) (hn : apply.needAdminPermission rq = true)
    (h : apply.adminPassL (.on γa) hs rq) :
    auth.adminOk st (some (auth.authInfoM (apply.principalOf rq))) :=
  h hn st hl

/-- **An admitted admin request's `apply.Apply` keeps the KV log and the chain** (E3n): an admin
kind is neither of the pre-v3 kinds nor a store kind, so its dispatched outcome leaves the log
(`dispatchStep`'s last case), and it is not an alarm request. -/
theorem applyStep_admin_keep (rq : apply.IRRModel) (x x' : apply.ApplyKV) (out : apply.ApplyOut)
    (hk : apply.adminKindOk rq) (h : apply.applyStep rq true x x' out) :
    x'.log = x.log ∧ x'.chain = x.chain := by
  have hkd : apply.dispatchKind rq = .authUserAdd ∨ apply.dispatchKind rq = .authRoleAdd ∨
      apply.dispatchKind rq = .authUserGrantRole ∨
      apply.dispatchKind rq = .authRoleGrantPermission ∨ apply.dispatchKind rq = .authEnable ∨
      apply.dispatchKind rq = .authenticate := by
    unfold apply.adminKindOk at hk
    split at hk <;> simp_all
  have hpv : apply.preV3Kind (apply.dispatchKind rq) = false := by
    rcases hkd with h | h | h | h | h | h <;> rw [h] <;> rfl
  have hsk : apply.storeKind (apply.dispatchKind rq) = false := by
    rcases hkd with h | h | h | h | h | h <;> rw [h] <;> rfl
  have hna : apply.dispatchKind rq ≠ .alarm := by
    rcases hkd with h | h | h | h | h | h <;> rw [h] <;> decide
  cases out with
  | skipped => obtain ⟨-, rfl⟩ := h; exact ⟨rfl, rfl⟩
  | rejected => obtain ⟨-, rfl⟩ := h; exact ⟨rfl, rfl⟩
  | dispatched o b =>
    obtain ⟨-, hd, hl, hc⟩ := h
    unfold apply.dispatchStep at hd
    rw [if_neg (by simp [hpv]), if_neg (by simp [hsk])] at hd
    refine ⟨hl.trans hd, ?_⟩
    rcases hc with hc | ⟨-, hal, -⟩
    · exact hc
    · exact absurd hal hna

end pure

section res
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **An admin step's result without an extra error, in the mode `on γa`** (`AdminReq.result`'s
four requests but `AuthEnable`, E3a): the authority family `Own` at the history after the outcome
of `R` at the latest state. -/
theorem adminOutX_on_noExtra (γa : auth.AuthNames) (Own : List auth.AuthState → IProp GF)
    (hs : List auth.AuthState) (R : auth.StepRel) (err : GoInterface) :
    auth.adminOutX (.on γa) Own hs R auth.noExtra err ⊢
      ∃ (st : auth.AuthState) (o : auth.Outcome), ⌜hs.getLast? = some st ∧ R st o⌝ ∗
        Own (histAfter hs o) := by
  unfold auth.adminOutX
  iintro (⟨%e, %hx, -, -⟩ | ⟨%st, %o, %h, Hr⟩)
  · exact absurd hx id
  · iexists st, o
    isplitr
    · ipureintro; exact h
    cases o <;> simp only [auth.outResX, histAfter] at * <;> icases Hr with ⟨Ho, -⟩ <;> iexact Ho

/-- `adminOutX_on_noExtra`, keeping what the error says of the outcome (E3x): no error, no
refusal (`auth.authErrOf`: an error variable's value, not `nil`). -/
theorem adminOutX_on_noExtraE (γa : auth.AuthNames) (Own : List auth.AuthState → IProp GF)
    (hs : List auth.AuthState) (R : auth.StepRel) (err : GoInterface) :
    auth.adminOutX (.on γa) Own hs R auth.noExtra err ⊢
      ∃ (st : auth.AuthState) (o : auth.Outcome), ⌜hs.getLast? = some st ∧ R st o ∧
        (err = GoInterface.nil → ∀ e, o ≠ .err e)⌝ ∗ Own (histAfter hs o) := by
  unfold auth.adminOutX
  iintro (⟨%e, %hx, -, -⟩ | ⟨%st, %o, %h, Hr⟩)
  · exact absurd hx id
  · cases o with
    | err e =>
      simp only [auth.outResX, histAfter]
      icases Hr with ⟨Ho, #He⟩
      iunfold auth.authErrOf at He
      icases He with ⟨%ei, -, %Hei⟩
      iexists st, .err e
      iframe Ho
      ipureintro
      refine ⟨h.1, h.2, fun hn => ?_⟩
      rw [Hei] at hn; cases hn
    | same =>
      simp only [auth.outResX, histAfter]
      icases Hr with ⟨Ho, -⟩
      iexists st, .same
      iframe Ho
      ipureintro
      exact ⟨h.1, h.2, fun _ e he => by cases he⟩
    | next st' =>
      simp only [auth.outResX, histAfter]
      icases Hr with ⟨Ho, -⟩
      iexists st, .next st'
      iframe Ho
      ipureintro
      exact ⟨h.1, h.2, fun _ e he => by cases he⟩

end res

section res2
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **An admin entry's outcome as the model's admin step** (E3n): `apply.Apply.adminSpecL`'s
admin outcome with `v3` (`adminOut`), the history `hs` whose latest state is `st`: a refusal at the
latest state keeps the authority (and the receipt) and the state (`adminStateR_of_rejL`); a
dispatched request's check passed there (`adminOk_of_passL`), and its result (without an extra
error) is the step to some `o`, with the authority at the history after it, whose latest state
`outState st o` the model's admin step reaches (`adminStateR_of_step`, `_of_authEnable`). -/
theorem adminOut_model (γa : auth.AuthNames) (Own : auth.AuthNames → List auth.AuthState → IProp GF)
    (hs : List auth.AuthState) (st : auth.AuthState) (rq : apply.IRRModel) (ar : Loc)
    (out : apply.ApplyOut) (hl : hs.getLast? = some st) (hn : apply.needAdminPermission rq = true)
    (hka : apply.adminKindOk rq)
    (hrej : out = .rejected → apply.needAdminPermission rq = true ∧ apply.adminRejL (.on γa) hs rq)
    (hpass : ∀ o b, out = .dispatched o b → apply.adminPassL (.on γa) hs rq)
    (hout : out = .rejected ∨ ∃ o b, out = .dispatched o b) :
    apply.adminOut Own γa (.on γa) hs rq true ar out ⊢
      ∃ (hs' : List auth.AuthState) (st' : auth.AuthState),
        ⌜hs'.getLast? = some st' ∧ adminStateR rq st st'⌝ ∗ Own γa hs' ∗
        adminTieAr ar rq st st' out := by
  rcases hout with rfl | ⟨o, b, rfl⟩
  · simp only [apply.adminOut]
    iintro ⟨Ho, -⟩
    iexists hs, st
    iframe Ho
    isplitr
    · ipureintro
      exact ⟨hl, adminStateR_of_rejL γa hs st rq hl (hrej rfl).2⟩
    iunfold adminTieAr
    ileft
    ipureintro
    exact Or.inr (fun o b h => by cases h)
  · have ha := adminOk_of_passL γa hs st rq hl hn (hpass o b rfl)
    simp only [apply.adminOut, apply.adminDone, ↓reduceIte]
    iintro ⟨%v, %ad, %resp, ⟨%had, -⟩, #Hv, Hres⟩
    unfold apply.adminReqOf at had
    split at had <;> rename_i hkd
    · -- `UserAdd`
      cases hm : rq.authUserAdd with
      | none => simp [hm] at had
      | some m =>
        simp only [hm, Option.map_some, Option.some.injEq] at had
        subst had
        simp only [apply.AdminReq.result]
        ihave ⟨%st1, %o', %h, Ho⟩ := adminOutX_on_noExtraE γa (Own γa) hs _ _ $$ Hres
        obtain ⟨h1, h2, h3⟩ := h
        rw [hl] at h1; cases h1
        iexists histAfter hs o', outState st o'
        iframe Ho
        isplitr
        · ipureintro
          exact ⟨histAfter_last hs st o' hl,
            adminStateR_of_step rq st o' ha (Or.inl ⟨m, hkd, hm, h2⟩)⟩
        iunfold adminTieAr
        iright
        iexists v
        iframe Hv
        ipureintro
        intro hn
        refine ⟨ha, o', ?_, h3 hn, rfl⟩
        unfold adminStepO
        rw [hkd]
        exact ⟨m, hm, h2⟩
    · -- `RoleAdd`
      cases hm : rq.authRoleAdd with
      | none => simp [hm] at had
      | some n =>
        simp only [hm, Option.map_some, Option.some.injEq] at had
        subst had
        simp only [apply.AdminReq.result]
        ihave ⟨%st1, %o', %h, Ho⟩ := adminOutX_on_noExtraE γa (Own γa) hs _ _ $$ Hres
        obtain ⟨h1, h2, h3⟩ := h
        rw [hl] at h1; cases h1
        iexists histAfter hs o', outState st o'
        iframe Ho
        isplitr
        · ipureintro
          exact ⟨histAfter_last hs st o' hl,
            adminStateR_of_step rq st o' ha (Or.inr (Or.inl ⟨n, hkd, hm, h2⟩))⟩
        iunfold adminTieAr
        iright
        iexists v
        iframe Hv
        ipureintro
        intro hn
        refine ⟨ha, o', ?_, h3 hn, rfl⟩
        unfold adminStepO
        rw [hkd]
        exact ⟨n, hm, h2⟩
    · -- `UserGrantRole`
      cases hm : rq.authUserGrantRole with
      | none => simp [hm] at had
      | some ur =>
        simp only [hm, Option.map_some, Option.some.injEq] at had
        subst had
        simp only [apply.AdminReq.result]
        ihave ⟨%st1, %o', %h, Ho⟩ := adminOutX_on_noExtraE γa (Own γa) hs _ _ $$ Hres
        obtain ⟨h1, h2, h3⟩ := h
        rw [hl] at h1; cases h1
        iexists histAfter hs o', outState st o'
        iframe Ho
        isplitr
        · ipureintro
          exact ⟨histAfter_last hs st o' hl,
            adminStateR_of_step rq st o' ha (Or.inr (Or.inr (Or.inl ⟨ur.1, ur.2, hkd, hm, h2⟩)))⟩
        iunfold adminTieAr
        iright
        iexists v
        iframe Hv
        ipureintro
        intro hn
        refine ⟨ha, o', ?_, h3 hn, rfl⟩
        unfold adminStepO
        rw [hkd]
        exact ⟨ur.1, ur.2, hm, h2⟩
    · -- `RoleGrantPermission`
      cases hm : rq.authRoleGrantPermission with
      | none => simp [hm] at had
      | some nw =>
        simp only [hm, Option.map_some, Option.some.injEq] at had
        subst had
        simp only [apply.AdminReq.result]
        ihave ⟨%st1, %o', %h, Ho⟩ := adminOutX_on_noExtraE γa (Own γa) hs _ _ $$ Hres
        obtain ⟨h1, h2, h3⟩ := h
        rw [hl] at h1; cases h1
        iexists histAfter hs o', outState st o'
        iframe Ho
        isplitr
        · ipureintro
          exact ⟨histAfter_last hs st o' hl,
            adminStateR_of_step rq st o' ha (Or.inr (Or.inr (Or.inr ⟨nw.1, nw.2, hkd, hm, h2⟩)))⟩
        iunfold adminTieAr
        iright
        iexists v
        iframe Hv
        ipureintro
        intro hn
        refine ⟨ha, o', ?_, h3 hn, rfl⟩
        unfold adminStepO
        rw [hkd]
        exact ⟨nw.1, nw.2, hm, h2⟩
    · -- `AuthEnable`
      cases had
      simp only [apply.AdminReq.result]
      icases Hres with ⟨%en, -, Hx⟩
      ihave ⟨%st1, %o', %h, Ho⟩ := adminOutX_on_noExtraE γa (Own γa) hs _ _ $$ Hx
      obtain ⟨h1, h2, h3⟩ := h
      rw [hl] at h1; cases h1
      iexists histAfter hs o', outState st o'
      iframe Ho
      isplitr
      · ipureintro
        exact ⟨histAfter_last hs st o' hl, adminStateR_of_authEnable γa rq st en o' ha hkd h2⟩
      iunfold adminTieAr
      iright
      iexists v
      iframe Hv
      ipureintro
      intro hn
      refine ⟨ha, o', ?_, h3 hn, rfl⟩
      unfold adminStepO
      rw [hkd]
      exact apply.authEnableR_on γa en st o' h2
    · -- `Authenticate` (C1's A2): admitted only needing no admin permission, against `hn`
      exfalso
      unfold apply.adminKindOk at hka
      rw [hkd] at hka
      rw [hka] at hn
      cases hn
    · cases had

end res2

end EtcdGrove
end Perennial
