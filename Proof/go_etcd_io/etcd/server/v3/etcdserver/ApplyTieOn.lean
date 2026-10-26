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
variable [ext : FfiSyntax]

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

end pure

section res
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
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

end res

end EtcdGrove
end Perennial
