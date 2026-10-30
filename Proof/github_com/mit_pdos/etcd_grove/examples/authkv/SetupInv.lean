/-
**`SetUp`'s ghost state** (the auth-mode merge's 5b, 2026-10-29). Lean-first (no Rocq
counterpart).

`SetUp` turns its client's view of the auth history (`authHistView`) into a freezable cell
(`authHistCell`) and keeps the cell's open half in an invariant (`setupInv`), with what holds of
the history while it is open (`setupOpenOk`: every state of the set-up's shape, every effect kept
to the last state; `SetupHist.lean`). Each admin call's update (`clientHistAu`) opens both:
- open: the call's step is appended (`setup_histAu`), or, for `AuthEnable` after the other seven
  effects, appended and the cell frozen at `setupSt` (`setup_histAu_enable`);
- frozen: no update commits. The history's last state is enabled, so the step's admission needs a
  user, and the call's header has none: its token is the context's (no credential,
  `attemptTokOk conn (fun _ => False)`), the context carries no metadata
  (`context.WithTimeoutBackgroundMd`), and the server has no TLS identity (`setupCtx`).
A reply gives the call's effect (`setup_reply`), recorded or already there; `AuthEnable`'s gives
the frozen history and the published state (`setup_reply_enable`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.authkv.SetupHist
public import Proof.go_etcd_io.etcd.client.v3.AuthServiceOn
public import Proof.go_etcd_io.etcd.client.v3.InvClientAuth

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace authkv

open Iris Iris.BI Iris.ProofMode auth go_etcd_io.etcd.server.v3.etcdserver

section pure
variable [GooseExts] [go_gctx : GoGlobalContext]

/-- The namespace of `SetUp`'s invariant. -/
def setupN : Namespace := nroot .@ "authkv_setup"

theorem authHistN_mask : (↑authHistN : CoPset) ⊆ (⊤ \ ↑srvRaftN) \ ↑kvN := by
  intro p hp
  rw [Iris.Std.LawfulSet.mem_diff, Iris.Std.LawfulSet.mem_diff]
  exact ⟨⟨CoPset.mem_full, fun h' => ndot_ne_disjoint nroot (by decide) p ⟨hp, h'⟩⟩,
    fun h' => ndot_ne_disjoint nroot (by decide) p ⟨hp, h'⟩⟩

theorem setupN_mask : (↑setupN : CoPset) ⊆ ((⊤ \ ↑srvRaftN) \ ↑kvN) \ ↑authHistN := by
  intro p hp
  rw [Iris.Std.LawfulSet.mem_diff, Iris.Std.LawfulSet.mem_diff, Iris.Std.LawfulSet.mem_diff]
  exact ⟨⟨⟨CoPset.mem_full, fun h' => ndot_ne_disjoint nroot (by decide) p ⟨hp, h'⟩⟩,
    fun h' => ndot_ne_disjoint nroot (by decide) p ⟨hp, h'⟩⟩,
    fun h' => ndot_ne_disjoint nroot (by decide) p ⟨hp, h'⟩⟩

theorem setupN_authHistN (E : CoPset) (h1 : (↑authHistN : CoPset) ⊆ E) (h2 : (↑setupN : CoPset) ⊆ E) :
    (↑setupN : CoPset) ⊆ E \ ↑authHistN := by
  intro p hp
  rw [Iris.Std.LawfulSet.mem_diff]
  exact ⟨h2 p hp, fun h' => ndot_ne_disjoint nroot (by decide) p ⟨hp, h'⟩⟩

/-- **The history while `SetUp`'s cell is open**: not empty, every state of the set-up's shape,
every effect of a state kept to the last. -/
def setupOpenOk (hs : List AuthState) : Prop :=
  hs ≠ [] ∧ (∀ st ∈ hs, setupLike st) ∧
    ∀ j st, st ∈ hs → setupEff j st → setupEff j (hs.getLastD srvAuthSt0)

/-- **The history once frozen**: an open history, then `setupSt`. -/
def setupFrozenOk (hs : List AuthState) : Prop :=
  ∃ r hs₀, hs = hs₀ ++ [setupSt r] ∧ setupOpenOk hs₀

theorem getLastD_mem (hs : List AuthState) (d : AuthState) (h : hs ≠ []) : hs.getLastD d ∈ hs := by
  rw [List.getLastD_eq_getLast?, List.getLast?_eq_getLast h]
  exact List.getLast_mem h

theorem setupOpenOk_init : setupOpenOk [srvAuthSt0] := by
  refine ⟨by simp, ?_, ?_⟩
  · intro st h; simp at h; subst h; exact srvAuthSt0_setupLike
  · intro j st h he; simp at h; subst h; simpa using he

/-- **A set-up step but `AuthEnable` keeps the open history's facts**, and has its effect if it
changed the state. -/
theorem setupOpenOk_snoc (j : Nat) (rq₀ : apply.IRRModel) (hj : setupReqAt j rq₀) (hj7 : j < 7)
    (hm : apply.HeaderModel) (hs : List AuthState) (st' : AuthState) (ho : setupOpenOk hs)
    (hR : adminStateR (apply.withHeader rq₀ hm) (hs.getLastD srvAuthSt0) st') :
    setupOpenOk (hs ++ [st']) ∧ (st' ≠ hs.getLastD srvAuthSt0 → setupEff j st') := by
  obtain ⟨hne, hl, he⟩ := ho
  obtain ⟨hl', hmono, hj'⟩ :=
    setup_step j rq₀ hj hj7 hm _ st' (hl _ (getLastD_mem hs _ hne)) hR
  refine ⟨⟨by simp, ?_, ?_⟩, hj'⟩
  · intro st h
    rcases List.mem_append.1 h with h | h
    · exact hl st h
    · simp at h; subst h; exact hl'
  · intro i st h hi
    simp only [List.getLastD_eq_getLast?, List.getLast?_append, List.getLast?_singleton,
      Option.some_or, Option.getD_some]
    rcases List.mem_append.1 h with h | h
    · exact hmono i (he i st h hi)
    · simp at h; subst h; exact hi

/-- **An update that fired changed the state**: the history grew, so the entry was recorded
(`admEntry`), and a recorded step changes the state. -/
theorem hist_changed (γk : KVNames) (L : List EntryModel) (e : EntryModel) (rq : apply.IRRModel)
    (hs : List AuthState) (x : AuthState) (hL : admStates γk srvAuthSt0 L = hs)
    (hL' : admStates γk srvAuthSt0 (L ++ [e]) = hs ++ [x])
    (hdec : apply.irrDecode e.data = some rq) :
    adminNext rq (hs.getLastD srvAuthSt0) ≠ hs.getLastD srvAuthSt0 := by
  have hlast : hs.getLastD srvAuthSt0 = srvAuthAtLog γk srvAuthSt0 L := by
    rw [← hL, admStates_getLastD]
  rw [hlast]
  by_cases ha : admEntry γk.c0 (srvAuthAtLog γk srvAuthSt0 L) e
  · obtain ⟨-, -, rq', hd', -, -, -, hne⟩ := ha
    rw [hdec] at hd'
    cases hd'
    exact hne
  · rw [admStates_snoc_other γk srvAuthSt0 L e ha, hL] at hL'
    have := congrArg List.length hL'
    simp at this

/-- A header with no user is admin-permitted only while auth is disabled. -/
theorem adminOk_anon (st : AuthState) (rq : apply.IRRModel) (hm : apply.HeaderModel)
    (hu : hm.username = (zeroValDef : GoString))
    (h : adminOk st (some (authInfoM (apply.principalOf (apply.withHeader rq hm))))) :
    st.enabled = false := by
  rcases h with h | ⟨a, u, ha, hne, -, -⟩
  · exact h
  · cases ha
    exact absurd (by simp [authInfoM, principalOf_withHeader, hu]; rfl) hne

/-- **`AuthEnable`'s success at a state with every set-up effect** enables exactly `setupSt`. -/
theorem setup_enable_ok (hm : apply.HeaderModel) (st st' : AuthState) (hl : setupLike st)
    (he : ∀ i, i < 7 → setupEff i st)
    (hok : adminStepOk (apply.withHeader irrAuthEnable hm) st st') :
    st' = setupSt st.revision := by
  obtain ⟨-, o, hO, hne, rfl⟩ := hok
  unfold adminStepO at hO
  simp only [dispatchKind_withHeader] at hO
  have hk : apply.dispatchKind irrAuthEnable = .authEnable := by
    simp [apply.dispatchKind, irrAuthEnable, apply.irrEmpty]
  rw [hk] at hO
  unfold stepOf at hO
  subst hO
  unfold authEnableF at hne ⊢
  rw [hl.1] at hne ⊢
  simp only [Bool.false_eq_true, ↓reduceIte] at hne ⊢
  cases hu : st.users !! rootRole with
  | none => simp [hu] at hne
  | some u =>
    by_cases hr : isRoot u
    · simp only [hr, if_true, outState]
      exact setup_enable st hl he
    · simp [hu, hr] at hne

/-- A state of a set-up history that is disabled has the set-up's shape. -/
theorem setupHist_like (hs : List AuthState) (st : AuthState)
    (h : setupOpenOk hs ∨ setupFrozenOk hs) (hm : st ∈ hs) (hd : st.enabled = false) :
    setupLike st := by
  rcases h with h | ⟨r, hs₀, rfl, h⟩
  · exact h.2.1 st hm
  · rcases List.mem_append.1 hm with hm | hm
    · exact h.2.1 st hm
    · simp at hm; subst hm; simp [setupSt] at hd

/-- `SetUp`'s requests need the admin permission and have no range end. -/
theorem setupReqAt_admin (j : Nat) (rq : apply.IRRModel) (hj : setupReqAt j rq)
    (hm : apply.HeaderModel) :
    apply.needAdminPermission (apply.withHeader rq hm) = true ∧ irrNoZeroEnd rq := by
  have hz : rq.range = none → rq.deleteRange = none → rq.txn = none → irrNoZeroEnd rq :=
    irrNoZeroEnd_admin rq
  match j, hj with
  | 0, ⟨um, h, _⟩ | 4, ⟨um, h, _⟩ | 6, ⟨um, h, _⟩ =>
    subst h
    exact ⟨by simp [apply.needAdminPermission, apply.withHeader, irrUserAdd, apply.irrEmpty],
      hz (by simp [irrUserAdd, apply.irrEmpty]) (by simp [irrUserAdd, apply.irrEmpty])
        (by simp [irrUserAdd, apply.irrEmpty])⟩
  | 1, h | 5, h =>
    subst h
    exact ⟨by simp [apply.needAdminPermission, apply.withHeader, irrUserGrantRole, apply.irrEmpty],
      hz (by simp [irrUserGrantRole, apply.irrEmpty]) (by simp [irrUserGrantRole, apply.irrEmpty])
        (by simp [irrUserGrantRole, apply.irrEmpty])⟩
  | 2, h =>
    subst h
    exact ⟨by simp [apply.needAdminPermission, apply.withHeader, irrRoleAdd, apply.irrEmpty],
      hz (by simp [irrRoleAdd, apply.irrEmpty]) (by simp [irrRoleAdd, apply.irrEmpty])
        (by simp [irrRoleAdd, apply.irrEmpty])⟩
  | 3, h =>
    subst h
    exact ⟨by simp [apply.needAdminPermission, apply.withHeader, irrRoleGrantPermission,
        apply.irrEmpty],
      hz (by simp [irrRoleGrantPermission, apply.irrEmpty])
        (by simp [irrRoleGrantPermission, apply.irrEmpty])
        (by simp [irrRoleGrantPermission, apply.irrEmpty])⟩
  | 7, h =>
    subst h
    exact ⟨by simp [apply.needAdminPermission, apply.withHeader, irrAuthEnable, apply.irrEmpty],
      hz (by simp [irrAuthEnable, apply.irrEmpty]) (by simp [irrAuthEnable, apply.irrEmpty])
        (by simp [irrAuthEnable, apply.irrEmpty])⟩

end pure

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

instance authHistOpen_timeless' (γz : GName) (hs : List AuthState) :
    Timeless (authHistOpen (GF := GF) γz hs) := by
  unfold authHistOpen; infer_instance

/-- **`SetUp`'s invariant** (persistent): the cell's other open half and the open history's facts,
or the cell's mark at a frozen history. -/
def setupInv (γz : GName) : IProp GF :=
  inv setupN iprop(∃ hs : List AuthState,
    (authHistOpen γz hs ∗ ⌜setupOpenOk hs⌝) ∨ (authHistMark γz hs ∗ ⌜setupFrozenOk hs⌝))

instance setupInv_persistent (γz : GName) : Persistent (setupInv (GF := GF) γz) := by
  unfold setupInv; infer_instance

/-- **The `j`-th effect, at a state of a lower bound of the history** (persistent). -/
def effLb (γk : KVNames) (j : Nat) : IProp GF :=
  iprop(∃ (h : List AuthState) (st : AuthState), authHistLb γk h ∗ ⌜st ∈ h ∧ setupEff j st⌝)

instance effLb_persistent (γk : KVNames) (j : Nat) : Persistent (effLb (GF := GF) γk j) := by
  unfold effLb; infer_instance

/-- **What `AuthEnable`'s update tells, at the history `hs` before it** (persistent): the history
frozen after `hs` at `setupSt r` (`r` its last state's revision, every set-up effect there), at a
lower bound `Lset` of the requested log. -/
def setupDone (γ : ServerRaftNames) (γk : KVNames) (γz : GName) (hs : List AuthState) :
    IProp GF :=
  iprop(∃ (Lset : List EntryModel) (r : Nat), srvReqLogLb γ Lset ∗
    authHistMark γz (hs ++ [setupSt r]) ∗
    ⌜admStates γk srvAuthSt0 Lset = hs ++ [setupSt r] ∧
      srvAuthAtLog γk srvAuthSt0 Lset = setupSt r ∧
      setupLike (hs.getLastD srvAuthSt0) ∧ (∀ i, i < 7 → setupEff i (hs.getLastD srvAuthSt0)) ∧
      r = (hs.getLastD srvAuthSt0).revision⌝)

instance setupDone_persistent (γ : ServerRaftNames) (γk : KVNames) (γz : GName)
    (hs : List AuthState) : Persistent (setupDone (GF := GF) γ γk γz hs) := by
  unfold setupDone; infer_instance

/-- **`SetUp`'s calls carry no user** (persistent): no attempt on `conn` carries a credential token,
the context `ctx` has no outgoing metadata, and the server has no TLS identity. -/
def setupCtx (s conn : Loc) (ctx : GoInterface) : IProp GF :=
  iprop(attemptTokOk conn (fun _ => iprop(False)) ∗ □ (srvTLSId s -∗ False) ∗
    ⌜metadata.outgoingOf ctx = none⌝)

instance setupCtx_persistent (s conn : Loc) (ctx : GoInterface) :
    Persistent (setupCtx (GF := GF) s conn ctx) := by
  unfold setupCtx; infer_instance

end defs

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- **A header bound to an attempt of `SetUp`'s calls has no user.** -/
theorem setupHdr_anon (s conn : Loc) (ctx : GoInterface) (M : AuthMode) (hm : apply.HeaderModel)
    (md : GrpcMd) (hmd : clientAttemptMd conn ctx md) :
    ⊢ setupCtx (GF := GF) s conn ctx -∗ v3rpc.hdrBoundT s M (auth.mdTokenOf md) hm -∗
      ⌜hm.username = (zeroValDef : GoString)⌝ := by
  iintro #Hc #Hb
  iunfold setupCtx at Hc
  icases Hc with ⟨#Ht, #Htls, %Hout⟩
  iunfold attemptTokOk at Ht
  ihave Htk := Ht $$ %(metadata.outgoingOf ctx) %md %hmd
  have hnone : auth.mdTokenOf md = auth.mdTokenOf (metadata.mdNorm (metadata.outgoingOf ctx)) →
      auth.mdTokenOf md = none := by
    intro h; rw [h, Hout]; rfl
  iunfold v3rpc.hdrBoundT at Hb
  icases Hb with (%Hu | (⟨%tok, %Htok, -⟩ | Htls'))
  · ipureintro; exact Hu
  · icases Htk with (⟨%t, %_, #Hf⟩ | %Hn)
    · iexfalso; iexact Hf
    · rw [hnone Hn] at Htok; cases Htok
  · iexfalso; iapply Htls $$ Htls'

/-- **The cell and `SetUp`'s invariant agree**, opened together: the history is open, at `hs`
with the cell's open half, or frozen at `hs`. -/
theorem setup_open_agree (γz : GName) (hs hs' : List AuthState) :
    ⊢ (dghostVar (GF := GF) γz (.own (1 : Qp).half) (false, hs) ∨ authHistMark γz hs) -∗
      ((authHistOpen γz hs' ∗ ⌜setupOpenOk hs'⌝) ∨ (authHistMark γz hs' ∗ ⌜setupFrozenOk hs'⌝)) -∗
      ⌜hs = hs'⌝ ∗
      ((dghostVar γz (.own (1 : Qp).half) (false, hs) ∗ authHistOpen γz hs ∗ ⌜setupOpenOk hs⌝) ∨
        (authHistMark γz hs ∗ ⌜setupFrozenOk hs⌝)) := by
  iintro Hz Hn
  icases Hz with (Hz | #Hz) <;> icases Hn with (⟨Hn, %Hok⟩ | ⟨#Hn, %Hok⟩)
  · iunfold authHistOpen at Hn
    ihave %Hag := dghostVar_agree γz _ _ _ _ $$ Hz Hn
    have he : hs = hs' := (Prod.mk.inj Hag).2
    subst he
    isplitr
    · ipureintro; rfl
    ileft; iframe Hz; unfold authHistOpen; iframe Hn; ipureintro; exact Hok
  · iexfalso; iapply authHistOpen_mark γz hs hs' _ $$ Hz Hn
  · iexfalso; iunfold authHistOpen at Hn; iapply authHistOpen_mark γz hs' hs _ $$ Hn Hz
  · ihave %he := authHistMark_agree γz hs hs' $$ Hz Hn
    subst he
    isplitr
    · ipureintro; rfl
    iright; iframe Hz; ipureintro; exact Hok

/-- **A lower bound's disabled states have the set-up's shape** (`authHistN`, `setupN` in `E`). -/
theorem setup_lb_like (γk : KVNames) (γz : GName) (h : List AuthState) (st : AuthState)
    (E : CoPset) (h1 : (↑authHistN : CoPset) ⊆ E) (h2 : (↑setupN : CoPset) ⊆ E)
    (hm : st ∈ h) (hd : st.enabled = false) :
    ⊢ authHistCell (GF := GF) γk γz -∗ setupInv γz -∗ authHistLb γk h ={E}=∗ ⌜setupLike st⌝ := by
  iintro #Hc #Hn #Hlb
  have h2' := setupN_authHistN E h1 h2
  iunfold authHistCell at Hc
  iinv Hc with >Hi Hclose
  icases Hi with ⟨%hs, Hv, Hz⟩
  iunfold setupInv at Hn
  iinv Hn with >Hi' Hclose'
  icases Hi' with ⟨%hs', Hn⟩
  ihave ⟨%he, Hzn⟩ := setup_open_agree γz hs hs' $$ Hz Hn
  subst he
  ihave %Hp := authHistView_prefix γk hs h $$ [Hv Hlb]
  · iframe Hv Hlb
  have hm' : st ∈ hs := by obtain ⟨t, rfl⟩ := Hp; exact List.mem_append_left _ hm
  icases Hzn with (⟨Hz, Ho, %Hok⟩ | ⟨#Hm, %Hok⟩)
  · imod Hclose' $$ [Ho] with -
    · inext; iexists hs; ileft; iframe Ho; ipureintro; exact Hok
    imod Hclose $$ [Hv Hz] with -
    · inext; iexists hs; iframe Hv; ileft; iexact Hz
    imodintro; ipureintro; exact setupHist_like hs st (Or.inl Hok) hm' hd
  · imod Hclose' $$ [] with -
    · inext; iexists hs; iright; iframe Hm; ipureintro; exact Hok
    imod Hclose $$ [Hv] with -
    · inext; iexists hs; iframe Hv; iright; iexact Hm
    imodintro; ipureintro; exact setupHist_like hs st (Or.inr Hok) hm' hd

/-- A lower bound's effect is at a state of the history. -/
theorem effLb_view (γk : KVNames) (hs : List AuthState) (i : Nat) :
    ⊢ authHistView (GF := GF) γk hs -∗ effLb γk i -∗ ⌜∃ st ∈ hs, setupEff i st⌝ := by
  iintro Hv #He
  iunfold effLb at He
  icases He with ⟨%h, %st, #Hlb, %Hst⟩
  ihave %Hp := authHistView_prefix γk hs h $$ [Hv Hlb]
  · iframe Hv Hlb
  ipureintro
  obtain ⟨t, rfl⟩ := Hp
  exact ⟨st, List.mem_append_left _ Hst.1, Hst.2⟩

/-- **The update of `SetUp`'s `j`-th request but `AuthEnable`**: appended to the open history,
with its effect. -/
theorem setup_histAu (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (conn : Loc) (ctx : GoInterface)
    (γz : GName) (j : Nat) (rq₀ : apply.IRRModel) (hj : setupReqAt j rq₀) (hj7 : j < 7) :
    ⊢ authHistCell (GF := GF) ρ.kv γz -∗ setupInv γz -∗ setupCtx s conn ctx -∗
      client.clientHistAu s E ρ conn ctx rq₀ (fun _ => effLb ρ.kv j) := by
  iintro #Hc #Hn #Hx
  unfold client.clientHistAu histAu
  imodintro
  iauintro
  unfold atomic_acc
  have h1 := authHistN_mask
  have h2 := setupN_mask
  iunfold authHistCell at Hc
  iinv Hc with >Hi Hclose
  icases Hi with ⟨%hs, Hv, Hz⟩
  iunfold setupInv at Hn
  iinv Hn with >Hi' Hclose'
  icases Hi' with ⟨%hs', Hn'⟩
  ihave ⟨%he, Hzn⟩ := setup_open_agree γz hs hs' $$ Hz Hn'
  subst he
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ (((⊤ \ ↑srvRaftN) \ ↑kvN) \ ↑authHistN) \ ↑setupN
    from Std.LawfulSet.empty_subset)
  iintro Hclose2
  isimp only [texist_cons, texist_nil, tforall_nil, Std.Tele.app, ULift.down]
  iexists hs
  iframe Hv
  isplit
  · iintro Hv
    imod Hclose2 with -
    icases Hzn with (⟨Hz, Ho, %Hok⟩ | ⟨#Hm, %Hok⟩)
    · imod Hclose' $$ [Ho] with -
      · inext; iexists hs; ileft; iframe Ho; ipureintro; exact Hok
      imod Hclose $$ [Hv Hz] with -
      · inext; iexists hs; iframe Hv; ileft; iexact Hz
      imodintro; iempintro
    · imod Hclose' $$ [] with -
      · inext; iexists hs; iright; iframe Hm; ipureintro; exact Hok
      imod Hclose $$ [Hv] with -
      · inext; iexists hs; iframe Hv; iright; iexact Hm
      imodintro; iempintro
  · iintro ⟨%hm, %L, %e, #Hb, #HL, #HLe, %Hp, Hv⟩
    imod Hclose2 with -
    icases Hb with ⟨%md, %hmd, #Hb⟩
    ihave %Hu := setupHdr_anon s conn ctx E.authMode hm md hmd $$ Hx Hb
    obtain ⟨hdec, hL, hok, hdet, hL'⟩ := Hp
    have hen := adminOk_anon _ rq₀ hm Hu hok
    have hch := hist_changed ρ.kv L e _ hs _ hL hL' hdec
    icases Hzn with (⟨Hz, Ho, %Hok⟩ | ⟨#Hm, %Hok⟩)
    · obtain ⟨Hok', Heff⟩ := setupOpenOk_snoc j rq₀ hj hj7 hm hs _ Hok
        (adminStateR_adminNext _ _ hdet)
      imod (authHistOpen_update γz hs hs
        (hs ++ [adminNext (apply.withHeader rq₀ hm) (hs.getLastD srvAuthSt0)])) $$ Ho Hz
        with ⟨-, Ho, Hz⟩
      iunfold authHistView at Hv
      ihave #Hlb := monoListLbOwn_get ρ.kv.hist _
        (hs ++ [adminNext (apply.withHeader rq₀ hm) (hs.getLastD srvAuthSt0)]) $$ Hv
      imod Hclose' $$ [Ho] with -
      · inext; iexists _; ileft; iframe Ho; ipureintro; exact Hok'
      imod Hclose $$ [Hv Hz] with -
      · inext; iexists _; iunfold authHistView; iframe Hv; ileft; iexact Hz
      imodintro; imodintro
      iunfold effLb
      iexists _, adminNext (apply.withHeader rq₀ hm) (hs.getLastD srvAuthSt0)
      iunfold authHistLb
      iframe Hlb
      ipureintro
      exact ⟨by simp, Heff hch⟩
    · obtain ⟨r, hs₀, rfl, -⟩ := Hok
      simp [List.getLastD_eq_getLast?, setupSt] at hen

/-- **`AuthEnable`'s update, after the other seven effects**: appended to the open history at
`setupSt`, and the cell frozen there. -/
theorem setup_histAu_enable (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (conn : Loc)
    (ctx : GoInterface) (γz : GName) :
    ⊢ authHistCell (GF := GF) ρ.kv γz -∗ setupInv γz -∗ setupCtx s conn ctx -∗
      (□ ∀ i, ⌜i < 7⌝ -∗ effLb ρ.kv i) -∗
      client.clientHistAu s E ρ conn ctx irrAuthEnable (setupDone ρ.raft ρ.kv γz) := by
  iintro #Hc #Hn #Hx #Hall
  unfold client.clientHistAu histAu
  imodintro
  iauintro
  unfold atomic_acc
  have h1 := authHistN_mask
  have h2 := setupN_mask
  iunfold authHistCell at Hc
  iinv Hc with >Hi Hclose
  icases Hi with ⟨%hs, Hv, Hz⟩
  iunfold setupInv at Hn
  iinv Hn with >Hi' Hclose'
  icases Hi' with ⟨%hs', Hn'⟩
  ihave ⟨%he, Hzn⟩ := setup_open_agree γz hs hs' $$ Hz Hn'
  subst he
  ihave #E0 := Hall $$ %0 %(by decide)
  ihave #E1 := Hall $$ %1 %(by decide)
  ihave #E2 := Hall $$ %2 %(by decide)
  ihave #E3 := Hall $$ %3 %(by decide)
  ihave #E4 := Hall $$ %4 %(by decide)
  ihave #E5 := Hall $$ %5 %(by decide)
  ihave #E6 := Hall $$ %6 %(by decide)
  ihave %e0 := effLb_view ρ.kv hs 0 $$ Hv E0
  ihave %e1 := effLb_view ρ.kv hs 1 $$ Hv E1
  ihave %e2 := effLb_view ρ.kv hs 2 $$ Hv E2
  ihave %e3 := effLb_view ρ.kv hs 3 $$ Hv E3
  ihave %e4 := effLb_view ρ.kv hs 4 $$ Hv E4
  ihave %e5 := effLb_view ρ.kv hs 5 $$ Hv E5
  ihave %e6 := effLb_view ρ.kv hs 6 $$ Hv E6
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ (((⊤ \ ↑srvRaftN) \ ↑kvN) \ ↑authHistN) \ ↑setupN
    from Std.LawfulSet.empty_subset)
  iintro Hclose2
  isimp only [texist_cons, texist_nil, tforall_nil, Std.Tele.app, ULift.down]
  iexists hs
  iframe Hv
  isplit
  · iintro Hv
    imod Hclose2 with -
    icases Hzn with (⟨Hz, Ho, %Hok⟩ | ⟨#Hm, %Hok⟩)
    · imod Hclose' $$ [Ho] with -
      · inext; iexists hs; ileft; iframe Ho; ipureintro; exact Hok
      imod Hclose $$ [Hv Hz] with -
      · inext; iexists hs; iframe Hv; ileft; iexact Hz
      imodintro; iempintro
    · imod Hclose' $$ [] with -
      · inext; iexists hs; iright; iframe Hm; ipureintro; exact Hok
      imod Hclose $$ [Hv] with -
      · inext; iexists hs; iframe Hv; iright; iexact Hm
      imodintro; iempintro
  · iintro ⟨%hm, %L, %e, #Hb, #HL, #HLe, %Hp, Hv⟩
    imod Hclose2 with -
    icases Hb with ⟨%md, %hmd, #Hb⟩
    ihave %Hu := setupHdr_anon s conn ctx E.authMode hm md hmd $$ Hx Hb
    obtain ⟨hdec, hL, hok, hdet, hL'⟩ := Hp
    have hen := adminOk_anon _ irrAuthEnable hm Hu hok
    have hch := hist_changed ρ.kv L e _ hs _ hL hL' hdec
    icases Hzn with (⟨Hz, Ho, %Hok⟩ | ⟨#Hm, %Hok⟩)
    · have hlast := Hok.2.1 _ (getLastD_mem hs srvAuthSt0 Hok.1)
      have heff : ∀ i, i < 7 → setupEff i (hs.getLastD srvAuthSt0) := by
        intro i hi
        have hx : ∀ st ∈ hs, setupEff i st → setupEff i (hs.getLastD srvAuthSt0) :=
          fun st hm' he' => Hok.2.2 i st hm' he'
        have hi' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by omega
        rcases hi' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · obtain ⟨st, hm', he'⟩ := e0; exact hx st hm' he'
        · obtain ⟨st, hm', he'⟩ := e1; exact hx st hm' he'
        · obtain ⟨st, hm', he'⟩ := e2; exact hx st hm' he'
        · obtain ⟨st, hm', he'⟩ := e3; exact hx st hm' he'
        · obtain ⟨st, hm', he'⟩ := e4; exact hx st hm' he'
        · obtain ⟨st, hm', he'⟩ := e5; exact hx st hm' he'
        · obtain ⟨st, hm', he'⟩ := e6; exact hx st hm' he'
      have hst : adminNext (apply.withHeader irrAuthEnable hm) (hs.getLastD srvAuthSt0) =
          setupSt (hs.getLastD srvAuthSt0).revision := by
        rcases setup_step_enable hm _ _ hlast (adminStateR_adminNext _ _ hdet) with h | ⟨u, -, -, h⟩
        · exact absurd h hch
        · rw [h]; exact setup_enable _ hlast heff
      rw [hst] at hL'
      imod (authHistOpen_freeze γz hs hs
        (hs ++ [setupSt (hs.getLastD srvAuthSt0).revision])) $$ Ho Hz with ⟨-, #Hm⟩
      imod Hclose' $$ [] with -
      · inext; iexists _; iright; iframe Hm; ipureintro
        exact ⟨_, hs, rfl, Hok⟩
      rw [hst]
      imod Hclose $$ [Hv] with -
      · inext; iexists _; iframe Hv; iright; iexact Hm
      imodintro; imodintro
      iunfold setupDone
      iexists L ++ [e], (hs.getLastD srvAuthSt0).revision
      iframe HLe Hm
      ipureintro
      refine ⟨hL', ?_, hlast, heff, rfl⟩
      rw [← admStates_getLastD ρ.kv srvAuthSt0 _ srvAuthSt0, hL']
      simp [List.getLastD_eq_getLast?]
    · obtain ⟨r, hs₀, rfl, -⟩ := Hok
      simp [List.getLastD_eq_getLast?, setupSt] at hen

/-- `authPubAt` in the mode `on`. -/
theorem authPubAt_on (M : AuthMode) (γa : auth.AuthNames) (st : AuthState) (h : M = .on γa) :
    authPubAt (GF := GF) M st ⊢ ∃ k, auth.authPubLb γa k ∗ auth.authStateAt γa k st := by
  subst h; unfold authPubAt; exact .rfl

/-- **The reply to a set-up request**, at a lower bound of the history, of a state it left
disabled: the state had the set-up's shape. -/
theorem setup_reply_like (ρ : ReqNames) (γz : GName) (L : List EntryModel)
    (E : CoPset) (h1 : (↑authHistN : CoPset) ⊆ E) (h2 : (↑setupN : CoPset) ⊆ E)
    (hd : (srvAuthAtLog ρ.kv srvAuthSt0 L).enabled = false) :
    ⊢ authHistCell (GF := GF) ρ.kv γz -∗ setupInv γz -∗
      authHistLb ρ.kv (admStates ρ.kv srvAuthSt0 L) ={E}=∗
      ⌜setupLike (srvAuthAtLog ρ.kv srvAuthSt0 L)⌝ := by
  iintro #Hc #Hn #Hlb
  have hm : srvAuthAtLog ρ.kv srvAuthSt0 L ∈ admStates ρ.kv srvAuthSt0 L := by
    rw [← admStates_getLastD ρ.kv srvAuthSt0 L srvAuthSt0]
    exact getLastD_mem _ _ (admStates_ne_nil _ _ _)
  iapply setup_lb_like ρ.kv γz _ _ E h1 h2 hm hd $$ Hc Hn Hlb

/-- **A reply to `SetUp`'s `j`-th request but `AuthEnable`**: its effect, recorded by the update
or already there. -/
theorem setup_reply (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (conn : Loc) (ctx : GoInterface)
    (γz : GName) (j : Nat) (rq₀ : apply.IRRModel) (hj : setupReqAt j rq₀) (md : GrpcMd)
    (hmd : clientAttemptMd conn ctx md) (Ek : CoPset) (h1 : (↑authHistN : CoPset) ⊆ Ek)
    (h2 : (↑setupN : CoPset) ⊆ Ek) :
    ⊢ authHistCell (GF := GF) ρ.kv γz -∗ setupInv γz -∗ setupCtx s conn ctx -∗
      v3rpc.adminReplied s E ρ (auth.mdTokenOf md) rq₀ (fun _ => effLb ρ.kv j) ={Ek}=∗
      effLb ρ.kv j := by
  iintro #Hc #Hn #Hx #Hr
  iunfold v3rpc.adminReplied at Hr
  icases Hr with ⟨%hm, %rq', %L, %Hw, #HL, #Hpub, #Hq, #Hb⟩
  iunfold adminQh at Hq
  icases Hq with ⟨-, #Hrec⟩
  iunfold adminRecRes at Hrec
  icases Hrec with ⟨#Hlb, #Hrec⟩
  icases Hrec with (⟨%Hadm, #Hq⟩ | %Hnadm)
  · imodintro; iexact Hq
  obtain ⟨hna, hz⟩ := setupReqAt_admin j rq₀ hj hm
  have hrq := irrWireOf_eq rq₀ rq' hm Hw.1 hz
  subst hrq
  have hok := Hw.2 hna
  ihave %Hu := setupHdr_anon s conn ctx E.authMode hm md hmd $$ Hx Hb
  have hen := adminOk_anon _ rq₀ hm Hu hok.1
  imod (setup_reply_like ρ γz L Ek h1 h2 hen) $$ Hc Hn Hlb with Hl
  icases Hl with %hl
  have hsame : adminNext (apply.withHeader rq₀ hm) (srvAuthAtLog ρ.kv srvAuthSt0 L) =
      srvAuthAtLog ρ.kv srvAuthSt0 L := by
    exact _root_.Classical.byContradiction fun hne => Hnadm ⟨hok.1, hne⟩
  obtain ⟨-, he⟩ := setup_notRec_eff j rq₀ hj hm _ hl hok hsame
  imodintro
  iunfold effLb
  iexists _, srvAuthAtLog ρ.kv srvAuthSt0 L
  iframe Hlb
  ipureintro
  refine ⟨?_, he⟩
  rw [← admStates_getLastD ρ.kv srvAuthSt0 L srvAuthSt0]
  exact getLastD_mem _ _ (admStates_ne_nil _ _ _)

/-- **`AuthEnable`'s reply**: the history frozen at `setupSt r`, at a lower bound `Lset` of the
requested log, and `setupSt r` published. -/
theorem setup_reply_enable (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (conn : Loc)
    (ctx : GoInterface) (γz : GName) (γa : auth.AuthNames) (md : GrpcMd)
    (hmd : clientAttemptMd conn ctx md) (hmode : E.authMode = .on γa)
    (hc0 : uint.Z ρ.kv.c0 ≤ uint.Z ρ.raft.ai0) (Ek : CoPset) (h1 : (↑authHistN : CoPset) ⊆ Ek)
    (h2 : (↑setupN : CoPset) ⊆ Ek) :
    ⊢ authHistCell (GF := GF) ρ.kv γz -∗ setupInv γz -∗ setupCtx s conn ctx -∗
      v3rpc.adminReplied s E ρ (auth.mdTokenOf md) irrAuthEnable (setupDone ρ.raft ρ.kv γz)
      ={Ek}=∗
      ∃ (hs : List AuthState) (Lset : List EntryModel) (k : Nat) (r : Nat),
        authHistFrozen ρ.kv γz hs ∗ srvReqLogLb ρ.raft Lset ∗
        ⌜admStates ρ.kv srvAuthSt0 Lset = hs ∧ srvAuthAtLog ρ.kv srvAuthSt0 Lset = setupSt r⌝ ∗
        auth.authPubLb γa k ∗ auth.authStateAt γa k (setupSt r) := by
  iintro #Hc #Hn #Hx #Hr
  iunfold v3rpc.adminReplied at Hr
  icases Hr with ⟨%hm, %rq', %L, %Hw, #HL, #Hpub, #Hq, #Hb⟩
  iunfold adminQh at Hq
  icases Hq with ⟨-, #Hrec⟩
  iunfold adminRecRes at Hrec
  icases Hrec with ⟨#Hlb, #Hrec⟩
  obtain ⟨hna, hz⟩ := setupReqAt_admin 7 irrAuthEnable rfl hm
  have hrq := irrWireOf_eq irrAuthEnable rq' hm Hw.1 hz
  subst hrq
  have hok := Hw.2 hna
  ihave %Hu := setupHdr_anon s conn ctx E.authMode hm md hmd $$ Hx Hb
  have hen := adminOk_anon _ irrAuthEnable hm Hu hok.1
  icases Hrec with (⟨%Hadm, #Hq⟩ | %Hnadm)
  · iunfold setupDone at Hq
    icases Hq with ⟨%Lset, %r, #HLs, #Hm, %Hd⟩
    obtain ⟨hLs, hLr, hl, he, hr⟩ := Hd
    rw [admStates_getLastD] at hl he hr
    iunfold pubAfterM at Hpub
    icases Hpub with ⟨%e, #HLe, %He, #Hpa⟩
    ihave %Hidx := srvRLogLb_idx ρ.raft (L ++ [e]) $$ HLe
    have hv := srvIdxOkW_above _ _ _ Hidx hc0 e (by simp)
    have hsnoc := srvAuthAtLog_snoc_adm ρ.kv srvAuthSt0 L e _ He.1 He.2.1 He.2.2 hv hna
    have hset := setup_enable_ok hm _ _ hl he hok
    ihave Hpa' := authPubAt_on E.authMode γa _ hmode $$ Hpa
    icases Hpa' with ⟨%k, #Hk, #Hst⟩
    imodintro
    iexists _, Lset, k, r
    iunfold authHistFrozen
    iframe Hc Hm HLs Hk
    isplitr
    · ipureintro; exact ⟨hLs, hLr⟩
    have hx : (kvRaftOfOn ρ.kv.c0 ρ.kv.ch0 (srvAuthSt0, ρ.kv.log0) (L ++ [e])).1 = setupSt r := by
      show srvAuthAtLog ρ.kv srvAuthSt0 (L ++ [e]) = _
      rw [hsnoc]; refine hset.trans ?_; rw [hr]
    rw [← hx]
    iexact Hst
  · imod (setup_reply_like ρ γz L Ek h1 h2 hen) $$ Hc Hn Hlb with Hl
    icases Hl with %hl
    have hsame : adminNext (apply.withHeader irrAuthEnable hm) (srvAuthAtLog ρ.kv srvAuthSt0 L) =
        srvAuthAtLog ρ.kv srvAuthSt0 L := by
      exact _root_.Classical.byContradiction fun hne => Hnadm ⟨hok.1, hne⟩
    obtain ⟨h7, -⟩ := setup_notRec_eff 7 irrAuthEnable rfl hm _ hl hok hsame
    omega

/-! ### Each call's precondition and reply -/

/-- **What a set-up call's success tells**: some attempt's metadata, and the server's reply. -/
def setupReplied (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (conn : Loc) (ctx : GoInterface)
    (R : Option GoString → IProp GF) : Unit → IProp GF :=
  fun _ => iprop(∃ md, ⌜clientAttemptMd conn ctx md⌝ ∗ R (auth.mdTokenOf md))

/-- `UserAdd(name, pw)`, `SetUp`'s `j`-th request. -/
theorem setup_pre_userAdd (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (conn : Loc)
    (ctx : GoInterface) (γz : GName) (j : Nat) (name pw : GoString)
    (hj : ∀ um : apply.UserAddModel, um.name = name → um.pwSure → setupReqAt j (irrUserAdd um))
    (hj7 : j < 7) (hlen : name.length ≤ backend.maxKeySize) :
    ⊢ authHistCell (GF := GF) ρ.kv γz -∗ setupInv γz -∗ setupCtx s conn ctx -∗
      attemptPre conn ctx (v3rpc.etcdUserAddSpec s E ρ) (⟨name, pw⟩ : UserAddW)
        (setupReplied s E ρ conn ctx
          (fun tok => v3rpc.userAddReplied s E ρ tok name (fun _ => effLb ρ.kv j))) := by
  iintro #Hc #Hn #Hx
  iunfold attemptPre
  iintro %md %hmd
  iunfold v3rpc.etcdUserAddSpec
  iexists (fun _ => effLb ρ.kv j)
  isplitr
  · ipureintro; exact hlen
  isplitr
  · imodintro
    iintro %um %hum
    iapply client.clientHistAu_attempt s E ρ conn ctx md _ _ hmd
    iapply setup_histAu s E ρ conn ctx γz j _ (hj um hum.1 hum.2.2) hj7 $$ Hc Hn Hx
  · iintro #Hr
    iunfold setupReplied
    iexists md
    iframe Hr
    ipureintro; exact hmd

/-- `UserGrantRole(user, role)`, `SetUp`'s `j`-th request. -/
theorem setup_pre_userGrantRole (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (conn : Loc)
    (ctx : GoInterface) (γz : GName) (j : Nat) (user role : GoString)
    (hj : setupReqAt j (irrUserGrantRole user role)) (hj7 : j < 7)
    (hlen : user.length ≤ backend.maxKeySize) :
    ⊢ authHistCell (GF := GF) ρ.kv γz -∗ setupInv γz -∗ setupCtx s conn ctx -∗
      attemptPre conn ctx (v3rpc.etcdUserGrantRoleSpec s E ρ) (user, role)
        (setupReplied s E ρ conn ctx
          (fun tok => v3rpc.adminReplied s E ρ tok (irrUserGrantRole user role)
            (fun _ => effLb ρ.kv j))) := by
  iintro #Hc #Hn #Hx
  iunfold attemptPre
  iintro %md %hmd
  iunfold v3rpc.etcdUserGrantRoleSpec
  iexists (fun _ => effLb ρ.kv j)
  isplitr
  · ipureintro; exact hlen
  isplitr
  · iapply client.clientHistAu_attempt s E ρ conn ctx md _ _ hmd
    iapply setup_histAu s E ρ conn ctx γz j _ hj hj7 $$ Hc Hn Hx
  · iintro #Hr
    iunfold setupReplied
    iexists md
    iframe Hr
    ipureintro; exact hmd

/-- `RoleAdd(name)`, `SetUp`'s `j`-th request. -/
theorem setup_pre_roleAdd (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (conn : Loc)
    (ctx : GoInterface) (γz : GName) (j : Nat) (name : GoString)
    (hj : setupReqAt j (irrRoleAdd name)) (hj7 : j < 7)
    (hlen : name.length ≤ backend.maxKeySize) :
    ⊢ authHistCell (GF := GF) ρ.kv γz -∗ setupInv γz -∗ setupCtx s conn ctx -∗
      attemptPre conn ctx (v3rpc.etcdRoleAddSpec s E ρ) name
        (setupReplied s E ρ conn ctx
          (fun tok => v3rpc.adminReplied s E ρ tok (irrRoleAdd name) (fun _ => effLb ρ.kv j))) := by
  iintro #Hc #Hn #Hx
  iunfold attemptPre
  iintro %md %hmd
  iunfold v3rpc.etcdRoleAddSpec
  iexists (fun _ => effLb ρ.kv j)
  isplitr
  · ipureintro; exact hlen
  isplitr
  · iapply client.clientHistAu_attempt s E ρ conn ctx md _ _ hmd
    iapply setup_histAu s E ρ conn ctx γz j _ hj hj7 $$ Hc Hn Hx
  · iintro #Hr
    iunfold setupReplied
    iexists md
    iframe Hr
    ipureintro; exact hmd

/-- `RoleGrantPermission(name, w)`, `SetUp`'s `j`-th request. -/
theorem setup_pre_roleGrantPermission (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (conn : Loc)
    (ctx : GoInterface) (γz : GName) (j : Nat) (name : GoString) (w : PermW)
    (hj : setupReqAt j (irrRoleGrantPermission name (some w))) (hj7 : j < 7)
    (hlen : name.length ≤ backend.maxKeySize) :
    ⊢ authHistCell (GF := GF) ρ.kv γz -∗ setupInv γz -∗ setupCtx s conn ctx -∗
      attemptPre conn ctx (v3rpc.etcdRoleGrantPermissionSpec s E ρ) (name, w)
        (setupReplied s E ρ conn ctx
          (fun tok => v3rpc.adminReplied s E ρ tok (irrRoleGrantPermission name (some w))
            (fun _ => effLb ρ.kv j))) := by
  iintro #Hc #Hn #Hx
  iunfold attemptPre
  iintro %md %hmd
  iunfold v3rpc.etcdRoleGrantPermissionSpec
  iexists (fun _ => effLb ρ.kv j)
  isplitr
  · ipureintro; exact hlen
  isplitr
  · iapply client.clientHistAu_attempt s E ρ conn ctx md _ _ hmd
    iapply setup_histAu s E ρ conn ctx γz j _ hj hj7 $$ Hc Hn Hx
  · iintro #Hr
    iunfold setupReplied
    iexists md
    iframe Hr
    ipureintro; exact hmd

/-- `AuthEnable()`, after the other seven effects. -/
theorem setup_pre_authEnable (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (conn : Loc)
    (ctx : GoInterface) (γz : GName) :
    ⊢ authHistCell (GF := GF) ρ.kv γz -∗ setupInv γz -∗ setupCtx s conn ctx -∗
      (□ ∀ i, ⌜i < 7⌝ -∗ effLb ρ.kv i) -∗
      attemptPre conn ctx (v3rpc.etcdAuthEnableSpec s E ρ) ()
        (setupReplied s E ρ conn ctx
          (fun tok => v3rpc.adminReplied s E ρ tok irrAuthEnable (setupDone ρ.raft ρ.kv γz))) := by
  iintro #Hc #Hn #Hx #Hall
  iunfold attemptPre
  iintro %md %hmd
  iunfold v3rpc.etcdAuthEnableSpec
  iexists setupDone ρ.raft ρ.kv γz
  isplitr
  · iapply client.clientHistAu_attempt s E ρ conn ctx md _ _ hmd
    iapply setup_histAu_enable s E ρ conn ctx γz $$ Hc Hn Hx Hall
  · iintro #Hr
    iunfold setupReplied
    iexists md
    iframe Hr
    ipureintro; exact hmd

/-- **A set-up call's success**, but `UserAdd`'s and `AuthEnable`'s: its effect. -/
theorem setup_post (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (conn : Loc) (ctx : GoInterface)
    (γz : GName) (j : Nat) (rq₀ : apply.IRRModel) (hj : setupReqAt j rq₀) (Ek : CoPset)
    (h1 : (↑authHistN : CoPset) ⊆ Ek) (h2 : (↑setupN : CoPset) ⊆ Ek) :
    ⊢ authHistCell (GF := GF) ρ.kv γz -∗ setupInv γz -∗ setupCtx s conn ctx -∗
      setupReplied s E ρ conn ctx (fun tok => v3rpc.adminReplied s E ρ tok rq₀
        (fun _ => effLb ρ.kv j)) () ={Ek}=∗ effLb ρ.kv j := by
  iintro #Hc #Hn #Hx Hr
  iunfold setupReplied at Hr
  icases Hr with ⟨%md, %hmd, #Hr⟩
  iapply setup_reply s E ρ conn ctx γz j rq₀ hj md hmd Ek h1 h2 $$ Hc Hn Hx Hr

/-- **A set-up `UserAdd`'s success**: its effect. -/
theorem setup_post_userAdd (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (conn : Loc)
    (ctx : GoInterface) (γz : GName) (j : Nat) (name : GoString)
    (hj : ∀ um : apply.UserAddModel, um.name = name → um.pwSure → setupReqAt j (irrUserAdd um))
    (Ek : CoPset) (h1 : (↑authHistN : CoPset) ⊆ Ek) (h2 : (↑setupN : CoPset) ⊆ Ek) :
    ⊢ authHistCell (GF := GF) ρ.kv γz -∗ setupInv γz -∗ setupCtx s conn ctx -∗
      setupReplied s E ρ conn ctx (fun tok => v3rpc.userAddReplied s E ρ tok name
        (fun _ => effLb ρ.kv j)) () ={Ek}=∗ effLb ρ.kv j := by
  iintro #Hc #Hn #Hx Hr
  iunfold setupReplied at Hr
  icases Hr with ⟨%md, %hmd, #Hr⟩
  iunfold v3rpc.userAddReplied at Hr
  icases Hr with ⟨%um, %hum, #Hr⟩
  iapply setup_reply s E ρ conn ctx γz j _ (hj um hum.1 hum.2.2) md hmd Ek h1 h2 $$ Hc Hn Hx Hr

/-- **`AuthEnable`'s success**: the frozen history and the published `setupSt`. -/
theorem setup_post_enable (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (conn : Loc)
    (ctx : GoInterface) (γz : GName) (γa : auth.AuthNames) (hmode : E.authMode = .on γa)
    (hc0 : uint.Z ρ.kv.c0 ≤ uint.Z ρ.raft.ai0) (Ek : CoPset) (h1 : (↑authHistN : CoPset) ⊆ Ek)
    (h2 : (↑setupN : CoPset) ⊆ Ek) :
    ⊢ authHistCell (GF := GF) ρ.kv γz -∗ setupInv γz -∗ setupCtx s conn ctx -∗
      setupReplied s E ρ conn ctx
        (fun tok => v3rpc.adminReplied s E ρ tok irrAuthEnable (setupDone ρ.raft ρ.kv γz)) ()
      ={Ek}=∗
      ∃ (hs : List AuthState) (Lset : List EntryModel) (k : Nat) (r : Nat),
        authHistFrozen ρ.kv γz hs ∗ srvReqLogLb ρ.raft Lset ∗
        ⌜admStates ρ.kv srvAuthSt0 Lset = hs ∧ srvAuthAtLog ρ.kv srvAuthSt0 Lset = setupSt r⌝ ∗
        auth.authPubLb γa k ∗ auth.authStateAt γa k (setupSt r) := by
  iintro #Hc #Hn #Hx Hr
  iunfold setupReplied at Hr
  icases Hr with ⟨%md, %hmd, #Hr⟩
  iapply setup_reply_enable s E ρ conn ctx γz γa md hmd hmode hc0 Ek h1 h2 $$ Hc Hn Hx Hr

/-- **`SetUp`'s ghost state, from the client's view** (`authHistN`, `setupN` in `E`): the cell and
`SetUp`'s invariant, open at the boot history. -/
theorem setup_alloc (γk : KVNames) (E : CoPset) :
    ⊢ authHistView (GF := GF) γk [srvAuthSt0] ={E}=∗ ∃ γz, authHistCell γk γz ∗ setupInv γz := by
  iintro Hv
  imod (authHistCell_alloc γk [srvAuthSt0] E) $$ Hv with ⟨%γz, #Hc, Ho⟩
  imod (inv_alloc setupN E iprop(∃ hs : List AuthState,
    (authHistOpen γz hs ∗ ⌜setupOpenOk hs⌝) ∨ (authHistMark γz hs ∗ ⌜setupFrozenOk hs⌝)))
    $$ [Ho] with #Hn
  · inext; iexists [srvAuthSt0]; ileft; iframe Ho; ipureintro; exact setupOpenOk_init
  imodintro
  iexists γz
  iunfold setupInv
  iframe Hc Hn

end lemmas

end authkv
end EtcdGrove
end Perennial
