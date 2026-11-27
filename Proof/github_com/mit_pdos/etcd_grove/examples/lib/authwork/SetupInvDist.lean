/-
**`SetUp`'s ghost state at the cluster view** (F7 stage S4, step 2): `SetupInv.lean`'s cell and invariant
(`authHistCell`, `setupInv`, `effLb`, `setupDone`, all at a `KVNames`), used at the view's KV names `Γ.kv`
with the admin contracts across machines (`etcd_dist.authd.Auth_*_dist`). Lean-first (no Rocq
counterpart).

What changes from `SetupInv.lean`:
- the binding: a call's header is bound to a user its principal may be bound to
  (`etcd_dist.authd.userOk`), and `SetUp`'s client is anonymous (`principalOf cfg = none`), so the
  header has no user (`userOk_none`), where the single-process proof read it off the attempts' tokens
  and the server's TLS identity (`setupCtx`, `setupHdr_anon`);
- the update is `histAu` at the caller's raft names `γR` (`Auth_*_dist`'s premise), not
  `client.clientHistAu`;
- `UserAdd`'s update is asked for every `um` of the name with `noPassword = false`, not only those
  whose password choice cannot fail (`um.pwSure`, which `setupReqAt` asks): such a request's step is
  the same as the one of `um` with `noPassword` set, or keeps the state (`setupReqAtD`,
  `adminStateR_userAdd_sure`);
- the reply is `adminRepliedD` (the member, the requested log), with no publication: `AuthEnable`'s
  reply gives the frozen history at a lower bound of the requested log (`setupD_reply_enable`), not
  the member's published state nor a committed log (at the view a member's floor comes from a later
  barrier, `KV_GetOn_dist`'s `authFloorD`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.authwork.SetupInv
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.AuthViewDist

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_auth

open Iris Iris.BI Iris.ProofMode Net auth go_etcd_io.etcd.server.v3.etcdserver

section pure
variable [GooseExts] [go_gctx : GoGlobalContext]

/-- **The anonymous principal binds only the empty user.** -/
theorem userOk_none (u : GoString) (h : etcd_dist.authd.userOk none u) :
    u = (zeroValDef : GoString) := by
  rcases h with h | h
  · exact h
  · cases h

/-- **A request whose step is a set-up request's `j`-th, or keeps the state** (at every header and
state): `setupReqAt` but for `UserAdd`'s password choice (`setupReqAtD_userAdd`). -/
def setupReqAtD (j : Nat) (rq₀ : apply.IRRModel) : Prop :=
  ∃ rq₁, setupReqAt j rq₁ ∧ ∀ (hm : apply.HeaderModel) (st st' : AuthState),
    adminStateR (apply.withHeader rq₀ hm) st st' → st' = st ∨ adminStateR (apply.withHeader rq₁ hm) st st'

theorem setupReqAtD_of (j : Nat) (rq : apply.IRRModel) (h : setupReqAt j rq) : setupReqAtD j rq :=
  ⟨rq, h, fun _ _ _ h' => Or.inr h'⟩

/-- **A `UserAdd`'s step is the one of the same request with no password asked for**, or keeps the
state (the password choice failed). -/
theorem adminStateR_userAdd_sure (um : apply.UserAddModel) (hm : apply.HeaderModel) (st st' : AuthState)
    (h : adminStateR (apply.withHeader (irrUserAdd um) hm) st st') :
    st' = st ∨ adminStateR (apply.withHeader (irrUserAdd { um with noPassword := true }) hm) st st' := by
  have hk : ∀ m, apply.dispatchKind (irrUserAdd m) = .authUserAdd := by
    intro m; simp [apply.dispatchKind, irrUserAdd, apply.irrEmpty]
  have ha : ∀ m, (apply.withHeader (irrUserAdd m) hm).authUserAdd = some m := fun _ => rfl
  unfold adminStateR at h ⊢
  simp only [dispatchKind_withHeader, hk, ha] at h ⊢
  by_cases hok : adminOk st (some (authInfoM (apply.principalOf (apply.withHeader (irrUserAdd um) hm))))
  · have hok' : adminOk st (some (authInfoM (apply.principalOf
        (apply.withHeader (irrUserAdd { um with noPassword := true }) hm)))) := hok
    rw [if_pos hok] at h
    rw [if_pos hok']
    rcases h with ⟨-, h⟩ | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  · rw [if_neg hok] at h
    exact Or.inl h

/-- **`SetUp`'s `UserAdd`s, at any password choice.** -/
theorem setupReqAtD_userAdd (j : Nat) (name : GoString) (um : apply.UserAddModel)
    (hj : ∀ um' : apply.UserAddModel, um'.name = name → um'.pwSure → setupReqAt j (irrUserAdd um'))
    (hn : um.name = name) : setupReqAtD j (irrUserAdd um) :=
  ⟨irrUserAdd { um with noPassword := true }, hj _ hn (Or.inl rfl),
    fun hm st st' h => adminStateR_userAdd_sure um hm st st' h⟩

/-- **A changed step of a request of `setupReqAtD` keeps the open history's facts, with its effect.** -/
theorem setupOpenOk_snocD (j : Nat) (rq₀ : apply.IRRModel) (hj : setupReqAtD j rq₀) (hj7 : j < 7)
    (hm : apply.HeaderModel) (hs : List AuthState) (st' : AuthState) (ho : setupOpenOk hs)
    (hR : adminStateR (apply.withHeader rq₀ hm) (hs.getLastD srvAuthSt0) st')
    (hch : st' ≠ hs.getLastD srvAuthSt0) :
    setupOpenOk (hs ++ [st']) ∧ setupEff j st' := by
  obtain ⟨rq₁, hj1, hrel⟩ := hj
  rcases hrel hm _ _ hR with heq | hR1
  · exact absurd heq hch
  · obtain ⟨h1, h2⟩ := setupOpenOk_snoc j rq₁ hj1 hj7 hm hs st' ho hR1
    exact ⟨h1, h2 hch⟩

end pure

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- **The anonymous update of `SetUp`'s `j`-th request but `AuthEnable`** (`setup_histAu` at the
view): appended to the open history, with its effect. -/
theorem setupD_histAu (γR : ServerRaftNames) (γk : KVNames) (γz : GName) (j : Nat)
    (rq₀ : apply.IRRModel) (hj : setupReqAtD j rq₀) (hj7 : j < 7) (P : Option GoString)
    (hP : P = none) :
    ⊢ authHistCell (GF := GF) γk γz -∗ setupInv γz -∗
      histAu γR γk srvAuthSt0 (fun hm => iprop(⌜etcd_dist.authd.userOk P hm.username⌝)) rq₀
        (fun _ => effLb γk j) := by
  subst hP
  iintro #Hc #Hn
  unfold histAu
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
  · iintro ⟨%hm, %L, %e, %Hu, #HL, #HLe, %Hp, Hv⟩
    imod Hclose2 with -
    have Hu' := userOk_none _ Hu
    obtain ⟨hdec, hL, hok, hdet, hL'⟩ := Hp
    have hen := adminOk_anon _ rq₀ hm Hu' hok
    have hch := hist_changed γk L e _ hs _ hL hL' hdec
    icases Hzn with (⟨Hz, Ho, %Hok⟩ | ⟨#Hm, %Hok⟩)
    · obtain ⟨Hok', Heff⟩ := setupOpenOk_snocD j rq₀ hj hj7 hm hs _ Hok
        (adminStateR_adminNext _ _ hdet) hch
      imod (authHistOpen_update γz hs hs
        (hs ++ [adminNext (apply.withHeader rq₀ hm) (hs.getLastD srvAuthSt0)])) $$ Ho Hz
        with ⟨-, Ho, Hz⟩
      iunfold authHistView at Hv
      ihave #Hlb := monoListLbOwn_get γk.hist _
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
      exact ⟨by simp, Heff⟩
    · obtain ⟨r, hs₀, rfl, -⟩ := Hok
      simp [List.getLastD_eq_getLast?, setupSt] at hen

/-- **The anonymous update of `AuthEnable`, after the other seven effects** (`setup_histAu_enable`
at the view): appended to the open history at `setupSt`, and the cell frozen there. -/
theorem setupD_histAu_enable (γR : ServerRaftNames) (γk : KVNames) (γz : GName) (P : Option GoString)
    (hP : P = none) :
    ⊢ authHistCell (GF := GF) γk γz -∗ setupInv γz -∗ (□ ∀ i, ⌜i < 7⌝ -∗ effLb γk i) -∗
      histAu γR γk srvAuthSt0 (fun hm => iprop(⌜etcd_dist.authd.userOk P hm.username⌝))
        irrAuthEnable (setupDone γR γk γz) := by
  subst hP
  iintro #Hc #Hn #Hall
  unfold histAu
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
  ihave %e0 := effLb_view γk hs 0 $$ Hv E0
  ihave %e1 := effLb_view γk hs 1 $$ Hv E1
  ihave %e2 := effLb_view γk hs 2 $$ Hv E2
  ihave %e3 := effLb_view γk hs 3 $$ Hv E3
  ihave %e4 := effLb_view γk hs 4 $$ Hv E4
  ihave %e5 := effLb_view γk hs 5 $$ Hv E5
  ihave %e6 := effLb_view γk hs 6 $$ Hv E6
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
  · iintro ⟨%hm, %L, %e, %Hu, #HL, #HLe, %Hp, Hv⟩
    imod Hclose2 with -
    have Hu' := userOk_none _ Hu
    obtain ⟨hdec, hL, hok, hdet, hL'⟩ := Hp
    have hen := adminOk_anon _ irrAuthEnable hm Hu' hok
    have hch := hist_changed γk L e _ hs _ hL hL' hdec
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
      rw [← admStates_getLastD γk srvAuthSt0 _ srvAuthSt0, hL']
      simp [List.getLastD_eq_getLast?]
    · obtain ⟨r, hs₀, rfl, -⟩ := Hok
      simp [List.getLastD_eq_getLast?, setupSt] at hen

/-- **A reply to `SetUp`'s `j`-th request but `AuthEnable`, at the view** (`setup_reply`): its
effect, recorded by the update or already there. -/
theorem setupD_reply [NetProtoGS] (eps : List GoString) (Γ : etcd_dist.DistView) (γR : ServerRaftNames)
    (γz : GName) (j : Nat) (rq₀ : apply.IRRModel) (hj : setupReqAt j rq₀) (Ek : CoPset)
    (h1 : (↑authHistN : CoPset) ⊆ Ek) (h2 : (↑setupN : CoPset) ⊆ Ek) (P : Option GoString)
    (hP : P = none) :
    ⊢ authHistCell (GF := GF) Γ.kv γz -∗ setupInv γz -∗
      etcd_dist.authd.adminRepliedD eps Γ γR P rq₀ (fun _ => effLb Γ.kv j) ={Ek}=∗
      effLb Γ.kv j := by
  subst hP
  iintro #Hc #Hn Hr
  iunfold etcd_dist.authd.adminRepliedD at Hr
  icases Hr with ⟨%mid, %hm, %rq', %L, -, %Hw, -, Hq⟩
  iunfold adminQh at Hq
  icases Hq with ⟨-, #Hrec⟩
  iunfold adminRecRes at Hrec
  icases Hrec with ⟨#Hlb, #Hrec⟩
  icases Hrec with (⟨%Hadm, #Hq⟩ | %Hnadm)
  · imodintro; iexact Hq
  obtain ⟨hna, hz⟩ := setupReqAt_admin j rq₀ hj hm
  have hrq := irrWireOf_eq rq₀ rq' hm Hw.1 hz
  subst hrq
  have hok := Hw.2.1 hna
  have Hu := userOk_none _ Hw.2.2
  have hen := adminOk_anon _ rq₀ hm Hu hok.1
  have hmem : srvAuthAtLog Γ.kv srvAuthSt0 L ∈ admStates Γ.kv srvAuthSt0 L := by
    rw [← admStates_getLastD Γ.kv srvAuthSt0 L srvAuthSt0]
    exact getLastD_mem _ _ (admStates_ne_nil _ _ _)
  imod (setup_lb_like Γ.kv γz _ _ Ek h1 h2 hmem hen) $$ Hc Hn Hlb with Hl
  icases Hl with %hl
  have hsame : adminNext (apply.withHeader rq₀ hm) (srvAuthAtLog Γ.kv srvAuthSt0 L) =
      srvAuthAtLog Γ.kv srvAuthSt0 L := by
    exact _root_.Classical.byContradiction fun hne => Hnadm ⟨hok.1, hne⟩
  obtain ⟨-, he⟩ := setup_notRec_eff j rq₀ hj hm _ hl hok hsame
  imodintro
  iunfold effLb
  iexists _, srvAuthAtLog Γ.kv srvAuthSt0 L
  iframe Hlb
  ipureintro
  exact ⟨hmem, he⟩

/-- **`AuthEnable`'s reply, at the view** (`setup_reply_enable` without the member's publication):
the history frozen at `setupSt r`, at a lower bound `Lset` of the requested log. -/
theorem setupD_reply_enable [NetProtoGS] (eps : List GoString) (Γ : etcd_dist.DistView)
    (γR : ServerRaftNames) (γz : GName) (Ek : CoPset) (h1 : (↑authHistN : CoPset) ⊆ Ek)
    (h2 : (↑setupN : CoPset) ⊆ Ek) (P : Option GoString) (hP : P = none) :
    ⊢ authHistCell (GF := GF) Γ.kv γz -∗ setupInv γz -∗
      etcd_dist.authd.adminRepliedD eps Γ γR P irrAuthEnable (setupDone γR Γ.kv γz) ={Ek}=∗
      ∃ (hs : List AuthState) (Lset : List EntryModel) (r : Nat),
        authHistFrozen Γ.kv γz hs ∗ srvReqLogLb γR Lset ∗
        ⌜admStates Γ.kv srvAuthSt0 Lset = hs ∧ srvAuthAtLog Γ.kv srvAuthSt0 Lset = setupSt r⌝ := by
  subst hP
  iintro #Hc #Hn Hr
  iunfold etcd_dist.authd.adminRepliedD at Hr
  icases Hr with ⟨%mid, %hm, %rq', %L, -, %Hw, -, Hq⟩
  iunfold adminQh at Hq
  icases Hq with ⟨-, #Hrec⟩
  iunfold adminRecRes at Hrec
  icases Hrec with ⟨#Hlb, #Hrec⟩
  icases Hrec with (⟨%Hadm, #Hq⟩ | %Hnadm)
  · iunfold setupDone at Hq
    icases Hq with ⟨%Lset, %r, #HLs, #Hm, %Hd⟩
    obtain ⟨hLs, hLr, -, -, -⟩ := Hd
    imodintro
    iexists _, Lset, r
    iunfold authHistFrozen
    iframe Hc Hm HLs
    ipureintro; exact ⟨hLs, hLr⟩
  obtain ⟨hna, hz⟩ := setupReqAt_admin 7 irrAuthEnable rfl hm
  have hrq := irrWireOf_eq irrAuthEnable rq' hm Hw.1 hz
  subst hrq
  have hok := Hw.2.1 hna
  have Hu := userOk_none _ Hw.2.2
  have hen := adminOk_anon _ irrAuthEnable hm Hu hok.1
  have hmem : srvAuthAtLog Γ.kv srvAuthSt0 L ∈ admStates Γ.kv srvAuthSt0 L := by
    rw [← admStates_getLastD Γ.kv srvAuthSt0 L srvAuthSt0]
    exact getLastD_mem _ _ (admStates_ne_nil _ _ _)
  imod (setup_lb_like Γ.kv γz _ _ Ek h1 h2 hmem hen) $$ Hc Hn Hlb with Hl
  icases Hl with %hl
  have hsame : adminNext (apply.withHeader irrAuthEnable hm) (srvAuthAtLog Γ.kv srvAuthSt0 L) =
      srvAuthAtLog Γ.kv srvAuthSt0 L := by
    exact _root_.Classical.byContradiction fun hne => Hnadm ⟨hok.1, hne⟩
  obtain ⟨h7, -⟩ := setup_notRec_eff 7 irrAuthEnable rfl hm _ hl hok hsame
  omega

end lemmas

end etcd_auth
end EtcdGrove
end Perennial
