/-
**`Recover` at the snapshot install with auth on, and the install's mode-indexed facts**
(`notes/snapshot-auth-on-plan.md`, P6.2; moved from `SnapAuthOnDraft.lean`, 2026-11-03, for the
mode-generic walk `applySnapshot_walk` to take them).

* the history's catch-up: `authHistTie_catchup`, `catchup_list` (proved), `srvHist_wf` (pure model
  facts, proved), `auth.authCatchUpFirst` (proved);
* `authRecoverOn.spec`, the server-level triple of the auth store's `Recover` at the install, and
  its glue `authRecoverOn_glue` (proved from the restated `auth.authStore.Recover.spec`);
* the install's mode-indexed facts (F9): `srvAuthSnapOk`, `snapAuthImgM`, `snapRestImgM`,
  `snapAuthResM`.

Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthTie
public import Proof.go_etcd_io.etcd.server.v3.auth.CatchUpDraft
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SnapRecvOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.StoreLatest
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthSnapKit
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SnapRO
public import Spec.go_etcd_io.etcd.server.v3.auth.authStore__Recover
public import Proof.go_etcd_io.etcd.server.v3.auth.Fuel
public import Proof.go_etcd_io.etcd.server.v3.auth.Boot
public import Proof.go_etcd_io.etcd.server.v3.auth.GrantPermLemmas
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVModelDefs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section draft
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **The cap raised to a committed image's history** (the catch-up's tie half): with the store's
history `hs` at the applied log `A` (its latest state `A`'s) and a committed `A'` extending `A`,
`hs` is a prefix of `srvHist A'` and the cap is at least `srvHist A'`: every state of
`(srvHist A').drop hs.length` may be appended (`capLb` of the whole list covers each prefix). -/
theorem authHistTie_catchup (E : apply.AEnv GF) (γr : ReadNames) (γa : auth.AuthNames)
    (A A' : List EntryModel) (hs : List auth.AuthState) (E' : CoPset) (hM : E.authMode = .on γa)
    (hpre : A <+: A')
    (hl : hs.getLast? = some (srvAuthAtLog γr.kv (auth.bump auth.bootState) A))
    (hE1 : ↑authTieN ⊆ E') (hE2 : ↑(nroot.@"authRev") ⊆ E') :
    authHistTie E γr (auth.bump auth.bootState) ∗ srvRLogLb γr.raft A' ∗
        auth.authOwn (.on γa) hs ={E'}=∗
      auth.authOwn (.on γa) hs ∗ ⌜hs <+: srvHist γr.kv A'⌝ ∗ auth.capLb γa (srvHist γr.kv A') := by
  have hne : hs ≠ [] := by intro he; rw [he] at hl; cases hl
  have hlast : hs.getLast? = (srvHist γr.kv A).getLast? := by rw [hl, srvHist_last]
  unfold authHistTie
  rw [hM]
  iintro ⟨⟨⟨%stl, %R, #Hinv⟩, #Htinv⟩, #Hlb, Ho⟩
  imod auth.authOwn_capped stl R γa hs E' hE2 $$ [Hinv Ho] with ⟨Ho, #Hhc⟩
  · iframe Hinv Ho
  iinv Htinv with Hi Hclose
  icases Hi with ⟨%A₀, >#HA₀, >Hcap⟩
  ihave Hcap : auth.capAuth γa (srvHist γr.kv A₀) $$ [Hcap]
  · simp only [srvHist]; iexact Hcap
  ihave %Hcmp := srvRLogLb_prefix γr.raft A₀ A' $$ [HA₀ Hlb]
  · iframe HA₀ Hlb
  ihave %Hhs0 := capAuth_lb_prefixW γa _ hs $$ Hcap Hhc
  rcases Hcmp with h0 | h0
  · -- the cap's log is behind the image's: raise it to `A'`
    imod auth.capAuth_update γa (srvHist γr.kv A') (srvHist_prefix γr.kv A₀ _ h0) $$ Hcap
      with Hcap
    ihave ⟨Hcap, #Hcl⟩ := auth.capAuth_lb γa _ $$ Hcap
    imod Hclose $$ [Hcap] with -
    · inext; iexists A'; iframe Hlb; unfold srvHist; iexact Hcap
    imodintro
    iframe Ho Hcl
    ipureintro
    exact (by exact Hhs0 : hs <+: srvHist γr.kv A₀).trans (srvHist_prefix γr.kv A₀ _ h0)
  · -- the cap's log is at or past the image's: the history is the applied log's
    ihave ⟨Hcap, #Hcl0⟩ := auth.capAuth_lb γa _ $$ Hcap
    imod Hclose $$ [Hcap] with -
    · inext; iexists A₀; iframe HA₀; simp only [srvHist]; iexact Hcap
    have hseq : hs = srvHist γr.kv A :=
      prefix_eq_of_last _ hs _ (srvHist_nodup γr.kv A₀) Hhs0
        ((srvHist_prefix γr.kv A A' hpre).trans (srvHist_prefix γr.kv _ A₀ h0)) hlast hne
    ihave #Hcl : auth.capLb γa (srvHist γr.kv A') $$ [Hcl0]
    · iapply (auth.capLb_le γa (srvHist γr.kv A') (srvHist_prefix γr.kv A' A₀ h0)) $$ Hcl0
    imodintro
    iframe Ho Hcl
    ipureintro
    rw [hseq]; exact srvHist_prefix γr.kv A A' hpre

/-- **The skipped states and the image's** (pure): with `hs` a prefix of `srvHist A'`, the catch-up
appends `N := (srvHist A').drop hs.length`, after which the history is `srvHist A'`, whose last
state is `A'`'s (`srvHist_last`). `N` is empty when no admin entry was skipped and the image's
state is the applied one (the cap's list has no state twice: nothing may be appended then). -/
theorem catchup_list (γk : KVNames) (A' : List EntryModel) (hs : List auth.AuthState)
    (h : hs <+: srvHist γk A') :
    hs ++ (srvHist γk A').drop hs.length = srvHist γk A' ∧
      (hs ++ (srvHist γk A').drop hs.length).getLast? =
        some (srvAuthAtLog γk (auth.bump auth.bootState) A') := by
  obtain ⟨t, ht⟩ := h
  have hd : (srvHist γk A').drop hs.length = t := by
    rw [← ht, List.drop_left]
  rw [hd, ht]
  exact ⟨rfl, srvHist_last γk A'⟩

/-! ## Q3 (b): the auth buckets of a backend's data, and the mode-on image (`srvImageOn`) -/

-- (P5, F8) `imageAtOn`, `dbImageOn`, `srvImageOn` are `ImageOn.lean`'s.

-- (P6.1) `SnapImageFactsOn` is `SnapRecvOn.lean`'s.

/-- A well-formed auth state: its permission keys non-empty, small (`auth.authSmall`). -/
def histWf (st : auth.AuthState) : Prop := auth.permKeysOk st ∧ auth.authSmall st

/-- A step relation's successor keeps a well-formed state, the revision bumped at most once, when
the step keeps the permission keys and is small. -/
theorem authRelState_wf (R : auth.StepRel) (hS : auth.StepSmall R)
    (hK : ∀ st st', auth.permKeysOk st → R st (.next st') → auth.permKeysOk st')
    (st st' : auth.AuthState) (h : histWf st) (hR : authRelState R st st') :
    histWf st' ∧ st'.revision ≤ st.revision + 1 := by
  obtain ⟨o, ho, rfl⟩ := hR
  cases o with
  | err e => exact ⟨h, Nat.le_succ _⟩
  | same => exact ⟨h, Nat.le_succ _⟩
  | next st'' =>
    obtain ⟨hr, hs⟩ := hS st st'' h.2 ho
    exact ⟨⟨hK st st'' h.1 ho, hs⟩, hr⟩

/-- **An admin entry's effect keeps a well-formed state**, the revision bumped at most once (the
five kinds `adminStateR` steps, `auth/Fuel.lean`'s `StepSmall`s; a user's name a bbolt key, the
request model's `adminKindOk`). -/
theorem adminStateR_wf (rq : apply.IRRModel) (st st' : auth.AuthState) (h : histWf st)
    (hU : ∀ m, rq.authUserAdd = some m → apply.dispatchKind rq = .authUserAdd →
      m.name.length ≤ backend.maxKeySize) (hG : apply.irrUtf8 rq)
    (hR : adminStateR rq st st') : histWf st' ∧ st'.revision ≤ st.revision + 1 := by
  unfold adminStateR at hR
  split at hR
  · split at hR <;> rename_i hk
    · split at hR <;> rename_i m hm
      · rcases hR with ⟨-, rfl⟩ | hR
        · exact ⟨h, Nat.le_succ _⟩
        · refine authRelState_wf _ (auth.stepSmall_userAdd m.name (hU m hm hk)) ?_ st st' h hR
          intro s s' hs hn
          simp only [auth.stepOf, auth.userAddF] at hn
          split at hn
          · cases hn
          · split at hn
            · cases hn
            · cases hn; exact auth.permKeysOk_bump _ (auth.permKeysOk_putUser _ _ _ hs)
      · subst hR; exact ⟨h, Nat.le_succ _⟩
    · split at hR <;> rename_i n hn
      · refine authRelState_wf _ (auth.stepSmall_roleAdd n) ?_ st st' h hR
        intro s s' hs hn
        simp only [auth.stepOf, auth.roleAddF] at hn
        split at hn
        · cases hn
        · split at hn
          · cases hn
          · cases hn
            exact auth.permKeysOk_bump _ (auth.permKeysOk_putRole _ _ _ hs (by simp))
      · subst hR; exact ⟨h, Nat.le_succ _⟩
    · split at hR <;> rename_i u r hur
      · refine authRelState_wf _ (auth.stepSmall_userGrantRole u r (hG (u, r) hur)) ?_ st st' h hR
        intro s s' hs hn
        simp only [auth.userGrantRoleR] at hn
        split at hn
        · cases hn
        · split at hn
          · cases hn
          · split at hn
            · cases hn
            · obtain ⟨u', -, -, hn⟩ := hn
              cases hn
              exact auth.permKeysOk_bump _ (auth.permKeysOk_putUser _ _ _ hs)
      · subst hR; exact ⟨h, Nat.le_succ _⟩
    · split at hR <;> rename_i r w hrw
      · refine authRelState_wf _ (auth.stepSmall_roleGrantPermission r w) ?_ st st' h hR
        intro s s' hs hn
        simp only [auth.roleGrantPermissionR] at hn
        split at hn
        · cases hn
        · rename_i w'
          split at hn
          · cases hn
          · rename_i hv
            split at hn
            · cases hn
            · rename_i ps hps
              cases hn
              exact auth.permKeysOk_bump _ (auth.permKeysOk_putRole _ _ _ hs
                (auth.grant_keys ps w' (Classical.not_not.1 hv).1 (fun p hp => hs r ps hps p hp)))
      · subst hR; exact ⟨h, Nat.le_succ _⟩
    · refine authRelState_wf _ (auth.stepSmall_authEnable st.enabled) ?_ st st' h hR
      intro s s' hs hn
      simp only [auth.stepOf, auth.authEnableF] at hn
      split at hn
      · cases hn
      · split at hn
        · cases hn
        · split at hn
          · cases hn; exact auth.permKeysOk_enabled _ _ hs
          · cases hn
    · subst hR; exact ⟨h, Nat.le_succ _⟩
  · subst hR; exact ⟨h, Nat.le_succ _⟩

/-- The model's admin step keeps a well-formed state (`adminNext`: a determinate entry's
successor, `adminStateR`'s; else the state kept). -/
theorem adminNext_wf (rq : apply.IRRModel) (st : auth.AuthState) (h : histWf st)
    (hU : ∀ m, rq.authUserAdd = some m → apply.dispatchKind rq = .authUserAdd →
      m.name.length ≤ backend.maxKeySize) (hG : apply.irrUtf8 rq) :
    histWf (adminNext rq st) ∧ (adminNext rq st).revision ≤ st.revision + 1 := by
  unfold adminNext
  split
  · rename_i hd
    exact adminStateR_wf rq st _ h hU hG (Classical.choose_spec hd).1
  · exact ⟨h, Nat.le_succ _⟩

/-- A mode-on entry's request names a user by a bbolt key (`plainEntryOn`: a plain request is no
`UserAdd`; an admin one's kind is `adminKindOk`'s). -/
theorem plainEntryOn_userAdd (m : EntryModel) (hm : plainEntryOn m) (h0 : m.typ = W32 0)
    (hd : m.data ≠ []) (rq : apply.IRRModel) (hdec : apply.irrDecode m.data = some rq) :
    ∀ u, rq.authUserAdd = some u → apply.dispatchKind rq = .authUserAdd →
      u.name.length ≤ backend.maxKeySize := by
  intro u hu hk
  rcases hm h0 hd rq hdec with ⟨⟨-, hp⟩, -⟩ | ⟨ha, -⟩
  · rw [hk] at hp; simp [putgetKind] at hp
  · unfold apply.adminKindOk at ha
    rw [hk] at ha
    exact (ha u hu).1

/-- A mode-on entry keeps the auth state well formed, its revision bumped at most once. -/
theorem kvEntryOn_wf (c₀ : w64) (ch : apply.Chain) (s : auth.AuthState × mvcc.Log)
    (m : EntryModel) (hm : plainEntryOn m) (h : histWf s.1) :
    histWf (kvEntryOn c₀ ch s m).1 ∧ (kvEntryOn c₀ ch s m).1.revision ≤ s.1.revision + 1 := by
  unfold kvEntryOn
  split
  · rename_i hn
    split
    · rename_i rq hdec
      split
      · exact adminNext_wf rq s.1 h (plainEntryOn_userAdd m hm hn.1 hn.2 rq hdec)
          (apply.irrDecode_utf8 _ rq hdec)
      · split
        · exact ⟨h, Nat.le_succ _⟩
        · exact ⟨h, Nat.le_succ _⟩
    · exact ⟨h, Nat.le_succ _⟩
  · exact ⟨h, Nat.le_succ _⟩

/-- Induction over a list from its end. -/
theorem list_snoc_ind {α : Type _} {P : List α → Prop} (h0 : P [])
    (hs : ∀ A m, P A → P (A ++ [m])) : ∀ A, P A := by
  intro A
  rw [← List.reverse_reverse A]
  induction A.reverse with
  | nil => exact h0
  | cons m B ih => rw [List.reverse_cons]; exact hs _ _ ih

/-- **Along a mode-on log**, every recorded state of the history well formed, the last too, its
revision at most the start's plus the log's length. -/
theorem admStatesR_wf (c₀ : w64) (ch : apply.Chain) (s₀ : auth.AuthState × mvcc.Log)
    (h₀ : histWf s₀.1) (A : List EntryModel) (hp : plainLogOn A) :
    (∀ x ∈ admStatesR c₀ ch s₀ A, histWf x) ∧ histWf (kvRaftOfOn c₀ ch s₀ A).1 ∧
      (kvRaftOfOn c₀ ch s₀ A).1.revision ≤ s₀.1.revision + A.length := by
  revert hp
  refine list_snoc_ind (P := fun A => plainLogOn A →
      (∀ x ∈ admStatesR c₀ ch s₀ A, histWf x) ∧ histWf (kvRaftOfOn c₀ ch s₀ A).1 ∧
        (kvRaftOfOn c₀ ch s₀ A).1.revision ≤ s₀.1.revision + A.length) ?_ ?_ A
  · intro _
    refine ⟨?_, h₀, by simp [kvRaftOfOn_nil]⟩
    intro x hx
    rw [admStatesR_nil, List.mem_singleton] at hx
    subst hx; exact h₀
  · intro A m ih hp
    have hpA : plainLogOn A := fun e he => hp e (List.mem_append_left _ he)
    have hpm : plainEntryOn m := hp m (List.mem_append_right _ (List.mem_singleton_self _))
    obtain ⟨hall, hlast, hrev⟩ := ih hpA
    have hstep := kvEntryOn_wf c₀ ch (kvRaftOfOn c₀ ch s₀ A) m hpm hlast
    rw [← kvRaftOfOn_snoc] at hstep
    refine ⟨?_, hstep.1, by rw [List.length_append, List.length_singleton]; omega⟩
    intro x hx
    rw [admStatesR_snoc] at hx
    split at hx
    · rcases List.mem_append.1 hx with hx | hx
      · exact hall x hx
      · rw [List.mem_singleton] at hx; subst hx; exact hstep.1
    · exact hall x hx

/-- **The states of the committed log's history are well formed** (pure; the catch-up needs them:
`authHist` keeps `permKeysOk` of every state, `Recover` the image state's `permsFit`, the fuel
its size and a revision bound), of a mode-on log (`plainLogOn`; review R1's F2: without it false,
the model's `userAddF` refusing only the empty name while `authSmall` bounds names by `maxKeySize`;
`adminKindOk` bounds them). Proved (2026-11-03) over the five kinds' `StepSmall`s and their permission keys (`adminStateR_wf`). The revision is `1` plus
the number of state-changing admin entries, so at most the log's length plus one (review round 1's
F3: `< 2^61` is false of `2^61 - 1` distinct `UserAdd`s). -/
theorem srvHist_wf (γk : KVNames) (A' : List EntryModel) (hlen : A'.length < 2 ^ 61)
    (hp : plainLogOn A') :
    (∀ x ∈ srvHist γk A', auth.permKeysOk x) ∧
      auth.permsFit (srvAuthAtLog γk srvAuthSt0 A') ∧
      auth.authSmall (srvAuthAtLog γk srvAuthSt0 A') ∧
      (srvAuthAtLog γk srvAuthSt0 A').revision ≤ A'.length + 1 := by
  have h₀ : histWf (auth.bump auth.bootState) :=
    ⟨auth.permKeysOk_bump _ auth.bootState_permKeysOk, auth.authSmall_bump _ auth.bootState_small⟩
  obtain ⟨hall, hlast, hrev⟩ :=
    admStatesR_wf γk.c0 γk.ch0 (auth.bump auth.bootState, γk.log0) h₀ A' hp
  have hrev' : (srvAuthAtLog γk srvAuthSt0 A').revision ≤ A'.length + 1 := by
    have h1 : (auth.bump auth.bootState, γk.log0).1.revision = 1 := rfl
    rw [h1] at hrev
    show (kvRaftOfOn γk.c0 γk.ch0 (auth.bump auth.bootState, γk.log0) A').1.revision ≤ A'.length + 1
    omega
  refine ⟨?_, auth.permsFit_of_small _ hlast.2 (by omega), hlast.2, hrev'⟩
  intro x hx
  unfold srvHist at hx
  rcases List.mem_cons.1 hx with rfl | hx
  · exact auth.bootState_permKeysOk
  · exact (hall x hx).1

end draft

section bk
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.auth.Assumptions]

/-- **The catch-up, before `Recover`** (candidate (ii); ghost only, proved): with the whole
authority at `hs` and the cap's permission at `hs ++ N` (`authHistTie_catchup`), the states of `N`
are appended to the history (the revision invariant's quarter with it, its cap bound raised to
`hs ++ N`); the admin side keeps the pending authority, the lock's share is at the new last state
`stI` (for the new backend's lock), and `stI` is recorded. (It opens only `revInv`'s `revCur`, which
the restatement leaves unchanged, and frames `revFresh`.) -/
theorem auth.authCatchUpFirst (stl : Loc) (R : IProp GF) (γa : auth.AuthNames)
    (hs N : List auth.AuthState) (stI : auth.AuthState) (E' : CoPset)
    (hE : ↑(nroot.@"authRev") ⊆ E') (hk : ∀ x ∈ N, auth.permKeysOk x)
    (hl : (hs ++ N).getLast? = some stI) :
    auth.authInv (GF := GF) stl R (.on γa) ∗ auth.authOwnF (.on γa) hs ∗
        auth.capLb γa (hs ++ N) ={E'}=∗
      auth.authOwnP γa hs N ∗ auth.authLockI (.on γa) stI ∗
        auth.authStateAt γa ((hs ++ N).length - 1) stI := by
  have hi : (hs ++ N)[(hs ++ N).length - 1]? = some stI := by
    rw [List.getLast?_eq_getElem?] at hl; exact hl
  simp only [auth.authOwnF]
  iintro ⟨#Hinv, ⟨Hh, ⟨%stl', %Hl, Hc⟩⟩, #Hcap⟩
  iunfold auth.authInv at Hinv
  icases Hinv with ⟨-, #Hrev, -⟩
  iinv Hrev with Hi Hclose
  iunfold auth.revInv at Hi
  icases Hi with ⟨%r, >Hr, Hv, >Hcur, Hf⟩
  iunfold auth.revCur at Hcur
  icases Hcur with ⟨%stc, Hc2, %Hrc, %hh, Hq, -⟩
  ihave %Hhh := auth.authHist_rev_agree γa hs hh $$ Hh Hq
  subst Hhh
  imod (auth.authHist_appendL γa hs N hk) $$ [Hh Hq] with ⟨Hh, Hq⟩
  · iframe Hh Hq
  imod (auth.authHist_stateAt_keep γa (hs ++ N) ((hs ++ N).length - 1) stI hi) $$ Hh
    with ⟨Hh, #Hst⟩
  imod Hclose $$ [Hr Hv Hc2 Hq Hf] with -
  · inext; iunfold auth.revInv; iexists r; iframe Hr Hv Hf
    iunfold auth.revCur; iexists stc; iframe Hc2; isplitr
    · ipureintro; exact Hrc
    · iexists hs ++ N; iframe Hq Hcap
  icases (auth.authHist_split γa (hs ++ N)).1 $$ Hh with ⟨Hh, Hlk⟩
  imodintro
  iframe Hst
  isplitl [Hh Hc]
  · iunfold auth.authOwnP; iframe Hh; iexists stl'; iframe Hc; ipureintro; exact Hl
  · iunfold auth.authLockI; iexists hs ++ N; simp only [auth.authLockShare]; iframe Hlk
    ipureintro; exact hl

end bk

/-! ## The premise: boot's and every snapshot backend's (trusted; one premise)

- **The store's `R`** is fixed at the store's construction (`beP`, the readers' `authRd`), so the
  snapshot clause is produced by the boot premise, at the boot's `R`, and carried (TaDa).
- **`Recover`'s own read** needs one `R`: the apply thread's copy of `RD` (in `authApplyResPre`).
- **The open share** `authOpenQ` of every server backend: a quarter, out of the apply thread's half
  (which keeps the other quarter); the old backend's comes back at its release, for its `Close`. -/

section premise
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]

/- (P6.2, 2026-11-03) The Draft's `authFuelB`, `authStepsAny`, `AonDraft.authApplyResPre`/
`authApplyResB` are superseded: the fuel's base is `auth.fuelOk`'s (the user's choice (a)), and lean's
`authApplyResB` carries what the install needs (`authInstallPre`, the reader ticket; `StoreLatest`). -/

/-! ## `Recover` at the install, with auth on (the server-level triple, and its glue) -/

/-- **`ast.Recover(NewAuthBackend(lg, newbe))` at the install, auth on** (the mode-on case of
`authRecoverOk`, gated by `E.authMode` in the merge): the apply thread's auth resource on the old
backend `dO` at the applied log `A`'s state `sa`, the store's tie to the log (`authHistTie`), the
image's committed log `A'` extending `A`, the new backend `dn` opened with its hook frozen, the
client's idle half of its auth buckets `r` holding `A'`'s state (`rbOwnIn … authBkts`; the install
keeps the other buckets' half), its open share for the realization, and the snapshot clause at the
store's `R` (`RD` the checks' reader over it; `Recover` reads with the apply thread's copy, N4):
after `Recover`, the store on the new backend (`authBeOn`), the apply thread's auth resource on it at
`A'`'s state, and **the old backend's open share** (after an update: its release, for the close
goroutine; decision 3c; its reader slots stay the realization's, R4's F1). -/
abbrev authRecoverOn.spec : Prop :=
  ∀ (ast abl lg : Loc) (dO dn : mvcc.KBReal) (W Pk PkO : IProp GF) (f : GoFunc) (fO : GoFunc)
    (r : GMap GoString backend.BktData) (γa : auth.AuthNames) (R RD : IProp GF) (E : apply.AEnv GF)
    (γr : ReadNames) (A A' : List EntryModel) (sa : auth.AuthState),
  E.authMode = .on γa →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.auth ∗
      authBeOn ast dO.be ∗ authApplyResB (.on γa) ast sa dO PkO fO RD ∗
      auth.authInv ast R (.on γa) ∗ authSchemaSnap γa R ∗ ⌜RD = auth.authRd ast R (.on γa)⌝ ∗
      authHistTie E γr srvAuthSt0 ∗ srvRLogLb γr.raft A' ∗
      -- (review R1's F2) the image's committed log a mode-on log (`kvInvOn`'s), whose admin entries
      -- are bounded (`adminKindOk`)
      ⌜A <+: A' ∧ sa = srvAuthAtLog γr.kv srvAuthSt0 A ∧ A'.length < 2 ^ 61 ∧ plainLogOn A'⌝ ∗
      ⌜lg ≠ null⌝ ∗ ablOn abl dn.be lg ∗
      ⌜dn.P.has mvcc.authBI ∧ dn.P.has mvcc.authUsersBI ∧ dn.P.has mvcc.authRolesBI⌝ ∗
      backend.isBackend dn.γB dn.P W Pk dn.be ∗ backend.plHookRO dn.γB f ∗ ⌜f ≠ func.nil⌝ ∗
      backend.rbOwnIn dn.γB authBkts r ∗ authRdSlots dn ∗
      backend.bOpen dn.γB authOpenQ ∗ ⌜authBucketsAt (srvAuthAtLog γr.kv srvAuthSt0 A') r⌝ }}
    (App (Val (ast @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.auth.authStore.ty @!!
      go!"Recover")) (Val #(authBkIface abl)))
  {{ RET #(); |={⊤}=> (authBeOn ast dn.be ∗
      authApplyResB (.on γa) ast (srvAuthAtLog γr.kv srvAuthSt0 A') dn Pk f RD ∗
      backend.bOpen dO.γB authOpenQ) }}

end premise

section glue
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **The glue: `Recover` at the install from the restated `Recover.spec`** (its `on` case): the
tie's catch-up half and the list, the old token retired for the lock's share (`authBkLife`'s
retire, the publication quarter with it), the history caught up before the call
(`authCatchUpFirst`), the snapshot clause at the new backend (fresh `γc`), `Recover`, then the old
backend released (its whole currency from `Recover`, the retired token: its open share and the
publication quarter back); the fuel moved to the image's base. -/
theorem authRecoverOn_glue (hRec : auth.authStore.Recover.spec (GF := GF) (hG := hG)) :
    authRecoverOn.spec (GF := GF) (hG := hG) := by
  intro ast abl lg dO dn W Pk PkO f fO r γa R RD E γr A A' sa hM
  simp only [authApplyResB]
  iintro %Φ ⟨#Hpkg, Hbeon, Hres, #Hinv, #Hsnap, %HRD, #Htie, #HA', %Hp, %Hlg, #Habl, %Hhas,
    #HisB, #Hhk, %Hf, Hrb, Hslots, HbO, %Hbk⟩ HΦ
  obtain ⟨hpre, hsa, hlen, hplain⟩ := Hp
  obtain ⟨hk, hfit, hsmall, hrev⟩ := srvHist_wf γr.kv A' hlen hplain
  icases Hres with ⟨%hs, %P0, %f0, %γc₀, %be, Hfu, Htr, -, HTh, -, Hpub, Htp, %Hlast, -, -, #Hins,
    Hrd⟩
  iunfold auth.authOwnFu at Hfu
  icases Hfu with ⟨Hown, Hfu⟩
  iunfold authInstallPre at Hins
  icases Hins with ⟨#Hlife, -, #Hsteps, -⟩
  iunfold auth.authWHeld at HTh
  icases HTh with ⟨HT, Hbk0⟩
  -- the tie's half: the history a prefix of the image's, the cap at it
  imod authHistTie_catchup E γr γa A A' hs ⊤ hM hpre (by rw [Hlast, hsa]; rfl) (by simp) (by simp)
    $$ [Hown] with ⟨Hown, %Hpfx, #Hcap⟩
  · simp only [srvAuthSt0] at *; iframe Htie HA' Hown
  obtain ⟨hcat, hcl⟩ := catchup_list γr.kv A' hs Hpfx
  -- the old backend's token retired: the lock's share, joined with the admin side's
  iunfold auth.authBkLife at Hlife
  icases Hlife with ⟨#Hret0, #Hrel0, -⟩
  imod Hret0 $$ [HT Hpub] with ⟨⟨%st0, Hlk⟩, Hrtd, Hsucc⟩
  · iframe HT Hpub
  ihave ⟨HoF, -⟩ := auth.authOwn_lockI_join (.on γa) hs st0 $$ Hown Hlk
  ihave #Hcap' : auth.capLb γa (hs ++ (srvHist γr.kv A').drop hs.length) $$ [Hcap]
  · rw [hcat]; iexact Hcap
  -- the history caught up before the call
  imod auth.authCatchUpFirst ast R γa hs ((srvHist γr.kv A').drop hs.length)
      (srvAuthAtLog γr.kv srvAuthSt0 A') ⊤ (by simp)
      (fun x hx => hk x (List.mem_of_mem_drop hx)) hcl $$ [Hinv HoF Hcap']
    with ⟨HoP, Hlk, -⟩
  · iframe Hinv HoF Hcap'
  -- the snapshot clause at the new backend
  ihave #Hsn := Hsnap
  iunfold authSchemaSnap at Hsn
  imod Hsn $$ %lg %abl %dn %W %Pk %f %r %(srvAuthAtLog γr.kv srvAuthSt0 A') [] [] Habl [] HisB Hhk
      [] Hrb Hslots HbO Hlk Hsucc
    with ⟨%γc, #HokH, HCu, #HwR, #HwH, #HLend, HT', #Hlife'⟩
  · ipureintro; exact Hlg
  · ipureintro; exact Hbk
  · ipureintro; exact Hhas
  · ipureintro; exact Hf
  -- the apply thread's reader of the store: its `R`, for `Recover`
  rw [HRD]
  iunfold auth.authRd at Hrd
  icases Hrd with ⟨Hrd1, Hrd2, Hrd3, HR⟩
  -- `Recover`
  iunfold authBeOn at Hbeon
  icases Hbeon with ⟨%abl0, %lg0, -, Hbe, -, -⟩
  iunfold auth.tieRes at Htr
  icases Htr with ⟨%b0, %sc, Hfl, #Hev, Hca, #Hsc, -⟩
  ihave Hen := auth.flagAt_enabledHalf ast (.on γa) b0 $$ [Hfl]
  · iframe Hfl Hev
  ihave Hch := auth.cacheHalf_of_at ast (.on γa) sc $$ Hca Hsc
  wp_apply (hRec ast R (.on γa) hs ((srvHist γr.kv A').drop hs.length)
      (srvAuthAtLog γr.kv srvAuthSt0 A') (authBkIface abl) γc₀ γc)
      $$ [Hbe Hen Hch Htp HR HoP HT' HCu Hbk0]
    as ⟨Htp, HR, Hbe, ⟨Hown, Htr⟩, Hout⟩
  · iframe Hinv Hen Hch Htp HR HokH
    isplitl [HoP]
    · simp only [auth.authOwnPM]; iexact HoP
    isplitl [Hbe]
    · iexists authBkIface abl0; iexact Hbe
    isplitr
    · ipureintro; simp [authBkIface]
    isplitl [HT' HCu Hbk0]
    · simp only [auth.recoverIn]; iframe HT' HCu Hbk0
    simp only [auth.recoverFit]
    ipureintro
    exact ⟨hcl, hfit⟩
  iunfold auth.recoverOut at Hout
  icases Hout with ⟨HT', Hbk', HCu0⟩
  iapply HΦ
  -- the old backend released: its open share and the publication quarter back
  imod Hrel0 $$ [Hrtd HCu0] with ⟨HoO, Hpub⟩
  · iframe Hrtd HCu0
  imodintro
  iframe HoO
  isplitl [Hbe]
  · iunfold authBeOn; iexists abl, lg
    iunfold ablOn at Habl
    icases Habl with ⟨#H1, #H2⟩
    iframe Hbe H1 H2; ipureintro; exact Hlg
  ihave #Hw := auth.authWBackendOk_of_R (authBkIface abl) (.on γa) Pk f (auth.authWTok γc)
    (backend.wbTok dn.γB) $$ HwR
  iexists hs ++ (srvHist γr.kv A').drop hs.length, Pk, f, γc, authBkIface abl
  -- the fuel at the image's base: its admin entries, never paid for with receipts
  isplitl [Hown Hfu]
  · iunfold auth.authOwnFu
    iframe Hown
    iunfold auth.authFuel at Hfu
    icases Hfu with ⟨%k, Hk, -⟩
    iunfold auth.authFuel
    iexists k
    iframe Hk
    ipureintro
    refine auth.fuelOk_of_base _ k A'.length (by omega) ?_
    intro x hx
    rw [hcl] at hx
    cases hx
    exact ⟨by simp only [srvAuthSt0] at *; omega, hsmall⟩
  iframe Htr Hw Hpub Htp
  isplitl [HT' Hbk']
  · iunfold auth.authWHeld; iframe HT' Hbk'
  isplitr
  · iexists _; iexact Hlife'
  isplitr
  · ipureintro; exact hcl
  -- the hook facts at the new backend's frozen hook: its clause and the admin steps at any backend
  isplitr
  · iunfold authWBackendAt
    iintro !> %abl' %lg' #Hb #Hl
    iapply auth.authWBackendOk_of_R
    iunfold authWAtHook at HwH
    iapply HwH $$ %abl' %lg' %W %Pk %f [] HisB Hhk []
    · iunfold ablOn; iframe Hb Hl
    ipureintro; exact Hf
  isplitr
  · iunfold authStepsAny at Hsteps
    iapply Hsteps
  isplitr
  · iunfold authInstallPre; iframe Hlife' HwH Hsteps HLend
  iunfold auth.authRd; iframe Hrd1 Hrd2 Hrd3 HR

end glue

section install
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **The server's auth store with its snapshot clause** (persistent; auth on; decision 8:
`NewServer`, `bootOk` and `isServerRunC` carry it, as they do `#HmetaSnap`): the store its
`authStore` field holds, its invariant at its backend's read resource `R`, the snapshot clause at
`R`, and the apply environment's reader resource `RD` the checks' `authRd` over `R`. (Until this
round the draft took the invariant and the clause at `RD` itself: a bug of the draft, `authInv`'s
`R` being the backend's read resource and the server's `E.RD` the checks' `authRd ast R`, as
`authStoreKit_on` builds it.) -/
def srvAuthSnapOk (s : Loc) (γa : auth.AuthNames) (RD : IProp GF) : IProp GF :=
  iprop(∃ (ast : Loc) (R : IProp GF), srvAuthStoreAddr s ↦□ auth.authIface ast ∗
    auth.authInv ast R (.on γa) ∗ authSchemaSnap γa R ∗
    ⌜RD = auth.authRd ast R (.on γa)⌝)

instance srvAuthSnapOk_persistent (s : Loc) (γa : auth.AuthNames) (RD : IProp GF) :
    Persistent (srvAuthSnapOk (GF := GF) s γa RD) := by
  unfold srvAuthSnapOk; infer_instance

/-- **The image's auth facts by the auth mode** (F9, the user's decision of 2026-11-03: one
spec, `applySnapshot.specSnapM`, over `E.authMode`): `off`, lean's `hauthb` (the auth buckets at `authBoot`/empty); `on`,
the auth buckets in the table, the image's auth buckets holding the state after its log `A'`, below
raft's bound (`snapRecv_imageOn`'s); `any`, nothing (excluded by the specs' `E.authMode ≠ .any`).
(The lease-expiry plan's S2–S4, review r2 S2, DRAFT 2026-11-06: the `on` arm no longer repeats
`A <+: A'`, a premise of `specSnapM` in every mode.) -/
def snapAuthImgM (M : auth.AuthMode) (γr : ReadNames) (P : backend.BParams) (D : backend.Data)
    (A A' : List EntryModel) : Prop :=
  match M with
  | .off => ((backend.rbData P D).lookup go!"auth").getD ∅ = authBoot ∧
      ((backend.rbData P D).lookup go!"authUsers").getD ∅ = ∅ ∧
      ((backend.rbData P D).lookup go!"authRoles").getD ∅ = ∅
  | .on _ => (P.has mvcc.authBI ∧ P.has mvcc.authUsersBI ∧ P.has mvcc.authRolesBI) ∧
      authBucketsAt (srvAuthAtLog γr.kv srvAuthSt0 A') (backend.rbData P D) ∧
      A'.length < 2 ^ 61
  | .any => True

/-- **The rest model's buckets after the snapshot's entries `A'`, by the mode** (F9; S8d's named
premise): the image's rest buckets, the lessor's and the alarm store's aside (the lease bucket
the records', `imageLeasesAt`; the alarm bucket empty); with auth on, all but the auth ones (the rest model does not model the admin writes:
its auth buckets stay `authBoot`). -/
def snapRestImgM (on : Bool) (γr : ReadNames) (P : backend.BParams) (D : backend.Data)
    (A' : List EntryModel) : Prop :=
  match on with
  | false => (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A')).bk =
      <[go!"alarm" := ∅]> (<[go!"lease" := ∅]> (backend.rbData P D))
  | true => ∀ n, ¬ auth.authBkts n →
      (restModel γr.kv.c0 γr.raft.raft.boot (γr.raft.pre ++ A')).bk.lookup n =
      (<[go!"alarm" := ∅]> (<[go!"lease" := ∅]> (backend.rbData P D))).lookup n

/-- **The auth store's `Recover` facts, by the mode** (F9): `off`, lean's `authRecoverOk`; `on`,
the store's invariant at the server's read resource with the snapshot clause (`srvAuthSnapOk`);
`any`, nothing (excluded by the specs). (Review r2 S2, DRAFT 2026-11-06: the `on` arm no longer
repeats the image's committed log `srvRLogLb … A'`, a pre of `specSnapM` in every mode.) -/
def snapAuthResM (M : auth.AuthMode) (s ast : Loc) (RD : IProp GF) (γr : ReadNames)
    (A' : List EntryModel) : IProp GF :=
  match M with
  | .off => authRecoverOk ast
  | .on γa => srvAuthSnapOk s γa RD
  | .any => iprop(True)

instance snapAuthResM_persistent (M : auth.AuthMode) (s ast : Loc) (RD : IProp GF)
    (γr : ReadNames) (A' : List EntryModel) :
    Persistent (snapAuthResM (GF := GF) M s ast RD γr A') := by
  cases M <;> unfold snapAuthResM <;> infer_instance

/-- **`applySnapshot.specSnapM`'s auth facts in the mode `on`**, from `srvSnapRO`'s row
(`authSnapKitM`). -/
theorem snapAuthResM_on (s ast : Loc) (E : apply.AEnv GF) (γr : ReadNames) (A' : List EntryModel)
    (γa : auth.AuthNames) (hM : E.authMode = .on γa) :
    srvAuthStoreAddr s ↦□ auth.authIface ast ∗ authSnapKitM E.authMode ast E.RD ⊢
      snapAuthResM E.authMode s ast E.RD γr A' := by
  rw [hM]
  simp only [authSnapKitM, snapAuthResM]
  iintro ⟨#Ha, ⟨%R, #Hi, #Hs, %Hrd⟩⟩
  iunfold srvAuthSnapOk
  iexists ast, R
  iframe Ha Hi Hs
  ipureintro; exact Hrd

end install

end EtcdGrove
end Perennial
