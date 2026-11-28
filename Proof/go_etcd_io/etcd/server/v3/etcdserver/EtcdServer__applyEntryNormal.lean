/-
Proof of `Spec/EtcdServer__applyEntryNormal.lean`. Lean-first (no Rocq counterpart).

`wp_proofOn` (the auth plan's E3o) proves `specOn`, the step with auth on: the mode-off proof's
structure, with the mode-`on` model (`kvEntryOn`, `kvAppliedOn`) and three applications of an entry
with data: a KV request through the latest-state triple (`apply.Apply.kvSpecL`, the verdict at the
auth row's history, lent out of the row by `auth.ownFuT_lend`), a cluster request through
`apply.Apply.spec` (the log kept), an admin request through the auth row's admin steps
(`adminEntryOn.spec`, the row's history one admin step later).

The replay (`v3` false, R2d'a, Q23 (a), 2026-11-06; until then `ApplyEntryNormalR.lean`'s
`wp_proofRepOff`/`wp_proofRepOn` of two separate specs): `apply.Apply`'s premises that only
`dispatch`'s `v3` cases read are guarded by `v3` (Q22 (1) (a)), so the replay gives them nothing; the
rest buckets at the backend's table (`srvRestRp`) are `apply.Apply`'s `E.RO`, half and ids, and come
back with the attribute write (`restEntryV2`).
-/
module

public import Proof.go_etcd_io.etcd.pkg.v3.idutil.Lemmas
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__applyEntryNormal
public import Spec.go_etcd_io.raft.v3.raftpb.Entry__GetIndex
public import Spec.go_etcd_io.raft.v3.raftpb.Entry__GetTerm
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.cindex.consistentIndex__ConsistentIndex
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.cindex.consistentIndex__SetConsistentIndex
public import Spec.go_etcd_io.etcd.pkg.v3.notify.Notifier__Notify
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__isLeader
public import Spec.go_etcd_io.etcd.server.v3.config.ServerConfig__ElectionTimeout
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.apply.Apply
public import Spec.errors.Is
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3alarm.AlarmStore__Get
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Logger
public import Spec.go_uber_org.zap.String
public import Spec.go_uber_org.zap.Int64
public import Spec.go_uber_org.zap.Error
public import Spec.github_com.dustin.go_humanize.Bytes
public import Spec.go_uber_org.zap.Logger__Warn
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__GoAttach
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.GoAttachTok
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__MemberID
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.NoSpaceDead
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.RestOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVApply
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ApplyCmpArm
public import Proof.github_com.mit_pdos.etcd_grove.PkgInitMemo
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AdminEntryOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.NoSpaceDeadOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.ApplyFnKVL
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.ApplyRec
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ModeSpecs
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.UberOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthTie

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.cindex go_etcd_io.etcd.server.v3.etcdserver
  go_etcd_io.etcd.server.v3.storage

section lemmas
variable [GooseExts]

/-- (auth-lease S3a rev 7; S3a2 §4) **A non-admin entry of the auth-on log at the lease mode `lm`** is one the
generic apply arms cover (`plainOrCmpG lm`: plain, an admitted grant or revocation) or a leased put or
transaction (read through `kvCover`'s facts), and no admin one. -/
theorem plainOrCmpG_of_entryOn (lm : lease.Mode) (rq : apply.IRRModel)
    (h : (plainReqL lm rq ∧ noZeroEnds rq ∧ kvShapeAll rq) ∨ grantPropOk lm rq ∨ revokePropOk lm rq) :
    (plainOrCmpG lm rq ∨ kvCover rq) ∧ ¬ apply.adminKindOk rq := by
  rcases h with ⟨hpL, -, -⟩ | hg | hr
  · have hpk := (plainReqL_facts lm rq hpL).2.2
    refine ⟨?_, fun h => adminKindOk_notPutget rq h hpk⟩
    rcases plainReqL_cases lm rq hpL with hp | -
    · exact Or.inl (Or.inl (Or.inl hp.1))
    · exact Or.inr (kvCover_of_plainReqL lm rq hpL)
  · exact ⟨Or.inl (Or.inr (Or.inl hg)), fun h => adminKindOk_nonGrant rq h hg.2.1⟩
  · exact ⟨Or.inl (Or.inr (Or.inr hr)), fun h => adminKindOk_nonRevoke rq h hr.2.1⟩

/-- **`Apply`'s rest image at `v3 = false`** (R2d'a A3, DRAFT): the request's attribute write
(`restAfter … false`), whatever the outcome, for a request of a committed entry's shape. -/
theorem restOutA_false (lm : lease.Mode) (rq : apply.IRRModel) (x x' : apply.ApplyKV)
    (out : apply.ApplyOut) (T : List w64) (t : w64) (r : apply.RestM) (hp : plainOrCmpG lm rq ∨ kvCover rq)
    (hs : apply.applyStep rq false x x' out) :
    apply.revokeRestA T rq false out (apply.grantRestA t rq false out (apply.restOut rq false out r)) =
      apply.restAfter rq false r := by
  rw [restOut_plainOrCmpG lm rq false x x' out r hp hs]
  cases out <;> simp [apply.revokeRestA, apply.grantRestA, apply.revokeRest_noV3,
    apply.grantRest_noV3]

/-- `Apply`'s ids at `v3 = false`: unchanged. -/
theorem idsA_false (rq : apply.IRRModel) (out : apply.ApplyOut) (L : List w64) :
    apply.revokeIdsA rq false out (apply.grantIdsA rq false out L) = L ∧
      apply.grantIdsA rq false out L = L := by
  cases out <;> simp [apply.revokeIdsA, apply.grantIdsA, apply.revokeIds_noV3, apply.grantIds_noV3]

/-- A request's v2-only step is the entry's (`restEntryV2`). -/
theorem restEntryV2_req (m : EntryModel) (rq : apply.IRRModel) (r : apply.RestM)
    (ht : m.typ = W32 0) (hd : m.data ≠ []) (hdec : apply.irrDecode m.data = some rq) :
    restEntryV2 m r = apply.restAfter rq false r := by
  unfold restEntryV2; rw [if_pos ht, if_neg hd, hdec]

/-- An entry with no data: nothing. -/
theorem restEntryV2_nodata (m : EntryModel) (r : apply.RestM) (ht : m.typ = W32 0)
    (hd : m.data = []) : restEntryV2 m r = r := by
  unfold restEntryV2; rw [if_pos ht, if_pos hd]

/-- (auth-lease S4 item 7b) A backend outcome of a request that is neither a KV write nor a revocation keeps the log. -/
theorem backendStep_keep (rq : apply.IRRModel) (log : mvcc.Log) (oc : apply.Outcome)
    (hkv : apply.isKVKind (apply.dispatchKind rq) = false) (hr : apply.dispatchKind rq ≠ .leaseRevoke)
    (hb : apply.backendStep rq log oc) : oc.logAfter log = log := by
  revert hb
  unfold apply.backendStep
  cases hd : apply.dispatchKind rq <;> intro hb <;> rw [hd] at hkv hr <;> simp only [apply.isKVKind] at hkv <;>
    first
    | exact absurd hkv (by decide)
    | exact absurd rfl hr
    | exact hb.elim
    | (subst hb; rfl)
    | (rcases hb with rfl | rfl <;> rfl)

/-- (auth-lease S4 item 7b) **Past the auth layer, every backend outcome is one the verdict admits**: the latest-state
verdict `kvOutL` at an outcome other than the auth layer's rejection passed every check, so it admits each outcome of
the inner chain. -/
theorem kvOutL_of_pass (M : auth.AuthMode) (hs : List auth.AuthState) (ai : auth.AuthInfoM) (ci : apply.Chain)
    (rq : apply.IRRModel) (log : mvcc.Log) (oc oc' : apply.Outcome) (h : apply.kvOutL M hs ai ci rq log oc)
    (hne : oc ≠ .rejected .auth) (hb : apply.chainStep apply.backendStep ci rq log oc') :
    apply.kvOutL M hs ai ci rq log oc' := by
  unfold apply.kvOutL at h ⊢
  generalize apply.dispatchKind rq = k at h ⊢
  cases k <;> simp only at h ⊢ <;> try exact h.elim
  · obtain ⟨o, ho, e, he, h⟩ := h
    refine ⟨o, ho, e, he, ?_⟩
    rcases h with ⟨rfl, -⟩ | ⟨-, hp⟩
    · exact absurd rfl hne
    · exact Or.inr ⟨hb, hp⟩
  · obtain ⟨o, ho, h⟩ := h
    refine ⟨o, ho, ?_⟩
    rcases h with ⟨rfl, -⟩ | ⟨-, hp⟩
    · exact absurd rfl hne
    · exact Or.inr ⟨hb, hp⟩
  · obtain ⟨o, ho, e, he, h⟩ := h
    refine ⟨o, ho, e, he, ?_⟩
    rcases h with ⟨rfl, -⟩ | ⟨-, hp⟩
    · exact absurd rfl hne
    · exact Or.inr ⟨hb, hp⟩
  · obtain ⟨o, ho, h⟩ := h
    refine ⟨o, ho, ?_⟩
    rcases h with ⟨rfl, -⟩ | ⟨-, hp⟩
    · exact absurd rfl hne
    · exact Or.inr ⟨hb, hp⟩
  · obtain ⟨o, ho, h⟩ := h
    refine ⟨o, ho, ?_⟩
    rcases h with ⟨rfl, -⟩ | ⟨-, hp⟩
    · exact absurd rfl hne
    · exact Or.inr ⟨hb, hp⟩

end lemmas

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem ciEff_stLoaded (γ : ApplyNames) (st : ApplyState) :
    ciEff γ (stLoaded γ st).k = ciEff γ st.k := by
  unfold stLoaded; split <;> simp_all [ciEff]

theorem stLoaded_fields (γ : ApplyNames) (st : ApplyState) :
    (stLoaded γ st).p = st.p ∧ (stLoaded γ st).eff = st.eff ∧
      (stLoaded γ st).pending = st.pending := by
  unfold stLoaded; split <;> exact ⟨rfl, rfl, rfl⟩

/-- **The writer facts of an applier state** (`srvApplyKV_writer`'s, at the apply thread's window, `srvApplyKVW`,
under the store invariant alone: for a state unpacked from `srvApplyKV`/`srvApplyKVOn`, after `apply.Apply`; strict
M1, in place of the sole writer's `applyKV_idxCert`). -/
theorem applyKV_writer [mvccSem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
    (Hp : mvcc.api.persistent.law (GF := GF)) (Hr : mvcc.api.mvccState_reachable.law (GF := GF))
    (E : apply.AEnv GF) (hw : envWitOk E) (ua : GoInterface) (x : apply.ApplyKV) :
    □ srvApi.kvStoreInvG E.kv E.γ E.Nx E.Cp E.γs ⊢ srvApplyKVW E ua x ={⊤}=∗
      srvApplyKVW E ua x ∗ srvApi.kvLogLb E.γs x.log ∗ E.Nx x.log ∗ ⧖ (mvcc.logCh x.log) ∗
      ⌜∃ c, mvcc.api.MvccReachable (srvApi.stAt x.log c) ∧ x.log.length + 3 ≤ 2 ^ 63⌝ := by
  obtain ⟨h1, h2, h3, h4⟩ := hw
  iintro #Hs Hkv
  iunfold srvApplyKVW at Hkv
  icases Hkv with ⟨%wn, %Hwn, Hkv⟩
  iunfold apply.applyKV at Hkv
  icases Hkv with ⟨%p, %Hp', Ho, Hk, Hc⟩
  iunfold apply.kvOwn at Hk
  icases Hk with ⟨⟨%c, Hw⟩, Hk⟩
  imod srvApi.writer_facts E.Nx E.Cp Hp Hr E.kv E.γ E.γs x.log c $$ Hs Hw with
    ⟨Hw, #Hlb, #Hnx, #Hrc, %Hre⟩
  imodintro
  iframe Hlb Hnx Hrc
  isplitl
  · iunfold srvApplyKVW
    iexists wn
    isplitr
    · ipureintro; exact Hwn
    iunfold apply.applyKV
    iexists p
    iframe Ho Hc
    isplitr
    · ipureintro; exact Hp'
    iunfold apply.kvOwn
    iframe Hk
    iexists c
    iframe Hw
  · ipureintro; exact ⟨c, Hre⟩

/-- The applier state at a window the server's environment allows (`srvApplyKVW`). -/
theorem srvApplyKVW_of (E : apply.AEnv GF) (wn : Option lease.LWin) (ua : GoInterface) (x : apply.ApplyKV)
    (h : E.lg = false → wn = none) :
    apply.applyKV { E with win := wn } ua x ⊢ srvApplyKVW E ua x := by
  iintro H
  iunfold srvApplyKVW
  iexists wn
  iframe H
  ipureintro; exact h

/-- **The entry's window** (auth-lease S4 item 7b): in a cluster that grants leases, the apply thread opens the window
of the entry, its target the items of the committed model log `Lt` after it (`srvApi.applyKV_push`); otherwise the
state as it is (no window). -/
theorem srvApplyKVW_push (Hp : mvcc.api.persistent.law (GF := GF)) (Hr : mvcc.api.mvccState_reachable.law (GF := GF))
    (E : apply.AEnv GF) (Fr : Prop) (hq : E.stq = (1 : Qp).half.half) (hw : envWitOk E)
    (ua : GoInterface) (x : apply.ApplyKV) (Lt : mvcc.Log) (hlt : x.log <+: Lt) :
    □ srvApi.kvStoreInvG (GF := GF) E.kv E.γ E.Nx E.Cp E.γs ∗ srvApi.winTieRes E Fr ∗
      (⌜E.lg = true⌝ → □ E.Nx Lt) ∗ srvApplyKVW E ua x ={⊤}=∗
      ∃ wn : Option lease.LWin, ⌜(E.lg = false → wn = none) ∧
        (E.lg = true → ∃ s, wn = some (s, srvApi.itemsOfLog Lt))⌝ ∗ apply.applyKV { E with win := wn } ua x := by
  obtain ⟨h1, h2, h3, h4⟩ := hw
  iintro ⟨#Hk, #Ht, Hnx, Ha⟩
  iunfold srvApplyKVW at Ha
  icases Ha with ⟨%w0, %Hw0, Ha⟩
  cases hlg : E.lg
  · imodintro
    iexists w0
    iframe Ha
    ipureintro; exact ⟨fun _ => Hw0 hlg, fun h => by cases h⟩
  · ihave #Hnx := Hnx $$ %rfl
    imod (srvApi.applyKV_push Hp Hr E Fr hq w0 ua x Lt hlt) $$ [Hk Ht Ha Hnx] with ⟨%s, Ha⟩
    · iframe Hk Ht Ha Hnx
    imodintro
    iexists some (s, srvApi.itemsOfLog Lt)
    iframe Ha
    ipureintro; exact ⟨fun h => absurd h (by decide), fun _ => ⟨s, rfl⟩⟩

/-- `winTgt` at the entry's window: every backend outcome lease-exact at `L` leaves the committed model log `Lt`. -/
theorem winTgt_of_log (wn : Option lease.LWin) (rq : apply.IRRModel) (log Lt : mvcc.Log) (L : List w64)
    (hw : ∀ s T, wn = some (s, T) → T = srvApi.itemsOfLog Lt)
    (h : ∀ oc, apply.backendStep rq log oc → apply.leaseExactL L rq log oc → oc.logAfter log = Lt) :
    apply.winTgt wn rq log L := by
  intro s T hs oc hb he
  rw [hw s T hs, h oc hb he]

/-- `kvAppliedL`'s raft witness (`kvAppliedL_nx`), the state kept. -/
theorem kvAppliedL_nx' (γ : ServerRaftNames) (γk : KVNames) (B : List EntryModel) (l : mvcc.Log)
    (hk : mvcc.LogPutsLe etcdKeyMax (kvModel γk B)) :
    kvAppliedL (GF := GF) γ γk B l ⊢ kvAppliedL γ γk B l ∗ kvNxOff γ γk l := by
  iintro H
  iunfold kvAppliedL at H
  icases H with ⟨#HB, Hhi, #Hc, %Hl⟩
  isplitl
  · iunfold kvAppliedL; iframe HB Hhi Hc; ipureintro; exact Hl
  · iunfold kvNxOff; iexists B; iframe HB; ipureintro; exact ⟨Hl.symm, Hl ▸ hk⟩

/-- `kvAppliedLOn`'s raft witness in the mode `on` (`kvNxOn`), the state kept. -/
theorem kvAppliedLOn_nx (γ : ServerRaftNames) (γk : KVNames) (st₀ : auth.AuthState)
    (B : List EntryModel) (s : OnState)
    (hk : mvcc.LogPutsLe etcdKeyMax (kvModelOn γk st₀ B)) :
    kvAppliedLOn (GF := GF) γ γk st₀ B s ⊢ kvAppliedLOn γ γk st₀ B s ∗ kvNxOn γ γk st₀ s.2.1 := by
  iintro H
  iunfold kvAppliedLOn at H
  icases H with ⟨#HB, Hhi, #Hc, %Hl⟩
  isplitl
  · iunfold kvAppliedLOn; iframe HB Hhi Hc; ipureintro; exact Hl
  · iunfold kvNxOn; iexists B; iframe HB; ipureintro; rw [Hl]; exact ⟨rfl, hk⟩

/-- **The tokens `apply.Apply` takes, at the server's tie** (`apply.bkToks`): the write-back token
of the tie's backend `d` (`srvWT_at`), the apply thread's reader token of it (`srvBeOwn`'s), and,
with `v3`, the hook's run at `d`'s batch lock with the caller's update. -/
theorem bkToks_srv (v3 : Bool) (E : apply.AEnv GF) (d : mvcc.KBReal) (hd : E.BkTie = srvBkTie d)
    (Pre Q Post : IProp GF) :
    apply.bkWT d ∗ apply.bkRT d ∗
      (if v3 then iprop(mvcc.api.hookRun (E.Pk d) E.f Pre Q ∗ (Q ={⊤}=∗ E.Pk d ∗ Post))
       else iprop(True)) ⊢ apply.bkToks v3 E Pre Q Post := by
  iintro ⟨Hw, Hr, Hc⟩
  iunfold apply.bkToks
  rw [hd]
  iintro %B HT
  iunfold srvBkTie at HT
  icases HT with %hB
  subst hB
  iframe Hw Hr Hc
  iunfold srvBkTie; ipureintro; rfl

/-- **The applier state with the tie's tokens, as `kvSpecL` takes it** (`apply.kvOwnPre_of_toks`). -/
theorem applyKV_kvOwnPre (v3 : Bool) (E : apply.AEnv GF) (wn : Option lease.LWin) (ua : GoInterface)
    (x : apply.ApplyKV) (Pre Q Post : IProp GF) :
    apply.applyKV { E with win := wn } ua x ∗ apply.bkToks v3 E Pre Q Post ∗ Pre ⊢
      ∃ p : Loc, ⌜ua = interface.mkOk
          (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.apply.uberApplier.ty) #p⌝ ∗
        apply.uberOwn { E with win := wn } p x.chain ∗ apply.kvOwnPre v3 { E with win := wn } x.log Pre Q Post ∗
        apply.cmpOwn { E with win := wn } x.crev := by
  have h : apply.bkToks v3 E Pre Q Post = apply.bkToks v3 { E with win := wn } Pre Q Post := rfl
  rw [h]
  iintro ⟨Hkv, Ht, HP⟩
  iunfold apply.applyKV at Hkv
  icases Hkv with ⟨%p, %Hp, Ho, Hk, Hc⟩
  iexists p
  iframe Ho Hc
  isplitr
  · ipureintro; exact Hp
  iapply apply.kvOwnPre_of_toks
  iframe Hk Ht HP

set_option hygiene false in
/-- The deferred update after an entry processed with no writes (state `{st with p := i}`):
`ci` is below `i`, so it is advanced to `i`; then the postcondition. -/
local macro "tail_skip" : tactic => `(tactic| (
  wp_apply_core (wp_ci_get hC γ ci b { st with p := m.index } Hp) $$ [Hst Hbe] [-]
  · iframe Pci Hci Hinv Hst Hbe
  iintro ⟨Hst, Hbe⟩
  (try wp_auto)
  wp_apply hGI e m
  · iexact He
  (try wp_auto)
  rw [decide_eq_true hce]
  (try wp_auto)
  wp_apply hGI e m
  · iexact He
  wp_apply hGT e m
  · iexact He
  (try wp_auto)
  obtain ⟨hlp, hle, hlpend⟩ := stLoaded_fields γ { st with p := m.index }
  wp_apply_core (wp_ci_advance hS γ ci (stLoaded γ { st with p := m.index }) m.index m.term
      (by rw [hlpend]; exact Hp) (by rw [hlp]; exact Int.le_refl _)
      (by rw [ciEff_stLoaded]; exact hce)) $$ [Hst] [-]
  · iframe Pci Hci Hinv Hst
  iintro Hst
  (try wp_auto)
  iapply HΦ
  iframe Hbe Hlr Hgr Hmr HFS HKV
  (try simp only [↓reduceIte])
  iframe Happ
  (try iframe Htok)
  iexists st.eff
  have hfin : { stLoaded γ { st with p := m.index } with k := m.index } =
      ({ k := m.index, p := m.index, eff := st.eff, pending := false } : ApplyState) := by
    unfold stLoaded; split <;> simp [Hp]
  rw [hfin] at *
  iexact Hst))

set_option hygiene false in
/-- The deferred update after an entry whose writes went through the hook (state
`⟨i, i, i, false⟩`): `ci` is `i`, nothing to do; then the postcondition. -/
local macro "tail_done" : tactic => `(tactic| (
  wp_apply_core (wp_ci_get hC γ ci b ⟨m.index, m.index, m.index, false⟩ rfl) $$ [Hst Hbe] [-]
  · iframe Pci Hci Hinv Hst Hbe
  iintro ⟨Hst, Hbe⟩
  (try wp_auto)
  wp_apply hGI e m
  · iexact He
  (try wp_auto)
  rw [decide_eq_false (by unfold ciEff; rw [ite_eq_right hi0]; exact Int.lt_irrefl _)]
  (try wp_auto)
  iapply HΦ
  iframe Hbe Hlr Hgr Hmr HFS HKV
  (try simp only [↓reduceIte])
  iframe Happ
  (try iframe Htok)
  iexists m.index
  have hfin : stLoaded γ ⟨m.index, m.index, m.index, false⟩ =
      ({ k := m.index, p := m.index, eff := m.index, pending := false } : ApplyState) := by
    unfold stLoaded; rw [ite_eq_right hi0]
  rw [hfin] at *
  iexact Hst))

set_option hygiene false in
/-- `Trigger(id, ar)`'s premise: every expectation registered under the entry's id is the
proposer's `resultΨ` of the entry's request (the claims agree), which the result meets. -/
local macro "trig" : tactic => `(tactic| (
  iright; iright
  iunfold waitTrig
  iintro %Ψ HR
  iunfold reqWaitR at HR
  icases HR with ⟨%d', %rq', %γf', %F', #Hcl', #Hfl', %Hp'⟩
  obtain ⟨hd', hΨ, -⟩ := Hp'
  subst hΨ
  -- (R2c) a waiter's claim is the incarnation's: the entry's claim is of its key
  ihave %Hdd := idClaim_agree_entry ρ.ids id d' m.data γf' γf k0 $$ Hcl' Hcl0
  obtain ⟨Hdd, Hγ, hpx⟩ := Hdd
  replace hpx := hpx.symm
  subst Hdd Hγ
  -- (D21e (A)) a registered id is of the member's prefix: the floor its claim recorded
  ihave #HfF := HfFo $$ %hpx
  ihave %HFF := floorAt_agree γf' F' F $$ Hfl' HfF
  subst HFF
  rw [hdec] at hd'
  cases hd'
  iunfold resultΨ
  iexists ar, x.log
  isplitr
  · ipureintro; rfl
  isplitl [HTr]
  · iexact HTr
  isplitl
  rotate_left
  · iexact HeW
  iunfold resultIsW
  isplitr
  · ipureintro; exact Har0
  iexists x, x', out
  iframe HRes Hcert HMint Hcx' Hrcx' HGA HVA
  isplitr
  · ipureintro; exact ⟨Hstep0.1, Hstep0.2, rfl, Hwvf hpx⟩
  isplitl [Hcm HLpre Hmono]
  · iunfold appliedWit
    iexists m.index
    rw [Hrd]
    iframe Hcm HLpre Hmono
  ipureintro; exact Hwfl))

set_option hygiene false in
/-- The deferred update in either state. -/
local macro "tail_any" : tactic => `(tactic| (
  rcases hst1 with rfl | rfl
  · tail_done
  · tail_skip))

/-- `apply.Apply.specRec` at the apply thread's lessor window `wn` (auth-lease S4 item 7b, 2026-11-17): the triple at
`{ E with win := wn }`, with the resources that do not read the window at `E` (definitionally the same). -/
theorem Apply_specRec_win (h : apply.Apply.specRec (GF := GF) (hG := hG)) :
    ∀ (lg e : Loc) (m : EntryModel) (ua w : GoInterface) (v3 : Bool) (E : apply.AEnv GF) (wn : Option lease.LWin)
    (Pre Q Post : IProp GF) (x : apply.ApplyKV) (rq : apply.IRRModel) (id : w64) (RD : IProp GF)
    (K G : Option GName → w64 → IProp GF) (ot : Option GName) (F : mvcc.Log) (rs : apply.RestM)
    (T U : List w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
      apply.applierFor ua E ∗ waitOk w RD K G ∗ RD ∗ K ot id ∗ zapLoggerOk lg ∗ entryAt e m ∗
      apply.bkToks v3 E Pre Q Post ∗ Pre ∗
      apply.applyKV { E with win := wn } ua x ∗ apply.certPreV v3 E x.chain rq x.log ∗
      ⌜apply.irrDecode m.data = some rq ∧ apply.irrId rq = some id ∧ apply.rqOk E.lm x.log rq ∧
        apply.dispatchOk E.authOn rq ∧ (v3 = true → apply.cmpAdmit x.log rq) ∧
        apply.restReqOk rq rs⌝ ∗
      ⌜(E.lg = true → v3 = true → apply.winTgt wn rq x.log T) ∧ (E.lg = false → wn = none)⌝ ∗
      □ (⌜v3 = true⌝ → apply.cmpPermRq E rq) ∗ □ (⌜v3 = true⌝ → apply.grantPermRq E rq) ∗
      apply.ltHalf E T ∗ apply.everOwn E U ∗ □ (⌜v3 = true⌝ → apply.grantFresh E rq U) ∗
      apply.revokeOwn E rq ∗ apply.applyTok E ∗
      srvApi.kvLogLb E.γs F ∗ E.FS ∗ (if v3 then apply.ciSplit E Pre else iprop(True)) ∗ E.RO rs }}
    (App (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.apply.Apply))
      (Val #lg)) (Val #e)) (Val #ua)) (Val #w)) (Val #v3))
  {{ (ar : Loc) (id' : w64), RET (PairV #ar #id'); RD ∗ E.FS ∗ apply.applyTok E ∗ apply.bkRTOf E ∗
      (if v3 then iprop(Post ∨ Pre) else Pre) ∗ apply.resultErrOk ar ∗ apply.resTrace ar ∗
      ⌜id' = id⌝ ∗
      ∃ (x' : apply.ApplyKV) (out : apply.ApplyOut), apply.applyKV { E with win := wn } ua x' ∗
        apply.ltHalf E (apply.revokeIdsA rq v3 out (apply.grantIdsA rq v3 out T)) ∗
        apply.everOwn E (apply.grantIdsA rq v3 out U) ∗ apply.revokeOwn E rq ∗
        (∃ t : w64, ⌜apply.grantTTLOk rq t⌝ ∗ E.RO (apply.revokeRestA T rq v3 out
          (apply.grantRestA t rq v3 out (apply.restOut rq v3 out rs)))) ∗
        ⌜apply.grantOutOkA x.chain rq v3 T out⌝ ∗ apply.grantResA E rq out ar ∗
        apply.revokeAnsRA E rq out ar ∗
        ⌜apply.applyStep rq v3 x x' out ∧ apply.applyFloorOk rq v3 F x.log out⌝ ∗
        apply.applyResultIs rq v3 x.log ar out ∗ apply.applyAuthRes E.authMode x.chain rq v3 out ∗
        (⌜out.waived = false⌝ ∨ G ot id) }} :=
  fun lg e m ua w v3 E wn Pre Q Post x rq id RD K G ot F rs T U => h lg e m ua w v3 { E with win := wn } Pre Q Post x rq id RD K G ot F rs T U

set_option maxHeartbeats 2400000 in
theorem EtcdServer.applyEntryNormal.wp_proofOff
    (hGI : raftpb.Entry.GetIndex.spec (GF := GF) (hG := hG))
    (hGT : raftpb.Entry.GetTerm.spec (GF := GF) (hG := hG))
    (hC : consistentIndex.ConsistentIndex.spec (GF := GF) (hG := hG))
    (hS : consistentIndex.SetConsistentIndex.spec (GF := GF) (hG := hG))
    (hN : notify.Notifier.Notify.spec (GF := GF) (hG := hG))
    (hL : EtcdServer.isLeader.spec (GF := GF) (hG := hG))
    (hE : config.ServerConfig.ElectionTimeout.spec (GF := GF) (hG := hG))
    (hA0 : apply.Apply.spec (GF := GF) (hG := hG))
    (hUb : apply.uberApplier.Apply.spec (GF := GF) (hG := hG))
    (hIs : errors.Is.spec (GF := GF) (hG := hG))
    (hAG : v3alarm.AlarmStore.Get.spec (GF := GF) (hG := hG))
    (hLg : EtcdServer.Logger.spec (GF := GF) (hG := hG))
    (hZS : zap.String.spec (GF := GF) (hG := hG))
    (hZI : zap.Int64.spec (GF := GF) (hG := hG))
    (hZE : zap.Error.spec (GF := GF) (hG := hG))
    (hHB : go_humanize.Bytes.spec (GF := GF) (hG := hG))
    (hW : zap.Logger.Warn.spec (GF := GF) (hG := hG))
    (hGA : EtcdServer.GoAttach.spec (GF := GF) (hG := hG))
    (hMID : EtcdServer.MemberID.spec (GF := GF) (hG := hG))
    [mvccSem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
    (hPers : mvcc.api.persistent.law (GF := GF) (hG := hG))
    (hReach : mvcc.api.mvccState_reachable.law (GF := GF) (hG := hG)) :
    EtcdServer.applyEntryNormal.specOff (GF := GF) (hG := hG) := by
  have hA := apply.Apply.spec_rec hA0 hUb
  have hGI := wp_entryAt_GetIndex hGI
  have hGT := wp_entryAt_GetTerm hGT
  intro s γ ci TM E ρ b e m st v3 x γr ot v A A₀ r _hoff
  cases v3
  · -- (R2d'a, Q23 (a)) a replay: v2-only, the rest buckets at the backend's log
    simp only [Bool.false_eq_true, ↓reduceIte]
    wp_start as ⟨#Hsrv, #Hewo, #He, Hst, Hbe, Hlr, Hgr, Hmr, HKV, Hwt, HFS, #Hcm, HRS, #HA0, %HmA,
      %Hpo⟩
    obtain ⟨Hp, Hok, Htyp, Hci, Hmem⟩ := Hpo
    wp_apply wp_with_defer as %defer defer
    iunfold isServer at Hsrv
    icases Hsrv with ⟨%Hrd, #Hsci, ⟨%fv, #Hfv⟩, #Hat, #Hgen, -⟩
    ihave #Hat' := Hat
    iunfold srvAtomics at Hat'
    icases Hat' with ⟨-, -, #Hkvi⟩
    ihave #Hkvi' := Hkvi
    iunfold srvKVInvs at Hkvi'
    icases Hkvi' with ⟨#HkI, -, #HrI, #HsI, %Hktie, %HNx, %Hlmt, -⟩
    have HwOk := Hktie.2.2.1
    have ⟨hNxP, hNxT, hCpP, hCpT⟩ := HwOk
    -- the committed entry's shape (the KV invariant's, `kv_log_plain`)
    imod kv_log_plain γr.raft γr.kv A₀ $$ HkI HrI HA0 with %Hpc0
    have Hpe : plainEntryM γr.kv.cmp E.lm m := Hlmt ▸ Hpc0.1 m HmA
    imod srvApplyKV_writer hPers hReach s E γr ρ.wait x $$ Hkvi HKV with ⟨HKV, #Hcx, -, -, %Hwf⟩
    iunfold srvFieldsAt at Hfv
    icases Hfv with ⟨#Hlg, #Hlgnn, #Hw, #Hwok, %HE, %HEo, #Hhook, #Hlv, #Hlok, #Hfc, #Has, #Hcl, #Hrc, #Hq,
      #Hlgmu, #Hmid, #Hlead, #Het, #Htm, #Hnot, #Halm⟩
    have Hpl : ∀ rq, m.data ≠ [] → apply.irrDecode m.data = some rq → plainOrCmpG E.lm rq :=
      fun rq hd hdec => plainOrCmpG_of_entryM _ _ m Hpe Htyp hd rq hdec
    ihave ⟨%Hnn, %d, #Hfd, #Hds⟩ := entryAt_fields _ _ $$ He
    ihave %Hdlen := ownSlice_len _ _ _ $$ Hds
    ihave #Papp : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply $$ []
    · iPkgInit
    iunfold lessorOk at Hlok
    icases Hlok with ⟨%li, %Hli, #HPromote, -, -⟩
    wp_auto
    wp_if_destruct
    · -- no data: the first commit's notice, the lessor's promotion at a leader
      have hnil : m.data = [] := by
        apply List.eq_nil_of_length_eq_zero; rw [Hdlen.1, Hif]; rfl
      ihave HKV : iprop(∃ (x' : apply.ApplyKV) (out : apply.ApplyOut), srvApplyKV s E ρ.wait x' ∗
          ⌜entryStep m false x x' out⌝) $$ [HKV]
      · iexists x, apply.ApplyOut.skipped
        iframe HKV
        ipureintro; unfold entryStep; rw [ite_eq_left hnil]; exact ⟨rfl, rfl⟩
      ihave HRS : srvRestRp E γr A₀ (restEntryV2 m r) $$ [HRS]
      · rw [restEntryV2_nodata m r Htyp hnil]; iexact HRS
      wp_apply hN fv.firstCommit
      · iexact Hnot
      wp_apply hL s fv.memberID as %ldr -
      · iframe Hmid Hlead
      cases ldr
      · (try wp_auto)
        iapply HΦ
        iframe Hbe Hst Hlr Hgr Hmr HFS HKV HRS
      · (try wp_auto)
        wp_apply hE (srvCfgAddr s) fv.electionTicks fv.tickMs as %dur -
        · iframe Het Htm
        rw [Hli]
        (try wp_auto)
        (try dsimp only)
        ihave #HP := HPromote $$ %dur
        -- (prove-ps2-promote) `Promote` borrows the thread token (its sort's `Remaining()`)
        iunfold srvGoRes at Hgr
        icases Hgr with ⟨Hwgr, Htk⟩
        wp_apply HP $$ [$Htk] as Htk
        ihave Hgr : srvGoRes s $$ [Hwgr Htk]
        · iunfold srvGoRes; iframe
        (try wp_auto)
        iapply HΦ
        iframe Hbe Hst Hlr Hgr Hmr HFS HKV HRS
    · -- data: the applier, v2-only
      have hdata : m.data ≠ [] := by
        intro h; apply Hif
        have h1 := Hdlen.1; rw [h] at h1; simp only [List.length_nil] at h1
        have h2 := Hdlen.2
        have h1' : (sint.Z d.len).toNat = 0 := h1.symm
        have h3 : sint.Z d.len = 0 := by omega
        word
      obtain ⟨rq, hdec, ⟨id0, hid⟩, hrq, hdk⟩ := Hok.resolve_left hdata
      iunfold srvApplyKV at HKV
      icases HKV with ⟨%ua, Hua, #Happl, HKV, Hbo, HRA, HAR, ⟨%w', %RD, #Hw', #Hwok', HRD⟩, Hrdat⟩
      icombine Hw Hw' gives %Hweq
      subst Hweq
      ihave ⟨HKV, %HaOn⟩ := srvApplyKVW_authOn E ua x $$ HKV
      ihave #Hcp : apply.certPreV false E x.chain rq x.log $$ []
      · iunfold apply.certPreV; simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
      ihave HFSE : E.FS $$ [HFS]
      · rw [HEo.1]; iexact HFS
      ihave HSpF : iprop(if false = true then apply.ciSplit E iprop(True) else iprop(True)) $$ []
      · simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
      iapply wp_fupd
      -- the rest buckets at the backend's table: `apply.Apply`'s image, half and ids
      ihave ⟨HRS, HEv⟩ := (srvRestRp_eq_at E γr A₀ r).1 $$ HRS
      ihave ⟨%f, %Hfb, HRS, HLt, #HGI, #HRq⟩ := (srvRestAt_open E _ _).1 $$ HRS
      ihave ⟨%U, HEv, %HUok⟩ := srvEver_open E A₀ $$ HEv
      ihave #HGf : iprop(□ (⌜false = true⌝ → apply.grantFresh E rq U)) $$ []
      · iintro !> %h; cases h
      ihave #Hgpq : iprop(□ (⌜false = true⌝ → apply.grantPermRq E rq)) $$ []
      · iintro !> %h; cases h
      ihave #Hcpq : iprop(□ (⌜false = true⌝ → apply.cmpPermRq E rq)) $$ []
      · iintro !> %h; cases h
      (try wp_auto)
      ihave %Hat := entryWaitOk_attr ρ E m Htyp $$ Hewo
      have Hrr : apply.restReqOk rq r := by
        intro hk a ha'
        have hin := ((Hat Htyp hdata rq hdec) hk).2 a ha'
        have hin' : a.memberID ∈ γr.raft.raft.cfg := by rw [← Hrd]; exact hin
        exact Hmem _ hin'
      ihave ⟨Hrv, Hrdb⟩ := revokeOwn_take E rq (Or.inl (Hpl rq hdata hdec)) $$ [Hrdat]
      · iframe Hrdat HGI
      -- (strict M1) the tie's backend's tokens: the write-back token from the budget, the apply
      -- thread's reader token (`srvBeOwn`'s), given back by `bkRTOf_srv`
      icases srvBeOwn_pool s E $$ Hbo with ⟨%dB, %Hd, #Hbro, HplB, Hrt, Hbo⟩
      ihave Hwt := srvWT_at E dB Hd $$ Hwt
      ihave Htk := bkToks_srv false E dB Hd iprop(True) iprop(True) iprop(True) $$ [Hwt Hrt]
      · iframe Hwt Hrt; simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
      ihave Htt : apply.applyTok (GF := GF) E $$ [Hmr]
      · iunfold apply.applyTok; iexact Hmr
      iunfold srvApplyKVW at HKV
      icases HKV with ⟨%wn, %Hwn, HKV⟩
      wp_apply Apply_specRec_win hA fv.lg e m ua fv.w false E wn iprop(True) iprop(True) iprop(True) x rq id0 RD
        (fun ot id => waitRegdOpt ρ.wait id ot) (fun ot id => waitGoneOpt ρ.wait id ot) none x.log
        _ _ U $$ [HKV Htk Htt HRD HFSE HSpF HRS HLt HEv Hrv]
        as %ar %id ⟨HRD, HFS, Htt, Hrt, -, #Har, -, %Hid, %x', %out, HKV, HLt, HEv, Hrv, HRS, %Hgo,
          -, -, %Hstep0, -, -, -⟩
      · iframe Happl Hwok' HRD He HKV Htk Htt Hcp HFSE HSpF HRS HLt HEv HGf Hrv Hgpq
        isplitr
        · simp only [waitRegdOpt]; itrivial
        simp only [Bool.false_eq_true, ↓reduceIte]
        isplitr
        · iexact Hlgnn
        iframe Hcx
        iframe Hcpq
        ipureintro
        exact ⟨⟨hdec, hid, hrq, HaOn ▸ hdk, fun h => absurd h (by decide), by
          unfold apply.restReqOk; rw [apply.restLeasesWith_mem]; exact Hrr⟩, ⟨fun _ h => absurd h (by decide), Hwn⟩⟩
      ihave HFS : srvFS s $$ [HFS]
      · rw [← HEo.1]; iexact HFS
      have Hstep := Hstep0.1
      ihave Hrt := bkRTOf_srv E dB Hd $$ Hrt
      ihave Hbo := Hbo $$ HplB Hrt
      iunfold apply.applyTok at Htt
      irename Htt => Hmr
      ihave Hrdat := Hrdb $$ Hrv
      -- the rest buckets back, with the attribute write
      rw [(idsA_false rq out _).1, (idsA_false rq out U).2]
      icases HRS with ⟨%t, -, HRS⟩
      rw [restOutA_false E.lm rq x x' out _ t _ (Or.inl (Hpl rq hdata hdec)) Hstep,
        apply.restLeasesWith_comm (apply.restAfter rq false) (apply.restAfter_restGrantT rq false),
        ← restEntryV2_req m rq r Htyp hdata hdec]
      ihave HRS : srvRestRp E γr A₀ (restEntryV2 m r) $$ [HRS HLt HEv]
      · iapply (srvRestRp_eq_at E γr A₀ _).2
        isplitl [HRS HLt]
        · iapply (srvRestAt_open E _ _).2
          iexists f
          iframe HRS HLt HGI HRq
          ipureintro; exact Hfb
        iunfold srvEver; iexists U; iframe HEv; ipureintro; exact HUok
      ihave HKV := srvApplyKVW_of E wn ua x' Hwn $$ HKV
      imod applyKV_writer hPers hReach E HwOk ua x' $$ HsI HKV with ⟨HKV, -, -, -, %Hwf'⟩
      have Hlen : x'.log.length < 2 ^ 63 := by obtain ⟨_, -, h⟩ := Hwf'; omega
      imod revAuth_step E x.log x'.log (applyStep_grow Hstep) Hlen ⊤ $$ HRA with ⟨HRA, -⟩
      (try wp_auto)
      imodintro
      wp_pures
      iapply HΦ
      iframe Hbe Hst Hlr Hgr Hmr HFS HRS
      iexists x', out
      isplitl
      · iunfold srvApplyKV; iexists ua; isplitl [Hua]; · iexact Hua
        isplitr; · iexact Happl
        isplitl [HKV]; · iexact HKV
        isplitl [Hbo]; · iexact Hbo
        isplitl [HRA]; · iexact HRA
        isplitl [HAR]; · iexact HAR
        isplitr [Hrdat]
        · iexists fv.w, RD; iframe Hw Hwok' HRD
        iexact Hrdat
      ipureintro; unfold entryStep; rw [ite_eq_right hdata]; exact ⟨rq, id0, hdec, hid, Hstep⟩
  simp only [↓reduceIte]
  wp_start as ⟨#Hsrv, #Hewo, #Hreg, #He, Hst, Hbe, Hlr, Hgr, Hmr, HKV, Hwt, HFS, Hao, #HLv, #Hcm, Hka,
    HRS, %Hmc, #HAm, %HkA', %Hvi, %Hpo, Hv3⟩
  have HkA : uint.Z v = uint.Z γr.raft.ai0 + A.length ∧
      true = decide (uint.Z γr.kv.c0 < uint.Z m.index) :=
    ⟨HkA'.1, (decide_eq_true HkA'.2).symm⟩
  obtain ⟨Hp, Hok, Htyp⟩ := Hpo
  wp_apply wp_with_defer as %defer defer
  ihave #Hsrv0 := Hsrv
  iunfold isServer at Hsrv
  icases Hsrv with ⟨%Hrd, #Hsci, ⟨%fv, #Hfv⟩, #Hat, #Hgen, -⟩
  ihave #Hat' := Hat
  iunfold srvAtomics at Hat'
  icases Hat' with ⟨#Hainv, -, #Hkvi⟩
  ihave #Hmono := appliedMono_of_inv s E γr $$ Hainv
  -- the KV model (unit T1): the entry plain, the log after it the model's, certified
  ihave #Hkvi' := Hkvi
  iunfold srvKVInvs at Hkvi'
  icases Hkvi' with ⟨-, -, -, #HsI, %Hktie, %HNx, %Hlmt, #HwTie⟩
  have HwOk := Hktie.2.2.1
  have ⟨hNxP, hNxT, hCpP, hCpT⟩ := HwOk
  imod srvApplyKV_writer hPers hReach s E γr ρ.wait x $$ Hkvi HKV with ⟨HKV, #Hcx, -, -, %Hwf⟩
  obtain ⟨_, -, Hlx⟩ := Hwf
  icases kvApplied_log γr.raft γr.kv A x $$ Hka with ⟨Hka, %Hxl⟩
  imod kv_applied_step E γr A m x (kvEntry_len _ _ _ x m Hok Hlx) $$ Hkvi Hka HAm with ⟨%Hpe, Hka⟩
  obtain ⟨Hpe, Hxch, Hoff, Hxcr, Hnl⟩ := Hpe
  -- the start's chain (D19k: no NOSPACE outcome there)
  ihave #Hkvi'' := Hkvi
  iunfold srvKVInvs at Hkvi''
  icases Hkvi'' with ⟨#HkI, -, #HrI, -⟩
  imod kv_log_plain γr.raft γr.kv (A ++ [m]) $$ HkI HrI HAm with %Hpc0
  have Hch0 := Hpc0.2
  have HnaA : noAuthEnable γr.kv.c0 A :=
    noAuthEnable_of_plainLogM _ A (fun m' hm' => Hpc0.1 m' (List.mem_append_left _ hm'))
  imod (srvKVCoreM_keysA false E γr (A ++ [m])) $$ [] [] with %HkeysA
  · rw [srvKVCoreM_false]; iexact Hkvi
  · iexact HAm
  ihave ⟨Hka, #Hkc⟩ := kvAppliedL_nx' _ _ _ _ HkeysA $$ Hka
  have hiA : uint.Z m.index = uint.Z γr.raft.ai0 + A.length + 1 := by omega
  iunfold srvFieldsAt at Hfv
  icases Hfv with ⟨#Hlg, #Hlgnn, #Hw, #Hwok, %HE, %HEo, #Hhook, #Hlv, #Hlok, #Hfc, #Has, #Hcl, #Hrc, #Hq,
    #Hlgmu, #Hmid, #Hlead, #Het, #Htm, #Hnot, #Halm⟩
  -- (M2's apply side, 2026-10-31) the entry: a covered request (D22: its rest buckets' effect is
  -- `dispatch`'s), or, in the cluster's compaction mode, a compaction in M2's scope
  have Hpl : ∀ rq, m.data ≠ [] → apply.irrDecode m.data = some rq → plainOrCmpG E.lm rq :=
    fun rq hd hdec => plainOrCmpG_of_entryM _ _ m Hpe Htyp hd rq hdec
  -- a compaction's facts (`cmpAdmit`): its claim from the KV invariant's (`kv_entry_claim`, S3-3),
  -- the store compacting in the server's mode (`srvEnvOk`), the KV names' mode the server's
  imod kv_entry_claim γr.raft γr.kv A m $$ HkI HrI HAm with %Hcl
  imod kv_entry_grantFresh γr.raft γr.kv A m $$ HkI HrI HAm with %Hgf
  have Hca : ∀ rq, m.data ≠ [] → apply.irrDecode m.data = some rq →
      apply.cmpAdmit x.log rq :=
    fun rq hd hdec => cmpAdmit_of_entry γr.kv γr.kv.cmp A m rq x.log Hxl Htyp hd hdec Hcl
  -- (C3's server stage) a compaction's permit: the claim's revision the cluster's permit, which is
  -- the store's (`srvKVInvs`'s `crevPermIs`)
  ihave #HA0 := srvRLogLb_mono γr.raft A (A ++ [m]) (List.prefix_append _ _) $$ HAm
  imod (kv_revLbZ_of_rlogLb γr.raft γr.kv A ((kvModel γr.kv A).length - 1) (by omega))
    $$ HkI HrI HA0 with #HlbA
  ihave ⟨%Hnn, %d, #Hfd, #Hds⟩ := entryAt_fields _ _ $$ He
  ihave %Hdlen := ownSlice_len _ _ _ $$ Hds
  ihave #Pnot : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.notify $$ []
  · iPkgInit
  ihave #Pcfg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.config $$ []
  · iPkgInit
  ihave #Papp : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply $$ []
  · iPkgInit
  ihave #Perr : isPkgInit (PROP := IProp GF) pkg_id.errors $$ []
  · iPkgInit
  ihave #Palm : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3alarm $$ []
  · iPkgInit
  ihave #Pzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  ihave #Phum : isPkgInit (PROP := IProp GF) pkg_id.github_com.dustin.go_humanize $$ []
  · iPkgInit
  ihave #Pci : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.cindex $$ []
  · iPkgInit
  ihave #Prpb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  ihave #Perrs : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.errors $$ []
  · iPkgInit
  iunfold lessorOk at Hlok
  icases Hlok with ⟨%li, %Hli, #HPromote, -, -⟩
  · -- the entry `i = p + 1`, above `ci`
    icases Hv3 with ⟨Happ, %Hv3⟩
    obtain ⟨hi, hlt, hce, hld⟩ := Hv3
    have hi0 : m.index ≠ W64 0 := by intro h; rw [h] at hlt; simp at hlt
    wp_auto
    wp_if_destruct
    · -- no data: processed with no writes
      have hnil : m.data = [] := by
        apply List.eq_nil_of_length_eq_zero; rw [Hdlen.1, Hif]; rfl
      have hl0 : x.log = kvEntry γr.kv.c0 x.chain (kvLeases γr.kv A) x.log m :=
        (kvEntry_nonwrite _ _ _ _ m (Or.inl hnil)).symm
      ihave ⟨Hka, #HkL⟩ := kvApplied_next γr A m x x m.index hiA hl0 Hxch
        (crevOf_batchStep γr.kv A m x x Hpe (by
          unfold batchStep; rw [if_pos Htyp]; exact ⟨.skipped, by unfold entryStep; rw [if_pos hnil]; exact ⟨rfl, rfl⟩⟩)
          Hxch Hxcr) $$ Hka
      imod applied_predeposit s E γr v m.index x.log x.log Hvi (List.prefix_refl _) $$ Hainv Hao HLv HkL
        with Hpre
      ihave HKV : iprop(∃ (x' : apply.ApplyKV) (out : apply.ApplyOut), srvApplyKV s E ρ.wait x' ∗
          ⌜entryStep m true x x' out⌝ ∗ entryDelivered ρ.wait m ot out ∗
          srvAppliedPre γr v m.index x'.log ∗ kvApplied γr.raft γr.kv (A ++ [m]) x' ∗
          srvRest E γr (A ++ [m])) $$ [HKV Hpre Hka HRS]
      · iexists x, apply.ApplyOut.skipped
        iframe HKV Hpre Hka
        ihave HRS := srvRest_nodata E γr A m Htyp hnil $$ HRS
        iframe HRS
        isplitr
        · ipureintro; unfold entryStep; rw [ite_eq_left hnil]; exact ⟨rfl, rfl⟩
        iunfold entryDelivered; ileft; ipureintro; left; exact hnil
      wp_apply hN fv.firstCommit
      · iexact Hnot
      wp_apply hL s fv.memberID as %ldr -
      · iframe Hmid Hlead
      iunfold isServerCI at Hsci
      icases Hsci with ⟨#Hcif, #Hci, #Hinv⟩
      imod skip_done γ st m.index Hp hi hlt $$ Hinv Hst with Hst
      cases ldr
      · (try wp_auto)
        tail_skip
      · (try wp_auto)
        wp_apply hE (srvCfgAddr s) fv.electionTicks fv.tickMs as %dur -
        · iframe Het Htm
        rw [Hli]
        (try wp_auto)
        (try dsimp only)
        ihave #HP := HPromote $$ %dur
        -- (prove-ps2-promote) `Promote` borrows the thread token (its sort's `Remaining()`)
        iunfold srvGoRes at Hgr
        icases Hgr with ⟨Hwgr, Htk⟩
        wp_apply HP $$ [$Htk] as Htk
        ihave Hgr : srvGoRes s $$ [Hwgr Htk]
        · iunfold srvGoRes; iframe
        (try wp_auto)
        tail_skip
    · -- data: the applier, in one critical section after the hook, or without writes
      iunfold isServerCI at Hsci
      icases Hsci with ⟨#Hcif, #Hci, #Hinv⟩
      have hpre : st.pending = false ∧ m.index = st.p + 1 ∧ uint.Z st.p < uint.Z m.index ∧
          uint.Z (ciEff γ st.k) < uint.Z m.index := ⟨Hp, hi, hlt, hce⟩
      have hdata : m.data ≠ [] := by
        intro h; apply Hif
        have h1 := Hdlen.1; rw [h] at h1; simp only [List.length_nil] at h1
        have h2 := Hdlen.2
        have h1' : (sint.Z d.len).toNat = 0 := h1.symm
        have h3 : sint.Z d.len = 0 := by omega
        word
      obtain ⟨rq, hdec, ⟨id0, hid⟩, hrq, hdk⟩ := Hok.resolve_left hdata
      iunfold srvApplyKV at HKV
      icases HKV with ⟨%ua, Hua, #Happl, HKV, Hbo, HRA, HAR, ⟨%w', %RD, #Hw', #Hwok', HRD⟩, Hrdat⟩
      icombine Hw Hw' gives %Hweq
      subst Hweq
      ihave ⟨HKV, %HaOn⟩ := srvApplyKVW_authOn E ua x $$ HKV
      -- the entry's certificate at `lean`'s lease mode, as in `wp_proofOff`
      ihave #Hcp := kv_certPre_G E γr.raft γr.kv HNx γr.kv.c0 (kvLeases γr.kv A) x m rq true E.lm
        (Hpl rq hdata hdec) Hoff Htyp
        hdata hdec HkA.2 Hnl (kvLeases_ne0_of γr.kv A HnaA) $$ Hkc
      obtain ⟨HEP, HEf, HEnn⟩ := HE
      -- the floor its proposer recorded with the entry's claim (the vertical slice's unit V2)
      -- (and, unit T1, the committed log it is in)
      have he : entryWaitOk ρ E m = iprop((∀ (rq : apply.IRRModel) (id : w64),
            ⌜m.data ≠ [] ∧ apply.irrDecode m.data = some rq ∧ apply.irrId rq = some id⌝ -∗
              ∃ (γf : GName) (k : IdKey),
                id ↪[ρ.ids.issued]□ (some (m.data, γf, k) : Option IdClaimV) ∗
                idRegdAt ρ.ids k id) ∗
            ∃ L : List EntryModel, srvRLogLb ρ.raft L ∗ ⌜m ∈ L ∧ attrEntryOk ρ.raft.raft.cfg m⌝) := by
        unfold entryWaitOk; rw [ite_eq_left Htyp]
      ihave #Hewo' : iprop((∀ (rq : apply.IRRModel) (id : w64),
            ⌜m.data ≠ [] ∧ apply.irrDecode m.data = some rq ∧ apply.irrId rq = some id⌝ -∗
              ∃ (γf : GName) (k : IdKey),
                id ↪[ρ.ids.issued]□ (some (m.data, γf, k) : Option IdClaimV) ∗
                idRegdAt ρ.ids k id) ∗
            ∃ L : List EntryModel, srvRLogLb ρ.raft L ∗ ⌜m ∈ L ∧ attrEntryOk ρ.raft.raft.cfg m⌝) $$ []
      · rw [← he]; iexact Hewo
      icases Hewo' with ⟨#Hewc, %Lw, #HLw, %HmLw'⟩
      have HmLw := HmLw'.1
      ihave ⟨%γf, %k0, #Hcl0, -⟩ := Hewc $$ %rq %id0 %(⟨hdata, hdec, hid⟩)
      ihave #Hgen' := Hgen
      iunfold srvGenAt at Hgen'
      icases Hgen' with ⟨%gidg, -, #Hidg⟩
      -- (D21e (A), stage M4) an id of the member's prefix: the floor its claimer recorded (the
      -- generator's facts); another member's: no waiter here (`reqWaitR`), the empty floor
      -- (R2c) by the claim's key: the incarnation's own claim, or another key's (another
      -- member's, or an earlier incarnation's): no waiter here, the empty floor
      ihave Hfl : iprop(|={⊤}=> ∃ F : mvcc.Log, srvApi.kvLogLb E.γs F ∗
          (⌜k0 = ρ.ids.key⌝ -∗ floorAt γf F)) $$ []
      · by_cases hpx : k0 = ρ.ids.key
        · ihave #Hcl0o : idClaim ρ.ids id0 m.data γf $$ []
          · iunfold idClaim; rw [← hpx]; iexact Hcl0
          imod idClaim_fact ρ.ids gidg (srvFloorFact E) id0 m.data γf ⊤ (by simp)
            $$ Hidg Hcl0o with Hff
          icases Hff with >#Hff
          iunfold srvFloorFact at Hff
          iunfold srvFloorFacts at Hff
          icases Hff with ⟨%F, #HfF, #HcF⟩
          imodintro
          iexists F
          iunfold srvApi.kvLogLb
          iframe HcF
          iintro -
          iexact HfF
        · ihave HcF : iprop(|==> srvApi.kvLogLb E.γs ([] : mvcc.Log)) $$ []
          · iunfold srvApi.kvLogLb; iapply monoListLbOwn_nil
          imod HcF with #HcF
          imodintro
          iexists []
          iframe HcF
          iintro %hpx'
          exact absurd hpx' hpx
      imod Hfl with ⟨%F, #HcF, #HfFo⟩
      -- D14i: the snapshot right and the consistent index's resources, lent out of `Pre`
      ihave HFSE : E.FS $$ [HFS]
      · rw [HEo.1]; iexact HFS
      ihave #HSp : apply.ciSplit E iprop(applyThread γ st ∗ ciApplying ci m.index m.term ∗
          applyBackend γ ci b ∗ ⌜st.pending = false ∧ m.index = st.p + 1 ∧
            uint.Z st.p < uint.Z m.index ∧ uint.Z (ciEff γ st.k) < uint.Z m.index⌝) $$ []
      · iunfold apply.ciSplit
        iintro !> ⟨Hst', Happ', Hbe', %Hf'⟩
        iexists iprop(applyThread γ st ∗ applyBackend γ ci b), ciEff γ st.k
        iframe Hst' Hbe'
        isplitr
        · ipureintro; rw [HEo.2.1]; exact ⟨st, b, rfl, Hp, hld, rfl⟩
        iintro ⟨Hst', Hbe'⟩
        iframe Hst' Happ' Hbe'
        ipureintro; exact Hf'
      ihave HSpT : iprop(if true = true then apply.ciSplit E iprop(applyThread γ st ∗
          ciApplying ci m.index m.term ∗ applyBackend γ ci b ∗ ⌜st.pending = false ∧
            m.index = st.p + 1 ∧ uint.Z st.p < uint.Z m.index ∧
            uint.Z (ciEff γ st.k) < uint.Z m.index⌝) else iprop(True)) $$ []
      · simp only [↓reduceIte]; iexact HSp
      (try wp_auto)
      ihave ⟨%f, %Hfb, HRS, HLt, #HGI, #HRq, HEv⟩ := srvRest_open E γr A $$ HRS
      ihave ⟨%U, HEv, #HGf, %HUok⟩ := srvEver_applyPre E γr.kv A m rq Htyp hdata hdec
        (Hpl rq hdata hdec) Hlmt Hgf $$ [$HGI $HEv]
      ihave #Hgpq := srvGrantIf_permPG E rq (Hpl rq hdata hdec) $$ HGI
      ihave %Hat := entryWaitOk_attr ρ E m Htyp $$ Hewo
      have Hrr := restReqOk_of_attr γr.raft γr.kv.c0 A m rq Hmc (by rw [← Hrd]; exact Hat) Htyp
        hdata hdec
      ihave ⟨Hrv, Hrdb⟩ := revokeOwn_take E rq (Or.inl (Hpl rq hdata hdec)) $$ [$Hrdat $HGI]
      ihave #Hcpq := cmpPermRq_of_entry E γr.kv Hktie.2.2.2 A m rq Hcl Htyp hdata hdec $$ HlbA
      ihave #Hcpq := apply.v3Gate true _ $$ Hcpq
      ihave #HGf := apply.v3Gate true _ $$ HGf
      ihave #Hgpq := apply.v3Gate true _ $$ Hgpq
      -- (strict M1) the tie's backend's tokens and the hook's run at its batch lock
      icases srvBeOwn_pool s E $$ Hbo with ⟨%dB, %Hd, #Hbro, HplB, Hrt, Hbo⟩
      ihave Hwt := srvWT_at E dB Hd $$ Hwt
      ihave Htk := bkToks_srv true E dB Hd
        iprop(applyThread γ st ∗ ciApplying ci m.index m.term ∗ applyBackend γ ci b ∗
          ⌜st.pending = false ∧ m.index = st.p + 1 ∧ uint.Z st.p < uint.Z m.index ∧
            uint.Z (ciEff γ st.k) < uint.Z m.index⌝)
        iprop(hookDone γ TM ∗ applyThread γ { st with k := m.index, pending := true } ∗
          ciApplying ci m.index m.term ∗ applyBackend γ ci b)
        iprop(applyThread γ ⟨m.index, m.index, m.index, false⟩ ∗ ciApplying ci m.index m.term ∗
          applyBackend γ ci b) $$ [Hwt Hrt]
      · iframe Hwt Hrt
        simp only [↓reduceIte, mvcc.api.hookRun, if_neg HEnn]
        rw [HEP, ← HEf]
        isplitr
        · iunfold hookSpec at Hhook
          ihave #Hh := Hhook $$ %st %m.index %m.term %b
          imodintro
          iexact Hh
        · iintro ⟨Hdone, Hst, Happ, Hbe⟩
          imod writes_done γ { st with k := m.index, pending := true } rfl $$ Hinv Hst
            with ⟨Hst, Htok⟩
          iunfold hookDone at Hdone
          icases Hdone with ⟨%mm, Hmt, HTM, #Hreg⟩
          imodintro
          iframe Happ Hbe
          isplitl [Hmt HTM Htok]
          · iunfold batchLockInv; iexists mm; iframe; iexact Hreg
          iexact Hst
      ihave Htt : apply.applyTok (GF := GF) E $$ [Hmr]
      · iunfold apply.applyTok; iexact Hmr
      -- (auth-lease S4 item 7b) the entry's window, its target the items of the model log after the entry
      imod (srvApplyKVW_push hPers hReach E _ HEo.2.2.1.2 HwOk ua x _
          (kvEntry_prefix γr.kv.c0 x.chain (kvLeases γr.kv A) x.log m)) $$ [HKV] with ⟨%wn, %Hwn, HKV⟩
      · iframe HsI HwTie HKV
        iintro %_ !>
        rw [HNx]; iexact Hkc
      have Hwt : ∀ T, E.lg = true → true = true → apply.winTgt wn rq x.log T := fun T hlg _ =>
        winTgt_of_log wn rq x.log _ _
          (fun s0 T0 h => by obtain ⟨s1, hs1⟩ := Hwn.2 hlg; rw [hs1] at h; cases h; rfl)
          (fun oc hb _ => by
            rw [backendStep_kvEntryM γr.kv.c0 (kvLeases γr.kv A) γr.kv.cmp E.lm m x.log rq oc Hpe Htyp hdata hdec
              HkA.2.symm Hnl (kvLeases_ne0_of γr.kv A HnaA) hb, Hxch.trans Hch0])
      wp_apply Apply_specRec_win hA fv.lg e m ua fv.w true E wn
        iprop(applyThread γ st ∗ ciApplying ci m.index m.term ∗ applyBackend γ ci b ∗
          ⌜st.pending = false ∧ m.index = st.p + 1 ∧ uint.Z st.p < uint.Z m.index ∧
            uint.Z (ciEff γ st.k) < uint.Z m.index⌝)
        iprop(hookDone γ TM ∗ applyThread γ { st with k := m.index, pending := true } ∗
          ciApplying ci m.index m.term ∗ applyBackend γ ci b)
        iprop(applyThread γ ⟨m.index, m.index, m.index, false⟩ ∗ ciApplying ci m.index m.term ∗
          applyBackend γ ci b) x rq id0 RD
        (fun ot id => waitRegdOpt ρ.wait id ot) (fun ot id => waitGoneOpt ρ.wait id ot) ot F
        _ _ U $$ [Hst Happ Hbe HKV Htk Htt HRD HFSE HSpT HRS HLt HEv Hrv] as %ar %id
          ⟨HRD, HFS, Htt, Hrt, Hout, #Har, HTr, %Hid, %x', %out, HKV, HLt, HEv, Hrv, HRS, %Hgo, HGr, HVr, %Hstep0, HRes, -, #Hdel⟩
      · iframe Happl Hwok' HRD He HKV Htk Htt Hcp HFSE HSpT HRS HLt HEv HGf Hrv Hgpq
        isplitr
        · iunfold entryRegd at Hreg
          ihave ⟨#Hr1, -⟩ := Hreg $$ %rq %id0 %(⟨hdec, hid⟩)
          iexact Hr1
        try simp only [↓reduceIte]
        isplitr
        · iexact Hlgnn
        iframe Hst Happ Hbe HcF
        iframe Hcpq
        ipureintro; exact ⟨hpre, ⟨hdec, hid, hrq, HaOn ▸ hdk, fun _ => Hca rq hdata hdec, by unfold apply.restReqOk; rw [apply.restLeasesWith_mem]; exact Hrr⟩, ⟨fun h _ => Hwt _ h rfl, Hwn.1⟩⟩
      ihave HFS : srvFS s $$ [HFS]
      · rw [← HEo.1]; iexact HFS
      have Hstep := Hstep0.1
      ihave Hrt := bkRTOf_srv E dB Hd $$ Hrt
      ihave Hbo := Hbo $$ HplB Hrt
      iunfold apply.applyTok at Htt
      irename Htt => Hmr
      ihave Hrdat := Hrdb $$ Hrv
      ihave HEv := srvEver_grant E A m rq true out U Htyp hdata hdec (plainOrCmpG_lg E rq (Hpl rq hdata hdec)) HUok $$ HEv
      ihave ⟨HGr, HRes, #Hgrq⟩ := grantReqA_of_res E rq true x.log ar out $$ [$HGr $HRes]
      ihave HRS := srvRest_applyPGR E γr A m rq true x x' out f Htyp hdata hdec HkA.2 Hxch Hch0
        (Hpl rq hdata hdec) Hstep Hfb $$ [HLt HRS HEv]
      · iframe HGI HRq Hgrq HLt HRS HEv; ipureintro; exact Hgo
      ihave Hj : iprop(|={⊤}=> ∃ st1 : ApplyState, applyThread γ st1 ∗
          ciApplying ci m.index m.term ∗ applyBackend γ ci b ∗
          ⌜st1 = ⟨m.index, m.index, m.index, false⟩ ∨ st1 = { st with p := m.index }⌝) $$ [Hout]
      · icases Hout with (⟨Hst, Happ, Hbe⟩ | ⟨Hst, Happ, Hbe, -⟩)
        · imodintro; iexists _; iframe Hst Happ Hbe; ipureintro; left; rfl
        · imod skip_done γ st m.index Hp hi hlt $$ Hinv Hst with Hst
          imodintro; iexists _; iframe Hst Happ Hbe; ipureintro; right; rfl
      imod Hj with ⟨%st1, Hst, Happ, Hbe, %hst1⟩
      ihave HKV := srvApplyKVW_of E wn ua x' Hwn.1 $$ HKV
      imod applyKV_writer hPers hReach E HwOk ua x' $$ HsI HKV with ⟨HKV, #Hcert, #Hcx', #Hrcx', %Hwf'⟩
      have Hlen : x'.log.length < 2 ^ 63 := by obtain ⟨_, -, h⟩ := Hwf'; omega
      have Hwfl : mvcc.LogWf' x'.log ∧ x'.log.length + 3 ≤ 2 ^ 63 := by
        obtain ⟨_, hr, h⟩ := Hwf'; exact ⟨(mvcc.api.reach_logWf _ hr).1, h⟩
      imod revAuth_step E x.log x'.log (applyStep_grow Hstep) Hlen ⊤ $$ HRA with ⟨HRA, HMint⟩
      have hes : entryStep m true x x' out := by
        unfold entryStep; rw [ite_eq_right hdata]; exact ⟨rq, id0, hdec, hid, Hstep⟩
      obtain ⟨hc', hl'⟩ := batchStep_plainMG γr.kv.c0 (kvLeases γr.kv A) _ _ m x x' Hpe Hoff Hnl
        (kvLeases_ne0_of γr.kv A HnaA)
        (batchStep_of_entryStep γr.kv.c0 m true x x' out Htyp HkA.2 hes)
      ihave ⟨Hka, #HkL⟩ := kvApplied_next γr A m x x' m.index hiA hl' (hc'.trans Hxch)
        (crevOf_batchStep γr.kv A m x x' Hpe
          (batchStep_of_entryStep γr.kv.c0 m true x x' out Htyp HkA.2 hes) Hxch Hxcr) $$ Hka
      imod applied_predeposit s E γr v m.index x.log x'.log Hvi
        (applyStep_prefix rq true x x' out Hstep) $$ Hainv Hao HLv HkL with Hpre
      icases srvAppliedPre_log γr v m.index x'.log $$ Hpre with ⟨Hpre, #HLpre⟩
      ihave HKV : iprop(∃ (x'' : apply.ApplyKV) (out' : apply.ApplyOut), srvApplyKV s E ρ.wait x'' ∗
          ⌜entryStep m true x x'' out'⌝ ∗ entryDelivered ρ.wait m ot out' ∗
          srvAppliedPre γr v m.index x''.log ∗ kvApplied γr.raft γr.kv (A ++ [m]) x'' ∗
          srvRest E γr (A ++ [m])) $$ [HKV Hua Hbo HRD HRA HAR Hrdat Hpre Hka HRS]
      · iexists x', out
        iframe Hpre Hka HRS
        isplitl
        · iunfold srvApplyKV; iexists ua; isplitl [Hua]; · iexact Hua
          isplitr; · iexact Happl
          isplitl [HKV]; · iexact HKV
          isplitl [Hbo]; · iexact Hbo
          isplitl [HRA]; · iexact HRA
          isplitl [HAR]; · iexact HAR
          isplitr [Hrdat]
          · iexists fv.w, RD; iframe Hw Hwok' HRD
          iexact Hrdat
        isplitr
        · ipureintro; unfold entryStep; rw [ite_eq_right hdata]; exact ⟨rq, id0, hdec, hid, Hstep⟩
        iunfold entryDelivered
        icases Hdel with (%Hwv | #Hg)
        · ileft; ipureintro; right; exact Hwv
        · iright; iexists rq, id0; iframe Hg; ipureintro; exact ⟨hdec, hid⟩
      (try wp_auto)
      wp_if_destruct
      · (try wp_auto)
        tail_any
      iunfold apply.resultErrOk at Har
      icases Har with (%Hnull | ⟨%err, #Herr, #HerrIs⟩)
      · exact absurd Hnull Hif
      have Har0 : ar ≠ null := Hif
      ihave Hei : (go_etcd_io.etcd.server.v3.etcdserver.errors.errorsInit : IProp GF) $$ []
      · iapply isPkgInit_access $$ Perrs
      icases Hei with ⟨⟨%ens, #Hens, %Hensp⟩, -⟩
      -- D19k: the result's error is not `ErrNoSpace`'s (a plain request at the start's chain),
      -- so `errors.Is(ar.Err, ErrNoSpace)` is `false` and the NOSPACE alarm branch is dead
      ihave Hai : (go_etcd_io.etcd.server.v3.etcdserver.apply.applyInit : IProp GF) $$ []
      · iapply isPkgInit_access $$ Papp
      icases Hai with ⟨-, -, #Hev⟩
      ihave #Plea : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease $$ []
      · iPkgInit
      ihave #Hli : (go_etcd_io.etcd.server.v3.lease.leaseInit : IProp GF) $$ []
      · iapply isPkgInit_access $$ Plea
      ihave ⟨HGr, HRes, #Hnn⟩ := applyResultIs_notNoSpace_G E E.lm rq x x' ar out
        (Hpl rq hdata hdec) (Hxch.trans Hch0) Hstep $$ Hev Hli HGr HRes
      ihave HGA := grantArM_of_res E ar rq out Har0 $$ HGr
      ihave HVA := revokeArM_of_res E ar rq out Har0 $$ HVr
      icases Hnn with (%Hn0 | ⟨%err', #Herr', #Hnn⟩)
      · exact absurd Hn0 Har0
      icombine Herr Herr' gives %Heq
      subst Heq
      (try wp_auto)
      wp_apply (wp_Is_notNoSpace hIs err ens Hensp) $$ []
      · iframe #
      iunfold waitInv at Hwok
      icases Hwok with ⟨⟨%RD0, Hwok⟩, #Hwn⟩
      iunfold isWait at Hwok
      icases Hwok with ⟨%wi, %Hwi, -, #HTrig, -⟩
      subst Hid
      -- the entry at its position after the applied raft log `A`, whose model the entry met
      -- (unit W-M3: the proposer's update fired at the state of `x.log`)
      ihave #Hcl0a : idClaimAny ρ.ids id m.data γf $$ []
      · iunfold idClaimAny; iexists k0; iexact Hcl0
      ihave #HeW : iprop(entryWit ρ rq x.log) $$ []
      · iunfold entryWit
        iexists A ++ [m], A.length, m, id, γf
        simp only [ReqNames.raft, ReqNames.kv, Hrd]
        iframe HAm Hcl0a
        ipureintro
        refine ⟨by simp, Htyp, hdec, hid, ?_⟩
        rw [List.take_left' rfl, Hxl]
      -- the caller's certificate of the log after (unit W-M3)
      -- not `ErrNoSpace` (D19k: `errors.Is` answered `false`): hand the result to the waiter
      (try wp_auto)
      rw [Hwi]
      (try wp_auto)
      (try dsimp only)
      ihave #HT := HTrig $$ %id %(interface.mkOk (go.GoType.PointerType
        go_etcd_io.etcd.server.v3.etcdserver.apply.Result.ty) #ar)
      -- (linkv-txn stage B1) the result handed over is of a full application: the outcome not
      -- waived, or the registration gone (nothing is sent), or the id another member's
      ihave %Hot := entryRegd_none_key ρ.wait ρ.ids m ot rq id γf k0 ⟨hdec, hid⟩ $$ Hreg Hcl0
      icases Hdel with (%Hwv | #Hg)
      · have Hwvf : k0 = ρ.ids.key → out.waived = false := fun _ => Hwv
        wp_apply HT $$ [HRes HTr HMint HGA HVA]
        · trig
        (try wp_auto)
        tail_any
      · cases ot with
        | some t =>
          wp_apply HT $$ []
          · ileft; iexists t; iunfold waitGoneOpt at Hg; iexact Hg
          (try wp_auto)
          tail_any
        | none =>
          have Hwvf : k0 = ρ.ids.key → out.waived = false := fun h => absurd h (Hot rfl hdata)
          wp_apply HT $$ [HRes HTr HMint HGA HVA]
          · trig
          (try wp_auto)
          tail_any

variable [apkg_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

set_option hygiene false in
/-- The uber-applier's row put back (`srvApplyKVOn`) at the names of the call. -/
local macro "repack" : tactic => `(tactic| (
  iunfold srvApplyKVOn
  iexists ua
  isplitl [Hua]
  · iexact Hua
  isplitr
  · iexact Hb
  isplitr
  · iexact Happl
  isplitl [HKV]
  · iexact HKV
  isplitl [Hbo]
  · iexact Hbo
  isplitl [HRA]
  · iexact HRA
  isplitl [HAR]
  · iexact HAR
  isplitr [Hrdat]
  · iexists fv.w, RD
    iframe Hw Hwok' HRD
  iexact Hrdat))

set_option hygiene false in
/-- The hook's triple and the closing of `Q` (the premise `apply.Apply`'s triples take with `v3`). -/
local macro "hook_pre" : tactic => `(tactic| (
  icases srvBeOwn_pool s E $$ Hbo with ⟨%dB, %Hd, #Hbro, Hpl, Hrt, Hbo⟩
  ihave Hwt := srvWT_at E dB Hd $$ Hwt
  ihave Hhk := bkToks_srv true E dB Hd
    iprop(applyThread γ st ∗ ciApplying ci m.index m.term ∗ applyBackend γ ci b ∗
      ⌜st.pending = false ∧ m.index = st.p + 1 ∧ uint.Z st.p < uint.Z m.index ∧
        uint.Z (ciEff γ st.k) < uint.Z m.index⌝)
    iprop(hookDone γ TM ∗ applyThread γ { st with k := m.index, pending := true } ∗
      ciApplying ci m.index m.term ∗ applyBackend γ ci b)
    iprop(applyThread γ ⟨m.index, m.index, m.index, false⟩ ∗ ciApplying ci m.index m.term ∗
      applyBackend γ ci b) $$ [Hwt Hrt]
  · iframe Hwt Hrt
    simp only [↓reduceIte, mvcc.api.hookRun, if_neg HEnn]
    rw [HEP, ← HEf]
    isplitr
    · iunfold hookSpec at Hhook
      ihave #Hh := Hhook $$ %st %m.index %m.term %b
      imodintro
      iexact Hh
    · iintro ⟨Hdone, Hst, Happ, Hbe⟩
      imod writes_done γ { st with k := m.index, pending := true } rfl $$ Hinv Hst
        with ⟨Hst, Htok⟩
      iunfold hookDone at Hdone
      icases Hdone with ⟨%mm, Hmt, HTM, #Hreg⟩
      imodintro
      iframe Happ Hbe
      isplitl [Hmt HTM Htok]
      · iunfold batchLockInv; iexists mm; iframe; iexact Hreg
      iexact Hst
  ihave Htt : apply.applyTok (GF := GF) E $$ [Hmr]
  · iunfold apply.applyTok; iexact Hmr))

set_option hygiene false in
/-- A replayed entry's application (`v3` false) to the postcondition: the log and the chain kept
(`hkeep`), the auth state too (`HAR` at `sa`), the rest buckets one entry later (`HRS`). -/
local macro "tail_off" : tactic => `(tactic| (
  ihave HFS : srvFS s $$ [HFS]
  · rw [← HEo.1]; iexact HFS
  ihave Hrt := bkRTOf_srv E dB Hd $$ Hrt
  ihave Hbo := Hbo $$ Hpl Hrt
  iunfold apply.applyTok at Htt
  irename Htt => Hmr
  imod applyKV_writer hPers hReach E HwOk ua x' $$ HsI HKV with ⟨HKV, #Hcert, #Hcx', #Hrcx', %Hwf'⟩
  have Hlen : x'.log.length < 2 ^ 63 := by obtain ⟨_, -, h⟩ := Hwf'; omega
  have Hwfl : mvcc.LogWf' x'.log ∧ x'.log.length + 3 ≤ 2 ^ 63 := by
    obtain ⟨_, hr, h⟩ := Hwf'; exact ⟨(mvcc.api.reach_logWf _ hr).1, h⟩
  imod revAuth_step E x.log x'.log (applyStep_grow Hstep) Hlen ⊤ $$ HRA with ⟨HRA, -⟩
  (try wp_auto)
  ihave Hka : kvAppliedLOn γr.raft γr.kv srvAuthSt0 (A ++ [m]) (sa, x'.log, kvLeasesOn γr.kv srvAuthSt0 A) $$ [Hka]
  · irevert Hka; rw [kvEntryOn_below _ _ _ m hv, hkeep.1]; iintro Hka; iexact Hka
  ihave ⟨Hka, #HkL⟩ := kvApplied_nextOn γr A m x' sa _ m.index hiA (hkeep.2.trans Hxch) $$ Hka
  imod applied_predepositM true s E γr v m.index x.log x'.log Hvi
    (applyStep_prefix rq false x x' out Hstep) $$ Hainv Hao HLv HkL with Hpre
  imodintro
  first | iapply HΦ | (wp_pure; wp_pure; iapply HΦ)
  iframe Hbe Hst Hlr Hgr Hmr HFS
  (try iframe Htok)
  iexists x', out, sa
  iframe Hpre Hka HRS
  isplitl
  · repack
  isplitr
  · ipureintro; unfold entryStep; rw [ite_eq_right hdata]; exact ⟨rq, id0, hdec, hid, Hstep⟩
  iunfold entryDelivered
  icases Hdel with (%Hwv | #Hg)
  · ileft; ipureintro; right; exact Hwv
  · iright; iexists rq, id0; iframe Hg; ipureintro; exact ⟨hdec, hid⟩))

set_option hygiene false in
/-- `Trigger(id, ar)`'s premise in the mode `on`: every expectation registered under the entry's
id is the proposer's `resultΨOn` of the entry's request, which the result meets. -/
local macro "trig_on" : tactic => `(tactic| (
  iright; iright
  iunfold waitTrig
  iintro %Ψ HR
  iunfold reqWaitRM at HR
  icases HR with ⟨%d', %rq', %γf', %F', #Hcl', #Hfl', %Hp'⟩
  obtain ⟨hd', hΨ, -⟩ := Hp'
  subst hΨ
  -- (R2c) a waiter's claim is the incarnation's: the entry's claim is of its key
  ihave %Hdd := idClaim_agree_entry ρ.ids id d' m.data γf' γf k0 $$ Hcl' Hcl0
  obtain ⟨Hdd, Hγ, hpx⟩ := Hdd
  replace hpx := hpx.symm
  subst Hdd Hγ
  ihave #HfF := HfFo $$ %hpx
  ihave %HFF := floorAt_agree γf' F' F $$ Hfl' HfF
  subst HFF
  rw [hdec] at hd'
  cases hd'
  rw [resultΨM_true]
  iunfold resultΨOn
  iexists ar, x.log, sa, (kvLeasesOn γr.kv srvAuthSt0 A)
  isplitr
  · ipureintro; rfl
  isplitl [HTr]
  · iexact HTr
  isplitl
  rotate_left
  · iexact HeW
  iunfold resultIsWOn
  isplitr
  · ipureintro; exact Har0
  iexists x, x', out
  iframe HRes Hcert HMint Hcx' Hrcx' HGA HVA
  isplitr
  · ipureintro; exact ⟨Hstep0.1, Hstep0.2, rfl, Hwvf hpx, Htie⟩
  isplitr [HAu]; rotate_left
  · isplitr
    · iexact HtA
    iframe HAu
    ipureintro; exact Hwfl
  iunfold appliedWit
  iexists m.index
  rw [Hrd]
  iframe Hcm HLpre Hmono))

set_option hygiene false in
/-- An entry's application above the start (`v3` true) to the postcondition: the deferred update,
the result handed to the waiter (the NOSPACE branch dead, `Hnn`), at the call's names: the step
and floor (`Hstep0`), the auth layer's verdict tied (`Htie`), the model's state after it
(`hmod`, `hc'`) at the table `lt'`, the auth row at `sa'` (`HAR`), the rest buckets one entry later (`HRS`). -/
local macro "tail_on" sa':term:max lt':term:max : tactic => `(tactic| (
  ihave Hj : iprop(|={⊤}=> ∃ st1 : ApplyState, applyThread γ st1 ∗
      ciApplying ci m.index m.term ∗ applyBackend γ ci b ∗
      ⌜st1 = ⟨m.index, m.index, m.index, false⟩ ∨ st1 = { st with p := m.index }⌝) $$ [Hout]
  · icases Hout with (⟨Hst, Happ, Hbe⟩ | ⟨Hst, Happ, Hbe, -⟩)
    · imodintro; iexists _; iframe Hst Happ Hbe; ipureintro; left; rfl
    · imod skip_done γ st m.index Hp hi hlt $$ Hinv Hst with Hst
      imodintro; iexists _; iframe Hst Happ Hbe; ipureintro; right; rfl
  imod Hj with ⟨%st1, Hst, Happ, Hbe, %hst1⟩
  ihave Hrt := bkRTOf_srv E dB Hd $$ Hrt
  ihave Hbo := Hbo $$ Hpl Hrt
  iunfold apply.applyTok at Htt
  irename Htt => Hmr
  imod applyKV_writer hPers hReach E HwOk ua x' $$ HsI HKV with ⟨HKV, #Hcert, #Hcx', #Hrcx', %Hwf'⟩
  have Hlen : x'.log.length < 2 ^ 63 := by obtain ⟨_, -, h⟩ := Hwf'; omega
  have Hwfl : mvcc.LogWf' x'.log ∧ x'.log.length + 3 ≤ 2 ^ 63 := by
    obtain ⟨_, hr, h⟩ := Hwf'; exact ⟨(mvcc.api.reach_logWf _ hr).1, h⟩
  imod revAuth_step E x.log x'.log (applyStep_grow Hstep0.1) Hlen ⊤ $$ HRA with ⟨HRA, HMint⟩
  ihave Hka : kvAppliedLOn γr.raft γr.kv srvAuthSt0 (A ++ [m]) ($sa', x'.log, $lt') $$ [Hka]
  · rw [hmod]; iexact Hka
  ihave ⟨Hka, -, %Hafter⟩ := kvAppliedLOn_cert _ _ _ _ _ $$ Hka
  ihave ⟨Hka, #HkL⟩ := kvApplied_nextOn γr A m x' $sa' _ m.index hiA (hc'.trans Hxch) $$ Hka
  -- (E3t) the auth state after the entry published, for the waiter
  imod srvAuthApplyResB_publish s ua E γa $sa' hM $$ Hb HAR with ⟨HAR, #HpA⟩
  imod applied_predepositM true s E γr v m.index x.log x'.log Hvi
    (applyStep_prefix rq true x x' out Hstep0.1) $$ Hainv Hao HLv HkL with Hpre
  icases srvAppliedPre_log γr v m.index x'.log $$ Hpre with ⟨Hpre, #HLpre⟩
  ihave HKV : iprop(∃ (x'' : apply.ApplyKV) (out' : apply.ApplyOut) (sa'' : auth.AuthState),
      srvApplyKVOn s E ρ.wait x'' sa'' ∗ ⌜entryStep m true x x'' out'⌝ ∗
      entryDelivered ρ.wait m ot out' ∗ srvAppliedPre γr v m.index x''.log ∗
      kvAppliedOn γr.raft γr.kv srvAuthSt0 (A ++ [m]) x'' sa'' (kvLeasesOn γr.kv srvAuthSt0 (A ++ [m])) ∗ srvRestM true E γr (A ++ [m]))
      $$ [HKV Hua Hbo HRD HRA HAR Hrdat Hpre Hka HRS]
  · iexists x', out, $sa'
    iframe Hpre Hka HRS
    isplitl
    · repack
    isplitr
    · ipureintro; unfold entryStep; rw [ite_eq_right hdata]
      exact ⟨rq, id0, hdec, hid, Hstep0.1⟩
    iunfold entryDelivered
    icases Hdel with (%Hwv | #Hg)
    · ileft; ipureintro; right; exact Hwv
    · iright; iexists rq, id0; iframe Hg; ipureintro; exact ⟨hdec, hid⟩
  (try wp_auto)
  wp_if_destruct
  · (try wp_auto)
    tail_any
  iunfold apply.resultErrOk at Har
  icases Har with (%Hnull | ⟨%err, #Herr, #HerrIs⟩)
  · exact absurd Hnull Hif
  have Har0 : ar ≠ null := Hif
  ihave HGA := HGA0 $$ %Har0
  ihave HVA := HVA0 $$ %Har0
  ihave Hei : (go_etcd_io.etcd.server.v3.etcdserver.errors.errorsInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Perrs
  icases Hei with ⟨⟨%ens, #Hens, %Hensp⟩, -⟩
  icases Hnn with (%Hn0 | ⟨%err', #Herr', #Hnn⟩)
  · exact absurd Hn0 Har0
  icombine Herr Herr' gives %Heq
  subst Heq
  (try wp_auto)
  wp_apply (wp_Is_notNoSpace hIs err ens Hensp) $$ []
  · iframe #
  iunfold waitInvM at Hwok
  icases Hwok with ⟨⟨%RD0, Hwok⟩, #Hwn⟩
  iunfold isWait at Hwok
  icases Hwok with ⟨%wi, %Hwi, -, #HTrig, -⟩
  subst Hid
  -- the entry at its position after the applied raft log `A`, whose mode-`on` model is the
  -- auth state and the log the entry met
  ihave #Hcl0a : idClaimAny ρ.ids id m.data γf $$ []
  · iunfold idClaimAny; iexists k0; iexact Hcl0
  ihave #HeW : iprop(entryWitOn E.authMode ρ rq x.log sa (kvLeasesOn γr.kv srvAuthSt0 A)) $$ []
  · iunfold entryWitOn
    iexists A ++ [m], A.length, m, id, γf
    simp only [ReqNames.raft, ReqNames.kv, Hrd]
    iframe HAm Hcl0a
    isplitr
    · ipureintro
      refine ⟨by simp, Htyp, hdec, hid, ?_⟩
      rw [List.take_left' rfl, ← Hxl]
    have htk : (A ++ [m]).take (A.length + 1) = A ++ [m] := List.take_of_length_le (by simp)
    rw [htk, ← Hafter]
    iexact HpA
  (try wp_auto)
  rw [Hwi]
  (try wp_auto)
  (try dsimp only)
  ihave #HT := HTrig $$ %id %(interface.mkOk (go.GoType.PointerType
    go_etcd_io.etcd.server.v3.etcdserver.apply.Result.ty) #ar)
  ihave %Hot := entryRegd_none_key ρ.wait ρ.ids m ot rq id γf k0 ⟨hdec, hid⟩ $$ Hreg Hcl0
  icases Hdel with (%Hwv | #Hg)
  · have Hwvf : k0 = ρ.ids.key → out.waived = false := fun _ => Hwv
    wp_apply HT $$ [HRes HTr HMint HAu HGA HVA]
    · trig_on
    (try wp_auto)
    tail_any
  · cases ot with
    | some t =>
      wp_apply HT $$ []
      · ileft; iexists t; iunfold waitGoneOpt at Hg; iexact Hg
      (try wp_auto)
      tail_any
    | none =>
      have Hwvf : k0 = ρ.ids.key → out.waived = false := fun h => absurd h (Hot rfl hdata)
      wp_apply HT $$ [HRes HTr HMint HAu HGA HVA]
      · trig_on
      (try wp_auto)
      tail_any))

set_option hygiene false in
/-- The uber-applier's row put back (`srvApplyKVOn`), as `EtcdServer__applyEntryNormal.lean`'s. -/
local macro "repackR" : tactic => `(tactic| (
  iunfold srvApplyKVOn
  iexists ua
  isplitl [Hua]
  · iexact Hua
  isplitr
  · iexact Hb
  isplitr
  · iexact Happl
  isplitl [HKV]
  · iexact HKV
  isplitl [Hbo]
  · iexact Hbo
  isplitl [HRA]
  · iexact HRA
  isplitl [HAR]
  · iexact HAR
  isplitr [Hrdat]
  · iexists fv.w, RD; iframe Hw Hwok' HRD
  iexact Hrdat))

set_option hygiene false in
/-- After `apply.Apply`: the KV row's certificate, its revision authority, the return. -/
local macro "tailR" : tactic => `(tactic| (
  ihave HFS : srvFS s $$ [HFS]
  · rw [← HEo.1]; iexact HFS
  imod applyKV_writer hPers hReach E HwOk ua x' $$ HsI HKV with ⟨HKV, -, -, -, %Hwf'⟩
  have Hlen : x'.log.length < 2 ^ 63 := by obtain ⟨_, -, h⟩ := Hwf'; omega
  imod revAuth_step E x.log x'.log (applyStep_grow Hstep) Hlen ⊤ $$ HRA with ⟨HRA, -⟩
  (try wp_auto)
  imodintro
  first | iapply HΦ | (wp_pures; iapply HΦ)
  iframe Hbe Hst Hlr Hgr Hmr HFS HRS
  iexists x', out
  isplitl
  · repackR
  ipureintro; unfold entryStep; rw [ite_eq_right hdata]; exact ⟨rq, id0, hdec, hid, Hstep⟩))

/-- `srvUberOn_kv` at the apply thread's window `wn` (auth-lease S4 item 7b): the row's KV contract at
`{ E with win := wn }` (the base's resources do not read the window). -/
theorem srvUberOn_kv_win (s : Loc) (E : apply.AEnv GF) (wn : Option lease.LWin) (γa : auth.AuthNames)
    (ua : GoInterface) (hM : E.authMode = .on γa) (γc : auth.AuthBkNames) :
    srvUberOn (GF := GF) s ∗ srvUberBase s ua E ⊢
      ∃ stl : Loc, srvAuthStoreAddr s ↦□ auth.authIface stl ∗
        apply.uberKVC ua { E with win := wn } (.quota .backend) (auth.latestResC stl (.on γa) γc) :=
  srvUberOn_kv s { E with win := wn } γa ua hM γc

/-- `srvUberOn_adm` at the apply thread's window `wn` (as `srvUberOn_kv_win`). -/
theorem srvUberOn_adm_win (s : Loc) (E : apply.AEnv GF) (wn : Option lease.LWin) (γa : auth.AuthNames)
    (ua : GoInterface) (stl bel : Loc) (T : auth.AuthBkNames) (Pk Wb : IProp GF) (hM : E.authMode = .on γa)
    (hPk : E.Pk = fun _ => Pk) :
    srvUberOn (GF := GF) s ∗ srvUberBase s ua E ∗ srvAuthStoreAddr s ↦□ auth.authIface stl ∗
      □ (apply.bkWTFor E -∗ Wb) ∗
      apply.isAuthStepsX (auth.authIface stl) Pk E.f (.on γa) (auth.tieRes stl (.on γa))
        (adminW stl bel (.on γa) Pk E.f (auth.authWTok T) Wb) Wb E.RD ⊢
      apply.uberAdmC ua { E with win := wn } (adminWC stl bel γa Pk E.f T Wb)
        (fun γa' h => iprop(auth.authOwnFu γa' h ∗ auth.tieRes stl (.on γa) h))
        (auth.latestResC stl (.on γa) T) :=
  srvUberOn_adm s { E with win := wn } γa ua stl bel T Pk Wb hM hPk

/-- `apply.Apply.kvSpecL` at the apply thread's lessor window `wn` (auth-lease S4 item 7b, 2026-11-17): the triple at
`{ E with win := wn }`, with the resources that do not read the window at `E` (definitionally the same). -/
theorem Apply_kvSpecL_win (h : apply.Apply.kvSpecL (GF := GF) (hG := hG)) :
    ∀ (lg e : Loc) (m : EntryModel) (ua w : GoInterface) (v3 : Bool) (E : apply.AEnv GF) (wn : Option lease.LWin)
    (Pre Q Post : IProp GF) (x : apply.ApplyKV) (rq : apply.IRRModel) (id : w64) (RD : IProp GF)
    (K G : Option GName → w64 → IProp GF) (ot : Option GName) (F : mvcc.Log) (rs : apply.RestM)
    (ci : apply.Chain) (L : List auth.AuthState → IProp GF) (hs : List auth.AuthState) (T : List w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
      apply.uberKVC ua { E with win := wn } ci L ∗ waitOk w RD K G ∗ RD ∗ K ot id ∗ zapLoggerOk lg ∗ entryAt e m ∗
      (∃ p : Loc, ⌜ua = interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.apply.uberApplier.ty) #p⌝ ∗
        apply.uberOwn { E with win := wn } p x.chain ∗ apply.kvOwnPre v3 { E with win := wn } x.log Pre Q Post ∗
        apply.cmpOwn { E with win := wn } x.crev) ∗
      apply.certPreVW v3 E x.chain rq x.log
        (apply.kvOutLT E.authMode E.lg hs (auth.authInfoM (apply.principalOf rq)) ci rq x.log T) ∗
      ⌜apply.irrDecode m.data = some rq ∧ apply.irrId rq = some id ∧ apply.rqOk E.lm x.log rq ∧
        apply.dispatchOk E.authOn rq⌝ ∗ ⌜(E.lg = true → apply.winTgtL E.authMode hs (auth.authInfoM (apply.principalOf rq)) ci rq x.log wn T) ∧
          (E.lg = false → wn = none)⌝ ∗
      srvApi.kvLogLb E.γs F ∗ apply.applyTok E ∗
      E.FS ∗ (if v3 then apply.ciSplit E Pre else iprop(True)) ∗ E.RO rs ∗
      apply.ltHalf E T ∗ apply.revokeOwn E rq ∗ L hs ∗
      ⌜x.chain = apply.baseChain E.authOn ∧ apply.authKVKind (apply.dispatchKind rq) = true ∧
        apply.kvShapedL E.authMode hs x.log rq⌝ }}
    (App (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.apply.Apply))
      (Val #lg)) (Val #e)) (Val #ua)) (Val #w)) (Val #v3))
  {{ (ar : Loc) (id' : w64), RET (PairV #ar #id'); apply.applyTok E ∗ apply.bkRTOf E ∗
      RD ∗ E.FS ∗ apply.revokeOwn E rq ∗
      (if v3 then iprop(Post ∨ Pre) else Pre) ∗ apply.resultErrOk ar ∗ apply.resTrace ar ∗
      ⌜id' = id⌝ ∗
      ∃ (x' : apply.ApplyKV) (out : apply.ApplyOut), apply.applyKV { E with win := wn } ua x' ∗
        apply.ltHalf E (apply.revokeIdsA rq v3 out T) ∗
        E.RO (apply.revokeRestA T rq v3 out (apply.restOut rq v3 out rs)) ∗ apply.revokeAnsRA E rq out ar ∗
        ⌜apply.applyStep rq v3 x x' out ∧ apply.applyFloorOk rq v3 F x.log out⌝ ∗
        apply.applyResultIs rq v3 x.log ar out ∗ apply.applyAuthRes E.authMode x.chain rq v3 out ∗
        L hs ∗
        ⌜∀ o b, out = .dispatched o b → v3 = true →
          apply.kvOutL E.authMode hs (auth.authInfoM (apply.principalOf rq)) ci rq x.log o⌝ ∗
        ⌜∀ o b, out = .dispatched o b → v3 = true → E.lg = true → apply.leaseExactL T rq x.log o⌝ ∗
        (⌜out.waived = false⌝ ∨ G ot id) }} :=
  fun lg e m ua w v3 E wn Pre Q Post x rq id RD K G ot F rs ci L hs T => h lg e m ua w v3 { E with win := wn } Pre Q Post x rq id RD K G ot F rs ci L hs T

/-- `adminEntryOn.spec` at the apply thread's lessor window `wn` (auth-lease S4 item 7b, 2026-11-17): the triple at
`{ E with win := wn }`, with the resources that do not read the window at `E` (definitionally the same). -/
theorem adminEntryOn_win (h : adminEntryOn.spec (GF := GF) (hG := hG)) :
    ∀ (lg e : Loc) (m : EntryModel) (ua w : GoInterface) (v3 : Bool) (E : apply.AEnv GF) (wn : Option lease.LWin)
    (Pre Q Post : IProp GF) (x : apply.ApplyKV) (rq : apply.IRRModel) (id : w64) (RD : IProp GF)
    (K G : Option GName → w64 → IProp GF) (ot : Option GName) (γa : auth.AuthNames)
    (stl bel : Loc) (T : auth.AuthBkNames) (Pk Wb : IProp GF) (st : auth.AuthState) (rs : apply.RestM)
    (hs : List auth.AuthState),
    E.authMode = .on γa → apply.noSideEffect rq = false → E.Pk = (fun _ => Pk) →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply ∗
        Perennial.EtcdGrove.apply.uberAdmC ua { E with win := wn } (adminWC stl bel γa Pk E.f T Wb)
          (fun γa' h => iprop(auth.authOwnFu γa' h ∗ auth.tieRes stl (.on γa) h))
          (auth.latestResC stl (.on γa) T) ∗
        waitOk w RD K G ∗ RD ∗ K ot id ∗ zapLoggerOk lg ∗ entryAt e m ∗
        apply.bkToks v3 E Pre Q Post ∗ Pre ∗
        apply.applyKV { E with win := wn } ua x ∗ apply.applyTok E ∗
        ⌜apply.irrDecode m.data = some rq ∧ apply.irrId rq = some id ∧ apply.adminKindOk rq ∧
          apply.dispatchOk E.authOn rq ∧ receiptBound GF ≤ 2 ^ 48⌝ ∗
        ⌜x.chain = apply.baseChain E.authOn⌝ ∗
        (auth.authOwnFu γa hs ∗ auth.tieRes stl (.on γa) hs ∗ ⌜hs.getLast? = some st⌝) ∗
        auth.authWHeld γa T ∗ auth.tpAdmin stl (.on γa) ∗
        authWBackendAt bel (.on γa) Pk E.f (auth.authWTok T) Wb ∗
        roLendsAuthBe E.RO stl bel ∗ E.RO rs ∗ ⧗ 1 ∗ apply.adminWTs E ∗ (if v3 then apply.adminExtraG E γa rq hs Pre else iprop(True)) }}
      (App (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.apply.Apply))
        (Val #lg)) (Val #e)) (Val #ua)) (Val #w)) (Val #v3))
    {{ (ar : Loc) (id' : w64), RET (PairV #ar #id'); RD ∗ apply.applyTok E ∗ apply.bkRTOf E ∗
        (if v3 then iprop(Post ∨ Pre) else Pre) ∗
        apply.resultErrOk ar ∗ apply.resTrace ar ∗ ⌜id' = id⌝ ∗
        ∃ (x' : apply.ApplyKV) (out : apply.ApplyOut), apply.applyKV { E with win := wn } ua x' ∗
          ⌜apply.applyStep rq v3 x x' out ∧ x'.log = x.log ∧ x'.chain = x.chain⌝ ∗
          apply.applyResultIs rq v3 x.log ar out ∗ (⌜out.waived = false⌝ ∨ G ot id) ∗
          apply.adminRejErr ar out ∗
          (if v3 then iprop(⌜ar = null⌝ ∨ ∃ err : GoInterface,
              structFieldRef go_etcd_io.etcd.server.v3.etcdserver.apply.Result go!"Err" ar ↦□ err ∗
              notNoSpaceErr err)
           else iprop(True)) ∗
          E.RO rs ∗ auth.authWHeld γa T ∗ auth.tpAdmin stl (.on γa) ∗
          ∃ (hs' : List auth.AuthState) (st' : auth.AuthState),
            auth.authOwnFu γa hs' ∗ auth.tieRes stl (.on γa) hs' ∗
            ⌜hs'.getLast? = some st' ∧ (if v3 then adminStateR rq st st' else st' = st)⌝ ∗
            (if v3 then adminTieAr ar rq st st' out else iprop(True)) ∗
          (if v3 then adminAuthnAr γa ar rq out else iprop(True)) }} :=
  fun lg e m ua w v3 E wn Pre Q Post x rq id RD K G ot γa stl bel T Pk Wb st rs hs hM hn hPk =>
    h lg e m ua w v3 { E with win := wn } Pre Q Post x rq id RD K G ot γa stl bel T Pk Wb st rs hs hM hn hPk

set_option maxHeartbeats 3200000 in
theorem EtcdServer.applyEntryNormal.wp_proofOn
    (hGI : raftpb.Entry.GetIndex.spec (GF := GF) (hG := hG))
    (hGT : raftpb.Entry.GetTerm.spec (GF := GF) (hG := hG))
    (hC : consistentIndex.ConsistentIndex.spec (GF := GF) (hG := hG))
    (hS : consistentIndex.SetConsistentIndex.spec (GF := GF) (hG := hG))
    (hN : notify.Notifier.Notify.spec (GF := GF) (hG := hG))
    (hL : EtcdServer.isLeader.spec (GF := GF) (hG := hG))
    (hE : config.ServerConfig.ElectionTimeout.spec (GF := GF) (hG := hG))
    (hA0 : apply.Apply.spec (GF := GF) (hG := hG))
    (hUb : apply.uberApplier.Apply.spec (GF := GF) (hG := hG))
    (hIs : errors.Is.spec (GF := GF) (hG := hG))
    (hAG : v3alarm.AlarmStore.Get.spec (GF := GF) (hG := hG))
    (hLg : EtcdServer.Logger.spec (GF := GF) (hG := hG))
    (hZS : zap.String.spec (GF := GF) (hG := hG))
    (hZI : zap.Int64.spec (GF := GF) (hG := hG))
    (hZE : zap.Error.spec (GF := GF) (hG := hG))
    (hHB : go_humanize.Bytes.spec (GF := GF) (hG := hG))
    (hW : zap.Logger.Warn.spec (GF := GF) (hG := hG))
    (hGA : EtcdServer.GoAttach.spec (GF := GF) (hG := hG))
    (hMID : EtcdServer.MemberID.spec (GF := GF) (hG := hG))
    [mvccSem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
    (hPers : mvcc.api.persistent.law (GF := GF) (hG := hG))
    (hReach : mvcc.api.mvccState_reachable.law (GF := GF) (hG := hG)) :
    EtcdServer.applyEntryNormal.specOn (GF := GF) (hG := hG) := by
  have hA := apply.Apply.spec_rec hA0 hUb
  have hK := apply.Apply.wp_kvL hA0
  have hAd := apply_admin_entry_on (apply.Apply.wp_adminL hA0)
  have hGI := wp_entryAt_GetIndex hGI
  have hGT := wp_entryAt_GetTerm hGT
  intro s γ ci TM E ρ b e m st v3 x γr ot v A γa sa A₀ r hM
  cases v3
  · -- (R2d'a, Q23 (a)) a replay: v2-only, the rest buckets at the backend's log
    simp only [Bool.false_eq_true, ↓reduceIte]
    wp_start as ⟨#Hsrv, #Hewo, #He, Hst, Hbe, Hlr, Hgr, Hmr, HKV, Hwt, HFS, Hlc, Hawt, #Hcm, HRS, #HA0, %HmA,
      %Hpo⟩
    obtain ⟨Hp, Hok, Htyp, Hci, Hrb, Hxch, Hmem⟩ := Hpo
    have hAuthOn : E.authOn = true := by rw [apply.AEnv.authOn_eq, hM]; rfl
    wp_apply wp_with_defer as %defer defer
    iunfold isServerM at Hsrv
    icases Hsrv with ⟨%Hrd, #Hsci, ⟨%fv, #Hfv⟩, #Hat, #Hgen, -⟩
    ihave #Hat' := Hat
    iunfold srvAtomicsM at Hat'
    icases Hat' with ⟨-, -, #Hkvi⟩
    ihave #Huon := srvKVInvsM_uberOn _ _ _ $$ Hkvi
    ihave #Hkvi : srvKVInvsOn E γr srvAuthSt0 $$ []
    · iapply srvKVInvsM_true; iexact Hkvi
    ihave #Hkvi' := Hkvi
    iunfold srvKVInvsOn at Hkvi'
    icases Hkvi' with ⟨#HkI, -, #HrI, #Htie0, #HsI, %Hktie, %HNx, %Hrows, -⟩
    have HwOk := Hktie.1
    have ⟨hNxP, hNxT, hCpP, hCpT⟩ := HwOk
    -- the committed entry's shape (the KV invariant's, `kv_log_plain_on`)
    imod kv_log_plain_on γr.raft γr.kv srvAuthSt0 A₀ $$ HkI HrI HA0 with %Hpc0
    -- (auth-lease S3a rev 7) the entry at the environment's lease mode (`srvKVInvsOn`'s `lm = E.lm`)
    have Hpe : plainEntryOn E.lm m := by
      obtain ⟨-, hlmE, -⟩ := Hrows; rw [← hlmE]; exact Hpc0.1 m HmA
    have Hch : x.chain = apply.alarmChain true false false := Hxch.trans Hpc0.2.2
    imod srvApplyKVOn_writer hPers hReach s E γr srvAuthSt0 ρ.wait x sa $$ Hkvi HKV with
      ⟨HKV, #Hcx, -, -, %Hwf⟩
    icases srvApplyKVOn_authOn s E ρ.wait x sa $$ HKV with ⟨HKV, %HaOn⟩
    iunfold srvFieldsAtM at Hfv
    icases Hfv with ⟨#Hlg, #Hlgnn, #Hw, #Hwok, %HE, %HEo, #Hhook, #Hlv, #Hlok, #Hfc, #Has, #Hcl,
      #Hrc, #Hq, #Hlgmu, #Hmid, #Hlead, #Het, #Htm, #Hnot, #Halm⟩
    ihave ⟨%Hnn, %d, #Hfd, #Hds⟩ := entryAt_fields _ _ $$ He
    ihave %Hdlen := ownSlice_len _ _ _ $$ Hds
    ihave #Papp : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply $$ []
    · iPkgInit
    iunfold lessorOk at Hlok
    icases Hlok with ⟨%li, %Hli, #HPromote, -, -⟩
    wp_auto
    wp_if_destruct
    · -- no data: the first commit's notice, the lessor's promotion at a leader
      have hnil : m.data = [] := by
        apply List.eq_nil_of_length_eq_zero; rw [Hdlen.1, Hif]; rfl
      ihave HKV : iprop(∃ (x' : apply.ApplyKV) (out : apply.ApplyOut), srvApplyKVOn s E ρ.wait x' sa ∗
          ⌜entryStep m false x x' out⌝) $$ [HKV]
      · iexists x, apply.ApplyOut.skipped
        iframe HKV
        ipureintro; unfold entryStep; rw [ite_eq_left hnil]; exact ⟨rfl, rfl⟩
      ihave HRS : srvRestRpM true E γr A₀ (restEntryV2 m r) $$ [HRS]
      · rw [restEntryV2_nodata m r Htyp hnil]; iexact HRS
      wp_apply hN fv.firstCommit
      · iexact Hnot
      wp_apply hL s fv.memberID as %ldr -
      · iframe Hmid Hlead
      cases ldr
      · (try wp_auto)
        iapply HΦ
        iframe Hbe Hst Hlr Hgr Hmr HFS HKV HRS
      · (try wp_auto)
        wp_apply hE (srvCfgAddr s) fv.electionTicks fv.tickMs as %dur -
        · iframe Het Htm
        rw [Hli]
        (try wp_auto)
        (try dsimp only)
        ihave #HP := HPromote $$ %dur
        -- (prove-ps2-promote) `Promote` borrows the thread token (its sort's `Remaining()`)
        iunfold srvGoRes at Hgr
        icases Hgr with ⟨Hwgr, Htk⟩
        wp_apply HP $$ [$Htk] as Htk
        ihave Hgr : srvGoRes s $$ [Hwgr Htk]
        · iunfold srvGoRes; iframe
        (try wp_auto)
        iapply HΦ
        iframe Hbe Hst Hlr Hgr Hmr HFS HKV HRS
    · -- data: the applier, v2-only
      have hdata : m.data ≠ [] := by
        intro h; apply Hif
        have h1 := Hdlen.1; rw [h] at h1; simp only [List.length_nil] at h1
        have h2 := Hdlen.2
        have h1' : (sint.Z d.len).toNat = 0 := h1.symm
        have h3 : sint.Z d.len = 0 := by omega
        word
      obtain ⟨rq, hdec, ⟨id0, hid⟩, hrq, hdk⟩ := Hok.resolve_left hdata
      iunfold srvApplyKVOn at HKV
      icases HKV with ⟨%ua, Hua, #Hb, #Happl, HKV, Hbo, HRA, HAR, ⟨%w', %RD, #Hw', #Hwok', HRD⟩,
        Hrdat⟩
      icombine Hw Hw' gives %Hweq
      subst Hweq
      iunfold srvApplyKVW at HKV
      icases HKV with ⟨%wn, %Hwn, HKV⟩
      -- the rest buckets at the backend's table: `apply.Apply`'s image, half and ids
      ihave ⟨HRS, HEv⟩ := (srvRestRpM_eq_at true E γr A₀ r).1 $$ HRS
      ihave ⟨%f, %Hfb, HRS, HLt, #HGI, #HRq⟩ := (srvRestAt_open E _ _).1 $$ HRS
      ihave ⟨%U, HEv, %HUok⟩ := srvEver_open E A₀ $$ HEv
      -- (strict M1) the tie's backend's tokens, the thread's token
      icases srvBeOwn_pool s E $$ Hbo with ⟨%dB, %Hd, #Hbro, HplB, Hrt, Hbo⟩
      ihave Hwt := srvWT_at E dB Hd $$ Hwt
      ihave Htk := bkToks_srv false E dB Hd iprop(True) iprop(True) iprop(True) $$ [Hwt Hrt]
      · iframe Hwt Hrt; simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
      ihave Htt : apply.applyTok (GF := GF) E $$ [Hmr]
      · iunfold apply.applyTok; iexact Hmr
      rcases Hpe Htyp hdata rq hdec with hpl0 | ⟨hadm, hns⟩
      · -- a plain request, a grant or a revocation: `apply.Apply`, nothing written
        obtain ⟨hpl, hnadm⟩ := plainOrCmpG_of_entryOn E.lm rq hpl0
        have hrq' : apply.rqOk E.lm x.log rq := hrq.resolve_right hnadm
        ihave #Hcp : apply.certPreV false E x.chain rq x.log $$ []
        · simp only [apply.certPreV, Bool.false_eq_true, ↓reduceIte]; itrivial
        ihave HFSE : E.FS $$ [HFS]
        · rw [HEo.1]; iexact HFS
        ihave HSpF : iprop(if false = true then apply.ciSplit E iprop(True) else iprop(True)) $$ []
        · simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
        ihave #HGf : iprop(□ (⌜false = true⌝ → apply.grantFresh E rq U)) $$ []
        · iintro !> %h; cases h
        ihave #Hgpq : iprop(□ (⌜false = true⌝ → apply.grantPermRq E rq)) $$ []
        · iintro !> %h; cases h
        ihave #Hcpq : iprop(□ (⌜false = true⌝ → apply.cmpPermRq E rq)) $$ []
        · iintro !> %h; cases h
        iapply wp_fupd
        (try wp_auto)
        ihave %Hat := entryWaitOk_attr ρ E m Htyp $$ Hewo
        have Hrr : apply.restReqOk rq r := by
          intro hk a ha'
          have hin := ((Hat Htyp hdata rq hdec) hk).2 a ha'
          have hin' : a.memberID ∈ γr.raft.raft.cfg := by rw [← Hrd]; exact hin
          exact Hmem _ hin'
        ihave ⟨Hrv, Hrdb⟩ := revokeOwn_take E rq hpl $$ [Hrdat]
        · iframe Hrdat HGI
        wp_apply Apply_specRec_win hA fv.lg e m ua fv.w false E wn iprop(True) iprop(True) iprop(True) x rq id0 RD
          (fun ot id => waitRegdOpt ρ.wait id ot) (fun ot id => waitGoneOpt ρ.wait id ot) none x.log
          _ _ U $$ [HKV Htk Htt HRD HFSE HSpF HRS HLt HEv Hrv]
          as %ar %id ⟨HRD, HFS, Htt, Hrt, -, #Har, -, %Hid, %x', %out, HKV, HLt, HEv, Hrv, HRS, %Hgo,
            -, -, %Hstep0, -, -, -⟩
        · iframe Happl Hwok' HRD He HKV Htk Htt Hcp HFSE HSpF HRS HLt HEv HGf Hrv Hgpq
          isplitr
          · simp only [waitRegdOpt]; itrivial
          simp only [Bool.false_eq_true, ↓reduceIte]
          isplitr
          · iexact Hlgnn
          iframe Hcx
          iframe Hcpq
          ipureintro
          exact ⟨⟨hdec, hid, hrq', HaOn ▸ hdk, fun h => absurd h (by decide),
            by unfold apply.restReqOk; rw [apply.restLeasesWith_mem]; exact Hrr⟩, ⟨fun _ h => absurd h (by decide), Hwn⟩⟩
        ihave HKV := srvApplyKVW_of E wn ua x' Hwn $$ HKV
        have Hstep := Hstep0.1
        ihave Hrdat := Hrdb $$ Hrv
        ihave Hrt := bkRTOf_srv E dB Hd $$ Hrt
        ihave Hbo := Hbo $$ HplB Hrt
        iunfold apply.applyTok at Htt
        irename Htt => Hmr
        rw [(idsA_false rq out _).1, (idsA_false rq out U).2]
        icases HRS with ⟨%t, -, HRS⟩
        rw [restOutA_false E.lm rq x x' out _ t _ hpl Hstep,
          apply.restLeasesWith_comm (apply.restAfter rq false) (apply.restAfter_restGrantT rq false),
          ← restEntryV2_req m rq r Htyp hdata hdec]
        ihave HRS : srvRestRpM true E γr A₀ (restEntryV2 m r) $$ [HRS HLt HEv]
        · iapply (srvRestRpM_eq_at true E γr A₀ _).2
          isplitl [HRS HLt]
          · iapply (srvRestAt_open E _ _).2
            iexists f
            iframe HRS HLt HGI HRq
            ipureintro; exact Hfb
          iunfold srvEver; iexists U; iframe HEv; ipureintro; exact HUok
        tailR
      · -- an admin request: the auth row's admin steps (`adminEntryOn`), nothing applied
        icases srvAuthApplyResB_open s E γa sa hM $$ HAR with ⟨%stl, %bel, %T, %Pk, %Wb, %hs, %HPk, #Hwbc, #Hasf, #Hlend,
          #Hwba, #Hsteps, Hfu, Htie, %Hhl, HT, Htp, Hcl⟩
        ihave #HUA := srvUberOn_adm_win s E wn γa ua stl bel T Pk Wb hM HPk $$ []
        · iframe Huon Hb Hasf Hwbc Hsteps
        iapply wp_fupd
        (try wp_auto)
        wp_apply adminEntryOn_win hAd fv.lg e m ua fv.w false E wn iprop(True) iprop(True) iprop(True) x rq id0 RD
          (fun ot id => waitRegdOpt ρ.wait id ot) (fun ot id => waitGoneOpt ρ.wait id ot) none γa stl
          bel T Pk Wb sa _ hs hM hns HPk $$ [HKV Htk Htt HRD Hfu Htie HT Htp HRS Hlc Hawt]
          as %ar %id ⟨HRD, Htt, Hrt, -, #Har, -, %Hid, %x', %out, HKV, %Hstep0, -, -, -, -, HRS, HT,
            Htp, %hs', %sa', Hfu, Htie, %Hsa', -, -⟩
        · simp only [↓reduceIte, Bool.false_eq_true]
          iframe HUA Hwok' HRD He HKV Htk Htt HT Htp Hwba Hlend HRS Hlc Hawt
          isplitr
          · simp only [waitRegdOpt]; itrivial
          isplitr
          · iexact Hlgnn
          isplitr
          · ipureintro; exact ⟨hdec, hid, hadm, HaOn ▸ hdk, Hrb⟩
          isplitr
          · ipureintro; rw [Hch, hAuthOn]; rfl
          iframe Hfu Htie; ipureintro; exact Hhl
        ihave HKV := srvApplyKVW_of E wn ua x' Hwn $$ HKV
        obtain ⟨Hstep, -, -⟩ := Hstep0
        ihave Hrt := bkRTOf_srv E dB Hd $$ Hrt
        ihave Hbo := Hbo $$ HplB Hrt
        iunfold apply.applyTok at Htt
        irename Htt => Hmr
        have hsa' : sa' = sa := by simpa using Hsa'.2
        ihave HAR := Hcl $$ %hs' %sa Hfu Htie %(by rw [← hsa']; exact Hsa'.1) HT Htp
        obtain ⟨h1, h2⟩ := adminKindOk_noCluster rq hadm
        have hR : restEntryV2 m r = r := by
          rw [restEntryV2_req m rq r Htyp hdata hdec, apply.restAfter_other rq _ _ h1 h2]
        ihave HRS : srvRestRpM true E γr A₀ (restEntryV2 m r) $$ [HRS HLt HEv]
        · rw [hR]
          iapply (srvRestRpM_eq_at true E γr A₀ _).2
          isplitl [HRS HLt]
          · iapply (srvRestAt_open E _ _).2
            iexists f
            iframe HRS HLt HGI HRq
            ipureintro; exact Hfb
          iunfold srvEver; iexists U; iframe HEv; ipureintro; exact HUok
        ihave HFS : E.FS $$ [HFS]
        · rw [HEo.1]; iexact HFS
        tailR
  simp only [↓reduceIte]
  wp_start as ⟨#Hsrv, #Hewo, #Hreg, #He, Hst, Hbe, Hlr, Hgr, Hmr, HKV, Hwt, HFS, Hlc, Hawt, Hao, #HLv,
    #Hcm, Hka, HRS, %Hmc, #HAm, %HkA', %Hvi, %Hpo, Hv3, Htok⟩
  have HkA : uint.Z v = uint.Z γr.raft.ai0 + A.length ∧
      true = decide (uint.Z γr.kv.c0 < uint.Z m.index) :=
    ⟨HkA'.1, (decide_eq_true HkA'.2).symm⟩
  obtain ⟨Hp, Hok, Htyp, Hrb⟩ := Hpo
  have hAuthOn : E.authOn = true := by rw [apply.AEnv.authOn_eq, hM]; rfl
  wp_apply wp_with_defer as %defer defer
  iunfold isServerM at Hsrv
  icases Hsrv with ⟨%Hrd, #Hsci, ⟨%fv, #Hfv⟩, #Hat, #Hgen, -⟩
  ihave #Hat' := Hat
  iunfold srvAtomicsM at Hat'
  icases Hat' with ⟨#Hainv, -, #Hkvi⟩
  ihave #Hmono := appliedMono_of_invM true s E γr $$ Hainv
  ihave #Huon := srvKVInvsM_uberOn _ _ _ $$ Hkvi
  ihave #Hkvi : srvKVInvsOn E γr srvAuthSt0 $$ []
  · iapply srvKVInvsM_true; iexact Hkvi
  ihave #Hkvi' := Hkvi
  iunfold srvKVInvsOn at Hkvi'
  icases Hkvi' with ⟨-, -, -, #Htie0, #HsI, %Hktie, %HNx, -, #HwTie⟩
  have HwOk := Hktie.1
  have ⟨hNxP, hNxT, hCpP, hCpT⟩ := HwOk
  imod srvApplyKVOn_writer hPers hReach s E γr srvAuthSt0 ρ.wait x sa $$ Hkvi HKV with
    ⟨HKV, #Hcx, -, -, %Hwf⟩
  obtain ⟨_, -, Hlx⟩ := Hwf
  icases srvApplyKVOn_authOn s E ρ.wait x sa $$ HKV with ⟨HKV, %HaOn⟩
  -- the mode-`on` model before the entry: `(sa, x.log, kvLeasesOn γr.kv srvAuthSt0 A)`, the start's chain
  iunfold kvAppliedOn at Hka
  icases Hka with ⟨Hka, %Hxch0⟩
  icases kvAppliedLOn_cert _ _ _ _ _ $$ Hka with ⟨Hka, -, %Hxl⟩
  ihave Hka : kvAppliedOn γr.raft γr.kv srvAuthSt0 A x sa (kvLeasesOn γr.kv srvAuthSt0 A) $$ [Hka]
  · iunfold kvAppliedOn; iframe Hka; ipureintro; exact Hxch0
  -- the model's step (E2 of the auth plan): the entry admitted and determinate, its state after
  imod kv_applied_step_on E γr srvAuthSt0 A m x sa _ (kvEntryOn_len _ _ sa x _ m Hok Hlx)
    $$ Hkvi Hka HAm with ⟨%Hpe, Hka⟩
  obtain ⟨Hpe, Hdet, Hxch, Hch⟩ := Hpe
  ihave #Hkvi' := Hkvi
  iunfold srvKVInvsOn at Hkvi'
  icases Hkvi' with ⟨#HkI', -, #HrI', -, -, -, -, %Hrows', -⟩
  -- (auth-lease S3a rev 7) the entry at the environment's lease mode (`srvKVInvsOn`'s `lm = E.lm`)
  have hlmE : γr.kv.lm = E.lm := Hrows'.2.1
  have hpreE : γr.raft.pre = [] := Hrows'.2.2
  have Hpe : plainEntryOn E.lm m := by rw [← hlmE]; exact Hpe
  imod (kvInvOn_keysA γr srvAuthSt0 (A ++ [m])) $$ HkI' HrI' HAm with %HkeysA
  icases kvAppliedLOn_nx _ _ _ _ _ HkeysA $$ Hka with ⟨Hka, #Hkc⟩
  have hiA : uint.Z m.index = uint.Z γr.raft.ai0 + A.length + 1 := by omega
  iunfold srvFieldsAtM at Hfv
  icases Hfv with ⟨#Hlg, #Hlgnn, #Hw, #Hwok, %HE, %HEo, #Hhook, #Hlv, #Hlok, #Hfc, #Has, #Hcl,
    #Hrc, #Hq, #Hlgmu, #Hmid, #Hlead, #Het, #Htm, #Hnot, #Halm⟩
  ihave ⟨%Hnn, %d, #Hfd, #Hds⟩ := entryAt_fields _ _ $$ He
  ihave %Hdlen := ownSlice_len _ _ _ $$ Hds
  ihave #Pnot : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.notify $$ []
  · iPkgInit
  ihave #Pcfg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.config $$ []
  · iPkgInit
  ihave #Papp : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.apply $$ []
  · iPkgInit
  ihave #Perr : isPkgInit (PROP := IProp GF) pkg_id.errors $$ []
  · iPkgInit
  ihave #Palm : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3alarm $$ []
  · iPkgInit
  ihave #Pzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  ihave #Phum : isPkgInit (PROP := IProp GF) pkg_id.github_com.dustin.go_humanize $$ []
  · iPkgInit
  ihave #Pci : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.cindex $$ []
  · iPkgInit
  ihave #Prpb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  ihave #Perrs : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.errors $$ []
  · iPkgInit
  iunfold lessorOk at Hlok
  icases Hlok with ⟨%li, %Hli, #HPromote, -, -⟩
  · -- the entry `i = p + 1`, above `ci`
    icases Hv3 with ⟨Happ, %Hv3⟩
    obtain ⟨hi, hlt, hce, hld⟩ := Hv3
    have hi0 : m.index ≠ W64 0 := by intro h; rw [h] at hlt; simp at hlt
    have hv : uint.Z γr.kv.c0 < uint.Z m.index := of_decide_eq_true HkA.2.symm
    -- (C1's A2) the rights at the entry: kept, or (an `Authenticate`) its token's right minted
    ihave HtokA := srvTokRights_next E _ m.index hce $$ Htok
    wp_auto
    wp_if_destruct
    · -- no data: processed with no writes
      icases HtokA with ⟨Htok, -⟩
      have hnil : m.data = [] := by
        apply List.eq_nil_of_length_eq_zero; rw [Hdlen.1, Hif]; rfl
      ihave Hka : kvAppliedLOn γr.raft γr.kv srvAuthSt0 (A ++ [m]) (sa, x.log, kvLeasesOn γr.kv srvAuthSt0 A) $$ [Hka]
      · irevert Hka; rw [kvEntryOn_nodata γr.kv.c0 x.chain (sa, x.log, kvLeasesOn γr.kv srvAuthSt0 A) m hnil]; iintro Hka
        iexact Hka
      ihave ⟨Hka, #HkL⟩ := kvApplied_nextOn γr A m x sa _ m.index hiA Hxch $$ Hka
      imod applied_predepositM true s E γr v m.index x.log x.log Hvi (List.prefix_refl _)
        $$ Hainv Hao HLv HkL with Hpre
      ihave HKV : iprop(∃ (x' : apply.ApplyKV) (out : apply.ApplyOut) (sa' : auth.AuthState),
          srvApplyKVOn s E ρ.wait x' sa' ∗ ⌜entryStep m true x x' out⌝ ∗
          entryDelivered ρ.wait m ot out ∗ srvAppliedPre γr v m.index x'.log ∗
          kvAppliedOn γr.raft γr.kv srvAuthSt0 (A ++ [m]) x' sa' (kvLeasesOn γr.kv srvAuthSt0 (A ++ [m])) ∗ srvRestM true E γr (A ++ [m]))
          $$ [HKV Hpre Hka HRS]
      · iexists x, apply.ApplyOut.skipped, sa
        iframe HKV Hpre Hka
        ihave HRS := srvRestM_nodata E γr A m Htyp hnil $$ HRS
        iframe HRS
        isplitr
        · ipureintro; unfold entryStep; rw [ite_eq_left hnil]; exact ⟨rfl, rfl⟩
        iunfold entryDelivered; ileft; ipureintro; left; exact hnil
      wp_apply hN fv.firstCommit
      · iexact Hnot
      wp_apply hL s fv.memberID as %ldr -
      · iframe Hmid Hlead
      iunfold isServerCI at Hsci
      icases Hsci with ⟨#Hcif, #Hci, #Hinv⟩
      imod skip_done γ st m.index Hp hi hlt $$ Hinv Hst with Hst
      cases ldr
      · (try wp_auto)
        tail_skip
      · (try wp_auto)
        wp_apply hE (srvCfgAddr s) fv.electionTicks fv.tickMs as %dur -
        · iframe Het Htm
        rw [Hli]
        (try wp_auto)
        (try dsimp only)
        ihave #HP := HPromote $$ %dur
        -- (prove-ps2-promote) `Promote` borrows the thread token (its sort's `Remaining()`)
        iunfold srvGoRes at Hgr
        icases Hgr with ⟨Hwgr, Htk⟩
        wp_apply HP $$ [$Htk] as Htk
        ihave Hgr : srvGoRes s $$ [Hwgr Htk]
        · iunfold srvGoRes; iframe
        (try wp_auto)
        tail_skip
    · -- data: the applier, in one critical section after the hook, or without writes
      iunfold isServerCI at Hsci
      icases Hsci with ⟨#Hcif, #Hci, #Hinv⟩
      have hpre : st.pending = false ∧ m.index = st.p + 1 ∧ uint.Z st.p < uint.Z m.index ∧
          uint.Z (ciEff γ st.k) < uint.Z m.index := ⟨Hp, hi, hlt, hce⟩
      have hdata : m.data ≠ [] := by
        intro h; apply Hif
        have h1 := Hdlen.1; rw [h] at h1; simp only [List.length_nil] at h1
        have h2 := Hdlen.2
        have h1' : (sint.Z d.len).toNat = 0 := h1.symm
        have h3 : sint.Z d.len = 0 := by omega
        word
      obtain ⟨rq, hdec, ⟨id0, hid⟩, hrq, hdk⟩ := Hok.resolve_left hdata
      iunfold srvApplyKVOn at HKV
      icases HKV with ⟨%ua, Hua, #Hb, #Happl, HKV, Hbo, HRA, HAR, ⟨%w', %RD, #Hw', #Hwok', HRD⟩, Hrdat⟩
      icombine Hw Hw' gives %Hweq
      subst Hweq
      -- (auth-lease S4 item 7b) the entry's window, its target the items of the model log after the entry
      imod (srvApplyKVW_push hPers hReach E _ HEo.2.2.1.2 HwOk ua x _
          (kvEntryOn_extends γr.kv.c0 x.chain (sa, x.log, kvLeasesOn γr.kv srvAuthSt0 A) m)) $$ [HKV]
        with ⟨%wn, %Hwn, HKV⟩
      · iframe HsI HwTie HKV
        iintro %_ !>
        rw [HNx]; iexact Hkc
      have Hwn2 : E.lg = true → ∀ s0 T0, wn = some (s0, T0) → T0 = srvApi.itemsOfLog
          (kvEntryOn γr.kv.c0 x.chain (sa, x.log, kvLeasesOn γr.kv srvAuthSt0 A) m).2.1 :=
        fun hlg s0 T0 h => by obtain ⟨s1, hs1⟩ := Hwn.2 hlg; rw [hs1] at h; cases h; rfl
      obtain ⟨HEP, HEf, HEnn⟩ := HE
      -- the floor its proposer recorded with the entry's claim (and the committed log it is in)
      have he : entryWaitOk ρ E m = iprop((∀ (rq : apply.IRRModel) (id : w64),
            ⌜m.data ≠ [] ∧ apply.irrDecode m.data = some rq ∧ apply.irrId rq = some id⌝ -∗
              ∃ (γf : GName) (k : IdKey),
                id ↪[ρ.ids.issued]□ (some (m.data, γf, k) : Option IdClaimV) ∗
                idRegdAt ρ.ids k id) ∗
            ∃ L : List EntryModel, srvRLogLb ρ.raft L ∗ ⌜m ∈ L ∧ attrEntryOk ρ.raft.raft.cfg m⌝) := by
        unfold entryWaitOk; rw [ite_eq_left Htyp]
      ihave #Hewo' : iprop((∀ (rq : apply.IRRModel) (id : w64),
            ⌜m.data ≠ [] ∧ apply.irrDecode m.data = some rq ∧ apply.irrId rq = some id⌝ -∗
              ∃ (γf : GName) (k : IdKey),
                id ↪[ρ.ids.issued]□ (some (m.data, γf, k) : Option IdClaimV) ∗
                idRegdAt ρ.ids k id) ∗
            ∃ L : List EntryModel, srvRLogLb ρ.raft L ∗ ⌜m ∈ L ∧ attrEntryOk ρ.raft.raft.cfg m⌝) $$ []
      · rw [← he]; iexact Hewo
      icases Hewo' with ⟨#Hewc, %Lw, #HLw, %HmLw'⟩
      have HmLw := HmLw'.1
      ihave ⟨%γf, %k0, #Hcl0, -⟩ := Hewc $$ %rq %id0 %(⟨hdata, hdec, hid⟩)
      ihave #Hgen' := Hgen
      iunfold srvGenAt at Hgen'
      icases Hgen' with ⟨%gidg, -, #Hidg⟩
      -- (R2c) by the claim's key: the incarnation's own claim, or another key's (another
      -- member's, or an earlier incarnation's): no waiter here, the empty floor
      ihave Hfl : iprop(|={⊤}=> ∃ F : mvcc.Log, srvApi.kvLogLb E.γs F ∗
          (⌜k0 = ρ.ids.key⌝ -∗ floorAt γf F)) $$ []
      · by_cases hpx : k0 = ρ.ids.key
        · ihave #Hcl0o : idClaim ρ.ids id0 m.data γf $$ []
          · iunfold idClaim; rw [← hpx]; iexact Hcl0
          imod idClaim_fact ρ.ids gidg (srvFloorFact E) id0 m.data γf ⊤ (by simp)
            $$ Hidg Hcl0o with Hff
          icases Hff with >#Hff
          iunfold srvFloorFact at Hff
          iunfold srvFloorFacts at Hff
          icases Hff with ⟨%F, #HfF, #HcF⟩
          imodintro
          iexists F
          iunfold srvApi.kvLogLb
          iframe HcF
          iintro -
          iexact HfF
        · ihave HcF : iprop(|==> srvApi.kvLogLb E.γs ([] : mvcc.Log)) $$ []
          · iunfold srvApi.kvLogLb; iapply monoListLbOwn_nil
          imod HcF with #HcF
          imodintro
          iexists []
          iframe HcF
          iintro %hpx'
          exact absurd hpx' hpx
      imod Hfl with ⟨%F, #HcF, #HfFo⟩
      ihave Hai : (go_etcd_io.etcd.server.v3.etcdserver.apply.applyInit : IProp GF) $$ []
      · iapply isPkgInit_access $$ Papp
      icases Hai with ⟨-, -, #Hev⟩
      hook_pre
      ihave ⟨%f, %Hfb, HRS, HLt, #HGI, #HRq, HEv⟩ := srvRestM_open true E γr A $$ HRS
      rcases Hpe Htyp hdata rq hdec with ((⟨hpL, hz, hsa⟩ | hgr | hgr) | ⟨hadm, hns⟩)
      rotate_left
      · -- (auth-lease S3a §6) a grant: `apply.Apply` (the auth layer passes a grant through), the
        -- log kept, the table the model's step (`kvEntryOn_grant`)
        have hg := hgr.2
        have hna : apply.needAdminPermission rq = false := hg.2.1
        have hkv' : apply.isKVKind (apply.dispatchKind rq) = false := by rw [hg.1]; rfl
        have hpG : plainOrCmpG E.lm rq := Or.inr (Or.inl hgr)
        icases HtokA with ⟨Htok, -⟩
        have hrq' : apply.rqOk E.lm x.log rq :=
          hrq.resolve_right (fun h => adminKindOk_nonGrant rq h hg.1)
        -- D14i: the snapshot right and the consistent index's resources, lent out of `Pre`
        ihave HFSE : E.FS $$ [HFS]
        · rw [HEo.1]; iexact HFS
        ihave #HSp : apply.ciSplit E iprop(applyThread γ st ∗ ciApplying ci m.index m.term ∗
            applyBackend γ ci b ∗ ⌜st.pending = false ∧ m.index = st.p + 1 ∧
              uint.Z st.p < uint.Z m.index ∧ uint.Z (ciEff γ st.k) < uint.Z m.index⌝) $$ []
        · iunfold apply.ciSplit
          iintro !> ⟨Hst', Happ', Hbe', %Hf'⟩
          iexists iprop(applyThread γ st ∗ applyBackend γ ci b), ciEff γ st.k
          iframe Hst' Hbe'
          isplitr
          · ipureintro; rw [HEo.2.1]; exact ⟨st, b, rfl, Hp, hld, rfl⟩
          iintro ⟨Hst', Hbe'⟩
          iframe Hst' Happ' Hbe'
          ipureintro; exact Hf'
        ihave HSpT : iprop(if true = true then apply.ciSplit E iprop(applyThread γ st ∗
            ciApplying ci m.index m.term ∗ applyBackend γ ci b ∗ ⌜st.pending = false ∧
              m.index = st.p + 1 ∧ uint.Z st.p < uint.Z m.index ∧
              uint.Z (ciEff γ st.k) < uint.Z m.index⌝) else iprop(True)) $$ []
        · simp only [↓reduceIte]; iexact HSp
        have hkeepM : kvEntryOn γr.kv.c0 x.chain (sa, x.log, kvLeasesOn γr.kv srvAuthSt0 A) m =
            (sa, x.log, kvTable γr.kv.c0 x.chain (kvLeasesOn γr.kv srvAuthSt0 A) m) :=
          kvEntryOn_grant _ _ _ m rq hdec hg
        ihave #Hcp : apply.certPreV true E x.chain rq x.log $$ []
        · simp only [apply.certPreV, ↓reduceIte]
          iapply kv_certPre_grantOn E γr.raft γr.kv srvAuthSt0 HNx x.chain rq x.log hg.1
          have hl0 : (kvEntryOn γr.kv.c0 x.chain (sa, x.log, kvLeasesOn γr.kv srvAuthSt0 A) m).2.1 = x.log := by
            rw [hkeepM]
          irevert Hkc; rw [hl0]; iintro #Hkc; iexact Hkc
        (try wp_auto)
        ihave %Hat := entryWaitOk_attr ρ E m Htyp $$ Hewo
        have Hrr := restReqOk_of_attr γr.raft γr.kv.c0 A m rq Hmc (by rw [← Hrd]; exact Hat) Htyp
          hdata hdec
        ihave Hrv : apply.revokeOwn E rq $$ []
        · rw [apply.revokeOwn_nonRevoke E rq (by rw [hg.1]; decide)]; itrivial
        imod kv_entry_grantFresh_on γr.raft γr.kv srvAuthSt0 A m $$ HkI' HrI' HAm with %Hgf
        ihave ⟨%U, HEv, #HGf, %HUok⟩ := srvEver_applyPre E γr.kv A m rq Htyp hdata hdec hpG hlmE Hgf
          $$ [$HGI $HEv]
        ihave #Hgpq := srvGrantIf_permPG E rq hpG $$ HGI
        ihave #Hcpq := apply.cmpPermRq_nonCmp E rq (by rw [hg.1]; decide)
        ihave #Hcpq := apply.v3Gate true _ $$ Hcpq
        ihave #HGf := apply.v3Gate true _ $$ HGf
        ihave #Hgpq := apply.v3Gate true _ $$ Hgpq
        wp_apply Apply_specRec_win hA fv.lg e m ua fv.w true E wn
            iprop(applyThread γ st ∗ ciApplying ci m.index m.term ∗ applyBackend γ ci b ∗
              ⌜st.pending = false ∧ m.index = st.p + 1 ∧ uint.Z st.p < uint.Z m.index ∧
                uint.Z (ciEff γ st.k) < uint.Z m.index⌝)
            iprop(hookDone γ TM ∗ applyThread γ { st with k := m.index, pending := true } ∗
              ciApplying ci m.index m.term ∗ applyBackend γ ci b)
            iprop(applyThread γ ⟨m.index, m.index, m.index, false⟩ ∗ ciApplying ci m.index m.term ∗
              applyBackend γ ci b) x rq id0 RD
            (fun ot id => waitRegdOpt ρ.wait id ot) (fun ot id => waitGoneOpt ρ.wait id ot) ot F
            _ _ U $$ [Hst Happ Hbe HKV Htt HRD HFSE HSpT HRS HLt Hhk HEv Hrv] as %ar %id
              ⟨HRD, HFS, Htt, Hrt, Hout, #Har, HTr, %Hid, %x', %out, HKV, HLt, HEv, -, HRS, %Hgo, HGr, HVr,
                %Hstep0, HRes, -, #Hdel⟩
        · simp only [↓reduceIte]
          iframe Happl Hwok' HRD He HKV Htt Hcp HFSE HSpT HRS Hhk HLt HEv HGf Hrv Hgpq
          isplitr
          · iunfold entryRegd at Hreg
            ihave ⟨#Hr1, -⟩ := Hreg $$ %rq %id0 %(⟨hdec, hid⟩)
            iexact Hr1
          isplitr
          · iexact Hlgnn
          iframe Hst Happ Hbe HcF
          iframe Hcpq
          ipureintro
          exact ⟨hpre, ⟨hdec, hid, hrq', HaOn ▸ hdk,
            fun _ => apply.cmpAdmit_nonCmp _ _ (by rw [hg.1]; decide),
            by unfold apply.restReqOk; rw [apply.restLeasesWith_mem]; exact Hrr⟩,
            ⟨fun hlg _ => winTgt_of_log wn rq x.log _ _ (Hwn2 hlg) (fun oc hb _ => by
              rw [backendStep_keep rq x.log oc (by rw [hg.1]; rfl) (by rw [hg.1]; decide) hb, hkeepM]), Hwn.1⟩⟩
        ihave HKV := srvApplyKVW_of E wn ua x' Hwn.1 $$ HKV
        have hkeep := applyStep_grant rq hg true x x' out Hstep0.1
        have hc' := hkeep.1
        have hmod : (sa, x'.log, kvTable γr.kv.c0 x.chain (kvLeasesOn γr.kv srvAuthSt0 A) m) =
            kvEntryOn γr.kv.c0 x.chain (sa, x.log, kvLeasesOn γr.kv srvAuthSt0 A) m := by
          rw [hkeepM, hkeep.2]
        have Htie : authTie sa x.log (kvLeasesOn γr.kv srvAuthSt0 A) rq out :=
          authTie_nonAuthKV sa x.log _ rq out (by rw [hg.1]; rfl)
        ihave #HtA : adminTieAr ar rq sa (adminNext rq sa) out $$ []
        · iapply (adminTieAr_nonAdmin ar rq sa (adminNext rq sa) out hna)
        ihave HFS : srvFS s $$ [HFS]
        · rw [← HEo.1]; iexact HFS
        ihave ⟨HLt, HRS⟩ := revokeA_drop E rq _ out _ _ _ (by rw [hg.1]; decide) $$ [$HLt $HRS]
        ihave HEv := srvEver_grant E A m rq true out U Htyp hdata hdec (plainOrCmpG_lg E rq hpG) HUok
          $$ HEv
        ihave ⟨HGr, HRes, #Hgrq⟩ := grantReqA_of_res E rq true x.log ar out $$ [$HGr $HRes]
        have hTt : appliedTableM true γr (A ++ [m]) =
            dispatchTable x.chain rq true (appliedTableM true γr A) := by
          rw [appliedTableM_true_snoc, kvEntryOn_grant _ _ _ m rq hdec hg]
          simp only
          rw [kvTable_dec _ _ _ m rq Htyp hdata hdec, ← HkA.2, appliedTableM_true_eq, Hxch]
        ihave HRS : srvRestM true E γr (A ++ [m]) $$ [HLt HRS HEv]
        · rw [show srvRestM (GF := GF) true E γr (A ++ [m]) =
              srvRestT E γr (appliedTableM true γr (A ++ [m])) (A ++ [m]) from rfl]
          iapply srvRestT_applyG E γr A m rq true x x' out f _ _ Htyp hdata hdec HkA.2 hTt
            (by rw [hg.1]; decide) (fun _ => hgr) (fun r => restOut_grant rq true x x' out r hg Hstep0.1)
            Hstep0.1 Hfb
          iframe HGI HRq Hgrq HLt HRS HEv
          ipureintro; exact Hgo
        ihave #Plea : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease $$ []
        · iPkgInit
        ihave #HlI : (go_etcd_io.etcd.server.v3.lease.leaseInit : IProp GF) $$ []
        · iapply isPkgInit_access $$ Plea
        ihave ⟨HGr, HRes, #Hnn⟩ := applyResultIs_notNoSpace_grantOn E rq x x' ar out hg Hch Hstep0.1
          $$ Hev HlI HGr HRes
        ihave HAu : authnArM true E ar rq out $$ []
        · iapply (authnArM_of_ne true E ar rq out (by rw [hg.1]; decide))
        ihave HGA0 := grantArM_of_resW E ar rq out $$ HGr
        ihave HVA0 := revokeArM_of_resW E ar rq out $$ HVr
        tail_on sa (kvTable γr.kv.c0 x.chain (kvLeasesOn γr.kv srvAuthSt0 A) m)
      · -- (auth-lease S3a §6) a revocation: the latest-state triple (`kvSpecL`: the auth layer checks a
        -- revocation, `authKVKind`), the verdict at the row's history; refused, the model's table kept,
        -- applied, the lease dropped (`revokeOn_after`)
        have hr := hgr.2
        have hk := hr.1
        have hna : apply.needAdminPermission rq = false := hr.2.1
        have hkv' : apply.isKVKind (apply.dispatchKind rq) = false := by rw [hk]; rfl
        have hpG : plainOrCmpG E.lm rq := Or.inr (Or.inr hgr)
        icases HtokA with ⟨Htok, -⟩
        have hrq' : apply.rqOk E.lm x.log rq :=
          hrq.resolve_right (fun h => adminKindOk_nonRevoke rq h hk)
        -- D14i: the snapshot right and the consistent index's resources, lent out of `Pre`
        ihave HFSE : E.FS $$ [HFS]
        · rw [HEo.1]; iexact HFS
        ihave #HSp : apply.ciSplit E iprop(applyThread γ st ∗ ciApplying ci m.index m.term ∗
            applyBackend γ ci b ∗ ⌜st.pending = false ∧ m.index = st.p + 1 ∧
              uint.Z st.p < uint.Z m.index ∧ uint.Z (ciEff γ st.k) < uint.Z m.index⌝) $$ []
        · iunfold apply.ciSplit
          iintro !> ⟨Hst', Happ', Hbe', %Hf'⟩
          iexists iprop(applyThread γ st ∗ applyBackend γ ci b), ciEff γ st.k
          iframe Hst' Hbe'
          isplitr
          · ipureintro; rw [HEo.2.1]; exact ⟨st, b, rfl, Hp, hld, rfl⟩
          iintro ⟨Hst', Hbe'⟩
          iframe Hst' Happ' Hbe'
          ipureintro; exact Hf'
        ihave HSpT : iprop(if true = true then apply.ciSplit E iprop(applyThread γ st ∗
            ciApplying ci m.index m.term ∗ applyBackend γ ci b ∗ ⌜st.pending = false ∧
              m.index = st.p + 1 ∧ uint.Z st.p < uint.Z m.index ∧
              uint.Z (ciEff γ st.k) < uint.Z m.index⌝) else iprop(True)) $$ []
        · simp only [↓reduceIte]; iexact HSp
        ihave ⟨Hrv, Hrdb⟩ := revokeOwn_take E rq (Or.inl hpG) $$ [$Hrdat $HGI]
        icases srvAuthApplyResB_open s E γa sa hM $$ HAR with ⟨%stl, %bel, %T, %Pk, %Wb, %hs, %HPk, #Hwbc,
          #Hasf, #Hlend, #Hwba, #Hsteps, Hfu, Htie, %Hhl, HT, Htp, Hcl⟩
        ihave ⟨%stl', #Hasf', #HUK⟩ := srvUberOn_kv_win s E wn γa ua hM T $$ []
        · iframe Huon Hb
        icombine Hasf Hasf' gives %Hst
        have Hst' := apply.mkOk_ptr_inj _ _ _ Hst
        subst Hst'
        ihave ⟨HL, HLback⟩ := auth.ownFuT_lend stl γa hs $$ [Hfu Htie]
        · iframe Hfu Htie
        ihave HL : auth.latestResC stl (.on γa) T hs $$ [HL HT]
        · iunfold auth.latestResC; iframe HL; simp only [auth.authWHeldM]; iexact HT
        -- the model's state at the entry: its keys' leases live, no id `0`, its leased keys not empty
        imod (kvInvOn_log0 γr.raft γr.kv srvAuthSt0) $$ HkI' with %Hln0
        imod kv_log_plain_on γr.raft γr.kv srvAuthSt0 (A ++ [m]) $$ HkI' HrI' HAm with %HpcA
        have hSm : (sa, x.log, kvLeasesOn γr.kv srvAuthSt0 A) =
            kvRaftOfOn γr.kv.c0 γr.kv.ch0 (srvAuthSt0, γr.kv.log0, []) A := Hxl
        have hlive : liveSt (kvLeasesOn γr.kv srvAuthSt0 A).ids (mvcc.stateAfter x.log) := by
          have h := liveSt_kvRaftOfOn γr.kv.c0 γr.kv.ch0 A (srvAuthSt0, γr.kv.log0, [])
            (fun kv hkv => Or.inl (mvcc.stateAfter_leaseZero γr.kv.log0 Hln0 kv hkv))
          rw [← hSm] at h; exact h
        have h0 : W64 0 ∉ (kvLeasesOn γr.kv srvAuthSt0 A).ids := by
          have h := kvRaftOfOn_ne0 γr.kv.c0 γr.kv.ch0 (srvAuthSt0, γr.kv.log0, []) A
            (by simp [LeaseTable.ids])
          rw [← hSm] at h; exact h
        have hne : keysNonEmpty x.log := by
          have h := keysNonEmpty_kvRaftOfOn γr.kv.lm γr.kv.c0 γr.kv.ch0 srvAuthSt0 γr.kv.log0 A
            (fun m' hm' => HpcA.1 m' (List.mem_append_left _ hm')) Hln0
          rw [← hSm] at h; exact h
        ihave #HcpW : apply.certPreVW true E x.chain rq x.log
            (apply.kvOutLT E.authMode E.lg hs (auth.authInfoM (apply.principalOf rq)) (.quota .backend)
              rq x.log (srvIds E (appliedTableM true γr A).ids)) $$ []
        · iapply certPreVW_kvOutLT_other E true x.chain rq x.log _ _ _ _ _
          rw [hM, Hch]
          iapply kv_certPreVW_revoke_on E γr.raft γr.kv srvAuthSt0 HNx γr.kv.c0
            (sa, x.log, kvLeasesOn γr.kv srvAuthSt0 A) m rq Htyp hdata hdec hv hr γa hs Hhl hlive h0 Hdet
          rw [← Hch]; iexact Hkc
        ihave HKV := applyKV_kvOwnPre true E wn ua x
            iprop(applyThread γ st ∗ ciApplying ci m.index m.term ∗ applyBackend γ ci b ∗
              ⌜st.pending = false ∧ m.index = st.p + 1 ∧ uint.Z st.p < uint.Z m.index ∧
                uint.Z (ciEff γ st.k) < uint.Z m.index⌝)
            iprop(hookDone γ TM ∗ applyThread γ { st with k := m.index, pending := true } ∗
              ciApplying ci m.index m.term ∗ applyBackend γ ci b)
            iprop(applyThread γ ⟨m.index, m.index, m.index, false⟩ ∗ ciApplying ci m.index m.term ∗
              applyBackend γ ci b) $$ [HKV Hhk Hst Happ Hbe]
        · iframe HKV Hhk Hst Happ Hbe; ipureintro; exact hpre
        (try wp_auto)
        wp_apply Apply_kvSpecL_win hK fv.lg e m ua fv.w true E wn
            iprop(applyThread γ st ∗ ciApplying ci m.index m.term ∗ applyBackend γ ci b ∗
              ⌜st.pending = false ∧ m.index = st.p + 1 ∧ uint.Z st.p < uint.Z m.index ∧
                uint.Z (ciEff γ st.k) < uint.Z m.index⌝)
            iprop(hookDone γ TM ∗ applyThread γ { st with k := m.index, pending := true } ∗
              ciApplying ci m.index m.term ∗ applyBackend γ ci b)
            iprop(applyThread γ ⟨m.index, m.index, m.index, false⟩ ∗ ciApplying ci m.index m.term ∗
              applyBackend γ ci b) x rq id0 RD
            (fun ot id => waitRegdOpt ρ.wait id ot) (fun ot id => waitGoneOpt ρ.wait id ot) ot F
            _ (.quota .backend) (auth.latestResC stl (.on γa) T) hs _
            $$ [HKV Htt HRD HFSE HSpT HRS HLt Hrv HL] as %ar %id
              ⟨Htt, Hrt, HRD, HFS, Hrv, Hout, #Har, HTr, %Hid, %x', %out, HKV, HLt, HRS, HVr, %Hstep0,
                HRes, -, HL, %HXo, -, #Hdel⟩
        · simp only [↓reduceIte]
          iframe HUK Hwok' HRD He HKV Htt HcpW HFSE HSpT HRS HLt Hrv HL
          isplitr
          · iunfold entryRegd at Hreg
            ihave ⟨#Hr1, -⟩ := Hreg $$ %rq %id0 %(⟨hdec, hid⟩)
            iexact Hr1
          isplitr
          · iexact Hlgnn
          iframe HcF
          isplitr
          · ipureintro; exact ⟨hdec, hid, hrq', HaOn ▸ hdk⟩
          ipureintro
          refine ⟨⟨fun hlg ⟨oc, hX, hne⟩ => winTgt_of_log wn rq x.log _ _ (Hwn2 hlg) (fun oc' hb _ => by
              have h1 : apply.kvOutL (.on γa) hs (auth.authInfoM (apply.principalOf rq)) (.quota .backend) rq x.log oc' := by
                have := kvOutL_of_pass _ hs _ _ rq x.log oc oc' hX hne hb; rwa [hM] at this
              have ho := outcomeOn_of_kvOutL_revoke γr.kv.c0 (sa, x.log, kvLeasesOn γr.kv srvAuthSt0 A) m rq Htyp hdata
                hdec hv hna hk γa hs Hhl (noZeroEnds_revoke rq hk) hlive h0 oc' h1
              rw [Hch]; exact congrArg (fun s : OnState => s.2.1) (outcomeOn_eq γr.kv.c0 _ _ _ m Hdet ho)), Hwn.1⟩,
            by rw [Hch, hAuthOn]; rfl, by rw [hk]; rfl, ?_⟩
          exact kvShapedL_revoke _ hs x.log rq hk hne
        ihave HKV := srvApplyKVW_of E wn ua x' Hwn.1 $$ HKV
        have HXo' : ∀ o b, out = .dispatched o b → apply.kvOutL (.on γa) hs
            (auth.authInfoM (apply.principalOf rq)) (.quota .backend) rq x.log o := by
          intro o b h; have := HXo o b h rfl; rwa [hM] at this
        obtain ⟨hc', o, bo, lt'', hout, hmod, hob⟩ := revokeOn_after γr.kv.c0 sa
          (kvLeasesOn γr.kv srvAuthSt0 A) x x' m rq out Htyp hdata hdec hv hr γa hs Hhl
          (noZeroEnds_revoke rq hk) hlive h0 Hdet Hch Hstep0.1 HXo'
        have Htie : authTie sa x.log (kvLeasesOn γr.kv srvAuthSt0 A) rq out :=
          authTie_of_kvOutL γa hs sa Hhl rq x.log _ out (noZeroEnds_revoke rq hk) HXo'
            (fun o _ _ => leaseExact_revoke rq hk _ x.log o)
        ihave #HtA : adminTieAr ar rq sa (adminNext rq sa) out $$ []
        · iapply (adminTieAr_nonAdmin ar rq sa (adminNext rq sa) out hna)
        iunfold auth.latestResC at HL
        icases HL with ⟨HL, HT⟩
        simp only [auth.authWHeldM]
        ihave ⟨Hfu, Htie'⟩ := HLback $$ HL
        ihave HAR := Hcl $$ %hs %sa Hfu Htie' %Hhl HT Htp
        ihave HFS : srvFS s $$ [HFS]
        · rw [← HEo.1]; iexact HFS
        ihave HEv := srvEver_snoc E A m $$ HEv
        ihave Hrdat := Hrdb $$ Hrv
        -- the auth-on table before and after: the model's (an empty raft prefix, `srvKVInvsOn`)
        have hpre0 : γr.raft.pre = [] := hpreE
        have hTA : appliedTableM true γr A = kvLeasesOn γr.kv srvAuthSt0 A := by
          rw [appliedTableM_true, hpre0, List.nil_append]
        have hTA' : appliedTableM true γr (A ++ [m]) = lt'' := by
          rw [appliedTableM_true_snoc, hpre0, List.nil_append, ← hSm, ← Hxch, ← hmod]
        have hoT : ∃ o b, out = .dispatched o b ∧
            ((o = .rejected .auth ∧ appliedTableM true γr (A ++ [m]) = appliedTableM true γr A) ∨
              (∃ l ns, o = .applied l ns ∧
                appliedTableM true γr (A ++ [m]) = backendTable rq (appliedTableM true γr A))) := by
          refine ⟨o, bo, hout, ?_⟩
          rw [hTA', hTA]
          exact hob
        ihave HRS : srvRestM true E γr (A ++ [m]) $$ [HLt HRS HEv]
        · rw [show srvRestM (GF := GF) true E γr (A ++ [m]) =
              srvRestT E γr (appliedTableM true γr (A ++ [m])) (A ++ [m]) from rfl]
          iapply srvRestT_applyR E γr A m rq out f _ _ Htyp hdata hdec HkA.2 hgr hoT Hfb
          iframe HGI HRq HLt HRS HEv
        ihave #Plea : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease $$ []
        · iPkgInit
        ihave #HlI : (go_etcd_io.etcd.server.v3.lease.leaseInit : IProp GF) $$ []
        · iapply isPkgInit_access $$ Plea
        ihave ⟨HRes, #Hnn⟩ := applyResultIs_notNoSpace_revokeOn rq x x' ar out hr Hch Hstep0.1
          $$ Hev HlI HRes
        ihave HAu : authnArM true E ar rq out $$ []
        · iapply (authnArM_of_ne true E ar rq out (by rw [hk]; decide))
        ihave HGA0 := grantArM_not_grantW E ar rq out (by rw [hk]; decide)
        ihave HVA0 := revokeArM_of_resW E ar rq out $$ HVr
        tail_on sa lt''
      rotate_left
      · -- (auth-lease S3a2 §4) a request of the auth-on log at the lease mode: plain, or a leased put or
        -- transaction (`plainReqL`); the arms read only `kvCover`'s facts
        obtain ⟨-, hna, hpk⟩ := plainReqL_facts _ rq hpL
        have hcv := kvCover_of_plainReqL _ rq hpL
        have hnl : apply.dispatchKind rq ≠ .leaseGrant ∧ apply.dispatchKind rq ≠ .leaseRevoke := by
          have h := hcv; unfold kvCover at h
          constructor <;> intro hk <;> rw [hk] at h <;> exact h.elim
        icases HtokA with ⟨Htok, -⟩
        have hrq' : apply.rqOk E.lm x.log rq :=
          hrq.resolve_right (fun h => adminKindOk_notPutget rq h hpk)
        ihave #Hgpq := srvGrantIf_perm E rq (fun h => absurd h hnl.1) $$ HGI
        -- D14i: the snapshot right and the consistent index's resources, lent out of `Pre`
        ihave HFSE : E.FS $$ [HFS]
        · rw [HEo.1]; iexact HFS
        ihave #HSp : apply.ciSplit E iprop(applyThread γ st ∗ ciApplying ci m.index m.term ∗
            applyBackend γ ci b ∗ ⌜st.pending = false ∧ m.index = st.p + 1 ∧
              uint.Z st.p < uint.Z m.index ∧ uint.Z (ciEff γ st.k) < uint.Z m.index⌝) $$ []
        · iunfold apply.ciSplit
          iintro !> ⟨Hst', Happ', Hbe', %Hf'⟩
          iexists iprop(applyThread γ st ∗ applyBackend γ ci b), ciEff γ st.k
          iframe Hst' Hbe'
          isplitr
          · ipureintro; rw [HEo.2.1]; exact ⟨st, b, rfl, Hp, hld, rfl⟩
          iintro ⟨Hst', Hbe'⟩
          iframe Hst' Happ' Hbe'
          ipureintro; exact Hf'
        ihave HSpT : iprop(if true = true then apply.ciSplit E iprop(applyThread γ st ∗
            ciApplying ci m.index m.term ∗ applyBackend γ ci b ∗ ⌜st.pending = false ∧
              m.index = st.p + 1 ∧ uint.Z st.p < uint.Z m.index ∧
              uint.Z (ciEff γ st.k) < uint.Z m.index⌝) else iprop(True)) $$ []
        · simp only [↓reduceIte]; iexact HSp
        by_cases hkv : apply.isKVKind (apply.dispatchKind rq) = true
        · -- a KV request: the latest-state triple (`kvSpecL`), the verdict at the row's history
          ihave Hrv : apply.revokeOwn E rq $$ []
          · rw [apply.revokeOwn_nonRevoke E rq (fun h => by rw [h] at hkv; simp [apply.isKVKind] at hkv)]
            itrivial
          icases srvAuthApplyResB_open s E γa sa hM $$ HAR with ⟨%stl, %bel, %T, %Pk, %Wb, %hs, %HPk, #Hwbc, #Hasf,
            #Hlend, #Hwba, #Hsteps, Hfu, Htie, %Hhl, HT, Htp, Hcl⟩
          ihave ⟨%stl', #Hasf', #HUK⟩ := srvUberOn_kv_win s E wn γa ua hM T $$ []
          · iframe Huon Hb
          icombine Hasf Hasf' gives %Hst
          have Hst' := apply.mkOk_ptr_inj _ _ _ Hst
          subst Hst'
          ihave ⟨HL, HLback⟩ := auth.ownFuT_lend stl γa hs $$ [Hfu Htie]
          · iframe Hfu Htie
          -- (the auth-on snapshot plan's Prove step) the checks take the write token too
          ihave HL : auth.latestResC stl (.on γa) T hs $$ [HL HT]
          · iunfold auth.latestResC; iframe HL; simp only [auth.authWHeldM]; iexact HT
          -- the model's state at the entry: its leased keys not empty (`kvShapedL_of_logL`)
          imod (kvInvOn_log0 γr.raft γr.kv srvAuthSt0) $$ HkI' with %Hln0
          imod kv_log_plain_on γr.raft γr.kv srvAuthSt0 (A ++ [m]) $$ HkI' HrI' HAm with %HpcA
          have hne : keysNonEmpty x.log := by
            have h := keysNonEmpty_kvRaftOfOn γr.kv.lm γr.kv.c0 γr.kv.ch0 srvAuthSt0 γr.kv.log0 A
              (fun m' hm' => HpcA.1 m' (List.mem_append_left _ hm')) Hln0
            have hSm : (sa, x.log, kvLeasesOn γr.kv srvAuthSt0 A) =
                kvRaftOfOn γr.kv.c0 γr.kv.ch0 (srvAuthSt0, γr.kv.log0, []) A := Hxl
            rw [← hSm] at h; exact h
          have hpK : plainReqL γr.kv.lm rq := by rw [hlmE]; exact hpL
          have hlmK : E.lg = false → γr.kv.lm = .none := fun hg => by
            rw [hlmE]; exact apply.AEnv.lm_of_lg_false hg
          -- the model's table is the server's live set when leases are granted (an empty raft prefix)
          have hTids : E.lg = true →
              (kvLeasesOn γr.kv srvAuthSt0 A).ids = srvIds E (appliedTableM true γr A).ids := fun hg => by
            rw [srvIds_lg E _ hg, appliedTableM_true, hpreE, List.nil_append]
          ihave #HcpW : apply.certPreVW true E x.chain rq x.log
              (apply.kvOutLT E.authMode E.lg hs (auth.authInfoM (apply.principalOf rq)) (.quota .backend)
                rq x.log (srvIds E (appliedTableM true γr A).ids)) $$ []
          · iapply certPreVW_kvOutLT_tie E true x.chain rq x.log _ _ _ _ _ _ hTids
            rw [hM, Hch]
            iapply kv_certPreVW_on E γr.raft γr.kv srvAuthSt0 HNx γr.kv.c0 (sa, x.log, kvLeasesOn γr.kv srvAuthSt0 A) m rq Htyp hdata hdec hv hna hkv
              hpK hlmK γa hs Hhl hz Hdet
            rw [← Hch]; iexact Hkc
          ihave HKV := applyKV_kvOwnPre true E wn ua x
            iprop(applyThread γ st ∗ ciApplying ci m.index m.term ∗ applyBackend γ ci b ∗
              ⌜st.pending = false ∧ m.index = st.p + 1 ∧ uint.Z st.p < uint.Z m.index ∧
                uint.Z (ciEff γ st.k) < uint.Z m.index⌝)
            iprop(hookDone γ TM ∗ applyThread γ { st with k := m.index, pending := true } ∗
              ciApplying ci m.index m.term ∗ applyBackend γ ci b)
            iprop(applyThread γ ⟨m.index, m.index, m.index, false⟩ ∗ ciApplying ci m.index m.term ∗
              applyBackend γ ci b) $$ [HKV Hhk Hst Happ Hbe]
          · iframe HKV Hhk Hst Happ Hbe; ipureintro; exact hpre
          (try wp_auto)
          wp_apply Apply_kvSpecL_win hK fv.lg e m ua fv.w true E wn
            iprop(applyThread γ st ∗ ciApplying ci m.index m.term ∗ applyBackend γ ci b ∗
              ⌜st.pending = false ∧ m.index = st.p + 1 ∧ uint.Z st.p < uint.Z m.index ∧
                uint.Z (ciEff γ st.k) < uint.Z m.index⌝)
            iprop(hookDone γ TM ∗ applyThread γ { st with k := m.index, pending := true } ∗
              ciApplying ci m.index m.term ∗ applyBackend γ ci b)
            iprop(applyThread γ ⟨m.index, m.index, m.index, false⟩ ∗ ciApplying ci m.index m.term ∗
              applyBackend γ ci b) x rq id0 RD
            (fun ot id => waitRegdOpt ρ.wait id ot) (fun ot id => waitGoneOpt ρ.wait id ot) ot F
            _ (.quota .backend) (auth.latestResC stl (.on γa) T) hs _
            $$ [HKV Htt HRD HFSE HSpT HRS HLt Hrv HL] as %ar %id
              ⟨Htt, Hrt, HRD, HFS, -, Hout, #Har, HTr, %Hid, %x', %out, HKV, HLt, HRS, -, %Hstep0,
                HRes, -, HL, %HXo, %HXe, #Hdel⟩
          · simp only [↓reduceIte]
            iframe HUK Hwok' HRD He HKV Htt HcpW HFSE HSpT HRS HLt Hrv HL
            isplitr
            · iunfold entryRegd at Hreg
              ihave ⟨#Hr1, -⟩ := Hreg $$ %rq %id0 %(⟨hdec, hid⟩)
              iexact Hr1
            isplitr
            · iexact Hlgnn
            iframe HcF
            isplitr
            · ipureintro; exact ⟨hdec, hid, apply.rqOk_kv _ _ _ _ hkv hrq', HaOn ▸ hdk⟩
            ipureintro
            refine ⟨⟨fun hlg ⟨oc, hX, hne⟩ => winTgt_of_log wn rq x.log _ _ (Hwn2 hlg) (fun oc' hb he => by
              have h1 : apply.kvOutL (.on γa) hs (auth.authInfoM (apply.principalOf rq)) (.quota .backend) rq x.log oc' := by
                have := kvOutL_of_pass _ hs _ _ rq x.log oc oc' hX hne hb; rwa [hM] at this
              have ho := outcomeOn_of_kvOutLL γr.kv.lm γr.kv.c0 (sa, x.log, kvLeasesOn γr.kv srvAuthSt0 A) m rq Htyp
                hdata hdec hv hna hkv hpK γa hs Hhl hz oc' h1 (Or.inr (by rw [hTids hlg]; exact he))
              rw [Hch]; exact congrArg (fun s : OnState => s.2.1) (outcomeOn_eq γr.kv.c0 _ _ _ m Hdet ho)), Hwn.1⟩,
              by rw [Hch, hAuthOn]; rfl, apply.authKVKind_of_isKVKind _ hkv, ?_⟩
            rw [hM]; exact kvShapedL_of_logL _ hs x.log rq hz hsa hne
          ihave HKV := srvApplyKVW_of E wn ua x' Hwn.1 $$ HKV
          have hnr : apply.dispatchKind rq ≠ .leaseRevoke := fun h => by
            rw [h] at hkv; simp [apply.isKVKind] at hkv
          irevert HLt HRS
          rw [apply.revokeIdsA_nonRevoke _ _ _ _ hnr, apply.revokeRestA_nonRevoke _ _ _ _ _ hnr]
          iintro HLt HRS
          have HXo' : ∀ o b, out = .dispatched o b → apply.kvOutL (.on γa) hs
              (auth.authInfoM (apply.principalOf rq)) (.quota .backend) rq x.log o := by
            intro o b h; have := HXo o b h rfl; rwa [hM] at this
          -- (S3a2) the outcome lease-exact at the model's table unless plain (`E.lg = false`: lease mode `none`)
          have HXL : ∀ o b, out = .dispatched o b → apply.kvOutL (.on γa) hs
              (auth.authInfoM (apply.principalOf rq)) (.quota .backend) rq x.log o ∧
                (plainCover rq ∨ apply.leaseExactL (kvLeasesOn γr.kv srvAuthSt0 A).ids rq x.log o) := by
            intro o b h
            refine ⟨HXo' o b h, ?_⟩
            cases hg : E.lg
            · left
              have hp0 : plainReqL .none rq := by rw [← hlmK hg]; exact hpK
              exact ((plainReqL_none rq).1 hp0).1
            · right; rw [hTids hg]; exact HXe o b h rfl hg
          obtain ⟨hc', hmod⟩ := kvOn_after_kv γr.kv.lm γr.kv.c0 sa _ x x' m rq out Htyp hdata hdec hv hna hkv hpK
            γa hs Hhl hz Hdet Hch Hstep0.1 HXL
          have Htie : authTie sa x.log (kvLeasesOn γr.kv srvAuthSt0 A) rq out :=
            authTie_of_kvOutL γa hs sa Hhl rq x.log _ out hz HXo' (fun o b h => (HXL o b h).2)
          ihave #HtA : adminTieAr ar rq sa (adminNext rq sa) out $$ []
          · iapply (adminTieAr_nonAdmin ar rq sa (adminNext rq sa) out hna)
          iunfold auth.latestResC at HL
          icases HL with ⟨HL, HT⟩
          simp only [auth.authWHeldM]
          ihave ⟨Hfu, Htie'⟩ := HLback $$ HL
          ihave HAR := Hcl $$ %hs %sa Hfu Htie' %Hhl HT Htp
          ihave HFS : srvFS s $$ [HFS]
          · rw [← HEo.1]; iexact HFS
          ihave HEv := srvEver_snoc E A m $$ HEv
          ihave HRS := srvRestM_applyP0 E γr A m rq true x x' out f Htyp hdata hdec HkA.2
            (Or.inr hcv) Hstep0.1 Hfb $$ [HLt HRS HEv]
          · iframe HGI HRq HLt HRS HEv
          ihave ⟨HRes, #Hnn⟩ := applyResultIs_notNoSpaceOn rq x x' ar out hcv Hch Hstep0.1
            $$ Hev HRes
          ihave HAu : authnArM true E ar rq out $$ []
          · iapply (authnArM_of_ne true E ar rq out (by intro h; rw [h] at hpk; simp [putgetKind] at hpk))
          ihave HGA0 := grantArM_not_grantW E ar rq out hnl.1
          ihave HVA0 := revokeArM_not_revokeW E ar rq out hnl.2
          tail_on sa (kvLeasesOn γr.kv srvAuthSt0 A)
        · -- a cluster request: `apply.Apply`, the log kept
          have hkv' : apply.isKVKind (apply.dispatchKind rq) = false := by simpa using hkv
          have hp : plainCover rq := by
            rcases plainReqL_cases _ rq hpL with h | h
            · exact h.1
            · exfalso; rcases h with h | h <;> rw [h] at hkv' <;> simp [apply.isKVKind] at hkv'
          obtain ⟨hw, hfl⟩ := putget_nonKV _ hpk hkv'
          have hkeepM := kvEntryOn_keep γr.kv.c0 x.chain (sa, x.log, kvLeasesOn γr.kv srvAuthSt0 A) m rq Htyp hdata hdec hna hw
          ihave #Hcp : apply.certPreV true E x.chain rq x.log $$ []
          · simp only [apply.certPreV, ↓reduceIte]
            iapply kv_certPre_keep E γr.raft γr.kv srvAuthSt0 HNx x.chain rq x.log hp hw
            have hl0 : (kvEntryOn γr.kv.c0 x.chain (sa, x.log, kvLeasesOn γr.kv srvAuthSt0 A) m).2.1 = x.log := by rw [hkeepM]
            irevert Hkc; rw [hl0]; iintro #Hkc; iexact Hkc
          (try wp_auto)
          ihave %Hat := entryWaitOk_attr ρ E m Htyp $$ Hewo
          have Hrr := restReqOk_of_attr γr.raft γr.kv.c0 A m rq Hmc (by rw [← Hrd]; exact Hat) Htyp
            hdata hdec
          ihave Hrv : apply.revokeOwn E rq $$ []
          · rw [apply.revokeOwn_nonRevoke E rq (by first | exact plainOrCmpG_rev _ rq (Hpl rq hdata hdec) | exact plainOrCmpG_rev .none rq (Or.inl (Or.inl hp)))]; itrivial
          ihave ⟨%U, HEv, #HGf, %HUok⟩ := srvEver_applyPreN E A rq (plainOrCmp_nonLease rq (Or.inl hp)).1 $$ HEv
          ihave #Hcpq := apply.cmpPermRq_nonCmp E rq (plainCover_nonCmp rq hp)
          ihave #Hcpq := apply.v3Gate true _ $$ Hcpq
          ihave #HGf := apply.v3Gate true _ $$ HGf
          ihave #Hgpq := apply.v3Gate true _ $$ Hgpq
          wp_apply Apply_specRec_win hA fv.lg e m ua fv.w true E wn
            iprop(applyThread γ st ∗ ciApplying ci m.index m.term ∗ applyBackend γ ci b ∗
              ⌜st.pending = false ∧ m.index = st.p + 1 ∧ uint.Z st.p < uint.Z m.index ∧
                uint.Z (ciEff γ st.k) < uint.Z m.index⌝)
            iprop(hookDone γ TM ∗ applyThread γ { st with k := m.index, pending := true } ∗
              ciApplying ci m.index m.term ∗ applyBackend γ ci b)
            iprop(applyThread γ ⟨m.index, m.index, m.index, false⟩ ∗ ciApplying ci m.index m.term ∗
              applyBackend γ ci b) x rq id0 RD
            (fun ot id => waitRegdOpt ρ.wait id ot) (fun ot id => waitGoneOpt ρ.wait id ot) ot F
            _ _ U $$ [Hst Happ Hbe HKV Htt HRD HFSE HSpT HRS HLt Hhk HEv Hrv] as %ar %id
              ⟨HRD, HFS, Htt, Hrt, Hout, #Har, HTr, %Hid, %x', %out, HKV, HLt, HEv, -, HRS, %Hgo, HGr, HVr, %Hstep0, HRes, -, #Hdel⟩
          · simp only [↓reduceIte]
            iframe Happl Hwok' HRD He HKV Htt Hcp HFSE HSpT HRS Hhk HLt HEv HGf Hrv Hgpq
            isplitr
            · iunfold entryRegd at Hreg
              ihave ⟨#Hr1, -⟩ := Hreg $$ %rq %id0 %(⟨hdec, hid⟩)
              iexact Hr1
            isplitr
            · iexact Hlgnn
            iframe Hst Happ Hbe HcF
            iframe Hcpq
            ipureintro; exact ⟨hpre, ⟨hdec, hid, hrq', HaOn ▸ hdk, fun _ => apply.cmpAdmit_nonCmp _ _ (plainCover_nonCmp rq hp), by unfold apply.restReqOk; rw [apply.restLeasesWith_mem]; exact Hrr⟩,
              ⟨fun hlg _ => winTgt_of_log wn rq x.log _ _ (Hwn2 hlg) (fun oc hb _ => by
                rw [backendStep_keep rq x.log oc hkv' (plainOrCmp_nonLease rq (Or.inl hp)).2 hb, hkeepM]), Hwn.1⟩⟩
          ihave HKV := srvApplyKVW_of E wn ua x' Hwn.1 $$ HKV
          have hkeep := applyStep_keep rq true x x' out hp hw Hstep0.1
          have hc' := hkeep.2
          have hmod : (sa, x'.log, kvLeasesOn γr.kv srvAuthSt0 A) = kvEntryOn γr.kv.c0 x.chain (sa, x.log, kvLeasesOn γr.kv srvAuthSt0 A) m := by
            rw [hkeepM, hkeep.1]
          have Htie : authTie sa x.log (kvLeasesOn γr.kv srvAuthSt0 A) rq out :=
            authTie_nonAuthKV sa x.log _ rq out (by
              unfold apply.authKVKind; rw [hkv']
              have hk := hpk; unfold putgetKind at hk
              rcases hk with hk | hk | hk | hk | hk <;> rw [hk] <;> rfl)
          ihave #HtA : adminTieAr ar rq sa (adminNext rq sa) out $$ []
          · iapply (adminTieAr_nonAdmin ar rq sa (adminNext rq sa) out hna)
          ihave HFS : srvFS s $$ [HFS]
          · rw [← HEo.1]; iexact HFS
          ihave ⟨HLt, HRS⟩ := revokeA_drop E rq _ out _ _ _ (by first | exact plainOrCmpG_rev _ rq (Hpl rq hdata hdec) | exact plainOrCmpG_rev .none rq (Or.inl (Or.inl hp))) $$ [$HLt $HRS]
          ihave HEv := srvEver_grant E A m rq true out U Htyp hdata hdec (fun hk => absurd hk (plainOrCmp_nonLease rq (Or.inl hp)).1) HUok $$ HEv
          ihave HRS := srvRestM_applyP E γr A m rq true x x' out f Htyp hdata hdec HkA.2
            (Or.inl hp) Hstep0.1 Hfb $$ [HLt HRS HEv]
          · iframe HGI HRq HLt HRS HEv
            isplitl []
            · iapply grantReqA_nonGrant E rq true out (plainOrCmp_nonLease rq (Or.inl hp)).1
            ipureintro; exact Hgo
          ihave ⟨HRes, #Hnn⟩ := applyResultIs_notNoSpaceOn rq x x' ar out hcv Hch Hstep0.1
            $$ Hev HRes
          ihave HAu : authnArM true E ar rq out $$ []
          · iapply (authnArM_of_ne true E ar rq out (by intro h; rw [h] at hpk; simp [putgetKind] at hpk))
          ihave HGA0 := grantArM_of_resW E ar rq out $$ HGr
          ihave HVA0 := revokeArM_of_resW E ar rq out $$ HVr
          tail_on sa (kvLeasesOn γr.kv srvAuthSt0 A)
      · -- an admin request: the auth row's admin steps (`adminEntryOn`)
        by_cases hka : apply.dispatchKind rq = .authenticate
        · -- (C1's A2) an `Authenticate`: the right to its token minted at the consistent index
          -- the backend reads, `ciEff γ st.k` (`srvTokRights_next`); its response (A3) dropped
          have hna : apply.needAdminPermission rq = false := by
            have h := hadm; unfold apply.adminKindOk at h; rw [hka] at h; exact h.1
          obtain ⟨am, ham⟩ := Option.isSome_iff_exists.mp (apply.dispatchKind_authenticate rq hka)
          -- the right to the token `<prefix>.<ci>` at the consistent index the backend reads
          icases HtokA with ⟨-, Hmint⟩
          ihave Hm := Hmint $$ %γa %am.simpleToken []
          · ipureintro; exact hM
          imod Hm with ⟨Htok, Hfr⟩
          ihave #HSpA : apply.ciSplitAt E iprop(applyThread γ st ∗ ciApplying ci m.index m.term ∗
              applyBackend γ ci b ∗ ⌜st.pending = false ∧ m.index = st.p + 1 ∧
                uint.Z st.p < uint.Z m.index ∧ uint.Z (ciEff γ st.k) < uint.Z m.index⌝)
              (ciEff γ st.k) $$ []
          · iunfold apply.ciSplitAt
            iintro !> ⟨Hst', Happ', Hbe', %Hf'⟩
            iexists iprop(applyThread γ st ∗ applyBackend γ ci b)
            iframe Hst' Hbe'
            isplitr
            · ipureintro; rw [HEo.2.1]; exact ⟨st, b, rfl, Hp, hld, rfl⟩
            iintro ⟨Hst', Hbe'⟩
            iframe Hst' Happ' Hbe'
            ipureintro; exact Hf'
          obtain ⟨hkv', hfl⟩ := adminKindOk_kinds rq hadm
          icases srvAuthApplyResB_open s E γa sa hM $$ HAR with ⟨%stl, %bel, %T, %Pk, %Wb, %hs, %HPk, #Hwbc, #Hasf, #Hlend,
            #Hwba, #Hsteps, Hfu, Htie, %Hhl, HT, Htp, Hcl⟩
          ihave Hx := apply.adminExtra_authenticate E γa rq hs _ am (ciEff γ st.k) hka ham $$ [HSpA Hfr]
          · iframe HSpA Hfr
          ihave #HUA := srvUberOn_adm_win s E wn γa ua stl bel T Pk Wb hM HPk $$ []
          · iframe Huon Hb Hasf Hwbc Hsteps
          (try wp_auto)
          wp_apply adminEntryOn_win hAd fv.lg e m ua fv.w true E wn
              iprop(applyThread γ st ∗ ciApplying ci m.index m.term ∗ applyBackend γ ci b ∗
                ⌜st.pending = false ∧ m.index = st.p + 1 ∧ uint.Z st.p < uint.Z m.index ∧
                  uint.Z (ciEff γ st.k) < uint.Z m.index⌝)
              iprop(hookDone γ TM ∗ applyThread γ { st with k := m.index, pending := true } ∗
                ciApplying ci m.index m.term ∗ applyBackend γ ci b)
              iprop(applyThread γ ⟨m.index, m.index, m.index, false⟩ ∗ ciApplying ci m.index m.term ∗
                applyBackend γ ci b) x rq id0 RD
              (fun ot id => waitRegdOpt ρ.wait id ot) (fun ot id => waitGoneOpt ρ.wait id ot) ot γa stl
              bel T Pk Wb sa _ hs hM hns HPk $$ [Hst Happ Hbe HKV Htt HRD Hfu Htie HT Htp HRS Hlc Hawt Hhk Hx]
              as %ar %id ⟨HRD, Htt, Hrt, Hout, #Har, HTr, %Hid, %x', %out, HKV, %Hstep0, HRes, #Hdel, -, HNS,
                HRS, HT, Htp, %hs', %sa', Hfu, Htie, %Hsa', #HtA0, HAu0⟩
          · simp only [↓reduceIte]
            iframe HUA Hwok' HRD He HKV Htt HT Htp Hwba Hlend HRS Hlc Hawt Hhk
            isplitr
            · iunfold entryRegd at Hreg
              ihave ⟨#Hr1, -⟩ := Hreg $$ %rq %id0 %(⟨hdec, hid⟩)
              iexact Hr1
            isplitr
            · iexact Hlgnn
            iframe Hst Happ Hbe
            isplitr
            · ipureintro; exact hpre
            isplitr
            · ipureintro; exact ⟨hdec, hid, hadm, HaOn ▸ hdk, Hrb⟩
            isplitr
            · ipureintro; rw [Hch, hAuthOn]; rfl
            isplitl [Hfu Htie]
            · iframe Hfu Htie; ipureintro; exact Hhl
            iunfold apply.adminExtraG; iintro -; iexact Hx
          ihave HKV := srvApplyKVW_of E wn ua x' Hwn.1 $$ HKV
          obtain ⟨Hstep, hl', hc'⟩ := Hstep0
          have Hstep0 : apply.applyStep rq true x x' out ∧ apply.applyFloorOk rq true F x.log out :=
            ⟨Hstep, applyFloorOk_nonFloor rq true F x.log out hfl⟩
          have hR : adminStateR rq sa sa' := by simpa using Hsa'.2
          have hsa : sa' = sa := by
            unfold adminStateR at hR; rw [hka] at hR; split at hR <;> exact hR
          subst sa'
          have hw : ¬ writeKind (apply.dispatchKind rq) := by rw [hka]; simp [writeKind]
          have hmod : (sa, x'.log, kvLeasesOn γr.kv srvAuthSt0 A) = kvEntryOn γr.kv.c0 x.chain (sa, x.log, kvLeasesOn γr.kv srvAuthSt0 A) m := by
            rw [hl', kvEntryOn_keep γr.kv.c0 x.chain (sa, x.log, kvLeasesOn γr.kv srvAuthSt0 A) m rq Htyp hdata hdec hna hw]
          have Htie : authTie sa x.log (kvLeasesOn γr.kv srvAuthSt0 A) rq out :=
            authTie_nonAuthKV sa x.log _ rq out (adminKindOk_nonAuthKV rq hadm)
          ihave #HtA : adminTieAr ar rq sa (adminNext rq sa) out $$ []
          · iapply (adminTieAr_nonAdmin ar rq sa (adminNext rq sa) out hna)
          ihave HAR := Hcl $$ %hs' %sa Hfu Htie %Hsa'.1 HT Htp
          ihave HRS : srvRestM true E γr (A ++ [m]) $$ [HRS HLt HEv]
          · iapply srvRestM_admin E γr A m rq Htyp hdata hdec hadm; iapply srvRestM_close true; iframe HLt HGI HRq HEv; iexists f; iframe HRS; ipureintro; exact Hfb
          ihave #Hnn : iprop(⌜ar = null⌝ ∨ ∃ err : GoInterface,
              structFieldRef go_etcd_io.etcd.server.v3.etcdserver.apply.Result go!"Err" ar ↦□ err ∗
              notNoSpaceErr err) $$ [HNS]
          · iexact HNS
          -- (C1's A3) the response, for the waiter
          ihave HAu : authnArM true E ar rq out $$ [HAu0]
          · iapply (authnArM_of_on E γa ar rq out hM) $$ HAu0
          ihave HGA0 := grantArM_not_grantW E ar rq out (adminKindOk_nonGrant rq hadm)
          ihave HVA0 := revokeArM_not_revokeW E ar rq out (adminKindOk_nonRevoke rq hadm)
          tail_on sa (kvLeasesOn γr.kv srvAuthSt0 A)
        icases HtokA with ⟨Htok, -⟩
        have hna := adminKindOk_needAdmin rq hadm hka
        obtain ⟨hkv', hfl⟩ := adminKindOk_kinds rq hadm
        icases srvAuthApplyResB_open s E γa sa hM $$ HAR with ⟨%stl, %bel, %T, %Pk, %Wb, %hs, %HPk, #Hwbc, #Hasf, #Hlend,
          #Hwba, #Hsteps, Hfu, Htie, %Hhl, HT, Htp, Hcl⟩
        ihave #HUA := srvUberOn_adm_win s E wn γa ua stl bel T Pk Wb hM HPk $$ []
        · iframe Huon Hb Hasf Hwbc Hsteps
        -- (H5) the cap raised to the log with `m`, and the step's cap permission
        have hsaA : srvAuthAtLog γr.kv (auth.bump auth.bootState) A = sa := by
          unfold srvAuthAtLog; rw [show auth.bump auth.bootState = srvAuthSt0 from rfl, ← Hxl]
        have hdetA : authDet rq sa := (Hdet Htyp hdata rq hdec).1 hv hna
        iunfold auth.authOwnFu at Hfu
        icases Hfu with ⟨Hown, Hfuel⟩
        imod authHistTie_raise E γr γa A m rq hs sa
            iprop(applyThread γ st ∗ ciApplying ci m.index m.term ∗ applyBackend γ ci b ∗
              ⌜st.pending = false ∧ m.index = st.p + 1 ∧ uint.Z st.p < uint.Z m.index ∧
                uint.Z (ciEff γ st.k) < uint.Z m.index⌝)
            ⊤ hM Htyp hdata hdec hv hna hka hsaA hdetA Hhl (by simp) (by simp) $$ [Hown]
          with ⟨Hown, Hx⟩
        · simp only [srvAuthSt0] at *; iframe Htie0 HAm Hown
        ihave Hfu : auth.authOwnFu γa hs $$ [Hown Hfuel]
        · iunfold auth.authOwnFu; iframe Hown Hfuel
        (try wp_auto)
        wp_apply adminEntryOn_win hAd fv.lg e m ua fv.w true E wn
            iprop(applyThread γ st ∗ ciApplying ci m.index m.term ∗ applyBackend γ ci b ∗
              ⌜st.pending = false ∧ m.index = st.p + 1 ∧ uint.Z st.p < uint.Z m.index ∧
                uint.Z (ciEff γ st.k) < uint.Z m.index⌝)
            iprop(hookDone γ TM ∗ applyThread γ { st with k := m.index, pending := true } ∗
              ciApplying ci m.index m.term ∗ applyBackend γ ci b)
            iprop(applyThread γ ⟨m.index, m.index, m.index, false⟩ ∗ ciApplying ci m.index m.term ∗
              applyBackend γ ci b) x rq id0 RD
            (fun ot id => waitRegdOpt ρ.wait id ot) (fun ot id => waitGoneOpt ρ.wait id ot) ot γa stl
            bel T Pk Wb sa _ hs hM hns HPk $$ [Hst Happ Hbe HKV Htt HRD Hfu Htie HT Htp HRS Hlc Hawt Hhk Hx]
            as %ar %id ⟨HRD, Htt, Hrt, Hout, #Har, HTr, %Hid, %x', %out, HKV, %Hstep0, HRes, #Hdel, -, HNS,
              HRS, HT, Htp, %hs', %sa', Hfu, Htie, %Hsa', #HtA0, -⟩
        · simp only [↓reduceIte]
          iframe HUA Hwok' HRD He HKV Htt HT Htp Hwba Hlend HRS Hlc Hawt Hhk
          isplitr
          · iunfold entryRegd at Hreg
            ihave ⟨#Hr1, -⟩ := Hreg $$ %rq %id0 %(⟨hdec, hid⟩)
            iexact Hr1
          isplitr
          · iexact Hlgnn
          iframe Hst Happ Hbe
          isplitr
          · ipureintro; exact hpre
          isplitr
          · ipureintro; exact ⟨hdec, hid, hadm, HaOn ▸ hdk, Hrb⟩
          isplitr
          · ipureintro; rw [Hch, hAuthOn]; rfl
          isplitl [Hfu Htie]
          · iframe Hfu Htie; ipureintro; exact Hhl
          iexact Hx
        ihave HKV := srvApplyKVW_of E wn ua x' Hwn.1 $$ HKV
        obtain ⟨Hstep, hl', hc'⟩ := Hstep0
        have Hstep0 : apply.applyStep rq true x x' out ∧ apply.applyFloorOk rq true F x.log out :=
          ⟨Hstep, applyFloorOk_nonFloor rq true F x.log out hfl⟩
        have hR : adminStateR rq sa sa' := by simpa using Hsa'.2
        have hmod : (sa', x'.log, kvLeasesOn γr.kv srvAuthSt0 A) = kvEntryOn γr.kv.c0 x.chain (sa, x.log, kvLeasesOn γr.kv srvAuthSt0 A) m := by
          rw [hl']
          exact outcomeOn_eq γr.kv.c0 x.chain (sa, x.log, kvLeasesOn γr.kv srvAuthSt0 A) (sa', x.log, kvLeasesOn γr.kv srvAuthSt0 A) m Hdet
            (outcomeOn_of_adminStateR γr.kv.c0 x.chain (sa, x.log, kvLeasesOn γr.kv srvAuthSt0 A) m rq sa' Htyp hdata hdec hv (adminDispatchKind_of_adminKindOk rq hadm hna) hR)
        have Htie : authTie sa x.log (kvLeasesOn γr.kv srvAuthSt0 A) rq out :=
          authTie_nonAuthKV sa x.log _ rq out (adminKindOk_nonAuthKV rq hadm)
        -- (E3x) the result's tie at the model's step
        have hsa : sa' = adminNext rq sa :=
          (Prod.mk.inj (hmod.trans (kvEntryOn_admin γr.kv.c0 x.chain (sa, x.log, kvLeasesOn γr.kv srvAuthSt0 A) m rq Htyp hdata
            hdec hv (adminDispatchKind_of_adminKindOk rq hadm hna)))).1
        ihave #HtA : adminTieAr ar rq sa (adminNext rq sa) out $$ []
        · rw [← hsa]; iexact HtA0
        ihave HAR := Hcl $$ %hs' %sa' Hfu Htie %Hsa'.1 HT Htp
        ihave HRS : srvRestM true E γr (A ++ [m]) $$ [HRS HLt HEv]
        · iapply srvRestM_admin E γr A m rq Htyp hdata hdec hadm; iapply srvRestM_close true; iframe HLt HGI HRq HEv; iexists f; iframe HRS; ipureintro; exact Hfb
        ihave #Hnn : iprop(⌜ar = null⌝ ∨ ∃ err : GoInterface,
            structFieldRef go_etcd_io.etcd.server.v3.etcdserver.apply.Result go!"Err" ar ↦□ err ∗
            notNoSpaceErr err) $$ [HNS]
        · iexact HNS
        ihave HAu : authnArM true E ar rq out $$ []
        · iapply (authnArM_of_ne true E ar rq out hka)
        ihave HGA0 := grantArM_not_grantW E ar rq out (adminKindOk_nonGrant rq hadm)
        ihave HVA0 := revokeArM_not_revokeW E ar rq out (adminKindOk_nonRevoke rq hadm)
        tail_on sa' (kvLeasesOn γr.kv srvAuthSt0 A)


/-- **`applyEntryNormal.spec`**, in the environment's auth mode (step 6 of the auth-mode merge,
2026-10-30): with auth off `wp_proofOff`'s, with auth on `wp_proofOn`'s, each case by case on `v3`. -/
theorem EtcdServer.applyEntryNormal.wp_proof
    (hGI : raftpb.Entry.GetIndex.spec (GF := GF) (hG := hG))
    (hGT : raftpb.Entry.GetTerm.spec (GF := GF) (hG := hG))
    (hC : consistentIndex.ConsistentIndex.spec (GF := GF) (hG := hG))
    (hS : consistentIndex.SetConsistentIndex.spec (GF := GF) (hG := hG))
    (hN : notify.Notifier.Notify.spec (GF := GF) (hG := hG))
    (hL : EtcdServer.isLeader.spec (GF := GF) (hG := hG))
    (hE : config.ServerConfig.ElectionTimeout.spec (GF := GF) (hG := hG))
    (hA0 : apply.Apply.spec (GF := GF) (hG := hG))
    (hUb : apply.uberApplier.Apply.spec (GF := GF) (hG := hG))
    (hIs : errors.Is.spec (GF := GF) (hG := hG))
    (hAG : v3alarm.AlarmStore.Get.spec (GF := GF) (hG := hG))
    (hLg : EtcdServer.Logger.spec (GF := GF) (hG := hG))
    (hZS : zap.String.spec (GF := GF) (hG := hG))
    (hZI : zap.Int64.spec (GF := GF) (hG := hG))
    (hZE : zap.Error.spec (GF := GF) (hG := hG))
    (hHB : go_humanize.Bytes.spec (GF := GF) (hG := hG))
    (hW : zap.Logger.Warn.spec (GF := GF) (hG := hG))
    (hGA : EtcdServer.GoAttach.spec (GF := GF) (hG := hG))
    (hMID : EtcdServer.MemberID.spec (GF := GF) (hG := hG))
    [mvccSem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
    (hPers : mvcc.api.persistent.law (GF := GF) (hG := hG))
    (hReach : mvcc.api.mvccState_reachable.law (GF := GF) (hG := hG)) :
    EtcdServer.applyEntryNormal.spec (GF := GF) (hG := hG) := by
  have h := EtcdServer.applyEntryNormal.wp_proofOff hGI hGT hC hS hN hL hE hA0 hUb hIs hAG hLg hZS hZI hZE hHB hW hGA hMID hPers hReach
  have hOn := EtcdServer.applyEntryNormal.wp_proofOn hGI hGT hC hS hN hL hE hA0 hUb hIs hAG hLg hZS hZI hZE hHB hW hGA hMID hPers hReach
  intro s γ ci TM E ρ b e m st v3 x γr ot v A sa A₀ r hany
  cases hm : E.authMode with
  | any => exact absurd hm hany
  | off =>
    have hoff : E.authOn = false := by rw [apply.AEnv.authOn_eq, hm]; rfl
    have hT : ∀ k, srvTokRights (GF := GF) E k = iprop(True) := by
      intro k; unfold srvTokRights; rw [hm]
    have h := h s γ ci TM E ρ b e m st v3 x γr ot v A A₀ r hoff
    rw [hoff]
    cases v3
    · simp only [isServerM_false, srvApplyKVM_false, entryOkM_false, srvRestRpM_false, Bool.false_eq_true,
        ↓reduceIte] at h ⊢
      iintro %Φ ⟨#Hpkg, -, -, #Hsrv, #Hew, He, Hst, Hbe, Hlr, Hgr, Hmr, HKV, Hwt, Hfs, #Hcm, HRS, #HA0,
        %HmA, %Hpo⟩ HΦ
      iapply h $$ [He Hst Hbe Hlr Hgr Hmr HKV Hwt Hfs HRS] HΦ
      iframe Hpkg Hsrv Hew He Hst Hbe Hlr Hgr Hmr HKV Hwt Hfs Hcm HRS HA0
      ipureintro; exact ⟨HmA, Hpo.1, Hpo.2.1, Hpo.2.2.1, Hpo.2.2.2.1, Hpo.2.2.2.2.2⟩
    · simp only [isServerM_false, srvApplyKVM_false, kvAppliedM_false,
        entryOkM_false, hT, srvRestM_false, Bool.false_eq_true, ↓reduceIte] at h ⊢
      iintro %Φ ⟨#Hpkg, -, -, #Hsrv, #Hew, Hrg, He, Hst, Hbe, Hlr, Hgr, Hmr, HKV, Hwt, Hfs, Hao, Hlog,
        #Hcm, Hka, HRS, %Hmc, #Hrl, %Hv, %Hidx, %Hpre, Hv3, -⟩ HΦ
      iapply h $$ [Hrg He Hst Hbe Hlr Hgr Hmr HKV Hwt Hfs Hao Hlog Hka HRS Hv3]
      · iframe Hpkg Hsrv Hew Hrg He Hst Hbe Hlr Hgr Hmr HKV Hwt Hfs Hao Hlog Hcm Hka HRS Hrl Hv3
        ipureintro; exact ⟨Hmc, Hv, Hidx, Hpre.1, Hpre.2.1, Hpre.2.2⟩
      inext
      iintro ⟨Hbe, Hlr, Hgr, Hmr, Hfs, ⟨%x', %out, HKV, %Hstep, Hdel, Hap, Hka, HRS⟩, Hst⟩
      iapply HΦ
      iframe Hbe Hlr Hgr Hmr Hfs Hst
      iexists x', out, sa; iframe HKV Hdel Hap Hka HRS; ipureintro; exact Hstep
  | on γa =>
    have hon : E.authOn = true := by rw [apply.AEnv.authOn_eq, hm]; rfl
    have hOn := hOn s γ ci TM E ρ b e m st v3 x γr ot v A γa sa A₀ r hm
    rw [hon]
    cases v3
    · simp only [srvApplyKVM_true, entryOkM_true, Bool.false_eq_true, ↓reduceIte] at hOn ⊢
      iintro %Φ ⟨#Hpkg, ⟨Hr, Hawt⟩, %Hrb, #Hsrv, #Hew, He, Hst, Hbe, Hlr, Hgr, Hmr, HKV, Hwt, Hfs, #Hcm, HRS,
        #HA0, %HmA, %Hpo⟩ HΦ
      iapply hOn $$ [He Hst Hbe Hlr Hgr Hmr HKV Hwt Hfs Hr Hawt HRS] HΦ
      iframe Hpkg Hsrv Hew He Hst Hbe Hlr Hgr Hmr HKV Hwt Hfs Hr Hawt Hcm HRS HA0
      ipureintro
      exact ⟨HmA, Hpo.1, Hpo.2.1, Hpo.2.2.1, Hpo.2.2.2.1, Hrb trivial,
        Hpo.2.2.2.2.1 trivial, Hpo.2.2.2.2.2⟩
    · simp only [srvApplyKVM_true, kvAppliedM_true, entryOkM_true,
        ↓reduceIte] at hOn ⊢
      iintro %Φ ⟨#Hpkg, ⟨Hr, Hawt⟩, %Hrb, #Hsrv, #Hew, Hrg, He, Hst, Hbe, Hlr, Hgr, Hmr, HKV, Hwt, Hfs, Hao,
        Hlog, #Hcm, Hka, HRS, %Hmc, #Hrl, %Hv, %Hidx, %Hpre, Hv3, Htok⟩ HΦ
      iapply hOn $$ [Hrg He Hst Hbe Hlr Hgr Hmr HKV Hwt Hfs Hr Hawt Hao Hlog Hka HRS Hv3 Htok] HΦ
      iframe Hpkg Hsrv Hew Hrg He Hst Hbe Hlr Hgr Hmr HKV Hwt Hfs Hr Hawt Hao Hlog Hcm Hka HRS Hrl Hv3 Htok
      ipureintro; exact ⟨Hmc, Hv, Hidx, Hpre.1, Hpre.2.1, Hpre.2.2, Hrb trivial⟩

end proof

end EtcdGrove
end Perennial
