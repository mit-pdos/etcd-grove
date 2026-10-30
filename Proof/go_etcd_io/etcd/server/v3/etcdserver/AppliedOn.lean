/-
**The apply thread's state in the auth mode `on`** (the auth plan's E3i, 2026-10-27; E3f's
blocker 3). Lean-first (no Rocq counterpart).

The applied index's invariant (`srvAppliedInv`) records every applied log as the KV model of the
committed raft log through its index (`kvLogsOk`, `kvLogAt`): the mode-`off` model (`kvModel`). In
the mode `on` the model is the auth-aware one (`kvModelOn` from the server's start state, `kvModelM
true`), so the invariant, its lower bounds and the apply thread's deposit (`applied_predeposit`)
get mode-indexed counterparts, each today's at `false` by definition (`…M_false`, `rfl`): what the
apply thread, the readers and the proposers in the mode `on` read.

Then the server as the apply thread sees it (`isServer`): `isServerM`, with the wait in the mode
(`waitInvM`, E3b) and the atomics' row in the mode (`srvAtomicsM`: `srvAppliedInvM` and
`srvKVInvsM`, E2w's `srvKVInvsOn` at `true`); and the apply thread's applier state with auth on
(`srvApplyKVOn`): `srvApplyKV` with the auth resource at the model's latest auth state
(`srvAuthApplyResB`, E3c/E3l) and the base applier's auth layer (`srvUberBase`, E3k; E3o), from
which the server applier's latest-state facts (`apply.uberKVL`, E2y; `apply.uberAuthStepsL`, E3c)
are derived.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ReqOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVApplyOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AuthApplyRes
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.ApplyFnKVL
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.ApplyFnAdminL
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.StartOn

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section applied
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem kvLogsOkM_insert (on : Bool) (γr : ReadNames) (M : GMap w64 mvcc.Log) (v : w64)
    (L : mvcc.Log) :
    kvLogsOkM (GF := GF) on γr M ∗ kvLogAtM on γr v L ⊢ kvLogsOkM on γr (M.insert v L) := by
  unfold kvLogAtM
  iunfold kvLogsOkM
  iintro ⟨⟨%Lb, #Hlb, %Hm⟩, ⟨%A, #HA, %Ha⟩⟩
  ihave %Hc := srvRLogLb_prefix γr.raft A Lb $$ [HA Hlb]
  · iframe HA Hlb
  rcases Hc with h | h
  · iexists Lb
    iframe Hlb
    ipureintro
    intro k L' hk
    rw [GMap.lookup_insert_Some] at hk
    rcases hk with ⟨rfl, rfl⟩ | ⟨-, hk⟩
    · exact ⟨A, h, Ha.1, Ha.2⟩
    · exact Hm k L' hk
  · iexists A
    iframe HA
    ipureintro
    intro k L' hk
    rw [GMap.lookup_insert_Some] at hk
    rcases hk with ⟨rfl, rfl⟩ | ⟨-, hk⟩
    · exact ⟨A, List.prefix_refl _, Ha.1, Ha.2⟩
    · obtain ⟨A', h1, h2, h3⟩ := Hm k L' hk
      exact ⟨A', h1.trans h, h2, h3⟩

/-- The applied logs of `kvLogsPubM` (E3u). -/
theorem kvLogsPubM_ok (on : Bool) (E : apply.AEnv GF) (γr : ReadNames) (M : GMap w64 mvcc.Log)
    (a : w64) : kvLogsPubM (GF := GF) on E γr M a ⊢ kvLogsOkM on γr M := by
  iintro H
  icases (kvLogsPubM_iff on E γr M a).1 $$ H with ⟨H, -⟩
  iexact H

/-- `kvLogsOkM_insert` under `kvLogsPubM` (E3u; the current applied index unchanged). -/
theorem kvLogsPubM_insert (on : Bool) (E : apply.AEnv GF) (γr : ReadNames) (M : GMap w64 mvcc.Log)
    (a v : w64) (L : mvcc.Log) :
    kvLogsPubM (GF := GF) on E γr M a ∗ kvLogAtM on γr v L ⊢ kvLogsPubM on E γr (M.insert v L) a := by
  iintro ⟨H, #HA⟩
  icases (kvLogsPubM_iff on E γr M a).1 $$ H with ⟨#Hk, #Hp⟩
  iapply (kvLogsPubM_iff on E γr _ a).2
  iframe Hp
  iapply kvLogsOkM_insert on γr M v L $$ [Hk HA]
  iframe Hk HA

/-- **The log after the next entry, deposited ahead, in the mode** (`applied_predeposit`'s
counterpart): the apply thread deposits a log `L` extending its current one as the log applied
through `v' = v + 1`, `L` the mode's model of the committed raft log through `v'`. -/
theorem applied_predepositM (on : Bool) (s : Loc) (E : apply.AEnv GF) (γr : ReadNames)
    (v v' : w64) (L₀ L : mvcc.Log) (hv : uint.Z v' = uint.Z v + 1) (hp : L₀ <+: L) :
    ⊢ srvAppliedInvM (GF := GF) on s E γr -∗ srvAppliedOwn γr v -∗ appliedLogAt γr v L₀ -∗
      kvLogAtM on γr v' L ={⊤}=∗ srvAppliedPre γr v v' L := by
  iintro #Hinv Hown #HL₀ #HkA
  iunfold srvAppliedInvM at Hinv
  iinv Hinv with Hi Hclose
  iunfold srvAppliedBodyM at Hi
  icases Hi with ⟨%vat, %v0, %Lc, %M, %p, Hat, >Hauth, >HM, >Hp, >%HMk, >#HLc, >#Hc, >#Hkl⟩
  iunfold srvAppliedOwn at Hown
  icases Hown with ⟨Hown, Hpo⟩
  ihave %Hag := monoNatAuthOwn_agree γr.applied _ _ _ _ $$ Hown Hauth
  have hv0 : v0 = v := by
    have h2 := Hag.2
    unfold uint.nat at h2
    exact (BitVec.eq_of_toNat_eq h2).symm
  subst hv0
  ihave %Hpg := ghostVar_agree γr.pend _ _ _ _ $$ Hpo Hp
  subst Hpg
  ihave %HLeq := appliedLogAt_agree γr v0 Lc L₀ $$ HLc HL₀
  subst HLeq
  ihave %HMv : iprop(⌜M.lookup v0 = some Lc⌝) $$ [HM]
  · iunfold appliedLogAt at HLc
    iapply ghost_map_lookup $$ HM HLc
  have hk : ∀ k L', M.lookup k = some L' → uint.Z k ≤ uint.Z v0 := by
    intro k L' h
    rcases HMk.2.1 k L' h with h | ⟨h, -⟩
    · exact h
    · cases h
  have hfresh : M.lookup v' = none := by
    cases h : M.lookup v' with
    | none => rfl
    | some L' => have := hk v' L' h; omega
  imod ghost_map_insert_persist v' L hfresh $$ HM with ⟨HM, #HLv'⟩
  imod ghostVar_update_halves true γr.pend false false $$ Hpo Hp with ⟨Hpo, Hp⟩
  ihave #Hkl' := kvLogsPubM_insert on E γr M v0 v' L $$ [Hkl HkA]
  · iframe Hkl HkA
  imod Hclose $$ [Hat Hauth HM Hp] with -
  · inext
    iunfold srvAppliedBodyM
    iexists vat, v0, Lc, M.insert v' L, true
    iframe Hat Hauth HM Hp HLc Hc Hkl'
    ipureintro
    refine ⟨HMk.1, ?_, appliedMonoMap_insert M v0 v' Lc L hk HMk.2.2 HMv hp (by omega)⟩
    intro k L' h
    rw [GMap.lookup_insert_Some] at h
    rcases h with ⟨rfl, -⟩ | ⟨-, h⟩
    · exact Or.inr ⟨rfl, hv⟩
    · exact Or.inl (hk k L' h)
  imodintro
  iunfold srvAppliedPre
  iframe Hown Hpo
  isplitr
  · iunfold appliedLogAt; iexact HLv'
  ipureintro; exact hv

/-- **An applied log is the mode's KV model of the committed raft log through its index**
(`appliedLogAt_kvLogAt`'s counterpart). -/
theorem appliedLogAt_kvLogAtM (on : Bool) (s : Loc) (E : apply.AEnv GF) (γr : ReadNames)
    (i : w64) (L1 : mvcc.Log) :
    ⊢ srvAppliedInvM (GF := GF) on s E γr -∗ appliedLogAt γr i L1 ={⊤}=∗ kvLogAtM on γr i L1 := by
  iintro #Hinv #H1
  iunfold srvAppliedInvM at Hinv
  iinv Hinv with Hi Hclose
  iunfold srvAppliedBodyM at Hi
  icases Hi with ⟨%vat, %v, %L, %M, %p, Hat, >Hauth, >HM, >Hp, >%HMk, >#HL, >#Hc, >#Hkl⟩
  ihave %Hm1 : iprop(⌜M.lookup i = some L1⌝) $$ [HM]
  · iunfold appliedLogAt at H1
    iapply ghost_map_lookup $$ HM H1
  imod Hclose $$ [Hat Hauth HM Hp] with -
  · inext
    iunfold srvAppliedBodyM
    iexists vat, v, L, M, p
    iframe Hat Hauth HM Hp HL Hc Hkl
    ipureintro; exact HMk
  imodintro
  ihave #Hkl := kvLogsPubM_ok on E γr M v $$ Hkl
  iunfold kvLogsOkM at Hkl
  icases Hkl with ⟨%Lb, #Hlb, %Hm⟩
  obtain ⟨A, hA, h1, h2⟩ := Hm i L1 Hm1
  iunfold kvLogAtM
  iexists A
  isplitr
  · iapply srvRLogLb_mono γr.raft A Lb hA $$ Hlb
  ipureintro; exact ⟨h1, h2⟩

end applied

section server
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftAsm : go_etcd_io.raft.v3.Assumptions]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **The server's atomics in the mode `on`** (`srvAtomics` at `false`): the applied index's
invariant over the mode's model (`srvAppliedInvM`) and the KV invariants in the mode
(`srvKVInvsM`). -/
def srvAtomicsM (on : Bool) (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) : IProp GF :=
  iprop(srvAppliedInvM on s E γr ∗
    inv srvN (∃ v : w64, sync.atomic.ownUint64 (srvTermAddr s) (DFrac.own 1) v) ∗
    srvKVInvsM on s E γr)

instance srvAtomicsM_persistent (on : Bool) (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) :
    Persistent (srvAtomicsM (GF := GF) on s E γr) := by
  unfold srvAtomicsM; infer_instance

theorem srvAtomicsM_false (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) :
    srvAtomicsM (GF := GF) false s E γr = srvAtomics s E γr := rfl

/-- **The server's fields in the mode `on`** (`srvFieldsAt` at `false`): the wait in the mode
(`waitInvM`, E3b: its results carry the auth layer's verdict). -/
def srvFieldsAtM (on : Bool) (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF)
    (E : apply.AEnv GF) (ρ : ReqNames) (v : SrvFields) : IProp GF :=
  iprop(srvLgAddr s ↦□ v.lg ∗ ⌜v.lg ≠ null⌝ ∗
      srvWAddr s ↦□ v.w ∗ waitInvM on v.w ρ E ∗
      ⌜E.P = batchLockInv γ TM ∧ E.f = v.hook⌝ ∗ ⌜srvEnvOk s γ ci E v.cluster⌝ ∗
      hookSpec γ ci TM v.hook ∗
      srvLessorAddr s ↦□ v.lessor ∗ lessorOk v.lessor ∗
      srvFirstCommitAddr s ↦□ v.firstCommit ∗ srvAlarmStoreAddr s ↦□ v.alarmStore ∗
      srvClusterAddr s ↦□ v.cluster ∗ membership.isRaftCluster v.cluster ∗
      srvQuotaAddr s ↦□ v.quota ∗
      srvLgMuAddr s ↦□ v.lgMu ∗ srvMemberIDAddr s ↦□ v.memberID ∗ srvLeadInv s ∗
      cfgElectionTicksAddr (srvCfgAddr s) ↦□ v.electionTicks ∗
      cfgTickMsAddr (srvCfgAddr s) ↦□ v.tickMs ∗
      isNotifier v.firstCommit ∗ isAlarmStore v.alarmStore)

instance srvFieldsAtM_persistent (on : Bool) (s : Loc) (γ : ApplyNames) (ci : Loc)
    (TM : MetaCI → IProp GF) (E : apply.AEnv GF) (ρ : ReqNames) (v : SrvFields) :
    Persistent (srvFieldsAtM on s γ ci TM E ρ v) := by
  unfold srvFieldsAtM; infer_instance

theorem srvFieldsAtM_false (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF)
    (E : apply.AEnv GF) (ρ : ReqNames) (v : SrvFields) :
    srvFieldsAtM (GF := GF) false s γ ci TM E ρ v = srvFieldsAt s γ ci TM E ρ v := rfl

/-- **The apply thread's view of the server in the mode `on`** (`isServer` at `false`): the
fields with the wait in the mode (`srvFieldsAtM`) and the atomics in the mode (`srvAtomicsM`). -/
def isServerM (on : Bool) (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF)
    (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) : IProp GF :=
  iprop(⌜ρ.rd = γr⌝ ∗ isServerCI s γ ci ∗ (∃ v : SrvFields, srvFieldsAtM on s γ ci TM E ρ v) ∗
    srvAtomicsM on s E γr ∗ srvGenAt s E ρ ∗ srvRaftNode s ρ.raft)

instance isServerM_persistent (on : Bool) (s : Loc) (γ : ApplyNames) (ci : Loc)
    (TM : MetaCI → IProp GF) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) :
    Persistent (isServerM on s γ ci TM E ρ γr) := by
  unfold isServerM; infer_instance

theorem isServerM_false (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF)
    (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) :
    isServerM (GF := GF) false s γ ci TM E ρ γr = isServer s γ ci TM E ρ γr := rfl

/-- **The server's atomics in the mode `on` from `start`'s construction premise** (E3k): the
applied index's invariant over the mode's model is allocated at the boot (`srvIndices_allocM`), so
`isServerBuiltOn` carries `srvAtomicsM true`'s three invariants. -/
theorem srvAtomicsM_of_builtOn (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF)
    (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (Er : RNEnv GF) (γn : RNNames)
    (b : GoInterface) (ai₀ at₀ c₀ : w64) (x₀ : apply.ApplyKV) (N : Nat) :
    isServerBuiltOn (GF := GF) s γ ci TM E ρ γr Er γn b ai₀ at₀ c₀ x₀ N ⊢
      srvAtomicsM true s E γr := by
  unfold isServerBuiltOn srvAtomicsM
  iintro ⟨-, -, -, -, -, -, -, #Hai, #Hkvi, #Hti, -⟩
  iframe Hai Hkvi Hti

/-- **The apply thread's applier state with auth on** at `x` and the model's auth state `st`
(`srvApplyKV`'s): the uber-applier with its base applier's auth layer at the server's store and
lessor (`srvUberBase`, what the latest-state triples come from: `srv_uberKVL_on`, and with the row's
admin steps `apply.uberAuthStepsL_of_base`), and the auth resource at `st` (`srvAuthApplyResB`: the
store's history's latest state is the model's). E3o: the latest-state triples are derived where
they are used rather than carried (until E3o this row named them, for families the construction
did not yet fix); `applyBuiltOn` holds the same parts. -/
def srvApplyKVOn (s : Loc) (E : apply.AEnv GF) (γw : GName) (x : apply.ApplyKV)
    (st : auth.AuthState) : IProp GF :=
  iprop(∃ ua : GoInterface, srvUberApplyAddr s ↦ ua ∗ srvUberBase s ua E ∗ apply.applierFor ua E ∗
    apply.applyKV E ua x ∗ srvBeOwn s E ∗ revAuth E x.log ∗ srvAuthApplyResB s E st ∗
    ∃ (w : GoInterface) (RD : IProp GF), srvWAddr s ↦□ w ∗
      waitOk w RD (fun ot id => waitRegdOpt γw id ot) (fun ot id => waitGoneOpt γw id ot) ∗ RD)

/-- **The apply thread's applier state in the mode `on`** (the auth-mode merge's step 1,
2026-10-29): `srvApplyKV` off (the auth state `st` unused), `srvApplyKVOn` on. -/
def srvApplyKVM (on : Bool) (s : Loc) (E : apply.AEnv GF) (γw : GName) (x : apply.ApplyKV)
    (st : auth.AuthState) : IProp GF :=
  match on with
  | false => srvApplyKV s E γw x
  | true => srvApplyKVOn s E γw x st

theorem srvApplyKVM_false (s : Loc) (E : apply.AEnv GF) (γw : GName) (x : apply.ApplyKV)
    (st : auth.AuthState) : srvApplyKVM (GF := GF) false s E γw x st = srvApplyKV s E γw x := rfl

theorem srvApplyKVM_true (s : Loc) (E : apply.AEnv GF) (γw : GName) (x : apply.ApplyKV)
    (st : auth.AuthState) : srvApplyKVM (GF := GF) true s E γw x st = srvApplyKVOn s E γw x st :=
  rfl

/-- **The KV model's applied state in the mode `on`** (step 1): `kvApplied` off (the start's auth
state `st₀` and the latest `st` unused), `kvAppliedOn` on. -/
def kvAppliedM (on : Bool) (γ : ServerRaftNames) (γk : KVNames) (st₀ : auth.AuthState)
    (A : List EntryModel) (x : apply.ApplyKV) (st : auth.AuthState) : IProp GF :=
  match on with
  | false => kvApplied γ γk A x
  | true => kvAppliedOn γ γk st₀ A x st

theorem kvAppliedM_false (γ : ServerRaftNames) (γk : KVNames) (st₀ : auth.AuthState)
    (A : List EntryModel) (x : apply.ApplyKV) (st : auth.AuthState) :
    kvAppliedM (GF := GF) false γ γk st₀ A x st = kvApplied γ γk A x := rfl

theorem kvAppliedM_true (γ : ServerRaftNames) (γk : KVNames) (st₀ : auth.AuthState)
    (A : List EntryModel) (x : apply.ApplyKV) (st : auth.AuthState) :
    kvAppliedM (GF := GF) true γ γk st₀ A x st = kvAppliedOn γ γk st₀ A x st := rfl

end server

section offlemma
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

open Iris.ProofMode in
/-- **The mode-off apply thread is in an environment with auth off** (the auth-mode merge,
2026-10-29: what a mode-off caller passes to a merged spec's `E.authOn = false`): the KV
invariant's start chain has the auth layer off (`kvInv_ch0_off`), the applier state's chain is it
(`kvApplied`), and the applier's chain's auth layer is the environment's (`applyKV_authOn`). -/
theorem authOn_false_of_off (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF)
    (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (γw : GName) (x : apply.ApplyKV)
    (A : List EntryModel) :
    isServer (GF := GF) s γ ci TM E ρ γr ∗ srvApplyKV s E γw x ∗ kvApplied γr.raft γr.kv A x ={⊤}=∗
      ⌜E.authOn = false⌝ ∗ srvApplyKV s E γw x ∗ kvApplied γr.raft γr.kv A x := by
  iintro ⟨#Hsrv, Hkv, Hka⟩
  iunfold isServer at Hsrv
  icases Hsrv with ⟨-, -, -, Hat, -, -⟩
  iunfold srvAtomics at Hat
  icases Hat with ⟨-, -, Hki⟩
  iunfold srvKVInvs at Hki
  icases Hki with ⟨#Hki, -⟩
  imod (kvInv_ch0_off γr.raft γr.kv) $$ Hki with %Hch
  iunfold srvApplyKV at Hkv
  icases Hkv with ⟨%ua, Hua, Hap, Hakv, Hrest⟩
  icases applyKV_authOn E ua x $$ Hakv with ⟨Hakv, %Hc⟩
  iunfold kvApplied at Hka
  icases Hka with ⟨Hka, %Hx⟩
  imodintro
  isplitr
  · ipureintro
    rw [← Hc, Hx, Hch, apply.alarmChain_authOn]
  isplitl [Hua Hap Hakv Hrest]
  · iunfold srvApplyKV
    iexists ua
    iframe Hua Hap Hakv; iexact Hrest
  iunfold kvApplied
  iframe Hka
  ipureintro; exact Hx

/-- **With the mode-`off` start state, auth is off** (`authOn_false_of_off`'s reasoning at the apply
thread's start, `kvRun`; the auth-mode merge, 2026-10-29: `start`'s reader view's gated row). -/
theorem authOn_false_of_run (E : apply.AEnv GF) (γr : ReadNames) (ua : GoInterface)
    (x : apply.ApplyKV) (ai₀ c₀ : w64) (A : List EntryModel) :
    srvKVInvs (GF := GF) E γr ∗ apply.applyKV E ua x ∗ kvRun γr ai₀ c₀ A x ={⊤}=∗
      ⌜E.authOn = false⌝ ∗ apply.applyKV E ua x ∗ kvRun γr ai₀ c₀ A x := by
  iintro ⟨#Hki, Hakv, Hkr⟩
  iunfold srvKVInvs at Hki
  icases Hki with ⟨#Hki, -⟩
  imod (kvInv_ch0_off γr.raft γr.kv) $$ Hki with %Hch
  icases applyKV_authOn E ua x $$ Hakv with ⟨Hakv, %Hc⟩
  iunfold kvRun at Hkr
  icases Hkr with ⟨Hka, %Hr⟩
  iunfold kvApplied at Hka
  icases Hka with ⟨Hka, %Hx⟩
  imodintro
  isplitr
  · ipureintro
    rw [← Hc, Hx, Hch, apply.alarmChain_authOn]
  iframe Hakv
  iunfold kvRun
  iunfold kvApplied
  iframe Hka
  ipureintro; exact ⟨Hx, Hr⟩

end offlemma


end EtcdGrove
end Perennial
