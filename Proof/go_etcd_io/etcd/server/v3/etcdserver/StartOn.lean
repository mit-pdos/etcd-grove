/-
**`start`'s construction premise in the auth mode `on`** (the auth plan's E2z, 2026-10-26;
`notes/decisions.md`, "E2z of the auth plan"): `isServerBuilt`'s counterpart over the mode-`on`
rows of `srvBuiltG true` (E2w), what `start`'s mode-`on` proof will take.

- `kvRunOn`: the apply thread's KV ghost state at the applied log `A`, over the mode-`on` model
  (`kvAppliedOn`, E2t), at some auth state the model reaches (the apply thread's tie of that state
  to the store's latest, `authApplyRes`'s history, is the apply loop's, not stated here);
  `kvRun_nil_on`: at the empty log the mode-off `kvRun` gives it (both models start at the start's
  log, `kvRaftOf_nil`, `kvRaftOfOn_nil`).
- `applyBuiltOn`, `isServerBuiltOn`: `applyBuilt` and `isServerBuilt` with `kvRunOn`,
  `srvReqBuiltM true`, `srvKVInvsM true` and `srvCM true`; `isServerBuiltM` the mode's
  (`isServerBuilt` at `on = false` by definition, `isServerBuiltM_false`).
- `isServerBuilt_of_gapM`: `NewServer.specM on`'s built part and the residual give
  `isServerBuiltM on` (`isServerBuilt_of_gap`'s), so `server_new_auth_on`'s post reaches `start`'s
  mode-`on` premise.

**Additive.** Nothing mode-off changes.

Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ServerOn

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **The apply thread's KV ghost state in the mode `on`** at the applied raft log `A` (`kvRun`'s,
over `kvAppliedOn` from `srvAuthSt0`, at the auth state `st` the model reaches). -/
def kvRunOn (γr : ReadNames) (ai₀ c₀ : w64) (A : List EntryModel) (x : apply.ApplyKV) :
    IProp GF :=
  iprop((∃ st : auth.AuthState, kvAppliedOn γr.raft γr.kv srvAuthSt0 A x st) ∗
    ⌜γr.kv.c0 = c₀ ∧ γr.raft.ai0 = ai₀⌝)

/-- **The apply thread's resources at `ai₀` in the mode `on`** (`applyBuilt` with `kvRunOn`, and,
since E3c, the auth resource at the model's start state `srvAuthSt0`: the store's history's latest
state, `srvAuthApplyResB`, E3l). -/
def applyBuiltOn (s : Loc) (γ : ApplyNames) (ci : Loc) (b : GoInterface) (E : apply.AEnv GF)
    (γr : ReadNames) (ai₀ c₀ : w64) (x₀ : apply.ApplyKV) : IProp GF :=
  iprop(∃ (st₀ : ApplyState) (a t : w64) (f : Bool),
    applyThread γ st₀ ∗ ⌜loopOk γ st₀ ai₀ ∧ c₀ = ciEff γ st₀.k⌝ ∗ applyBackend γ ci b ∗
    ciApplying ci a t ∗ srvLgReader s ∗ srvBemuReaderAt s E.γbe ∗ srvBeOwn s E ∗
    (∃ ua : GoInterface, srvUberApplyAddr s ↦ ua ∗ srvUberBase s ua E ∗ apply.applierFor ua E ∗
      apply.applyKV E ua x₀) ∗
    revAuth E x₀.log ∗ srvAuthApplyResB s E srvAuthSt0 ∗
    srvAppliedOwn γr ai₀ ∗ appliedLogAt γr ai₀ x₀.log ∗ kvRunOn γr ai₀ c₀ [] x₀ ∗
    srvRest E γr [] ∗ srvApRes s γr [] ∗ srvForceSnapAddr s ↦ f)

/-- **`start`'s construction premise in the mode `on`** (`isServerBuilt` with the mode-`on` rows:
`srvReqBuiltM true`, `srvKVInvsM true`, `srvCM true`, `applyBuiltOn`). -/
def isServerBuiltOn (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF)
    (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (Er : RNEnv GF) (γn : RNNames)
    (b : GoInterface) (ai₀ at₀ c₀ : w64) (x₀ : apply.ApplyKV) (N : Nat) :
    IProp GF :=
  iprop("#Hci" ∷ isServerCI s γ ci ∗
    "#Hfb" ∷ (∃ v : SrvFields, srvFieldsBuilt s γ ci TM E v) ∗
    "#Hreqb" ∷ (∃ v : ReqFields, srvReqBuiltM true s E ρ v) ∗
    "#Hrdb" ∷ (∃ v : ReadFields, srvReadBuilt s E v) ∗
    "#Hrunb" ∷ (∃ v : RunFields, srvRunBuilt s v) ∗
    "#Hsab" ∷ srvApplyAllBuilt s ∗
    "#Hai" ∷ srvAppliedInvM true s E γr ∗
    "#Hkvi" ∷ srvKVInvsM true E γr ∗
    "#Hti" ∷ inv srvN (∃ t : w64, sync.atomic.ownUint64 (srvTermAddr s) (DFrac.own 1) t) ∗
    "#Hci'" ∷ srvCommittedInv s γr ∗
    "#Hrn" ∷ isRaftNode Er γn (srvRAddr s) ∗
    "%HEr" ∷ ⌜Er.C = srvCM true ρ E ai₀ c₀ x₀ ∧ Er.γr = γr ∧
      (γn.node.mode.isDyn = true → uint.Z c₀ ≤ uint.Z ai₀)⌝ ∗
    "%Hρrd" ∷ ⌜ρ.rd = γr⌝ ∗
    "Hsnap" ∷ (∃ ms : Loc, rnRaftStorageAddr (srvRAddr s) ↦□ ms ∗ rnSnapOnce ms γn.γs ai₀ at₀) ∗
    "Hloop" ∷ rnLoopTok γn [] ∗ "Hsend" ∷ Er.S ∗ "Happly" ∷ rnApplyTok γn [] ∗
    "Hrdone" ∷ rnDoneTok γn (srvRAddr s) ∗
    "#HNR" ∷ □ (|==> idCred ρ.ids 1) ∗
    "#Hcv" ∷ clusterVersionOk s ∗
    "#Hcci" ∷ context.isClosedchanInit ∗
    "#Hwci" ∷ waitClosecInit ∗
    "%Hbound" ∷ ⌜threadBound GF ≤ 2 ^ 31⌝ ∗
    "Hw" ∷ (∃ w : GoInterface, srvWAddr s ↦ w) ∗
    "Haw" ∷ (∃ aw : GoInterface, srvApplyWaitAddr s ↦ aw) ∗
    "Hdone" ∷ (∃ c : Loc, srvDoneAddr s ↦ c) ∗
    "Hstop" ∷ (∃ c : Loc, srvStopAddr s ↦ c) ∗
    "Hstopping" ∷ (∃ c : Loc, srvStoppingAddr s ↦ c) ∗
    "Hctx" ∷ (∃ c : GoInterface, srvCtxAddr s ↦ c) ∗
    "Hcancel" ∷ (∃ c : GoFunc, srvCancelAddr s ↦ c) ∗
    "Hread" ∷ (∃ r : Loc, srvReadAddr s ↦ r) ∗
    "Hlc" ∷ (∃ n : Loc, srvLeaderChangedAddr s ↦ n) ∗
    "Hsc" ∷ (∃ n : w64, srvSnapCountAddr s ↦ n) ∗
    "Hscu" ∷ (∃ n : w64, srvSnapCatchUpAddr s ↦ n ∗
      ⌜receiptBound GF ≤ uint.Z (if n = W64 0 then W64 5000 else n) + 1⌝) ∗
    "Hwg" ∷ srvWgAddr s ↦ (zero_val sync.WaitGroup) ∗
    "HwgMu" ∷ srvWgMuAddr s ↦ (zero_val sync.RWMutex) ∗
    "Hcomm" ∷ (∃ c : w64, srvCommittedOwn γr c) ∗
    "Hnot" ∷ (∃ x : Loc × NeedNames, ghostVar γr.notifier 1 x) ∗
    "Happ" ∷ applyBuiltOn s γ ci b E γr ai₀ c₀ x₀ ∗
    "Hlr" ∷ srvLgReader s ∗
    "Hlrl" ∷ srvLgReader s ∗
    "Hfcr" ∷ (∃ n : Loc, srvFirstCommitAddr s ↦□ n ∗ notifyReader n) ∗
    "HWB" ∷ srvWTStock E N ∗
    "Hwtok" ∷ idWaitTok ρ.ids ∗
    -- (2026-10-26, D22 J1a) what the snapshot path takes of the construction (`SnapRO.lean`)
    "Hsnapb" ∷ srvSnapBoot s ci E γr)

/-- **`start`'s construction premise in the auth mode `on`**: `isServerBuilt` at `on = false` (by
definition: `isServerBuiltM_false`), `isServerBuiltOn` at `on = true`. -/
def isServerBuiltM (on : Bool) (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF)
    (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (Er : RNEnv GF) (γn : RNNames)
    (b : GoInterface) (ai₀ at₀ c₀ : w64) (x₀ : apply.ApplyKV) (N : Nat) : IProp GF :=
  match on with
  | false => isServerBuilt s γ ci TM E ρ γr Er γn b ai₀ at₀ c₀ x₀ N
  | true => isServerBuiltOn s γ ci TM E ρ γr Er γn b ai₀ at₀ c₀ x₀ N

theorem isServerBuiltM_false (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF)
    (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (Er : RNEnv GF) (γn : RNNames)
    (b : GoInterface) (ai₀ at₀ c₀ : w64) (x₀ : apply.ApplyKV) (N : Nat) :
    isServerBuiltM (GF := GF) false s γ ci TM E ρ γr Er γn b ai₀ at₀ c₀ x₀ N =
      isServerBuilt s γ ci TM E ρ γr Er γn b ai₀ at₀ c₀ x₀ N := rfl

theorem isServerBuiltM_true (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF)
    (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (Er : RNEnv GF) (γn : RNNames)
    (b : GoInterface) (ai₀ at₀ c₀ : w64) (x₀ : apply.ApplyKV) (N : Nat) :
    isServerBuiltM (GF := GF) true s γ ci TM E ρ γr Er γn b ai₀ at₀ c₀ x₀ N =
      isServerBuiltOn s γ ci TM E ρ γr Er γn b ai₀ at₀ c₀ x₀ N := rfl

end defs

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **At the empty applied log the mode-off `kvRun` gives the mode-`on` one**: both models start
at the start's log, the mode-`on` one at the auth state `srvAuthSt0`. -/
theorem kvRun_nil_on (γr : ReadNames) (ai₀ c₀ : w64) (x : apply.ApplyKV) :
    kvRun (GF := GF) γr ai₀ c₀ [] x ⊢ kvRunOn γr ai₀ c₀ [] x := by
  unfold kvRun kvApplied kvAppliedL kvRunOn kvAppliedOn kvAppliedLOn
  iintro ⟨⟨⟨#HL, Hhi, #Hc, %hl⟩, %hch⟩, %h⟩
  isplitl
  · iexists srvAuthSt0
    iframe HL Hhi Hc
    ipureintro
    refine ⟨?_, hch⟩
    rw [hl]
    rfl
  · ipureintro; exact h

/-- **`start`'s mode-`on` construction premise from `NewServer.specM true`'s built part and the
residual** (`isServerBuilt_of_gap`'s; see the file header). -/
theorem isServerBuilt_of_gapOn (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF)
    (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (Er : RNEnv GF) (γn : RNNames)
    (b : GoInterface) (ai₀ at₀ c₀ : w64) (x₀ : apply.ApplyKV) (N : Nat) :
    srvBuiltG true s γ ci TM E ρ γr Er γn b ai₀ c₀ x₀ N ∗ srvBuildGap s γn ai₀ at₀ ⊢
      isServerBuiltOn s γ ci TM E ρ γr Er γn b ai₀ at₀ c₀ x₀ N := by
  unfold srvBuiltG srvBuildGap isServerBuiltOn srvUberRowM
  iintro ⟨⟨#Hci, ⟨%v, #Hfb⟩, #Hreqb, ⟨%vr, #Hrdb⟩, #Hrunb, #Hsab, #Hai, #Hkvi, #Hti, #Hci',
      #Hrn, %HEr, %Hρrd, Hloop, Hsend, Happly, Hrdone, #Hcci, #Hwci, Hw, Haw, Hdone, Hstop, Hstopping,
      Hctx, Hcancel, Hread, Hlc, Hsc, Hscu, Hwg, HwgMu, Hcomm, Hnot, Happ, Hlr, Hlrl, Hfcr,
      ⟨%kv, %rv, #Hkv, #HisKV, #Hrv, #HisRV⟩, HWB, #Hsmall, #HNR, #Hcv, %Hbound,
      ⟨%ua, Hua, #HuB, #Hfor, Hakv⟩, Hwtok, Hsnapb⟩, Hsnap⟩
  iframe Hci Hreqb Hrunb Hsab Hai Hkvi Hti Hci' Hrn HNR Hcv Hcci Hwci
  iframe Hloop Hsend Happly Hrdone Hw Haw Hdone Hstop Hstopping Hctx Hcancel Hread Hlc Hsc Hscu Hwg
  iframe HwgMu Hcomm Hnot Hlr Hlrl Hfcr HWB Hsnap Hwtok Hsnapb
  isplitr
  · unfold srvFieldsBuiltNA
    iexists v
    unfold srvFieldsBuilt
    iframe Hfb
  isplitr
  · unfold srvReadBuiltNK
    iexists { vr with kv := kv, rv := rv }
    unfold srvReadBuilt
    iframe Hkv HisKV Hrv HisRV Hsmall Hrdb
  isplitr
  · ipureintro; exact HEr
  isplitr
  · ipureintro; exact Hρrd
  isplitr
  · ipureintro; exact Hbound
  unfold applyBuiltNAM applyBuiltNAOn applyBuiltOn
  icases Happ with ⟨%st₀, %a, %t, %f, Hth, %Hok, Hbe, Hca, Hlg, Hbm, Hbo, Hra, Har, Hao, Hal, Hkr, Hfs⟩
  iexists st₀, a, t, f
  iframe Hth Hbe Hca Hlg Hbm Hbo Hra Har Hao Hal Hfs
  isplitr
  · ipureintro; exact Hok
  isplitl [Hua Hakv]
  · iexists ua
    iframe Hua HuB Hfor Hakv
  iapply kvRun_nil_on $$ Hkr

/-- **`start`'s construction premise in the auth mode `on`, from `NewServer.specM on`'s built
part** (`isServerBuilt_of_gap` at `on = false`, `isServerBuilt_of_gapOn` at `on = true`). -/
theorem isServerBuilt_of_gapM (on : Bool) (s : Loc) (γ : ApplyNames) (ci : Loc)
    (TM : MetaCI → IProp GF) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (Er : RNEnv GF)
    (γn : RNNames) (b : GoInterface) (ai₀ at₀ c₀ : w64) (x₀ : apply.ApplyKV) (N : Nat) :
    srvBuiltG on s γ ci TM E ρ γr Er γn b ai₀ c₀ x₀ N ∗ srvBuildGap s γn ai₀ at₀ ⊢
      isServerBuiltM on s γ ci TM E ρ γr Er γn b ai₀ at₀ c₀ x₀ N := by
  cases on
  · rw [srvBuiltG_false, isServerBuiltM_false]
    exact isServerBuilt_of_gap s γ ci TM E ρ γr Er γn b ai₀ at₀ c₀ x₀ N
  · rw [isServerBuiltM_true]
    exact isServerBuilt_of_gapOn s γ ci TM E ρ γr Er γn b ai₀ at₀ c₀ x₀ N

end lemmas

end EtcdGrove
end Perennial

#print axioms Perennial.EtcdGrove.isServerBuilt_of_gapM
