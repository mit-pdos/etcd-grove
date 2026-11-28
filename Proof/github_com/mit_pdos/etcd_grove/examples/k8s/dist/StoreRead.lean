/-
Lean-first (no Rocq counterpart).

# k8s-dist K8-10: the store's read firings over the shared KV

`InvSteps.lean`'s read firings (`get_read_au`, `list_read_au`) on the shared cluster: the store's read update
of etcd is the share's (`KVPfxHist.kvPfxP_readAuH`, the store's `W` = `kInvDV`). Each firing catches the
store's half up with the share's state `σ` (`kInvDV_catchup`, to `σc`, equal to `σ` up to its leases) and, at
the prophesied revision, commits lintest's update with the model's output at `σc` (`linUD_commit`); the call's
commit bit records `σc`, which a later firing at that revision sees again (the revisions' map).

- `getCallD`, `readQD`: `getCall`/`readQ` over `linUD`; `readQD` records the caught-up state, equal to the
  read's up to its leases.
- `getD_read_au` (`get_read_au`).
- `listCallD`, `listQD` (the store's facts restricted to `/registry/`), `listD_read_au` (`list_read_au`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.dist.StoreFire

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_dist

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode k8s k8s_etcd3
open github_com.anishathalye.porcupine github_com.anishathalye.porcupine.Theory
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Obj item)
open go_etcd_io.etcd.server.v3.etcdserver

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]
variable [go_etcd_io.etcd.client.v3.Assumptions]
variable [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

theorem callN_cb : (↑callN : CoPset) ⊆ etcd_dist.kvPfxCbE := by
  intro p hp
  have hd : p ∈ (↑drvN : CoPset) := nclose_subseteq drvN "call" p hp
  obtain ⟨h1, h2, -⟩ := drvN_out p hd
  simp only [etcd_dist.kvPfxCbE, Std.LawfulSet.mem_diff]
  exact ⟨⟨⟨CoPset.mem_full, h1⟩, h2⟩, fun h => ndot_ne_disjoint nroot (by decide) p ⟨hd, h⟩⟩

theorem drvED_cb_call : ⊤ \ drvED ⊆ etcd_dist.kvPfxCbE \ ↑callN := by
  intro p hp
  have h := drvED_cb p hp
  simp only [drvED, drvE, Std.LawfulSet.mem_diff, Std.LawfulSet.mem_union] at hp
  refine Std.LawfulSet.mem_diff.2 ⟨h, fun hc => hp.2 (Or.inl (Or.inr (nclose_subseteq drvN "call" p hc)))⟩

theorem revOwnD_elem (γ : KNames) (σ : KVState) :
    revOwnD (GF := GF) γ σ ⊢ revOwnD γ σ ∗ ghostMapElem γ.r σ.rev DFrac.discard σ := by
  iintro H
  iunfold revOwnD at H
  icases H with ⟨%Mr, HA, #He, %Hok, Hch, %Hkh⟩
  iframe He
  iunfold revOwnD
  iexists Mr
  iframe He HA Hch
  ipureintro; exact ⟨Hok, Hkh⟩

/-- **`kvPfxP_readAuH` at `HeapGS`** (as `kvPfxP_au1HG`). -/
theorem kvPfxP_readAuHG (γk : KVNames) (p : GoString) (γ' : GName) (okp : mvcc.Change → Prop) (γh : GName)
    (σ₀ : KVState) (s : String) (hs : s ≠ "share")
    (W : etcd_dist.PfxV → IProp GF) [hW : ∀ v, Timeless (W v)] (l0 : List (List mvcc.Change))
    (Q : KVState → IProp GF) :
    etcd_dist.kvPfxHP γk p γ' okp γh σ₀ ∗
      inv (client.kvClientN .@ s) iprop(∃ v, ghostVar γ' (1 : Qp).half v ∗ W v) ∗
      monoListLbOwn γh l0 ∗
      □ (∀ σ, ⌜l0 <+: σ.changes ∧ etcd_dist.KVExt σ₀ σ ∧ etcd_dist.PfxChOk p okp σ.changes ∧ kvRoom σ⌝ -∗
        monoListAuthOwn γh 1 σ.changes -∗ W (etcd_dist.pfxVH p σ) -∗ |={etcd_dist.kvPfxCbE}=>
          (monoListAuthOwn γh 1 σ.changes ∗ W (etcd_dist.pfxVH p σ) ∗ □ Q σ)) ⊢
    kvReadAu γk Q :=
  etcd_dist.kvPfxP_readAuH γk p γ' okp γh σ₀ s hs W l0 Q

/-- **A `Get`'s call invariant on the shared KV** (`getCall` over `linUD`): the commit bit `γc` records the
store's caught-up state at the firing that committed. -/
def getCallD (γ : KNames) (c : StoreCfg GF DObj) (g0 : HSt) (eD eU : GoInterface)
    (γc γt γp : GName) (x : Input) (Φ : val → IProp GF) : IProp GF :=
  inv callN iprop(
    (linUD γ g0 (boxIn x) Φ ∗ £ 1 ∗ dghostVar γc (DFrac.own 1) (none : Option KVState)) ∨
    (∃ (σ : KVState) (R : w64), dghostVar γc DFrac.discard (some σ) ∗
      dghostVar γp DFrac.discard (some R) ∗ ⌜σ.rev = uint.nat R⌝ ∗
      ghostMapElem γ.r σ.rev DFrac.discard σ ∗
      ((contAt g0 x (kStep eD eU x (c.abs σ)).2 Φ ∗ ansOk c (kStep eD eU x (c.abs σ)).2) ∨
        dghostVar γt (DFrac.own 1) ())))

instance getCallD_persistent (γ : KNames) (c : StoreCfg GF DObj) (g0 : HSt) (eD eU : GoInterface)
    (γc γt γp : GName) (x : Input) (Φ : val → IProp GF) :
    Persistent (getCallD (GF := GF) γ c g0 eD eU γc γt γp x Φ) := by
  unfold getCallD; infer_instance

/-- **A read's post on the shared KV** (`readQ`): at the prophesied revision, the commit bit records a state
equal to the read's up to its leases. -/
def readQD (c : StoreCfg GF DObj) (γc : GName) (R : w64) (σ : KVState) : IProp GF :=
  iprop(⌜kvWf c σ ∧ σ.rev + 2 < 2 ^ 63⌝ ∗
    (⌜σ.rev = uint.nat R⌝ → ∃ σc, ⌜SameL σc σ⌝ ∗ dghostVar γc DFrac.discard (some σc)))

instance readQD_persistent (c : StoreCfg GF DObj) (γc : GName) (R : w64)
    (σ : KVState) : Persistent (readQD (GF := GF) c γc R σ) := by
  unfold readQD; infer_instance

/-- **A `Get`'s read update for the prophesied revision `R`, on the shared KV** (`get_read_au`): at its
first firing at a state of revision `R`, lintest's update commits with the model's output at the caught-up
state `σc` and the commit bit records `σc`; a later firing at revision `R` catches up to the same state (the
revisions' map). -/
theorem getD_read_au (γ : KNames) (c : StoreCfg GF DObj) (hc : CfgD c) (g0 : HSt) (γk : KVNames)
    (γs γsh : GName) (okS : mvcc.Change → Prop) (σ₀ : KVState) (l0 : List (List mvcc.Change))
    (eD eU : GoInterface) (γc γt γp : GName) (x : Input) (hx : InOk x) (hval : x.Val'.length ≤ 2 ^ 20)
    (hk : x.Kind' = W64 3) (R : w64) (Φ : val → IProp GF) :
    etcd_dist.kvPfxHP γk regP γs okS γsh σ₀ ∗ kInvD γ c g0 γs γsh σ₀ ∗ monoListLbOwn γsh l0 ∗
      getCallD γ c g0 eD eU γc γt γp x Φ ∗ dghostVar γp DFrac.discard (some R) ⊢
      kvReadAu γk (readQD c γc R) := by
  have Hcm := callN_cb
  have HE := drvED_cb_call
  unfold kInvD drvDInvN kInvDBody
  iintro ⟨#Hpfx, #Hinv, #Hl0, #Hc, #Hpr⟩
  iapply (kvPfxP_readAuHG γk regP γs okS γsh σ₀ "k8s" (by decide) (kInvDV γ c g0 γsh σ₀) l0)
  isplitl []
  · iexact Hpfx
  isplitl []
  · iexact Hinv
  isplitl []
  · iexact Hl0
  iintro !> %σ %Hpre Ha HW
  obtain ⟨-, he, -, hroom⟩ := Hpre
  have hrb : RevBoundD σ := by unfold RevBoundD; unfold kvRoom at hroom; omega
  imod (kInvDV_catchup γ c hc g0 γsh he hrb) $$ [Ha HW] with ⟨Ha, %σc, %hs, H⟩
  · iframe
  iunfold kInvDW at H
  icases H with ⟨%h, %S, %M, %nx, Hh, HM, Hr, Hs, %Hpure⟩
  obtain ⟨hel, hrun, hok⟩ := Hpure
  have hwσ : kvWf c σ := (kvWf_sameL c hs).1 hok.wf
  have hrc : σc.rev + 2 < 2 ^ 63 := by rw [hs.kvs_rev.2]; exact kvRoom_two hroom
  ihave ⟨Hr, #Hel⟩ := revOwnD_elem γ σc $$ Hr
  ihave ⟨Hs, #Hseen⟩ := histOwn_seen c σc $$ Hs
  ihave ⟨Hs, #Hone⟩ := histOwn_one c σc $$ Hs
  by_cases Hrev : σc.rev = uint.nat R
  · have hk4 : x.Kind' ≠ W64 4 := by rw [hk]; decide
    unfold getCallD
    iinv Hc with Hci Hclosec
    icases Hci with (⟨HU, >Hlc, >Hγc⟩ | ⟨%σ0, %R0, >#Hv, >#Hp0, >%Hrev0, >#HL, Hrest⟩)
    · -- the first firing at revision `R`: commit
      imod lc_fupd_elim_later $$ Hlc HU with HU
      have habs' : c.abs σc = (kStep eD eU x (c.abs σc)).1 := (kStep_get eD eU x hk _).symm
      obtain ⟨S', HS', Hok'⟩ := kOkD_ok hc hok eD eU x hx hval hk4 (by rw [hk]; decide) habs' hok.wf
        (Or.inl rfl) (k8s.keysIn_refl _ _) hrc
      have Hst : (pMF g0 decOp).step S (boxIn x, boxOut (kStep eD eU x (c.abs σc)).2) = some S' := by
        rw [stepF_box (GF := GF), kStep_plain, kStep_ansD hc hok hrc eD eU x hx hk4]; exact HS'
      imod (fupd_mask_subseteq HE) with Hclose3
      imod (linUD_commit γ g0 x _ Φ h S S' hrun Hst) $$ [Hh HU] with ⟨Hh, HΦ⟩
      · iframe
      imod Hclose3 with -
      imod dghostVar_update (some σc) γc none $$ Hγc with Hγc
      imod dghostVar_persist γc 1 _ $$ Hγc with #Hγc
      imod Hclosec $$ [HΦ] with -
      · inext
        iright
        iexists σc, R
        iframe Hγc Hpr Hel
        isplitr
        · ipureintro; exact Hrev
        ileft
        iframe HΦ
        iapply ansOk_read c σc hok.wf (mkeyL x.Key') _
          (by have := kStep_ansFrom eD eU x (c.abs σc); rwa [kStep_get eD eU x hk] at this)
        iframe Hseen Hone
      ihave HW : kInvDW γ c g0 σ₀ σc $$ [Hh HM Hr Hs]
      · iunfold kInvDW
        iexists _, S', M, nx
        iframe
        ipureintro; exact ⟨hel, runF_snoc g0 h S S' _ hrun Hst, Hok'⟩
      ihave ⟨Ha, HW⟩ := kInvDV_of_sameL γ c g0 γsh (1 : Qp) hs $$ [Ha HW]
      · iframe
      imodintro
      iframe Ha HW
      imodintro
      unfold readQD
      isplitr
      · ipureintro; exact ⟨hwσ, kvRoom_two hroom⟩
      iintro %_
      iexists σc
      iframe Hγc
      ipureintro; exact hs
    · -- a later firing at revision `R`: the same state, nothing to do
      ihave %HpR := dghostVar_agree γp _ _ _ _ $$ Hpr Hp0
      simp only [Option.some.injEq] at HpR
      subst HpR
      ihave %HLe := ghostMapElem_agree σc.rev γ.r _ _ _ _ $$ [HL] Hel
      · rw [Hrev, ← Hrev0]; iexact HL
      subst HLe
      imod Hclosec $$ [Hrest] with -
      · inext
        iright
        iexists σ0, R
        iframe Hv Hpr HL Hrest
        ipureintro; exact Hrev0
      ihave HW : kInvDW γ c g0 σ₀ σ0 $$ [Hh HM Hr Hs]
      · iunfold kInvDW
        iexists h, S, M, nx
        iframe
        ipureintro; exact ⟨hel, hrun, hok⟩
      ihave ⟨Ha, HW⟩ := kInvDV_of_sameL γ c g0 γsh (1 : Qp) hs $$ [Ha HW]
      · iframe
      imodintro
      iframe Ha HW
      imodintro
      unfold readQD
      isplitr
      · ipureintro; exact ⟨hwσ, kvRoom_two hroom⟩
      iintro %_
      iexists σ0
      iframe Hv
      ipureintro; exact hs
  · ihave HW : kInvDW γ c g0 σ₀ σc $$ [Hh HM Hr Hs]
    · iunfold kInvDW
      iexists h, S, M, nx
      iframe
      ipureintro; exact ⟨hel, hrun, hok⟩
    ihave ⟨Ha, HW⟩ := kInvDV_of_sameL γ c g0 γsh (1 : Qp) hs $$ [Ha HW]
    · iframe
    imodintro
    iframe Ha HW
    imodintro
    unfold readQD
    isplitr
    · ipureintro; exact ⟨hwσ, kvRoom_two hroom⟩
    iintro %H
    exact absurd (hs.kvs_rev.2.trans H) Hrev

/-- **A list's call invariant on the shared KV** (`listCall` over `linUD`). -/
def listCallD (γ : KNames) (g0 : HSt) (γc γt γp : GName) (x : Input) (tl : Bool)
    (Φ : val → IProp GF) : IProp GF :=
  inv callN iprop(
    (linUD γ g0 (boxIn x) Φ ∗ £ 1 ∗ dghostVar γc (DFrac.own 1) (none : Option KVState)) ∨
    (∃ (σ : KVState) (R : w64), dghostVar γc DFrac.discard (some σ) ∗
      dghostVar γp DFrac.discard (some R) ∗ ⌜listCommitOk x tl R σ⌝ ∗
      ghostMapElem γ.r σ.rev DFrac.discard σ ∗
      (contAt g0 x (lOut x σ) Φ ∨ dghostVar γt (DFrac.own 1) ())))

instance listCallD_persistent (γ : KNames) (g0 : HSt) (γc γt γp : GName) (x : Input) (tl : Bool)
    (Φ : val → IProp GF) : Persistent (listCallD (GF := GF) γ g0 γc γt γp x tl Φ) := by
  unfold listCallD; infer_instance

/-- **A list's first page's post on the shared KV** (`listQ`): at the store's caught-up state `σc`, equal to
the read's up to its leases, with the store's facts restricted to `/registry/` (`keysOkP`, `valsOkP`: the
shared KV's other keys are not the workload's; `listQ`'s `kvKeysShort` has no counterpart here). -/
def listQD (c : StoreCfg GF DObj) (γ : KNames) (γc : GName) (x : Input) (tl : Bool) (R : w64)
    (σ : KVState) : IProp GF :=
  iprop(∃ σc : KVState, ⌜SameL σc σ⌝ ∗
    ⌜kvWf c σc ∧ kvWfHist c σc ∧ keysOkP σc ∧ σc.rev + 2 < 2 ^ 63 ∧ valsOkP σc⌝ ∗
    ghostMapElem γ.r σc.rev DFrac.discard σc ∗
    (⌜listCommitOk x tl R σc⌝ →
      ∃ σ0 : KVState, dghostVar γc DFrac.discard (some σ0) ∗ ⌜lOut x σ0 = lOut x σc⌝))

instance listQD_persistent (c : StoreCfg GF DObj) (γ : KNames) (γc : GName) (x : Input) (tl : Bool)
    (R : w64) (σ : KVState) : Persistent (listQD (GF := GF) c γ γc x tl R σ) := by
  unfold listQD; infer_instance

/-- **A list's first page's read update for the prophesied revision `R`, on the shared KV**
(`list_read_au`, as `getD_read_au`). -/
theorem listD_read_au (γ : KNames) (c : StoreCfg GF DObj) (hc : CfgD c) (g0 : HSt) (γk : KVNames)
    (γs γsh : GName) (okS : mvcc.Change → Prop) (σ₀ : KVState) (l0 : List (List mvcc.Change))
    (γc γt γp : GName) (x : Input) (tl : Bool) (hx : InOk x) (hk4 : x.Kind' = W64 4)
    (R : w64) (Φ : val → IProp GF) :
    etcd_dist.kvPfxHP γk regP γs okS γsh σ₀ ∗ kInvD γ c g0 γs γsh σ₀ ∗ monoListLbOwn γsh l0 ∗
      listCallD γ g0 γc γt γp x tl Φ ∗ dghostVar γp DFrac.discard (some R) ⊢
      kvReadAu γk (listQD c γ γc x tl R) := by
  have Hcm := callN_cb
  have HE := drvED_cb_call
  unfold kInvD drvDInvN kInvDBody
  iintro ⟨#Hpfx, #Hinv, #Hl0, #Hc, #Hpr⟩
  iapply (kvPfxP_readAuHG γk regP γs okS γsh σ₀ "k8s" (by decide) (kInvDV γ c g0 γsh σ₀) l0)
  isplitl []
  · iexact Hpfx
  isplitl []
  · iexact Hinv
  isplitl []
  · iexact Hl0
  iintro !> %σ %Hpre Ha HW
  obtain ⟨-, he, -, hroom⟩ := Hpre
  have hrb : RevBoundD σ := by unfold RevBoundD; unfold kvRoom at hroom; omega
  imod (kInvDV_catchup γ c hc g0 γsh he hrb) $$ [Ha HW] with ⟨Ha, %σc, %hs, H⟩
  · iframe
  iunfold kInvDW at H
  icases H with ⟨%h, %S, %M, %nx, Hh, HM, Hr, Hs, %Hpure⟩
  obtain ⟨hel, hrun, hok⟩ := Hpure
  have hrc : σc.rev + 2 < 2 ^ 63 := by rw [hs.kvs_rev.2]; exact kvRoom_two hroom
  have hpure : kvWf c σc ∧ kvWfHist c σc ∧ keysOkP σc ∧ σc.rev + 2 < 2 ^ 63 ∧ valsOkP σc :=
    ⟨hok.wf, hok.hwf, hok.keys, hrc, hok.vals⟩
  ihave ⟨Hr, #Hel⟩ := revOwnD_elem γ σc $$ Hr
  by_cases Hrev : listCommitOk x tl R σc
  · unfold listCallD
    iinv Hc with Hci Hclosec
    icases Hci with (⟨HU, >Hlc, >Hγc⟩ | ⟨%σ0, %R0, >#Hv, >#Hp0, >%Hrev0, >#HL, Hrest⟩)
    · -- the first firing where it may: commit
      imod lc_fupd_elim_later $$ Hlc HU with HU
      obtain ⟨S', HS', Hok'⟩ := kOkD_list hok x hx hk4
      have Hst : (pMF g0 decOp).step S (boxIn x, boxOut (lOut x σc)) = some S' := by
        rw [stepF_box (GF := GF), lOut_plain, lOut_ans x σc hx hk4]; exact HS'
      imod (fupd_mask_subseteq HE) with Hclose3
      imod (linUD_commit γ g0 x _ Φ h S S' hrun Hst) $$ [Hh HU] with ⟨Hh, HΦ⟩
      · iframe
      imod Hclose3 with -
      imod dghostVar_update (some σc) γc none $$ Hγc with Hγc
      imod dghostVar_persist γc 1 _ $$ Hγc with #Hγc
      imod Hclosec $$ [HΦ] with -
      · inext
        iright
        iexists σc, R
        iframe Hγc Hpr Hel
        isplitr
        · ipureintro; exact Hrev
        ileft
        iframe HΦ
      ihave HW : kInvDW γ c g0 σ₀ σc $$ [Hh HM Hr Hs]
      · iunfold kInvDW
        iexists _, S', M, nx
        iframe
        ipureintro; exact ⟨hel, runF_snoc g0 h S S' _ hrun Hst, Hok'⟩
      ihave ⟨Ha, HW⟩ := kInvDV_of_sameL γ c g0 γsh (1 : Qp) hs $$ [Ha HW]
      · iframe
      imodintro
      iframe Ha HW
      imodintro
      unfold listQD
      iexists σc
      isplitr
      · ipureintro; exact hs
      isplitr
      · ipureintro; exact hpure
      iframe Hel
      iintro %_
      iexists σc
      iframe Hγc
      ipureintro; rfl
    · -- a later firing where it may: the committed state answers the same, nothing to do
      ihave %HpR := dghostVar_agree γp _ _ _ _ $$ Hpr Hp0
      simp only [Option.some.injEq] at HpR
      subst HpR
      ihave %Hsame : (⌜lOut x σ0 = lOut x σc⌝ : IProp GF) $$ []
      · unfold listCommitOk at Hrev Hrev0
        cases tl with
        | true =>
          simp only [↓reduceIte] at Hrev Hrev0
          ipureintro; rw [Hrev, Hrev0]
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte] at Hrev Hrev0
          ihave %HLe := ghostMapElem_agree σc.rev γ.r _ _ _ _ $$ [HL] Hel
          · rw [Hrev, ← Hrev0]; iexact HL
          ipureintro; rw [HLe]
      imod Hclosec $$ [Hrest] with -
      · inext
        iright
        iexists σ0, R
        iframe Hv Hp0 HL Hrest
        ipureintro; exact Hrev0
      ihave HW : kInvDW γ c g0 σ₀ σc $$ [Hh HM Hr Hs]
      · iunfold kInvDW
        iexists h, S, M, nx
        iframe
        ipureintro; exact ⟨hel, hrun, hok⟩
      ihave ⟨Ha, HW⟩ := kInvDV_of_sameL γ c g0 γsh (1 : Qp) hs $$ [Ha HW]
      · iframe
      imodintro
      iframe Ha HW
      imodintro
      unfold listQD
      iexists σc
      isplitr
      · ipureintro; exact hs
      isplitr
      · ipureintro; exact hpure
      iframe Hel
      iintro %_
      iexists σ0
      iframe Hv
      ipureintro; exact Hsame
  · ihave HW : kInvDW γ c g0 σ₀ σc $$ [Hh HM Hr Hs]
    · iunfold kInvDW
      iexists h, S, M, nx
      iframe
      ipureintro; exact ⟨hel, hrun, hok⟩
    ihave ⟨Ha, HW⟩ := kInvDV_of_sameL γ c g0 γsh (1 : Qp) hs $$ [Ha HW]
    · iframe
    imodintro
    iframe Ha HW
    imodintro
    unfold listQD
    iexists σc
    isplitr
    · ipureintro; exact hs
    isplitr
    · ipureintro; exact hpure
    iframe Hel
    iintro %H
    exact absurd H Hrev

end defs

end k8s_dist
end EtcdGrove
end Perennial
