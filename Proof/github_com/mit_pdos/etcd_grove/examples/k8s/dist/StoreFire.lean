/-
Lean-first (no Rocq counterpart).

# k8s-dist K8-9: the store's firings over the shared KV

`InvSteps.lean`'s firings (`create_au`, ...) on the shared cluster: the store's update of etcd is the share's
(`KVPfxHist.kvPfxP_au1H` at `f := kvOpStep op`, the store's `W` = `kInvDV`). Each firing first catches the
store's half up with the share's state (`kInvDV_catchup`: foreign revisions, or a foreign lease grant), then
takes the store's own step from the caught-up state (`invD_fire`: `invD_next` when etcd's state moves, nothing
otherwise), and commits lintest's update with the model's output there (`linUD_commit`).

- `drvED`, `kStateD`, `linUD`: lintest's linearization point (`Inv.lean`'s `linU`) over the model with foreign
  revisions (`pMF`, `kInvDW`'s ghost run), its mask without the client's invariants (`kvClientN`: the store's
  and the share's are open around the firing's step, `kvPfxCbE`).
- `createD_au`: a `Create` whose prophecy says the call answers (`create_au`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.dist.StoreInv

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

/-- **The namespaces lintest's linearization point avoids on the shared KV**: the in-process ones and the
client's (the store's invariant and the share's are open around a firing's step). -/
def drvED : CoPset := drvE ∪ ↑client.kvClientN

theorem drvED_cb : ⊤ \ drvED ⊆ etcd_dist.kvPfxCbE := by
  intro p hp
  simp only [drvED, drvE, etcd_dist.kvPfxCbE, Std.LawfulSet.mem_diff, Std.LawfulSet.mem_union] at hp ⊢
  exact ⟨⟨⟨hp.1, fun h => hp.2 (Or.inl (Or.inl (Or.inl (Or.inl h))))⟩,
    fun h => hp.2 (Or.inl (Or.inl (Or.inl (Or.inr h))))⟩, fun h => hp.2 (Or.inr h)⟩

/-- **lintest's abstract state over the model with foreign revisions** (`kState` over `pMF`). -/
def kStateD (γ : KNames) (g0 : HSt) (S : linkv.PSet HSt Input) : IProp GF :=
  iprop(∃ h : List OpV, ghostVar γ.h (1 : Qp).half h ∗ ⌜run (pMF g0 decOp) (fInit g0) h = some S⌝)

/-- **lintest's linearization point on the shared KV** (`linU` over `pMF`, mask `⊤ \ drvED`); the outputs'
check `ioOk` is the in-process model's. -/
def linUD (γ : KNames) (g0 : HSt) (i : GoInterface) (Φ : val → IProp GF) : IProp GF :=
  iprop(|={⊤ \ drvED, ∅}=> ∃ S, kStateD γ g0 S ∗ ∀ S' o,
    (kStateD γ g0 S' ∗ ⌜(pMF g0 decOp).step S (i, o) = some S'⌝) -∗
      |={∅, ⊤ \ drvED}=> (∀ o', ⌜∀ s, (pMF g0 decOp).step s (i, o') = (pMF g0 decOp).step s (i, o)⌝ -∗
        (k8setcd3S (GF := GF) g0).ioOk i o' -∗ Φ #o'))

theorem runF_snoc (g0 : HSt) (h : List OpV) (S S' : linkv.PSet HSt Input) (a : OpV)
    (h1 : run (pMF g0 decOp) (fInit g0) h = some S) (h2 : (pMF g0 decOp).step S a = some S') :
    run (pMF g0 decOp) (fInit g0) (h ++ [a]) = some S' := by
  suffices H : ∀ (s0 : linkv.PSet HSt Input) (l : List OpV),
      run (pMF g0 decOp) s0 (l ++ [a]) = (run (pMF g0 decOp) s0 l).bind ((pMF g0 decOp).step · a) by
    rw [H, h1]; exact h2
  intro s0 l
  induction l generalizing s0 with
  | nil =>
    simp only [List.nil_append, run, Option.bind_some]
    cases (pMF g0 decOp).step s0 a <;> rfl
  | cons b l ih =>
    simp only [List.cons_append, run]
    cases (pMF g0 decOp).step s0 b with
    | none => rfl
    | some s1 => exact ih s1

include hG sem package_sem in
/-- The model's step of a boxed input and output (`step_box` over `pMF`). -/
theorem stepF_box (g0 : HSt) (S : linkv.PSet HSt Input) (x : Input) (y : Output) :
    (pMF g0 decOp).step S (boxIn x, boxOut y) = (pSeqF g0).step S (x, ansOf (plainOut y)) :=
  pMF_step g0 decOp S _ x _ (decOp_box (sem := sem) (package_sem := package_sem) x y)

/-- **lintest's update on the shared KV, committed** at the output `y` (`linU_commit`). -/
theorem linUD_commit (γ : KNames) (g0 : HSt) (x : Input) (y : Output) (Φ : val → IProp GF)
    (h : List OpV) (S S' : linkv.PSet HSt Input)
    (hr : run (pMF g0 decOp) (fInit g0) h = some S)
    (hst : (pMF g0 decOp).step S (boxIn x, boxOut y) = some S') :
    ghostVar γ.h (1 : Qp).half h ∗ linUD γ g0 (boxIn x) Φ ⊢
      |={⊤ \ drvED}=> (ghostVar γ.h (1 : Qp).half (h ++ [(boxIn x, boxOut y)]) ∗
        contAt g0 x y Φ) := by
  iintro ⟨Hh, HU⟩
  iunfold linUD at HU
  imod HU with ⟨%S0, HS, HU⟩
  iunfold kStateD at HS
  icases HS with ⟨%h0, Hh0, %Hr0⟩
  ihave %Heq := ghostVar_agree γ.h h (1 : Qp).half h0 (1 : Qp).half $$ Hh Hh0
  subst Heq
  have HS0 : S0 = S := Option.some.inj (Hr0.symm.trans hr)
  subst HS0
  have Hr' := runF_snoc g0 h S0 S' _ hr hst
  imod ghostVar_update_halves (h ++ [(boxIn x, boxOut y)]) γ.h h h $$ Hh Hh0 with ⟨Hh, Hh0⟩
  imod HU $$ %S' %(boxOut y) [Hh0] with HΦ
  · isplitl [Hh0]
    · iunfold kStateD
      iexists _
      iframe Hh0
      ipureintro; exact Hr'
    · ipureintro; exact hst
  imodintro
  iframe Hh
  iintro %y' %hpl Hio
  ihave HΦ' := HΦ $$ %(boxOut y') %(fun s => by rw [stepF_box (GF := GF), stepF_box (GF := GF), hpl])
  iapply HΦ'
  iexact Hio

/-- The store's model's answer at the shared KV (`kStep_ans` over `KOkD`). -/
theorem kStep_ansD {c : StoreCfg GF DObj} (hc : CfgD c) {g0 : HSt} {S : linkv.PSet HSt Input}
    {σ : KVState} {M : GMap Nat Input} {nx : Nat} (H : KOkD c g0 S σ M nx) (hr : σ.rev + 2 < 2 ^ 63)
    (eD eU : GoInterface) (x : Input) (hx : InOk x) (_hk4 : x.Kind' ≠ W64 4) :
    ansOf (kStep eD eU x (c.abs σ)).2 = .ok (kStep eD eU x (c.abs σ)).2 := by
  obtain ⟨cf, -, hrel, -⟩ := H.cfg
  have hK := (krel_abs c hc σ cf.st.st (by omega)).2 hrel.2.1
  have hrv : (c.abs σ).rv + 1 < 2 ^ 64 := by rw [abs_rv]; omega
  by_cases hk3 : x.Kind' = W64 0 ∨ x.Kind' = W64 1 ∨ x.Kind' = W64 2
  · rw [(refine_step eD eU _ _ hK x hx hrv).2]
    exact ansOf_mstepL x cf.st.st hk3
  have h0 : ¬ x.Kind' = W64 0 := fun h => hk3 (Or.inl h)
  have h1 : ¬ x.Kind' = W64 1 := fun h => hk3 (Or.inr (Or.inl h))
  have h2 : ¬ x.Kind' = W64 2 := fun h => hk3 (Or.inr (Or.inr h))
  unfold ansOf
  rw [if_neg]
  simp only [kStep, h0, h1, h2, ↓reduceIte, KSt.get]
  repeat' split
  all_goals simp [outOf, objOutL, zeroOutL, tooLargeL, errOutL]

theorem kvWf_sameL (c : StoreCfg GF DObj) {σc σ : KVState} (hs : SameL σc σ) :
    kvWf c σc ↔ kvWf c σ := by
  obtain ⟨hk, hr⟩ := hs.kvs_rev
  unfold kvWf linkv.absSt; rw [hk, hr]

theorem keysIn_sameL {pfx : GoString} {σc σ σ' : KVState} (hs : SameL σc σ) (h : KeysIn pfx σ σ') :
    KeysIn pfx σc σ' := by
  intro v hv
  rcases h v hv with ⟨w, hw, hk⟩ | hp
  · exact Or.inl ⟨w, by rw [hs.kvs_rev.1]; exact hw, hk⟩
  · exact Or.inr hp

/-- **The store's step from the caught-up state** (both cases of `KvNext`): the share's `σ` steps to `σ'`;
the store's half, at `σc` (`σ` up to its leases), moves to `σd`, `σ'` up to its leases: `σc` itself when etcd's
state does not move, `σ'` otherwise (`invD_next`). -/
theorem invD_fire (γ : KNames) (c : StoreCfg GF DObj) {σc σ σ' : KVState} (hs : SameL σc σ)
    (hn : KvNext σ σ') (hw : kvWf c σc) (hw' : kvWf c σ') (hr : kvRoom σ)
    (hK : ∃ K, ∀ k, k ≠ K → (c.abs σ').items k = (c.abs σ).items k) :
    revOwnD (GF := GF) γ σc ∗ shistOwn c σc ⊢
      |==> ∃ σd, ⌜SameL σd σ' ∧ KvNext σc σd ∧ σd.rev + 2 < 2 ^ 63⌝ ∗
        revOwnD γ σd ∗ shistOwn c σd ∗ revSeen c.γh σc σd := by
  iintro ⟨Hrv, Hhist⟩
  by_cases hne : σ' = σ
  · subst hne
    imodintro
    iexists σc
    iframe Hrv Hhist
    isplit
    · ipureintro
      refine ⟨hs, Or.inl rfl, ?_⟩
      rw [hs.kvs_rev.2]; exact kvRoom_two hr
    · iunfold revSeen
      imodintro
      iintro %h
      omega
  · imod (invD_next γ c hs hn hne hw hw' hr hK) $$ [Hrv Hhist] with ⟨Hrv, Hhist, %Hr, #Hs⟩
    · iframe
    imodintro
    iexists σ'
    iframe Hrv Hhist Hs
    ipureintro
    exact ⟨SameL.refl σ', kvNext_sameL hs hn hne, Hr⟩

/-- **`kvPfxP_au1H` at `HeapGS`** (its ghost state's instances through `hG`, as `kInvD`'s: the same law,
`hG.goose_globalGS`'s instances unfolded). -/
theorem kvPfxP_au1HG (γk : KVNames) (p : GoString) (γ' : GName) (okp : mvcc.Change → Prop) (γh : GName)
    (σ₀ : KVState) (s : String) (hs : s ≠ "share")
    (W : etcd_dist.PfxV → IProp GF) [hW : ∀ v, Timeless (W v)] (l0 : List (List mvcc.Change))
    (f : KVState → KVState) (hf : etcd_dist.PfxLocal p f)
    (hok : ∀ σ new, (f σ).changes = σ.changes ++ new → ∀ cs ∈ new, ∀ c ∈ cs, okp c)
    (Q : KVState → IProp GF) :
    etcd_dist.kvPfxHP γk p γ' okp γh σ₀ ∗
      inv (client.kvClientN .@ s) iprop(∃ v, ghostVar γ' (1 : Qp).half v ∗ W v) ∗
      monoListLbOwn γh l0 ∗
      (∀ σ, ⌜l0 <+: σ.changes ∧ etcd_dist.KVExt σ₀ σ ∧ etcd_dist.PfxChOk p okp σ.changes ∧ kvRoom σ⌝ -∗
        monoListAuthOwn γh 1 σ.changes -∗ W (etcd_dist.pfxVH p σ) -∗ |={etcd_dist.kvPfxCbE}=>
          (monoListAuthOwn γh 1 (f σ).changes ∗ W (etcd_dist.pfxVH p (f σ)) ∗ Q σ)) ⊢
    AU <{ ∃∃ (σ : KVState), etcdKV γk σ }> @ (⊤ \ ↑srvRaftN) \ ↑kvN, ∅
      <{ etcdKV γk (f σ) ∗ ⌜kvRoom σ⌝, COMM Q σ }> :=
  etcd_dist.kvPfxP_au1H γk p γ' okp γh σ₀ s hs W l0 f hf hok Q

instance kInvDV_timeless (γ : KNames) (c : StoreCfg GF DObj) (g0 : HSt) (γsh : GName) (σ₀ : KVState)
    (v : etcd_dist.PfxV) : Timeless (kInvDV (GF := GF) γ c g0 γsh σ₀ v) := by
  unfold kInvDV kInvDW revOwnD shistOwn oneKeyRevs; infer_instance

/-- **A `Create` whose prophecy says the call answers, on the shared KV** (`create_au`): the store's update
of etcd is the share's (`kvPfxP_au1H`) at the transaction `op` whose step is the model's create; at its
firing the store catches up (`kInvDV_catchup`), takes its step (`invD_fire`, `kOkD_ok`) and commits
lintest's update with the model's output (`linUD_commit`). -/
theorem createD_au (γ : KNames) (c : StoreCfg GF DObj) (hc : CfgD c) (g0 : HSt) (γk : KVNames)
    (γs γsh : GName) (okS : mvcc.Change → Prop) (σ₀ : KVState) (l0 : List (List mvcc.Change))
    (eD eU : GoInterface) (x : Input) (hx : InOk x) (hval : x.Val'.length ≤ 2 ^ 20) (hk : x.Kind' = W64 0)
    (op : KVOp) (hop : op.isKV) (hloc : etcd_dist.PfxLocal regP (kvOpStep op))
    (hokS : ∀ σ new, (kvOpStep op σ).changes = σ.changes ++ new → ∀ cs ∈ new, ∀ ch ∈ cs, okS ch)
    (hstep : StepOk c op (fun s => (s.create (E := Empty) (mkeyL x.Key') (mkObj x) 0).1))
    (hkeys : ∀ σ, kvWf c σ → KeysIn c.pfx σ (kvOpStep op σ))
    (hone : ∀ σ, kvWf c σ → KvOne σ (kvOpStep op σ))
    (Φ : val → IProp GF) :
    etcd_dist.kvPfxHP γk regP γs okS γsh σ₀ ∗ kInvD γ c g0 γs γsh σ₀ ∗ monoListLbOwn γsh l0 ∗
      linUD γ g0 (boxIn x) Φ ⊢
    AU <{ ∃∃ (σ : KVState), etcdKV γk σ }> @ (⊤ \ ↑srvRaftN) \ ↑kvN, ∅
      <{ etcdKV γk (kvOpStep op σ) ∗ ⌜kvRoom σ⌝,
        COMM iprop(contAt g0 x (kStep eD eU x (c.abs σ)).2 Φ ∗ ansOk c (kStep eD eU x (c.abs σ)).2) }> := by
  unfold kInvD drvDInvN kInvDBody
  iintro ⟨#Hpfx, #Hinv, #Hl0, HU⟩
  iapply (kvPfxP_au1HG γk regP γs okS γsh σ₀ "k8s" (by decide) (kInvDV γ c g0 γsh σ₀) l0
    (kvOpStep op) hloc hokS)
  isplitl []
  · iexact Hpfx
  isplitl []
  · iexact Hinv
  isplitl []
  · iexact Hl0
  iintro %σ %Hpre Ha HW
  obtain ⟨-, he, -, hroom⟩ := Hpre
  have hrb : RevBoundD σ := by unfold RevBoundD; unfold kvRoom at hroom; omega
  imod (kInvDV_catchup γ c hc g0 γsh he hrb) $$ [Ha HW] with ⟨Ha, %σc, %hs, H⟩
  · iframe
  iunfold kInvDW at H
  icases H with ⟨%h, %S, %M, %nx, Hh, Hp, Hr, Hs, %Hpure⟩
  obtain ⟨_hel, hrun, hok⟩ := Hpure
  have hwσ : kvWf c σ := (kvWf_sameL c hs).1 hok.wf
  obtain ⟨hw', habs⟩ := hstep σ hwσ (kvRoom_two hroom)
  have hn : KvNext σ (kvOpStep op σ) := kvNext_step op σ hop (hone σ hwσ)
  have habs' : c.abs (kvOpStep op σ) = (kStep eD eU x (c.abs σ)).1 := by rw [habs]; simp [kStep, hk]
  have hac := abs_sameL c hs
  ihave ⟨Hs, #Hseen⟩ := histOwn_seen c σc $$ Hs
  ihave ⟨Hs, #Hone⟩ := histOwn_one c σc $$ Hs
  imod (invD_fire γ c hs hn hok.wf hw' hroom (kStep_oneKey c eD eU x σ _ habs')) $$ [Hr Hs]
    with ⟨%σd, %Hd, Hr, Hs, #Hrs⟩
  · iframe
  obtain ⟨hsd, hnd, hrd⟩ := Hd
  have hwd : kvWf c σd := (kvWf_sameL c hsd).2 hw'
  have hacd := abs_sameL c hsd
  have hrc : σc.rev + 2 < 2 ^ 63 := by rw [hs.kvs_rev.2]; exact kvRoom_two hroom
  obtain ⟨S', HS', Hok'⟩ := kOkD_ok hc hok eD eU x hx hval
    (by intro e; rw [e] at hk; simp at hk) (by intro e; rw [e] at hk; simp at hk)
    (by rw [hacd, hac]; exact habs') hwd hnd
    (keysIn_sameL hs (fun v hv => by rw [hsd.kvs_rev.1] at hv; exact hkeys σ hwσ v hv)) hrc
  ihave ⟨Hs, #Hseen'⟩ := histOwn_seen c σd $$ Hs
  ihave ⟨Hs, #Hone'⟩ := histOwn_one c σd $$ Hs
  ihave #Hans := ansOk_step c σc σd hok.wf hwd (mkeyL x.Key') (kStep eD eU x (c.abs σ)).2
    (by rw [hacd, hac, habs']; exact kStep_ansFrom eD eU x (c.abs σ)) $$ []
  · iframe Hseen Hone Hseen' Hone' Hrs
  have Hst : (pMF g0 decOp).step S (boxIn x, boxOut (kStep eD eU x (c.abs σ)).2) = some S' := by
    rw [stepF_box (GF := GF), kStep_plain, ← hac, kStep_ansD hc hok hrc eD eU x hx (by rw [hk]; decide), hac]
    rw [← hac]; exact HS'
  imod (fupd_mask_subseteq drvED_cb) with Hcl
  imod (linUD_commit γ g0 x _ Φ h S S' hrun Hst) $$ [Hh HU] with ⟨Hh, HΦ⟩
  · iframe
  imod Hcl with -
  have hpre : σ.changes <+: (kvOpStep op σ).changes := (kvNext_ext hn).2.2
  imod (monoListAuthOwn_update (GF := GF) (kvOpStep op σ).changes hpre) $$ Ha with ⟨Ha, #Hlb⟩
  imodintro
  iframe Ha HΦ Hans
  iunfold kInvDV
  iexists σd
  rw [← hsd.2.2]
  iframe Hlb
  isplit
  · ipureintro; exact pfxVH_sameL regP hsd
  iunfold kInvDW
  iexists _, S', M, nx
  iframe Hh Hp Hr Hs
  ipureintro
  refine ⟨⟨?_, ?_, ?_⟩, runF_snoc g0 h S S' _ hrun Hst, Hok'⟩
  · rw [hsd.1]; exact (kvNext_ext hn).1.symm.trans he.1
  · rw [hsd.2.1]; exact (kvNext_ext hn).2.1.symm.trans he.2.1
  · rw [hsd.2.2]; exact he.2.2.trans hpre

end defs

end k8s_dist
end EtcdGrove
end Perennial
