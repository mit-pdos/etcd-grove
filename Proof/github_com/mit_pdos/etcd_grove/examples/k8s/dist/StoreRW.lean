/-
Lean-first (no Rocq counterpart).
# k8s-dist K8-11: the store's firings for a write that may decline, on the shared KV
`InvSteps.lean`'s `rw_au` (a `Delete` or `GuaranteedUpdate`: `k8sAuRW`, then `k8sAuRW_kvAu1` at the
transaction `op`) on the shared cluster, fused: on the shared KV the store's facts (`kvWf`, `kvSeen`, so the
caller's `A`) exist only after the store's catch-up, inside the share's step (`kvPfxP_au1H`), so the decision
`b := ok σ || hand σ` at the real state `σ` is taken there, from `k8sAuRW_kvAu1`'s condition `h` applied at `σ`.
- `kvSeen_sameL`: the condition's hypotheses (`kvWf`, the revision, `kvSeen` hence `A`) read a state only up
  to its leases. Its conclusion does not (`kvOpStep` of a put or transaction naming a lease reads the lease
  table), which is why `h` is applied at the real `σ`, never at the caught-up `σc`.
- `rwCallD` (`rwCall` over `linUD`), `rwD_au` (`rw_au` then `k8sAuRW_kvAu1`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.dist.StoreRead

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

/-- **The history's view of a state reads its key-values only** (K8-11, the lease-invariance lemma of
`rwD_au`): two states equal up to their leases are seen alike. With `kvWf_sameL` and `SameL.kvs_rev`, every
hypothesis of `k8sAuRW_kvAu1`'s condition (`kvWf c σ`, `σ.rev + 2 < 2^63`, `A σ` from `kvSeen c.γh σ`) holds
at the real state when it holds at the caught-up one. -/
theorem kvSeen_sameL (γh : GName) {σc σ : KVState} (hs : SameL σc σ) :
    kvSeen (GF := GF) γh σc = kvSeen γh σ := by
  unfold kvSeen; rw [hs.kvs_rev.1]

/-- **A write's call invariant on the shared KV** (`rwCall` over `linUD`). -/
def rwCallD (γ : KNames) (g0 : HSt) (γt : GName) (x : Input) (Φ : val → IProp GF) : IProp GF :=
  inv callN iprop((linUD γ g0 (boxIn x) Φ ∗ £ 1) ∨ dghostVar γt (DFrac.own 1) ())

instance rwCallD_persistent (γ : KNames) (g0 : HSt) (γt : GName) (x : Input)
    (Φ : val → IProp GF) : Persistent (rwCallD (GF := GF) γ g0 γt x Φ) := by
  unfold rwCallD; infer_instance

/-- **A `Delete` or `GuaranteedUpdate` whose prophecy says it answers, on the shared KV** (`rw_au`, then
`k8sAuRW_kvAu1` at the transaction `op`): given the token `γt`, the client's one-shot update of etcd at `op`
is the share's (`kvPfxP_au1H`). At its firing the store catches up (`kInvDV_catchup`, to `σc`), learns
`kvSeen` at the real state `σ` (`kvSeen_sameL`), hence `A σ`, and applies the condition `h` at `σ`: when `ok
σ || hand σ` it takes its step (`invD_fire`, `kOkD_ok`), commits lintest's update with the model's output
(`linUD_commit`) and keeps the token in the call's invariant; otherwise etcd's state does not move and the
token comes back. -/
theorem rwD_au (γ : KNames) (c : StoreCfg GF DObj) (hc : CfgD c) (g0 : HSt) (γk : KVNames)
    (γs γsh : GName) (okS : mvcc.Change → Prop) (σ₀ : KVState) (l0 : List (List mvcc.Change))
    (eD eU : GoInterface) (x : Input) (hx : InOk x) (hval : x.Val'.length ≤ 2 ^ 20)
    (hk : x.Kind' = W64 1 ∨ x.Kind' = W64 2) (γt : GName) (Φ : val → IProp GF)
    (op : KVOp) (hop : op.isKV) (hloc : etcd_dist.PfxLocal regP (kvOpStep op))
    (hokS : ∀ σ new, (kvOpStep op σ).changes = σ.changes ++ new → ∀ cs ∈ new, ∀ ch ∈ cs, okS ch)
    (ok hand : KVState → Bool) (A : KVState → Prop)
    (h : ∀ σ, kvWf c σ → σ.rev + 2 < 2 ^ 63 → A σ →
      (ok σ = true → kvWf c (kvOpStep op σ) ∧
        c.abs (kvOpStep op σ) = (kStep eD eU x (c.abs σ)).1) ∧
      (ok σ = false → kvOpStep op σ = σ ∧ (hand σ = true → (kStep eD eU x (c.abs σ)).1 = c.abs σ)))
    (hkeys : ∀ σ, kvWf c σ → KeysIn c.pfx σ (kvOpStep op σ))
    (hone : ∀ σ, kvWf c σ → KvOne σ (kvOpStep op σ)) :
    etcd_dist.kvPfxHP γk regP γs okS γsh σ₀ ∗ kInvD γ c g0 γs γsh σ₀ ∗ monoListLbOwn γsh l0 ∗
      rwCallD γ g0 γt x Φ ∗ □ (∀ σ, kvSeen c.γh σ -∗ ⌜A σ⌝) ⊢
    □ (dghostVar γt (DFrac.own 1) () -∗
      kvOpAu1 γk op (fun σ => iprop(
        (if ok σ || hand σ then
          contAt g0 x (kStep eD eU x (c.abs σ)).2 Φ ∗ ansOk c (kStep eD eU x (c.abs σ)).2
        else dghostVar γt (DFrac.own 1) ()) ∗ rdFacts c σ ∗ ⌜A σ⌝))) := by
  have Hcm := callN_cb
  have HE := drvED_cb_call
  unfold kInvD drvDInvN kInvDBody kvOpAu1 kvAu1
  iintro ⟨#Hpfx, #Hinv, #Hl0, #Hc, #HA⟩
  iintro !> Htok
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
  icases H with ⟨%hh, %S, %M, %nx, Hh, Hp, Hr, Hs, %Hpure⟩
  obtain ⟨hel, hrun, hok⟩ := Hpure
  have hwσ : kvWf c σ := (kvWf_sameL c hs).1 hok.wf
  have hr : σ.rev + 2 < 2 ^ 63 := kvRoom_two hroom
  ihave ⟨Hs, #Hseen⟩ := histOwn_seen c σc $$ Hs
  ihave #Hseenσ := (show kvSeen (GF := GF) c.γh σc ⊢ kvSeen c.γh σ by
    rw [kvSeen_sameL c.γh hs]) $$ Hseen
  ihave %HAσ := HA $$ %σ Hseenσ
  have hst := h σ hwσ hr HAσ
  by_cases hb : (ok σ || hand σ) = true
  · -- the linearization point
    have hlin : kvWf c (kvOpStep op σ) ∧
        c.abs (kvOpStep op σ) = (kStep eD eU x (c.abs σ)).1 := by
      cases hokσ : ok σ
      · obtain ⟨hid, hhd⟩ := hst.2 hokσ
        have hh' : hand σ = true := by simpa [hokσ] using hb
        rw [hid]; exact ⟨hwσ, (hhd hh').symm⟩
      · exact hst.1 hokσ
    obtain ⟨hw', habs'⟩ := hlin
    have hn : KvNext σ (kvOpStep op σ) := kvNext_step op σ hop (hone σ hwσ)
    have hac := abs_sameL c hs
    ihave ⟨Hs, #Hone⟩ := histOwn_one c σc $$ Hs
    imod (invD_fire γ c hs hn hok.wf hw' hroom (kStep_oneKey c eD eU x σ _ habs')) $$ [Hr Hs]
      with ⟨%σd, %Hd, Hr, Hs, #Hrs⟩
    · iframe
    obtain ⟨hsd, hnd, hrd⟩ := Hd
    have hwd : kvWf c σd := (kvWf_sameL c hsd).2 hw'
    have hacd := abs_sameL c hsd
    have hrc : σc.rev + 2 < 2 ^ 63 := by rw [hs.kvs_rev.2]; exact hr
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
      rw [stepF_box (GF := GF), kStep_plain, ← hac,
        kStep_ansD hc hok hrc eD eU x hx (by intro e; rw [e] at hk; simp at hk), hac]
      rw [← hac]; exact HS'
    unfold rwCallD
    iinv Hc with Hci Hclosec
    icases Hci with (⟨HU, >Hlc⟩ | >Htok')
    · imod lc_fupd_elim_later $$ Hlc HU with HU
      imod (fupd_mask_subseteq HE) with Hcl
      imod (linUD_commit γ g0 x _ Φ hh S S' hrun Hst) $$ [Hh HU] with ⟨Hh, HΦ⟩
      · iframe
      imod Hcl with -
      imod Hclosec $$ [Htok] with -
      · inext
        iright
        iexact Htok
      have hpre : σ.changes <+: (kvOpStep op σ).changes := (kvNext_ext hn).2.2
      imod (monoListAuthOwn_update (GF := GF) (kvOpStep op σ).changes hpre) $$ Ha with ⟨Ha, #Hlb⟩
      imodintro
      iframe Ha
      isplitr [HΦ]
      · iunfold kInvDV
        iexists σd
        rw [← hsd.2.2]
        iframe Hlb
        isplit
        · ipureintro; exact pfxVH_sameL regP hsd
        iunfold kInvDW
        iexists _, S', M, nx
        iframe Hh Hp Hr Hs
        ipureintro
        refine ⟨⟨?_, ?_, ?_⟩, runF_snoc g0 hh S S' _ hrun Hst, Hok'⟩
        · rw [hsd.1]; exact (kvNext_ext hn).1.symm.trans he.1
        · rw [hsd.2.1]; exact (kvNext_ext hn).2.1.symm.trans he.2.1
        · rw [hsd.2.2]; exact he.2.2.trans hpre
      simp only [hb, ↓reduceIte]
      iframe HΦ Hans
      unfold rdFacts
      iframe Hseenσ
      ipureintro; exact ⟨⟨hwσ, hr⟩, HAσ⟩
    · iexfalso
      iapply tok_excl γt
      iframe Htok Htok'
  · -- a plain read: etcd's state does not move, the token comes back
    have hb' : (ok σ || hand σ) = false := by simpa using hb
    have hokσ : ok σ = false := by simp only [Bool.or_eq_false_iff] at hb'; exact hb'.1
    have hid : kvOpStep op σ = σ := (hst.2 hokσ).1
    ihave HW : kInvDW γ c g0 σ₀ σc $$ [Hh Hp Hr Hs]
    · iunfold kInvDW
      iexists hh, S, M, nx
      iframe
      ipureintro; exact ⟨hel, hrun, hok⟩
    ihave ⟨Ha, HW⟩ := kInvDV_of_sameL γ c g0 γsh (1 : Qp) hs $$ [Ha HW]
    · iframe
    rw [hid]
    imodintro
    iframe Ha HW
    simp only [hb', Bool.false_eq_true, ↓reduceIte]
    iframe Htok
    unfold rdFacts
    iframe Hseenσ
    ipureintro; exact ⟨⟨hwσ, hr⟩, HAσ⟩

end defs

end k8s_dist
end EtcdGrove
end Perennial
