/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/dist/client/MainReady.lean`. Lean-first.
- `MainReady.wp_proofKv` (N7-kv, M1): the kv arm, at `RunKV.spec OP`.
- `MainReady.wp_proof` (F8): every arm. The kv arm is `MainReady.specKv` at `kvOrchPre`; each other arm calls its
  workload's `Run*` at the share's parts (`wlShare_*`), the level-`0` token split off the thread token
  (`threadTok_level0`; `RunCache` takes it whole), and the pure facts; `auth` is `MainReadyAuth.spec`'s arm (F7 S14), `authLease` calls
  `RunAuthLease` at `authLeaseShare` (F7 fork); an unknown kind returns `ended`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.MainReady
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.RunKV
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.MainReadyAuth
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.RunAuthLease
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.deployment.NodeCount
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.RunCompact
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.RunWatch
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.RunCache
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.RunPutGet
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.RunDurable
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.RunLeaseRead
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.RunLeaseCatchup
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.RunLeaseExpiry
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.deployment.WellFormedLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist

open Iris Iris.BI Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.etcd.dist

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : client.Assumptions]

theorem MainReady.wp_proofKv (OP : List GoString → w64 → IProp GF)
    (hNC : NodeCount.spec (GF := GF) (hG := hG))
    (hRun : RunKV.spec (GF := GF) (hG := hG) OP) :
    MainReady.specKv (GF := GF) (hG := hG) OP := by
  intro w eps nodes ns ready
  wp_start as ⟨%Hk, #Hnodes, #Hready, HOP⟩
  wp_auto
  wp_if_destruct
  · wp_func_call; wp_call; wp_auto
    iapply HΦ; ipureintro; trivial
  wp_apply hNC
  wp_if_destruct
  · -- `hasSetUp(KV)` is false: `ready()`
    wp_func_call; wp_call; wp_auto
    simp only [Workload.val, Hk]
    wp_auto
    iunfold readySpec at Hready
    wp_apply Hready
    -- the switch: kind 0, `RunKV`
    wp_apply (hRun nodes ns w.ops ready) $$ [HOP] as %r -
    · iunfold readySpec; iframe #; iframe
    iapply HΦ; ipureintro; trivial
  · wp_func_call; wp_call; wp_auto
    iapply HΦ; ipureintro; trivial

end proof

section proofFull
open Net client etcd_dist_client etcd_dist.view
open github_com.mit_pdos.etcd_grove.examples.lib.remote
open github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : client.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [esrv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]

set_option maxHeartbeats 1600000 in
theorem MainReady.wp_proof
    (hNC : NodeCount.spec (GF := GF) (hG := hG))
    (hKv : ∀ [π : NetProtoGS] [ρ : RemoteGS],
      MainReady.specKv (GF := GF) (hG := hG) (kvOrchPre (Gg := hG.goose_globalGS) (ρ := ρ)))
    (hRW : RunWatch.spec (GF := GF) (hG := hG))
    (hRC : RunCache.spec (GF := GF) (hG := hG))
    (hCo : RunCompact.spec (GF := GF) (hG := hG))
    (hPG : RunPutGet.spec (GF := GF) (hG := hG))
    (hDu : RunDurable.spec (GF := GF) (hG := hG))
    (hLR : RunLeaseRead.spec (GF := GF) (hG := hG))
    (hLC : RunLeaseCatchup.spec (GF := GF) (hG := hG))
    (hLE : RunLeaseExpiry.spec (GF := GF) (hG := hG))
    (hA : MainReadyAuth.spec (GF := GF) (hG := hG))
    (hAL : RunAuthLease.spec (GF := GF) (hG := hG)) :
    MainReady.spec (GF := GF) (hG := hG) := by
  intro π ρ errA fmtA rpcA w eps nodes epsL ns ready
  by_cases hk0 : w.kind = W64 0
  · -- kv: M1's arm
    rw [wlShare_kv hk0]
    wp_start_folded as ⟨%Hp, Htok, #Heps, #Hnodes, #Hready, Hsh⟩
    wp_apply (hKv w eps nodes ns ready) $$ [Hsh] as %r -
    · iframe #
      iframe
      ipureintro; exact hk0
    iapply HΦ; ipureintro; trivial
  have hkk : kindKnown w.kind ∨ ¬ kindKnown w.kind := Classical.em _
  rcases hkk with hkn | hkn
  rotate_left
  · -- an unknown kind: `ended("unknown workload")`
    rw [wlShare_other hkn]
    have hd0 : decide (w.kind = W64 0) = false :=
      decide_eq_false (fun he => hkn (by rw [he]; decide))
    have hd1 : decide (w.kind = W64 1) = false :=
      decide_eq_false (fun he => hkn (by rw [he]; decide))
    have hd2 : decide (w.kind = W64 2) = false :=
      decide_eq_false (fun he => hkn (by rw [he]; decide))
    have hd3 : decide (w.kind = W64 3) = false :=
      decide_eq_false (fun he => hkn (by rw [he]; decide))
    have hd4 : decide (w.kind = W64 4) = false :=
      decide_eq_false (fun he => hkn (by rw [he]; decide))
    have hd5 : decide (w.kind = W64 5) = false :=
      decide_eq_false (fun he => hkn (by rw [he]; decide))
    have hd6 : decide (w.kind = W64 6) = false :=
      decide_eq_false (fun he => hkn (by rw [he]; decide))
    have hd7 : decide (w.kind = W64 7) = false :=
      decide_eq_false (fun he => hkn (by rw [he]; decide))
    have hd8 : decide (w.kind = W64 8) = false :=
      decide_eq_false (fun he => hkn (by rw [he]; decide))
    have hd9 : decide (w.kind = W64 9) = false :=
      decide_eq_false (fun he => hkn (by rw [he]; decide))
    have hd10 : decide (w.kind = W64 10) = false :=
      decide_eq_false (fun he => hkn (by rw [he]; decide))
    wp_start as ⟨%Hp, Htok, #Heps, #Hnodes, #Hready, Hsh⟩
    wp_auto
    wp_if_destruct
    · wp_func_call; wp_call; wp_auto
      iapply HΦ; ipureintro; trivial
    wp_apply hNC
    wp_if_destruct
    · wp_func_call; wp_call; wp_auto
      iterate 6 ((try simp only [hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd9, hd10]); (try wp_auto))
      iunfold readySpec at Hready
      wp_apply Hready
      iterate 12 ((try simp only [hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hd8, hd9, hd10]); (try wp_auto))
      wp_func_call; wp_call; wp_auto
      iapply HΦ; ipureintro; trivial
    · wp_func_call; wp_call; wp_auto
      iapply HΦ; ipureintro; trivial
  rcases kindKnown_cases w.kind hkn with hk | hk | hk | hk | hk | hk | hk | hk | hk | hk | hk
  · exact absurd hk hk0
  · -- watch
    rw [wlShare_watch hk]
    wp_start as ⟨%Hp, Htok, #Heps, #Hnodes, #Hready, Hsh⟩
    obtain ⟨hpure, hpl, hV, htb, hrb, hAs⟩ := Hp
    ihave %Hel := ownSlice_len _ _ _ $$ Heps
    ihave %Hnl := ownSlice_len _ _ _ $$ Hnodes
    wp_auto
    wp_if_destruct
    · wp_func_call; wp_call; wp_auto
      iapply HΦ; ipureintro; trivial
    wp_apply hNC
    wp_if_destruct
    · have hlen : (ns.length : Int) = sint.Z w.goNodeCount := by word
      wp_func_call; wp_call; wp_auto
      simp only [Workload.val, hk]
      wp_auto
      have hgn : w.goNodeCount = w.clients := by simp [Workload.goNodeCount, hk]
      obtain ⟨hops, hmul⟩ := hpure.2.2.1 (Or.inl hk)
      have hmul' : (ns.length : Int) * sint.Z w.ops < 2 ^ 63 := by
        rw [hlen, hgn]; exact Int.lt_of_lt_of_le hmul (by decide)
      icases (threadTok_level0 (GF := GF)).1 $$ Htok with ⟨Hlt, -⟩
      iunfold readySpec at Hready
      wp_apply (hRW eps nodes epsL ns w.ops ready hV htb hpl hops hmul' hrb) $$ [Hlt Hsh] as %r -
      · iframe #; iframe
      iapply HΦ; ipureintro; trivial
    · wp_func_call; wp_call; wp_auto
      iapply HΦ; ipureintro; trivial
  · -- cache
    rw [wlShare_cache hk]
    wp_start as ⟨%Hp, Htok, #Heps, #Hnodes, #Hready, Hsh⟩
    obtain ⟨hpure, hpl, hV, htb, hrb, hAs⟩ := Hp
    ihave %Hel := ownSlice_len _ _ _ $$ Heps
    ihave %Hnl := ownSlice_len _ _ _ $$ Hnodes
    wp_auto
    wp_if_destruct
    · wp_func_call; wp_call; wp_auto
      iapply HΦ; ipureintro; trivial
    wp_apply hNC
    wp_if_destruct
    · have hlen : (ns.length : Int) = sint.Z w.goNodeCount := by word
      wp_func_call; wp_call; wp_auto
      simp only [Workload.val, hk]
      wp_auto
      have hgn : w.goNodeCount = w.clients := by simp [Workload.goNodeCount, hk]
      obtain ⟨hops, hmul⟩ := hpure.2.2.1 (Or.inr hk)
      have hmul' : (ns.length : Int) * sint.Z w.ops < 2 ^ 63 := by
        rw [hlen, hgn]; exact Int.lt_of_lt_of_le hmul (by decide)
      iunfold readySpec at Hready
      wp_apply (hRC eps nodes epsL ns w.ops ready hV htb hpl hops hmul' hrb hAs) $$ [Htok Hsh] as %r -
      · iframe #; iframe
      iapply HΦ; ipureintro; trivial
    · wp_func_call; wp_call; wp_auto
      iapply HΦ; ipureintro; trivial
  · -- compact
    rw [wlShare_compact hk]
    wp_start as ⟨%Hp, Htok, #Heps, #Hnodes, #Hready, Hsh⟩
    obtain ⟨hpure, hpl, hV, htb, hrb, hAs⟩ := Hp
    wp_auto
    wp_if_destruct
    · wp_func_call; wp_call; wp_auto
      iapply HΦ; ipureintro; trivial
    wp_apply hNC
    wp_if_destruct
    · wp_func_call; wp_call; wp_auto
      simp only [Workload.val, hk]
      wp_auto
      iunfold readySpec at Hready
      wp_apply Hready
      icases (threadTok_level0 (GF := GF)).1 $$ Htok with ⟨Hlt, -⟩
      wp_apply (hCo eps epsL hV htb hpl hAs) $$ [Hlt Hsh] as %r -
      · iframe #; iframe
      iapply HΦ; ipureintro; trivial
    · wp_func_call; wp_call; wp_auto
      iapply HΦ; ipureintro; trivial
  · -- putget
    rw [wlShare_putget hk]
    wp_start as ⟨%Hp, Htok, #Heps, #Hnodes, #Hready, Hsh⟩
    obtain ⟨hpure, hpl, hV, htb, hrb, hAs⟩ := Hp
    ihave %Hel := ownSlice_len _ _ _ $$ Heps
    ihave %Hnl := ownSlice_len _ _ _ $$ Hnodes
    wp_auto
    wp_if_destruct
    · wp_func_call; wp_call; wp_auto
      iapply HΦ; ipureintro; trivial
    wp_apply hNC
    wp_if_destruct
    · have hlen : (ns.length : Int) = sint.Z w.goNodeCount := by word
      wp_func_call; wp_call; wp_auto
      simp only [Workload.val, hk]
      wp_auto
      iunfold readySpec at Hready
      wp_apply Hready
      icases (threadTok_level0 (GF := GF)).1 $$ Htok with ⟨Hlt, -⟩
      wp_apply (hPG eps epsL hV htb hpl hAs) $$ [Hlt Hsh] as %r -
      · iframe #; iframe
      iapply HΦ; ipureintro; trivial
    · wp_func_call; wp_call; wp_auto
      iapply HΦ; ipureintro; trivial
  · -- auth: `MainReadyAuth`'s arm (F7 S14), at `authShare`
    rw [wlShare_auth hk]
    wp_start_folded as ⟨%Hp, Htok, #Heps, #Hnodes, #Hready, Hsh⟩
    obtain ⟨-, -, hm⟩ := Hp
    wp_apply (hA w eps nodes epsL ns ready) $$ [Htok Hsh] as %r -
    · iframe #
      iframe
      ipureintro; exact ⟨hk, hm⟩
    iapply HΦ; ipureintro; trivial
  · -- authLease: `RunAuthLease` at `authLeaseShare` (F7 fork): the guards as `MainReadyAuth`'s
    rw [wlShare_authLease hk]
    wp_start as ⟨%Hp, Htok, #Heps, #Hnodes, #Hready, Hsh⟩
    obtain ⟨hpure, hpl, hV, htb, hrb, hAs⟩ := Hp
    ihave %Hel := ownSlice_len _ _ _ $$ Heps
    wp_auto
    wp_if_destruct
    · wp_func_call; wp_call; wp_auto
      iapply HΦ; ipureintro; trivial
    have hne : epsL ≠ [] := by
      intro h; rw [h] at Hel; simp at Hel; word
    wp_apply hNC
    wp_if_destruct
    · wp_func_call; wp_call; wp_auto
      simp only [Workload.val, hk]
      wp_auto
      iunfold authLeaseShare at Hsh
      icases Hsh with ⟨%Γ, %γR, %σ0, %Hq, #Hms, #HkvI, #HL0, HkV, Hview⟩
      obtain ⟨hauth, hlm, hγR, hau, hls, hσ0⟩ := Hq
      icases (threadTok_level0 (GF := GF)).1 $$ Htok with ⟨Hlt, -⟩
      wp_apply (hAL Γ eps epsL ready γR σ0 hV htb hAs hne hauth hlm hγR hau hls hσ0)
        $$ [Hlt HkV Hview] as %r -
      · iframe #; iframe
      iapply HΦ; ipureintro; trivial
    · wp_func_call; wp_call; wp_auto
      iapply HΦ; ipureintro; trivial
  · -- leaseRead
    rw [wlShare_leaseRead hk]
    unfold leaseShare
    wp_start as ⟨%Hp, Htok, #Heps, #Hnodes, #Hready, Hsh⟩
    obtain ⟨hpure, hpl, hV, htb, hrb, hAs⟩ := Hp
    ihave %Hel := ownSlice_len _ _ _ $$ Heps
    ihave %Hnl := ownSlice_len _ _ _ $$ Hnodes
    wp_auto
    wp_if_destruct
    · wp_func_call; wp_call; wp_auto
      iapply HΦ; ipureintro; trivial
    wp_apply hNC
    wp_if_destruct
    · have hlen : (ns.length : Int) = sint.Z w.goNodeCount := by word
      wp_func_call; wp_call; wp_auto
      simp only [Workload.val, hk]
      wp_auto
      iunfold readySpec at Hready
      wp_apply Hready
      icases (threadTok_level0 (GF := GF)).1 $$ Htok with ⟨Hlt, -⟩
      icases Hsh with ⟨%Γ, -, Hlm⟩
      wp_apply (hLR Γ eps epsL hV htb hAs) $$ [Hlt Hlm] as %r -
      · iframe #; iframe
      iapply HΦ; ipureintro; trivial
    · wp_func_call; wp_call; wp_auto
      iapply HΦ; ipureintro; trivial
  · -- leaseCatchup
    rw [wlShare_leaseCatchup hk]
    unfold leaseShare
    wp_start as ⟨%Hp, Htok, #Heps, #Hnodes, #Hready, Hsh⟩
    obtain ⟨hpure, hpl, hV, htb, hrb, hAs⟩ := Hp
    ihave %Hel := ownSlice_len _ _ _ $$ Heps
    ihave %Hnl := ownSlice_len _ _ _ $$ Hnodes
    wp_auto
    wp_if_destruct
    · wp_func_call; wp_call; wp_auto
      iapply HΦ; ipureintro; trivial
    wp_apply hNC
    wp_if_destruct
    · have hlen : (ns.length : Int) = sint.Z w.goNodeCount := by word
      wp_func_call; wp_call; wp_auto
      simp only [Workload.val, hk]
      wp_auto
      icases (threadTok_level0 (GF := GF)).1 $$ Htok with ⟨Hlt, -⟩
      icases Hsh with ⟨%Γ, %HΓ, Hlm⟩
      wp_apply (hLC Γ eps epsL ready hV htb hAs HΓ.1 HΓ.2 hpl.1) $$ [Hlt Hlm] as %r -
      · iframe #; iframe
        iintro %Ψ HΨ
        iunfold readySpec at Hready
        wp_apply Hready
        iexact HΨ
      iapply HΦ; ipureintro; trivial
    · wp_func_call; wp_call; wp_auto
      iapply HΦ; ipureintro; trivial
  · -- leaseExpiry
    rw [wlShare_leaseExpiry hk]
    unfold leaseShare
    wp_start as ⟨%Hp, Htok, #Heps, #Hnodes, #Hready, Hsh⟩
    obtain ⟨hpure, hpl, hV, htb, hrb, hAs⟩ := Hp
    ihave %Hel := ownSlice_len _ _ _ $$ Heps
    ihave %Hnl := ownSlice_len _ _ _ $$ Hnodes
    wp_auto
    wp_if_destruct
    · wp_func_call; wp_call; wp_auto
      iapply HΦ; ipureintro; trivial
    wp_apply hNC
    wp_if_destruct
    · have hlen : (ns.length : Int) = sint.Z w.goNodeCount := by word
      wp_func_call; wp_call; wp_auto
      simp only [Workload.val, hk]
      wp_auto
      iunfold readySpec at Hready
      wp_apply Hready
      icases (threadTok_level0 (GF := GF)).1 $$ Htok with ⟨Hlt, -⟩
      icases Hsh with ⟨%Γ, %HΓ, Hlm⟩
      wp_apply (hLE Γ eps epsL hV htb hAs HΓ.1 HΓ.2) $$ [Hlt Hlm] as %r -
      · iframe #; iframe
      iapply HΦ; ipureintro; trivial
    · wp_func_call; wp_call; wp_auto
      iapply HΦ; ipureintro; trivial
  · -- durable
    rw [wlShare_durable hk]
    wp_start as ⟨%Hp, Htok, #Heps, #Hnodes, #Hready, Hsh⟩
    obtain ⟨hpure, hpl, hV, htb, hrb, hAs⟩ := Hp
    ihave %Hel := ownSlice_len _ _ _ $$ Heps
    ihave %Hnl := ownSlice_len _ _ _ $$ Hnodes
    wp_auto
    wp_if_destruct
    · wp_func_call; wp_call; wp_auto
      iapply HΦ; ipureintro; trivial
    wp_apply hNC
    wp_if_destruct
    · have hlen : (ns.length : Int) = sint.Z w.goNodeCount := by word
      wp_func_call; wp_call; wp_auto
      simp only [Workload.val, hk]
      wp_auto
      iunfold readySpec at Hready
      wp_apply Hready
      icases (threadTok_level0 (GF := GF)).1 $$ Htok with ⟨Hlt, -⟩
      have hcl : 0 ≤ sint.Z w.clients := hpure.2.2.2 hk
      wp_apply (hDu eps epsL w.clients hcl hV htb hpl hAs) $$ [Hlt Hsh] as %r -
      · iframe #; iframe
      iapply HΦ; ipureintro; trivial
    · wp_func_call; wp_call; wp_auto
      iapply HΦ; ipureintro; trivial

end proofFull

end etcd_dist
end EtcdGrove
end Perennial
