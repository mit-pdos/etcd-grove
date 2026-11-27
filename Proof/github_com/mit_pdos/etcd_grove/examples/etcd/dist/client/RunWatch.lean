/-
Proof of `Spec/.../dist/client/RunWatch.lean` (#50 N10a). Lean-first (no Rocq counterpart).

`partition/MainWatch.lean`'s argument at the cluster's KV (`WatchWorkDefs.lean`): `GenAll` picks the
writers' Puts `trs` (`GenAll_receipts.spec`: fewer than `receiptBound GF ≤ 2 ^ 56`, `remoteWriters`' bound); the clients' adapter over the share's client half (`client.kmInv_alloc`, the plan's
property `wkW (trs.map pairOf)`, true of the boot's changes `[[]]`); `newClient` (its failure ends the
workload, `ended`); the client's `Watcher` a watcher of the cluster's KV (`watchClient_of_new`,
`kvWatcherW_of_dist` over the interim `Watch_dist`, a hypothesis), so etcd's watch contract at the
adapter's model (`isEtcdWatcher_of_kmW`); `WithCancel(Background())` and its `defer cancel()`; the
prefix watch from revision `1` (the read at `0`, `km_reached_of`); `ready()`; the writers at their
machines (`remoteWriters.spec`, a hypothesis: at the writers' share, each successful Put's `okFactK` at the
adapter, whose names go to the writers with their Puts, `kmOf`); the timer
(`AfterFunc`, `cancel` never panics; `Stop`); `MaxRev`; `Collect` (each response by `resp_km`); the
cancel; and the check: `CheckOk` from `collectOk` and the Puts' `okFactK`s (`checkOkK_of`). `Collect`'s
`false` ends the workload (`ended`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.RunWatch
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.remoteWriters
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.newClient
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.checked
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.ended
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.GenAllR
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.MaxRev
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Collect
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Check
public import Spec.go_etcd_io.etcd.client.v3.WithPrefix
public import Spec.go_etcd_io.etcd.client.v3.WithRev
public import Spec.go_etcd_io.etcd.client.v3.WithProgressNotify
public import Spec.go_etcd_io.etcd.client.v3.WithCreatedNotify
public import Perennial.Spec.time.AfterFunc
public import Perennial.Spec.time.Timer__Stop
public import Perennial.Proof.context.Link
public import Perennial.Proof.context.Results
public import Proof.github_com.mit_pdos.etcd_grove.PkgInitMemo

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist_client

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net client go_etcd_io.etcd.server.v3.etcdserver
  go_etcd_io.etcd.cache.v3
open etcd_dist etcdstart

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8192 in
theorem RunWatch.wp_proof
    (wp_GenAll : GenAll_receipts.spec (GF := GF) (hG := hG))
    (wp_newClient : newClient.spec (GF := GF) (hG := hG))
    (wp_ended : ended.spec (GF := GF) (hG := hG))
    (wp_checked : checked.spec (GF := GF) (hG := hG))
    (wp_Watch : Watch_dist.spec (GF := GF) (hG := hG))
    (wp_WithPrefix : WithPrefix.spec (GF := GF) (hG := hG))
    (wp_WithRev : WithRev.spec (GF := GF) (hG := hG))
    (wp_WithProgressNotify : WithProgressNotify.spec (GF := GF) (hG := hG))
    (wp_WithCreatedNotify : WithCreatedNotify.spec (GF := GF) (hG := hG))
    (wp_remoteWriters : remoteWriters.spec (GF := GF) (hG := hG))
    (wp_AfterFunc : time.AfterFunc.spec (GF := GF) (hG := hG))
    (wp_Stop : time.Timer.Stop.spec (GF := GF) (hG := hG))
    (wp_MaxRev : etcdstart.MaxRev.spec (GF := GF) (hG := hG))
    (wp_Collect : etcdstart.Collect.spec (GF := GF) (hG := hG))
    (wp_Check : etcdstart.Check.spec (GF := GF) (hG := hG)) :
    RunWatch.spec (GF := GF) (hG := hG) := by
  intro π ρ eps nodes addrs ns nops ready hV Htb hpl H0 Hmul Hrb
  wp_start as ⟨Hlt, #Heps, #Hnodes, #Hready, Hsh⟩
  iunfold watchShare at Hsh
  icases Hsh with ⟨%Γ, %σ₀, %Hσ0, #Hms, Hkv, HWS⟩
  ihave #Hcci : _root_.Perennial.context.isClosedchanInit (GF := GF) $$ []
  · iapply _root_.Perennial.context.isClosedchanInit_of_init
    iPkgInit
  ihave #Pctx : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  ihave #Pcli : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  ihave #Ppb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb $$ []
  · iPkgInit
  ihave #Pes : isPkgInit (PROP := IProp GF)
      pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart $$ []
  · iPkgInit
  ihave %Hnl := ownSlice_len $$ Hnodes
  have hnl : (ns.length : Int) = sint.Z nodes.len := by have := Hnl.1; word
  have hmul : sint.Z (nodes.len * nops) = ns.length * sint.Z nops := by
    have h1 : 0 ≤ sint.Z nodes.len * sint.Z nops := Int.mul_nonneg (by have := Hnl.2; word) H0
    have h2 : sint.Z nodes.len * sint.Z nops < 2 ^ 63 := by rw [← hnl]; exact Hmul
    rw [hnl]
    word
  (try wp_auto)
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  -- `tried := etcdstart.GenAll(len(nodes) * nops, keys)`
  wp_apply wp_slice_literal (l := etcd_partition.genKeys)
  isplitr
  · ipureintro; rfl
  iintro %ksl ⟨Hks, -⟩
  simp only [go.arrayLiteralSize, List.foldl, Int.reduceAdd,
    show max (max (3 : Int) 0) 0 = 3 from rfl]
  imod ownSlice_persist _ _ _ $$ Hks with #Hks
  (try wp_auto)
  wp_apply (wp_GenAll (nodes.len * nops) _ etcd_partition.genKeys
      (by rw [hmul]; exact Int.mul_nonneg (by omega) H0) (by decide) (by decide))
    as %tsl ⟨%trs, Htrs, %Htrs⟩
  · iframe #
  imod ownSlice_persist _ _ _ $$ Htrs with #Htrs
  have hpk := wk_genKeys_pfx trs Htrs.2.1
  have hps : ∀ p ∈ trs, pairOf p ∈ trs.map pairOf ∧ wkvSmall p := fun p hp =>
    ⟨List.mem_map_of_mem hp, genKv_small p (Htrs.2.1 p hp)⟩
  -- the Puts fewer than the receipts' bound, so than `2 ^ 56` (`remoteWriters`')
  have htr56 : trs.length < 2 ^ 56 := by
    have h := Htrs.2.2
    rw [← Htrs.1] at h
    omega
  have htl : (trs.length : Int) = ns.length * sint.Z nops := by
    have h0 : 0 ≤ sint.Z (nodes.len * nops) := by rw [hmul]; exact Int.mul_nonneg (by omega) H0
    rw [Htrs.1, ← hmul]; word
  -- the clients' adapter over the cluster's KV, its property the plan's
  have hW0 : etcd_partition.wkW (trs.map pairOf) σ₀.changes := by
    rw [Hσ0]; exact etcd_partition.wkW_start _
  imod (kmInv_alloc Γ.kv σ₀ (etcd_partition.wkW (trs.map pairOf)) hW0) $$ Hkv
    with ⟨%γ, %Hγ, #Hkm, #Hlb0⟩
  obtain ⟨hγk, hγW⟩ := Hγ
  have hγeq : kmOf Γ (γ.ch, γ.tok, trs.map pairOf) = γ := by
    cases γ; simp only at hγk hγW; simp [kmOf, hγk, hγW]
  ihave #Hlb : monoListLbOwn γ.ch ([[]] : List (List mvcc.Change)) $$ []
  · rw [← Hσ0]; iexact Hlb0
  (try wp_auto)
  -- the defer chain, empty
  ihave ⟨%dv, defer, #Hdv⟩ : iprop(∃ dv : GoFunc, defer ↦ dv ∗
      □ (∀ Ψ : val → IProp GF, ▷ Ψ #() -∗ WP (App (Val #dv) (Val #())) {{ Ψ }})) $$ [defer]
  · iexists _
    iframe defer
    iintro !> %Ψ HΨ
    wp_auto
    (try iexact HΨ)
  -- `watcher, err := newClient(eps)`
  wp_apply (wp_newClient eps addrs (Classical.choice hV) Htb hpl) $$ [$Hlt] as %cl %cerr ⟨Hlt, Hcl⟩
  · iframe #
  icases Hcl with (⟨%Hcerr, #Hnc, #Hnp, -⟩ | %Hcfail)
  rotate_left
  · obtain ⟨Hcerr, -⟩ := Hcfail
    cases cerr with
    | nil => exact absurd rfl Hcerr
    | ok ei => ?_
    (try wp_auto)
    wp_apply wp_ended as %r -
    (try wp_auto)
    wp_apply Hdv
    (try wp_auto)
    iapply HΦ; iframe Hlt
  subst Hcerr
  -- the client's `Watcher`: a watcher of the cluster's KV, etcd's watch contract at the adapter
  ihave ⟨%w, #Hwc⟩ := watchClient_of_new cl addrs (Classical.choice hV) Γ $$ [Hnc Hnp Hms]
  · iframe #
  ihave #Hwc' := Hwc
  iunfold watchClientAt at Hwc'
  icases Hwc' with ⟨-, -, #Hwf, -⟩
  ihave #HkwΓ := kvWatcherW_of_dist wp_Watch cl w addrs (Classical.choice hV) Γ $$ [Pcli Ppb Pctx Hwc]
  · iframe #
  ihave #Hkw : kvWatcherW (GF := GF) w γ.kv $$ []
  · rw [hγk]; iexact HkwΓ
  ihave #Hew := isEtcdWatcher_of_kmW w γ etcd_partition.wkPfx (by decide) (by decide) $$ [Hkw Hkm]
  · iframe #
  (try wp_auto)
  -- `wctx, cancel := context.WithCancel(context.Background())`, `defer cancel()`
  wp_apply context.wp_Background
  wp_apply context.wp_WithCancel_Background iprop(True) $$ [$Pctx $Hcci]
    as %wctx %γc %cancel ⟨#Hcancel, #Hwctx, -, #Hwfrom⟩
  ihave #HwC := metadata.outgoingCtxOkC_bgFrom wctx $$ Hwfrom
  (try wp_auto)
  ihave ⟨%dv', defer, #Hdv'⟩ : iprop(∃ dv' : GoFunc, defer ↦ dv' ∗
      □ (∀ Ψ : val → IProp GF, ▷ Ψ #() -∗ WP (App (Val #dv') (Val #())) {{ Ψ }})) $$ [defer]
  · iexists _
    iframe defer
    iintro !> %Ψ HΨ
    wp_auto
    wp_apply Hcancel $$ [] as -
    · itrivial
    (try wp_auto)
    iapply Hdv
    iexact HΨ
  iclear Hdv
  -- the watch's options
  wp_apply wp_WithPrefix as %f1 #Hf1
  wp_apply wp_WithRev (W64 1) as %f2 #Hf2
  wp_apply wp_WithProgressNotify as %f3 #Hf3
  wp_apply wp_WithCreatedNotify as %f4 #Hf4
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %osl ⟨Hosl, -⟩
  ipersist Hosl
  (try wp_auto)
  generalize hosl : slice.mk osl _ _ = optsSl
  have hfs : (([f1, zero_val GoFunc, zero_val GoFunc, zero_val GoFunc].set
      (sint.nat (W64 (0 + 1))) f2).set (sint.nat (W64 (0 + 1 + 1))) f3).set
      (sint.nat (W64 (0 + 1 + 1 + 1))) f4 = [f1, f2, f3, f4] := rfl
  ihave #Hopts : optsAt optsSl ([withPrefixM, withRevM (W64 1), withProgressNotifyM,
      withCreatedNotifyM] : List (OpFull → OpFull)) $$ []
  · iunfold optsAt
    iexists _
    iframe Hosl
    isplitr
    · ipureintro; rw [hfs]; rfl
    imodintro
    iintro %i %f %g %Hf %Hg
    rw [hfs] at Hf
    rcases i with _ | _ | _ | _ | i
    · cases Hf; cases Hg; iexact Hf1
    · cases Hf; cases Hg; iexact Hf2
    · cases Hf; cases Hg; iexact Hf3
    · cases Hf; cases Hg; iexact Hf4
    · simp at Hf
  -- `wch := watcher.Watcher.Watch(wctx, "wk/", ...)`, from revision `1` (the read at `0`)
  have h10 : (W64 1 - W64 1 : w64) = W64 0 := by decide
  ihave ⟨#Hre0, #Hra0⟩ := km_reached_of γ _ 0 (by omega) (by decide) $$ Hlb0
  ihave #Hrd0' : etcdRead (EM := etcdModelOfKV γ) (W64 1 - W64 1) $$ []
  · rw [h10]
    iunfold etcdRead
    isplitl
    · iexists W64 ((0 : Nat) : Int)
      isplitr
      · ipureintro; decide
      rw [etcdModelOfKV_etcdReadAt]
      iexact Hra0
    iunfold etcdReached
    ileft; ipureintro; decide
  iunfold isEtcdWatcher at Hew
  ihave #HW := Hew $$ %wctx
    %({ Values := ∅, Deadline := none, Done_gn := γc, PDone := iprop(True) } :
      _root_.Perennial.context.ContextDesc (IProp GF))
    %etcd_partition.wkPfx %optsSl
    %([withPrefixM, withRevM (W64 1), withProgressNotifyM, withCreatedNotifyM] :
      List (OpFull → OpFull))
    %(W64 1)
  wp_apply HW $$ [] as %wch %γw ⟨#Hwch, Hcons⟩
  · iframe Hwctx HwC Hopts
    isplitl []
    · ipureintro
      exact ⟨wk_watch_opts.1, wk_watch_opts.2, by decide⟩
    iExactEq Hrd0'; rfl
  (try wp_auto)
  -- `ready()`
  wp_apply Hready
  (try wp_auto)
  -- `oks := remoteWriters(nodes, tried, nops)`
  wp_apply (wp_remoteWriters nodes tsl ns trs nops Γ (γ.ch, γ.tok, trs.map pairOf) Htb H0 htl htr56 hps)
    $$ [$Hlt HWS] as %okSl ⟨Hlt, %oks, Hos, #Hoks0⟩
  · rw [hγeq]
    iframe #
    iframe
  ihave #Hoks : □ [∗list] p ∈ oks, etcd_partition.okFactK (GF := GF) γ p $$ []
  · rw [← hγeq]; iexact Hoks0
  (try wp_auto)
  -- `t := time.AfterFunc(readTimeout, cancel)`
  wp_apply (wp_AfterFunc _ cancel) $$ [] as %t Ht
  · wp_apply Hcancel $$ [] as -
    · itrivial
    ipureintro; exact isPanic_intoVal ()
  (try wp_auto)
  -- `evs, ok := etcdstart.Collect(wch, etcdstart.MaxRev(oks))`
  wp_apply (wp_MaxRev okSl oks (DFrac.own 1)) $$ [Hos] as %m ⟨Hos, %Hm⟩
  · iframe
  ihave Hcons : etcdWatchConsumer γw 0 (W64 0) $$ [Hcons]
  · rw [← h10]; iexact Hcons
  ihave #Hrc := etcdstart.isRespChan_of_etcdWatchChan (EM := etcdModelOfKV γ) wch γw
    etcd_partition.wkPfx $$ Hwch
  wp_apply (etcdstart.wp_Collect_plan wp_Collect
      (watchRespOk (EM := etcdModelOfKV γ) etcd_partition.wkPfx) (etcd_partition.revAtK γ)
      (kmInv γ) (trs.map pairOf) wch γw m (fun _ _ _ _ => inferInstance)
      (fun c c' v r => etcdstart.watchRespOk_closeErr' (EM := etcdModelOfKV γ)
        etcd_partition.wkPfx c c' v r)
      (fun n c c' v r hne hcur => by
        iintro #Hi Hok
        iapply (etcd_partition.resp_km γ (trs.map pairOf) hγW hpk n c c' v r hne hcur) $$ Hi Hok))
    $$ [Hcons] as %esl %ok2 Hcol
  · iframe; iframe #
  (try wp_auto)
  -- `t.Stop()`, `cancel()`
  wp_apply (wp_Stop t) $$ [Ht] as %b -
  · iright; iexact Ht
  (try wp_auto)
  wp_apply Hcancel $$ [] as -
  · itrivial
  (try wp_auto)
  cases ok2
  · -- the watch ended before it reported every successful Put
    (try wp_auto)
    wp_apply wp_ended as %r -
    (try wp_auto)
    wp_apply Hdv'
    (try wp_auto)
    iapply HΦ; iframe Hlt
  -- the check
  ihave ⟨%evs, Hes, Hcok⟩ := Hcol $$ %rfl
  ihave %HCk := checkOkK_of γ trs m evs oks Hm.2 $$ [Hcok]
  · iframe Hcok
    iexact Hoks
  imod ownSlice_persist _ _ _ $$ Hes with #Hes
  imod ownSlice_persist _ _ _ $$ Hos with #Hos
  (try wp_auto)
  wp_apply (wp_Check go!"dist watch" go!"put" esl tsl okSl evs trs oks HCk) $$ []
  · iframe #
  (try wp_auto)
  wp_apply wp_checked as %r -
  (try wp_auto)
  wp_apply Hdv'
  (try wp_auto)
  iapply HΦ; iframe Hlt

end proof

end etcd_dist_client
end EtcdGrove
end Perennial
