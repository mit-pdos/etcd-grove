/-
**What a watch of the cluster's prefix delivers, and what a writer's put leaves** (W4d of
`notes/watch-cut-plan.md`, 2026-10-22; watchkv's `LogFacts`, `WatchFacts` and `Writes` facts at
one server, `Proof/.../watchkv/`, over the cluster's history). Lean-first (no Rocq counterpart).

The history's names are the first member's read names `γr` (`watchEnv`'s), at watchkv's
workload `P` (`workload P`) and the start log `[[], []]`; the history's invariants are that
member's (`srvKVInvs E γr`: the KV invariant, the raft log's).

* `hist_wk`: a history log is a watchkv log (`WkLog`: the KV model of a committed prefix of plain
  entries, watchkv's `wk_log`'s second case).
* `revAtH γr r k v`: revision `r` of a history log is the put of `k ↦ v`; two agree
  (`revAtH_agree`: history logs are in prefix order, `histLog_two`).
* `evFactH`, `chain_hist`, `prog_step_hist`, `resp_hist`: watchkv's `evFact`, `chain_wk`,
  `prog_step_wk`, `resp_wk` at the history model (`etcdModelOfHistory`), their steps' logs
  history logs.
* `okFactH`, `okFactH_of_reply`: what the program knows of a successful put, from a member's
  reply (`putReplied`: the member's certified log, a history log, `histLog_of_cert`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.linkv3p.WatchBase
public import Proof.github_com.mit_pdos.etcd_grove.examples.watchkv.WatchFacts
public import Proof.github_com.mit_pdos.etcd_grove.examples.watchkv.Writes
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.HistoryModel

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkv3p

open Iris Iris.BI Iris.ProofMode Iris.Std go_etcd_io.etcd.server.v3.etcdserver
open watchkv (workload WkLog Cur step_wk prog_wk kvRaftOf_wk putNv_value putNv_modRev
  isProgressNotify_events')

section facts
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **A history log is a watchkv log** (see the file header). -/
theorem hist_wk (E : apply.AEnv GF) (γr : ReadNames) (P : List (GoString × GoString))
    (hwl : γr.kv.wl = workload P) (hlog : γr.kv.log0 = [[], []]) (L : mvcc.Log) :
    ⊢ srvKVInvs (GF := GF) E γr -∗ v3rpc.histLog γr.raft γr.kv L ={⊤}=∗ ⌜WkLog P L⌝ := by
  iintro #Hinvs #HL
  iunfold srvKVInvs at Hinvs
  icases Hinvs with ⟨#HkI, -, #HrI, -⟩
  iunfold v3rpc.histLog at HL
  icases HL with ⟨%A, #HA, %hA⟩
  iunfold kvInv at HkI
  iinv HkI with >Hi Hclose
  icases Hi with ⟨%Lc, HL, Hσ, %Hok, #Hw⟩
  imod srvRLog_lb γr.raft (⊤ \ ↑kvN) (mask_ndot_ne' nroot "raft_commit" "server_kv" (by decide))
    Lc A $$ HrI HL HA with ⟨HL, -, %Hp⟩
  imod Hclose $$ [HL Hσ] with -
  · inext; iexists Lc; iframe HL Hσ Hw; ipureintro; exact Hok
  imodintro
  ipureintro
  obtain ⟨hpl, -, -, hch, -⟩ := Hok
  have hplA : plainLog γr.kv.wl A := fun m hm => hpl m (Hp.subset hm)
  rw [hwl] at hplA
  rw [← hA.1]
  unfold kvModel
  rw [hch, hlog]
  exact kvRaftOf_wk P γr.kv.c0 A [[], []] hplA (watchkv.WkLog.start P) (by simp)

/-- **Revision `r` of the history is the put of `k ↦ v`** (persistent; see the file header). -/
def revAtH (γr : ReadNames) (r : Nat) (k v : GoString) : IProp GF :=
  iprop(∃ L : mvcc.Log, v3rpc.histLog γr.raft γr.kv L ∗
    ⌜L[r]? = some [mvcc.Change.put k v (W64 0)]⌝)

instance revAtH_persistent (γr : ReadNames) (r : Nat) (k v : GoString) :
    Persistent (revAtH (GF := GF) γr r k v) := by
  unfold revAtH; infer_instance

/-- **Two `revAtH`s of one revision agree.** -/
theorem revAtH_agree (γr : ReadNames) (r : Nat) (k v k' v' : GoString) :
    revAtH (GF := GF) γr r k v ∗ revAtH γr r k' v' ⊢ ⌜k = k' ∧ v = v'⌝ := by
  unfold revAtH
  iintro ⟨⟨%L, #H, %h⟩, ⟨%L', #H', %h'⟩⟩
  ihave %Hp := v3rpc.histLog_two γr.raft γr.kv L L' $$ [H H']
  · isplit
    · iexact H
    · iexact H'
  ipureintro
  obtain ⟨M, pL, pL', -⟩ := Hp
  have hrL : r < L.length := (List.getElem?_eq_some_iff.mp h).1
  have hrL' : r < L'.length := (List.getElem?_eq_some_iff.mp h').1
  have e1 : M[r]? = L[r]? := by
    obtain ⟨t, ht⟩ := pL; rw [← ht, List.getElem?_append_left hrL]
  have e2 : M[r]? = L'[r]? := by
    obtain ⟨t, ht⟩ := pL'; rw [← ht, List.getElem?_append_left hrL']
  have e : L[r]? = L'[r]? := e1.symm.trans e2
  rw [h, h'] at e
  simp at e
  exact e

/-- **A watched event `e`, the put at revision `r` of the history** (persistent; watchkv's
`evFact`: `common.evFactR` at `revAtH`). -/
abbrev evFactH (γr : ReadNames) (P : List (GoString × GoString)) (r : Nat) (e : EvModel) :
    IProp GF :=
  common.evFactR (revAtH γr) P r e

/-- **The chain of a watch's batches at the cluster** (watchkv's `chain_wk`, over the history). -/
theorem chain_hist (E : apply.AEnv GF) (γr : ReadNames) (P : List (GoString × GoString))
    (hwl : γr.kv.wl = workload P) (hlog : γr.kv.log0 = [[], []])
    (hpk : ∀ kv ∈ P, wkPfx <+: kv.1) :
    ∀ (bs : List Batch) (prev : w64) (n : Nat), Cur n prev → (∀ b ∈ bs, BatchOk b) →
      ⊢ srvKVInvs (GF := GF) E γr -∗
        watchChain (EM := v3rpc.etcdModelOfHistory γr.raft γr.kv) wkPfx prev bs ={⊤}=∗
        □ ∀ (j : Nat) (e : EvModel), ⌜bs.flatten[j]? = some e⌝ -∗ evFactH γr P (2 + n + j) e
  | [], _, _, _, _ => by
    iintro #Hinvs -
    imodintro
    iintro !> %j %e %h
    simp at h
  | b :: bs, prev, n, hcur, hok => by
    iintro #Hinvs Hch
    iunfold watchChain at Hch
    icases Hch with ⟨#Hcert, %Hlt, Hrest⟩
    iunfold etcdStepCertBody at Hcert
    icases Hcert with ⟨%cs, #Hm, #Hstep, -, -⟩
    ihave #Hstep' : v3rpc.histStep γr.raft γr.kv prev (batchRev b) wkPfx cs $$ []
    · iexact Hstep
    iunfold v3rpc.histStep at Hstep'
    iclear Hstep
    icases Hstep' with ⟨%L, #HL, %Hs⟩
    obtain ⟨h0, -, hr1, hnone, hcs⟩ := Hs
    imod hist_wk E γr P hwl hlog L $$ Hinvs HL with %Hwk
    iunfold evsMatch at Hm
    icases Hm with ⟨%Hml, #Hmv⟩
    obtain ⟨hbne, hbrev⟩ := hok b (List.mem_cons_self ..)
    have hcsne : txn.revEvs L wkPfx (sint.Z (batchRev b)).toNat ≠ [] := by
      rw [hcs]; intro h; rw [h] at Hml; exact hbne (List.length_eq_zero_iff.mp Hml.1)
    obtain ⟨hr, k, v, hkv, hL, he⟩ :=
      step_wk Hwk wkPfx hpk n prev (batchRev b) hcur Hlt hr1 hnone hcsne
    rw [hcs] at he
    subst he
    obtain ⟨e0, rfl⟩ : ∃ e0, b = [e0] := by
      have hlen : b.length = 1 := by rw [Hml.1]; rfl
      match b, hlen with
      | [e0], _ => exact ⟨e0, rfl⟩
    obtain ⟨hty, hkey, hrev⟩ := Hml.2 0 e0 _ rfl rfl
    ihave #Hval := Hmv $$ %0 %e0 %_ %rfl %rfl
    simp only [txn.changeEv, txn.putNv_key, putNv_modRev] at hty hkey hrev
    have hcur' : Cur (n + 1) (batchRev [e0]) := Or.inr ⟨by omega, by omega⟩
    imod chain_hist E γr P hwl hlog hpk bs (batchRev [e0]) (n + 1) hcur'
      (fun b' hb' => hok b' (List.mem_cons_of_mem _ hb')) $$ Hinvs Hrest with #Hrest
    imodintro
    iintro !> %j %e %hj
    cases j with
    | zero =>
      simp only [List.flatten_cons, List.singleton_append, List.getElem?_cons_zero,
        Option.some.injEq] at hj
      subst hj
      iunfold evFactH
      iunfold common.evFactR
      isplitr
      · ipureintro
        refine ⟨hty, ?_⟩
        rw [hrev]; simp only [Nat.add_zero]; word
      iexists v, _
      iframe Hval
      isplitr
      · ipureintro
        refine ⟨by simp [txn.changeEv, putNv_value], ?_⟩
        rw [hkey]; exact hkv
      iunfold revAtH
      iexists L
      iframe HL
      ipureintro
      rw [hkey]; simpa using hL
    | succ j =>
      simp only [List.flatten_cons, List.singleton_append, List.getElem?_cons_succ] at hj
      ihave H := Hrest $$ %j %e %hj
      rw [show 2 + n + (j + 1) = 2 + (n + 1) + j by omega]
      iexact H

/-- **A progress step at the cluster** (watchkv's `prog_step_wk`, over the history). -/
theorem prog_step_hist (E : apply.AEnv GF) (γr : ReadNames) (P : List (GoString × GoString))
    (hwl : γr.kv.wl = workload P) (hlog : γr.kv.log0 = [[], []])
    (hpk : ∀ kv ∈ P, wkPfx <+: kv.1) (n : Nat) (c p : w64) (hcur : Cur n c) :
    ⊢ srvKVInvs (GF := GF) E γr -∗
      EtcdStep (self := v3rpc.etcdModelOfHistory γr.raft γr.kv) c p wkPfx [] ={⊤}=∗
        ⌜c = p ∨ Cur n p⌝ := by
  iintro #Hinvs #Hstep
  ihave #Hstep' : v3rpc.histStep γr.raft γr.kv c p wkPfx [] $$ []
  · iexact Hstep
  iunfold v3rpc.histStep at Hstep'
  icases Hstep' with ⟨%L, #HL, %Hs⟩
  obtain ⟨-, hle, hp, -, hnone⟩ := Hs
  imod hist_wk E γr P hwl hlog L $$ Hinvs HL with %Hwk
  imodintro
  ipureintro
  exact prog_wk Hwk wkPfx hpk n c p hcur hle hp hnone

/-- **One response of a watch at the cluster** (watchkv's `resp_wk`, over the history): its events
are puts of the plan at the revisions after the position's, which becomes the last's. -/
theorem resp_hist (E : apply.AEnv GF) (γr : ReadNames) (P : List (GoString × GoString))
    (hwl : γr.kv.wl = workload P) (hlog : γr.kv.log0 = [[], []])
    (hpk : ∀ kv ∈ P, wkPfx <+: kv.1) (n : Nat) (c c' : w64)
    (v : go_etcd_io.etcd.client.v3.WatchResponse) (r : RespModel) (hne : ¬ watchErr v)
    (hcur : Cur n c) :
    ⊢ srvKVInvs (GF := GF) E γr -∗
      watchRespOk (EM := v3rpc.etcdModelOfHistory γr.raft γr.kv) wkPfx c c' v r ={⊤}=∗
      ⌜Cur (n + r.events.length) c'⌝ ∗
      □ ∀ (j : Nat) (e : EvModel), ⌜r.events[j]? = some e⌝ -∗ evFactH γr P (2 + n + j) e := by
  iintro #Hinvs Hok
  iunfold watchRespOk at Hok
  icases Hok with (⟨%H, -⟩ | %H | ⟨%H, #Hs, -⟩ | ⟨%H, Hc⟩)
  · exact absurd H.1 hne
  · obtain ⟨-, he, -, rfl⟩ := H
    imodintro
    rw [he]
    isplitr
    · ipureintro; simpa using hcur
    iintro !> %j %e %h
    simp at h
  · obtain ⟨-, hp, hle, rfl, -⟩ := H
    have he := isProgressNotify_events' hp
    ihave Hcp : iprop(|={⊤}=> ⌜c = r.hdrRev ∨ Cur n r.hdrRev⌝) $$ []
    · icases Hs with (%h | #Hst)
      · imodintro; ipureintro; left; exact h
      · iapply prog_step_hist E γr P hwl hlog hpk n c r.hdrRev hcur $$ Hinvs Hst
    imod Hcp with %Hcp
    imodintro
    rw [he]
    isplitr
    · ipureintro
      simp only [List.length_nil, Nat.add_zero]
      rcases Hcp with rfl | h
      · exact hcur
      · exact h
    iintro !> %j %e %h
    simp at h
  · obtain ⟨-, hne', -, -, hlast⟩ := H
    imod chain_hist E γr P hwl hlog hpk (splitBatches r.events) c n hcur
      (splitBatches_ok r.events) $$ Hinvs Hc with #Hch
    irevert Hch
    rw [splitBatches_flatten]
    iintro #Hch
    have hlen : 0 < r.events.length := List.length_pos_iff.mpr hne'
    obtain ⟨el, hel⟩ : ∃ el, r.events[r.events.length - 1]? = some el :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have hl : r.events.getLast? = some el := by
      rw [List.getLast?_eq_getElem?]; exact hel
    rw [hl] at hlast
    simp at hlast
    ihave #Hf := Hch $$ %(r.events.length - 1) %el %hel
    iunfold evFactH at Hf
    iunfold common.evFactR at Hf
    icases Hf with ⟨%Hfe, -⟩
    imodintro
    isplitr
    · ipureintro
      right
      refine ⟨by omega, ?_⟩
      rw [← hlast, Hfe.2]; push_cast; omega
    iexact Hch

/-- **What the program knows of a successful put it logged** (persistent; watchkv's `okFact`,
over the history). -/
def okFactH (γr : ReadNames) (p : wrec) : IProp GF :=
  iprop(⌜2 ≤ sint.Z p.Rev'⌝ ∗ revAtH γr (sint.Z p.Rev').toNat p.Key' p.Val')

instance okFactH_persistent (γr : ReadNames) (p : wrec) :
    Persistent (okFactH (GF := GF) γr p) := by
  unfold okFactH; infer_instance

/-- **A member's reply to a put gives `okFactH`** of its revision, key and value: the member's
certified log of the put is a history log (`histLog_of_cert`, at the member's KV invariants and
names agreeing with the history's). -/
theorem okFactH_of_reply (γr : ReadNames) (E : apply.AEnv GF) (γm : ReadNames)
    (hm : v3rpc.memberOf γr.raft γr.kv γm) (hrb : receiptBound GF ≤ 2 ^ 62) (F : mvcc.Log)
    (k v : GoString) (Q : KVState → IProp GF) (cid mid : w64) (m : PutRespM) :
    ⊢ srvKVInvs (GF := GF) E γm -∗
      client.putReplied E γm F (txn.putOpOf k v (W64 0) false false false) Q cid mid m ={⊤}=∗
      okFactH γr ⟨m.hdr.revision, k, v⟩ := by
  iintro #Hinvs H
  unfold client.putReplied
  icases H with ⟨%hm', %x, %x', %l, %skip, %Hp, #Hc, -, -, #Hco, -⟩
  obtain ⟨hstep, hrev, -, -, -, -, h2, h4⟩ := Hp
  have hlog := client.put_applied_log _ hm' x x' l skip hstep
  ihave #Hs := mvcc.idxCert_sealed _ _ $$ Hc
  ihave #Hsm := storeSmall_of_receipts E.γ hrb
  iunfold storeSmall at Hsm
  ihave %Hsmall := Hsm $$ %x'.log Hs
  ihave #Hl : v3rpc.srvLog E x'.log $$ []
  · iunfold v3rpc.srvLog; iframe Hs; ipureintro; exact Hsmall
  have h2' : 2 < x'.log.length := by rw [hlog]; simp; omega
  imod v3rpc.histLog_of_cert γr.raft γr.kv E γm hm ⊤ (fun _ _ => CoPset.mem_full) x'.log h2'
    $$ Hinvs Hl Hco with #Hh
  imodintro
  unfold okFactH revAtH
  simp only
  rw [hrev]
  have hz : sint.Z (W64 (x.log.length : Int)) = x.log.length := by word
  isplitr
  · ipureintro; rw [hz]; omega
  iexists x'.log
  iframe Hh
  ipureintro
  rw [hz, hlog]
  simp [txn.putOpOf, txn.putChangeOf, txn.putValOf, txn.putLeaseOf]

/-- **The history's read at revision `0`** (the watch from revision `1` reads at `0`; watchkv's
`srvReadAt` of the start log): the empty committed prefix, whose model is the start log. -/
theorem histRead_zero (E : apply.AEnv GF) (γr : ReadNames) :
    ⊢ srvKVInvs (GF := GF) E γr ={⊤}=∗
      etcdRead (EM := v3rpc.etcdModelOfHistory γr.raft γr.kv) (W64 0) := by
  iintro #Hinvs
  iunfold srvKVInvs at Hinvs
  icases Hinvs with ⟨-, #Hcinv, -, -⟩
  iunfold kvCertInv at Hcinv
  iinv Hcinv with >Hi Hclose
  icases Hi with ⟨%C, %hi, %Lb, HC, Hhi', #HLb, %Hok⟩
  imod Hclose $$ [HC Hhi'] with -
  · inext; iexists C, hi, Lb; iframe HC Hhi' HLb; ipureintro; exact Hok
  ihave #H0 := srvRLogLb_mono γr.raft [] Lb (List.nil_prefix) $$ HLb
  imodintro
  iunfold etcdRead
  isplitl
  · iexists W64 0
    isplitr
    · ipureintro; exact Int.le_refl _
    ihave #Hra : v3rpc.histReachedAt γr.raft γr.kv (W64 0) $$ []
    · iunfold v3rpc.histReachedAt
      iexists []
      iframe H0
      ipureintro
      unfold kvModel
      rw [kvRaftOf_nil]
      have := Hok.2
      have h0 : sint.Z (W64 0) = 0 := by decide
      rw [h0]
      omega
    iexact Hra
  iunfold etcdReached
  ileft; ipureintro; decide

end facts

end linkv3p
end EtcdGrove
end Perennial
