/-
**What a watch of a watchkv server's prefix delivers** (D23, 2026-10-20). Lean-first (no Rocq
counterpart).

`chain_gen`: etcd's chain of steps a response's events come with (the cache's watch contract,
`watchChain` of their batches), from the watch's position after `n` events (`Cur n prev`), is,
at a model whose steps are of watchkv logs (`wkSteps`; `step_wk`), one event per batch, the
`j`-th the put at revision `2 + n + j` of a key and value of the plan (`common.evFactR`: the
event's type, revision, its key-value's value field and `R`, what the model's logs say of that
revision). `prog_step_gen` and `resp_gen` follow (a progress step; one response).

The facts are generic in the model so that one proof serves both places watchkv's workload is
watched: a server (`v3rpc.etcdModelOfServer`, `wkSteps_srv` from `wk_log`, `R` the store's
`revAt`; `resp_wk`) and the cluster's history (`linkv3p.wkSteps_hist`, `linkv3p.resp_hist`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.watchkv.WatchModel
public import Proof.github_com.mit_pdos.etcd_grove.examples.watchkv.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace watchkv

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

export common (wp_etcdWatch_receive watchRespOk_closeErr')

section facts
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **An event's facts at revision `r`** at the store `E` (`common.evFactR` at `revAt E`). -/
abbrev evFact (E : apply.AEnv GF) (P : List (GoString × GoString)) (r : Nat) (e : EvModel) :
    IProp GF :=
  common.evFactR (revAt E) P r e

theorem putNv_value (r : w64) (k val : GoString) (l : w64) (s : List EtcdKv) :
    (txn.putNv r k val l s).value = val := by
  unfold txn.putNv
  cases s.find? (fun v => decide (v.key = k)) <;> rfl

theorem putNv_modRev (r : w64) (k val : GoString) (l : w64) (s : List EtcdKv) :
    (txn.putNv r k val l s).modRev = r := by
  unfold txn.putNv
  cases s.find? (fun v => decide (v.key = k)) <;> rfl

/-- **A step's facts at a log** (`v3rpc.srvStep`'s and `v3rpc.histStep`'s, about the log they
name): from `r0` to `r1` under `pfx`, no events strictly between, and `evs` at `r1`. -/
def StepFacts (L : mvcc.Log) (r0 r1 : w64) (pfx : GoString) (evs : List EtcdEv) : Prop :=
  0 ≤ sint.Z r0 ∧ sint.Z r0 ≤ sint.Z r1 ∧ sint.Z r1 < L.length ∧
    (∀ x : Nat, sint.Z r0 < x → x < sint.Z r1 → txn.revEvs L pfx x = []) ∧
    txn.revEvs L pfx (sint.Z r1).toNat = evs

/-- **The model `EM`'s steps are a watchkv server's** (persistent): each step under `wkPfx` is of
a watchkv log `L` (`WkLog P L`, `StepFacts`) whose puts give `R` (`revAt E` at a server,
`linkv3p.revAtH` at the cluster's history). The premise of `chain_gen`, `prog_step_gen` and
`resp_gen`, which watchkv (`resp_wk`) and linkv3p (`linkv3p.resp_hist`) instantiate. -/
def wkSteps (EM : EtcdModel GF) (P : List (GoString × GoString))
    (R : Nat → GoString → GoString → IProp GF) : IProp GF :=
  iprop(□ ∀ (r0 r1 : w64) (evs : List EtcdEv), EtcdStep (self := EM) r0 r1 wkPfx evs ={⊤}=∗
    ∃ L : mvcc.Log, ⌜WkLog P L ∧ StepFacts L r0 r1 wkPfx evs⌝ ∗
      □ ∀ (r : Nat) (k v : GoString), ⌜L[r]? = some [mvcc.Change.put k v (W64 0)]⌝ -∗ R r k v)

instance wkSteps_persistent (EM : EtcdModel GF) (P : List (GoString × GoString))
    (R : Nat → GoString → GoString → IProp GF) : Persistent (wkSteps EM P R) := by
  unfold wkSteps; infer_instance

/-- **A watchkv server's steps** (`wk_log`). -/
theorem wkSteps_srv (E : apply.AEnv GF) (γr : ReadNames) (P : List (GoString × GoString))
    (hwl : γr.kv.wl = workload P) (hlog : γr.kv.log0 = [[], []]) :
    ⊢ srvKVInvs (GF := GF) E γr -∗ mvcc.idxCert E.γ.idx [[], []] -∗
      wkSteps (v3rpc.etcdModelOfServer E) P (revAt E) := by
  iintro #Hinvs #H0
  iunfold wkSteps
  iintro !> %r0 %r1 %evs #Hstep
  ihave #Hstep' : v3rpc.srvStep E r0 r1 wkPfx evs $$ []
  · iexact Hstep
  iunfold v3rpc.srvStep at Hstep'
  icases Hstep' with ⟨%L, #Hsl, #Hc, %Hs⟩
  iunfold v3rpc.srvLog at Hsl
  icases Hsl with ⟨#Hsd, -⟩
  imod wk_log E γr P hwl hlog L $$ Hinvs H0 Hsd Hc with %Hwk
  imodintro
  iexists L
  isplitr
  · ipureintro; exact ⟨Hwk, Hs⟩
  iintro !> %r %k %v %h
  iunfold revAt
  iexists L
  iframe Hsd
  ipureintro; exact h

/-- **The chain of a watch's batches** at a model whose steps are a watchkv server's (`wkSteps`; see
the file header). -/
theorem chain_gen (EM : EtcdModel GF) (P : List (GoString × GoString))
    (R : Nat → GoString → GoString → IProp GF) (hpk : ∀ kv ∈ P, wkPfx <+: kv.1) :
    ∀ (bs : List Batch) (prev : w64) (n : Nat), Cur n prev → (∀ b ∈ bs, BatchOk b) →
      ⊢ wkSteps EM P R -∗ watchChain (EM := EM) wkPfx prev bs ={⊤}=∗
        □ ∀ (j : Nat) (e : EvModel), ⌜bs.flatten[j]? = some e⌝ -∗ common.evFactR R P (2 + n + j) e
  | [], _, _, _, _ => by
    iintro #HS -
    imodintro
    iintro !> %j %e %h
    simp at h
  | b :: bs, prev, n, hcur, hok => by
    iintro #HS Hch
    iunfold watchChain at Hch
    icases Hch with ⟨#Hcert, %Hlt, Hrest⟩
    iunfold etcdStepCertBody at Hcert
    icases Hcert with ⟨%cs, #Hm, #Hstep, -, -⟩
    ihave #HSw : wkSteps EM P R $$ []
    · iexact HS
    iunfold wkSteps at HS
    imod HS $$ %prev %(batchRev b) %cs Hstep with ⟨%L, %HL, #HR⟩
    iclear Hstep
    obtain ⟨Hwk, h0, -, hr1, hnone, hcs⟩ := HL
    iunfold evsMatch at Hm
    icases Hm with ⟨%Hml, #Hmv⟩
    obtain ⟨hbne, hbrev⟩ := hok b (List.mem_cons_self ..)
    have hcsne : txn.revEvs L wkPfx (sint.Z (batchRev b)).toNat ≠ [] := by
      rw [hcs]; intro h; rw [h] at Hml; exact hbne (List.length_eq_zero_iff.mp Hml.1)
    obtain ⟨hr, k, v, hkv, hL, he⟩ := step_wk Hwk wkPfx hpk n prev (batchRev b) hcur Hlt hr1 hnone hcsne
    rw [hcs] at he
    subst he
    -- the batch: its one event
    obtain ⟨e0, rfl⟩ : ∃ e0, b = [e0] := by
      have hlen : b.length = 1 := by rw [Hml.1]; rfl
      match b, hlen with
      | [e0], _ => exact ⟨e0, rfl⟩
    obtain ⟨hty, hkey, hrev⟩ := Hml.2 0 e0 _ rfl rfl
    ihave #Hval := Hmv $$ %0 %e0 %_ %rfl %rfl
    simp only [txn.changeEv, txn.putNv_key, putNv_modRev] at hty hkey hrev
    -- the rest of the chain, from `2 + n` after `n + 1` events
    have hcur' : Cur (n + 1) (batchRev [e0]) := Or.inr ⟨by omega, by omega⟩
    imod chain_gen EM P R hpk bs (batchRev [e0]) (n + 1) hcur'
      (fun b' hb' => hok b' (List.mem_cons_of_mem _ hb')) $$ HSw Hrest with #Hrest
    imodintro
    iintro !> %j %e %hj
    cases j with
    | zero =>
      simp only [List.flatten_cons, List.singleton_append, List.getElem?_cons_zero,
        Option.some.injEq] at hj
      subst hj
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
      iapply HR
      ipureintro
      rw [hkey]; simpa using hL
    | succ j =>
      simp only [List.flatten_cons, List.singleton_append, List.getElem?_cons_succ] at hj
      ihave H := Hrest $$ %j %e %hj
      rw [show 2 + n + (j + 1) = 2 + (n + 1) + j by omega]
      iexact H

/-- **A progress step** at a model whose steps are a watchkv server's stays at the position or,
before the first event, moves to at most `1`. -/
theorem prog_step_gen (EM : EtcdModel GF) (P : List (GoString × GoString))
    (R : Nat → GoString → GoString → IProp GF) (hpk : ∀ kv ∈ P, wkPfx <+: kv.1) (n : Nat)
    (c p : w64) (hcur : Cur n c) :
    ⊢ wkSteps EM P R -∗ EtcdStep (self := EM) c p wkPfx [] ={⊤}=∗ ⌜c = p ∨ Cur n p⌝ := by
  iintro #HS #Hstep
  iunfold wkSteps at HS
  imod HS $$ %c %p %([] : List EtcdEv) Hstep with ⟨%L, %HL, -⟩
  obtain ⟨Hwk, -, hle, hp, -, hnone⟩ := HL
  imodintro
  ipureintro
  exact prog_wk Hwk wkPfx hpk n c p hcur hle hp hnone

/-- **One response of a watch** at a model whose steps are a watchkv server's (see the file
header): its events are puts of the plan at the revisions after the position's, which becomes the
last's. -/
theorem resp_gen (EM : EtcdModel GF) (P : List (GoString × GoString))
    (R : Nat → GoString → GoString → IProp GF) (hpk : ∀ kv ∈ P, wkPfx <+: kv.1) (n : Nat)
    (c c' : w64)
    (v : go_etcd_io.etcd.client.v3.WatchResponse) (r : RespModel) (hne : ¬ watchErr v)
    (hcur : Cur n c) :
    ⊢ wkSteps EM P R -∗ watchRespOk (EM := EM) wkPfx c c' v r ={⊤}=∗
      ⌜Cur (n + r.events.length) c'⌝ ∗
      □ ∀ (j : Nat) (e : EvModel), ⌜r.events[j]? = some e⌝ -∗
        common.evFactR R P (2 + n + j) e := by
  iintro #HS Hok
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
    have he := isProgressNotify_events hp
    ihave Hcp : iprop(|={⊤}=> ⌜c = r.hdrRev ∨ Cur n r.hdrRev⌝) $$ []
    · icases Hs with (%h | #Hst)
      · imodintro; ipureintro; left; exact h
      · iapply prog_step_gen EM P R hpk n c r.hdrRev hcur $$ HS Hst
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
    imod chain_gen EM P R hpk (splitBatches r.events) c n hcur
      (splitBatches_ok r.events) $$ HS Hc with #Hch
    irevert Hch
    rw [splitBatches_flatten]
    iintro #Hch
    -- the last event's revision is `c'`
    have hlen : 0 < r.events.length := List.length_pos_iff.mpr hne'
    obtain ⟨el, hel⟩ : ∃ el, r.events[r.events.length - 1]? = some el :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have hl : r.events.getLast? = some el := by
      rw [List.getLast?_eq_getElem?]; exact hel
    rw [hl] at hlast
    simp at hlast
    ihave #Hf := Hch $$ %(r.events.length - 1) %el %hel
    iunfold common.evFactR at Hf
    icases Hf with ⟨%Hfe, -⟩
    imodintro
    isplitr
    · ipureintro
      right
      refine ⟨by omega, ?_⟩
      rw [← hlast, Hfe.2]; push_cast; omega
    iexact Hch

/-- **One response of a watch at a watchkv server** (`resp_gen` at `wkSteps_srv`). -/
theorem resp_wk (E : apply.AEnv GF) (γr : ReadNames) (P : List (GoString × GoString))
    (hwl : γr.kv.wl = workload P) (hlog : γr.kv.log0 = [[], []])
    (hpk : ∀ kv ∈ P, wkPfx <+: kv.1) (n : Nat) (c c' : w64)
    (v : go_etcd_io.etcd.client.v3.WatchResponse) (r : RespModel) (hne : ¬ watchErr v)
    (hcur : Cur n c) :
    ⊢ srvKVInvs (GF := GF) E γr -∗ mvcc.idxCert E.γ.idx [[], []] -∗
      watchRespOk (EM := v3rpc.etcdModelOfServer E) wkPfx c c' v r ={⊤}=∗
      ⌜Cur (n + r.events.length) c'⌝ ∗
      □ ∀ (j : Nat) (e : EvModel), ⌜r.events[j]? = some e⌝ -∗ evFact E P (2 + n + j) e := by
  iintro #Hinvs #H0 Hok
  ihave #HS := wkSteps_srv E γr P hwl hlog $$ Hinvs H0
  iapply resp_gen _ P (revAt E) hpk n c c' v r hne hcur $$ HS Hok

end facts

end watchkv
end EtcdGrove
end Perennial
