/-
**What a watch of the cluster's prefix delivers, and what a writer's put leaves, over etcd's KV
state** (2026-10-26, D45/D47/D48; until then `WatchHist.lean`, over the cluster's committed
history at watchkv's server workload). Lean-first (no Rocq counterpart).

The example keeps its facts about the KV state in the clients' adapter (`client.kmInv γ`,
`EtcdModelKV.lean`) with the application property `γ.W = wkW P` (`WatchLog.lean`: every revision
from `2` one put of the plan `P`), which every write's update must keep: the writers' puts of the
plan do (`km_put_au`, `km_write_au` at `wkW_put`). The watch is the client watcher's at the
adapter's model (`isEtcdWatcher_of_km`), so its responses are etcd's watch contract at
`etcdModelOfKV γ`, whose steps are of logs the client saw (`kmStep`).

* `revAtK γ r k v`: revision `r` of a state the client saw is the put of `k ↦ v` (a lower bound of
  the changes, `monoListLbOwn γ.ch`); two agree (`revAtK_agree`: the bounds are in prefix order).
* `wkSteps EM P R` (watchkv's, copied): each step of `EM` under `wkPfx` is of a watchkv log whose
  puts give `R`; at the adapter, `wkSteps_km` (the log a prefix of the invariant's state's, which
  has `γ.W`).
* `chain_gen`, `prog_step_gen`, `resp_gen` (watchkv's `WatchFacts.lean`, copied): one response's
  events are the plan's puts at the revisions after the position's (`common.evFactR`), which
  becomes the last's (`Cur`); `resp_km` at the adapter.
* `okFactK`, `okFactK_of_put`: what the program knows of a successful put it logged, from the
  write update's result (`kmWriteQ`) at the state the put met.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.linkv3p.WatchLog
public import Proof.go_etcd_io.etcd.client.v3.KMWatch

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkv3p

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section facts
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **Revision `r` of a state the client saw is the put of `k ↦ v`** (persistent). -/
def revAtK (γ : client.KMNames) (r : Nat) (k v : GoString) : IProp GF :=
  iprop(∃ l : List (List mvcc.Change), monoListLbOwn γ.ch l ∗
    ⌜(([] :: l : mvcc.Log))[r]? = some [mvcc.Change.put k v (W64 0)]⌝)

instance revAtK_persistent (γ : client.KMNames) (r : Nat) (k v : GoString) :
    Persistent (revAtK (GF := GF) γ r k v) := by
  unfold revAtK; infer_instance

/-- **Two `revAtK`s of one revision agree.** -/
theorem revAtK_agree (γ : client.KMNames) (r : Nat) (k v k' v' : GoString) :
    revAtK (GF := GF) γ r k v ∗ revAtK γ r k' v' ⊢ ⌜k = k' ∧ v = v'⌝ := by
  unfold revAtK
  iintro ⟨⟨%l, #H, %h⟩, ⟨%l', #H', %h'⟩⟩
  ihave %Hp := mono_list_lb_valid γ.ch l l' $$ H H'
  ipureintro
  have hrl : r < ([] :: l : mvcc.Log).length := (List.getElem?_eq_some_iff.mp h).1
  have hrl' : r < ([] :: l' : mvcc.Log).length := (List.getElem?_eq_some_iff.mp h').1
  have e : ([] :: l : mvcc.Log)[r]? = ([] :: l' : mvcc.Log)[r]? := by
    rcases Hp with ⟨t, rfl⟩ | ⟨t, rfl⟩
    · rw [show ([] :: (l ++ t) : mvcc.Log) = ([] :: l) ++ t from rfl,
        List.getElem?_append_left hrl]
    · rw [show ([] :: (l' ++ t) : mvcc.Log) = ([] :: l') ++ t from rfl,
        List.getElem?_append_left hrl']
  rw [h, h'] at e
  simp at e
  exact e

/-- **A step's facts at a log** (`kmStep`'s about the log it names): from `r0` to `r1` under
`pfx`, no events strictly between, and `evs` at `r1`. -/
def StepFacts (L : mvcc.Log) (r0 r1 : w64) (pfx : GoString) (evs : List EtcdEv) : Prop :=
  0 ≤ sint.Z r0 ∧ sint.Z r0 ≤ sint.Z r1 ∧ sint.Z r1 < L.length ∧
    (∀ x : Nat, sint.Z r0 < x → x < sint.Z r1 → txn.revEvs L pfx x = []) ∧
    txn.revEvs L pfx (sint.Z r1).toNat = evs

/-- **The model `EM`'s steps are of watchkv logs** (persistent; see the file header). -/
def wkSteps (EM : EtcdModel GF) (P : List (GoString × GoString))
    (R : Nat → GoString → GoString → IProp GF) : IProp GF :=
  iprop(□ ∀ (r0 r1 : w64) (evs : List EtcdEv), EtcdStep (self := EM) r0 r1 wkPfx evs ={⊤}=∗
    ∃ L : mvcc.Log, ⌜WkLog P L ∧ StepFacts L r0 r1 wkPfx evs⌝ ∗
      □ ∀ (r : Nat) (k v : GoString), ⌜L[r]? = some [mvcc.Change.put k v (W64 0)]⌝ -∗ R r k v)

instance wkSteps_persistent (EM : EtcdModel GF) (P : List (GoString × GoString))
    (R : Nat → GoString → GoString → IProp GF) : Persistent (wkSteps EM P R) := by
  unfold wkSteps; infer_instance

/-- **The adapter's steps are of watchkv logs** when its property is the plan's: a step's log is a
prefix of the log of a state the client saw, a prefix of the invariant's state's. -/
theorem wkSteps_km (γ : client.KMNames) (P : List (GoString × GoString)) (hW : γ.W = wkW P) :
    ⊢ client.kmInv (GF := GF) γ -∗ wkSteps (client.etcdModelOfKV γ) P (revAtK γ) := by
  iintro #Hinv
  iunfold wkSteps
  iintro !> %r0 %r1 %evs #Hstep
  ihave #Hs : client.kmStep γ r0 r1 wkPfx evs $$ []
  · iexact Hstep
  iunfold client.kmStep at Hs
  icases Hs with ⟨%L, #HL, %Hs⟩
  iunfold client.kmLog at HL
  icases HL with ⟨%l, #Hlb, %Hw⟩
  iunfold client.kmInv at Hinv
  iinv Hinv with >Hi Hclose
  icases Hi with ⟨%σ, %m, Hσ, Hc, Ht, %Hm⟩
  ihave %Hp := mono_list_auth_lb_valid γ.ch 1 σ.changes l $$ Hc Hlb
  imod Hclose $$ [Hσ Hc Ht] with -
  · inext; iexists σ, m; iframe; ipureintro; exact Hm
  imodintro
  have hWσ : wkW P σ.changes := by rw [← hW]; exact Hm.2
  have hwk : WkLog P ([] :: l) := hWσ.prefix Hp.2
  iexists L
  isplitr
  · ipureintro; exact ⟨hwk.prefix Hw.1, Hs⟩
  iintro !> %r %k %v %h
  iunfold revAtK
  iexists l
  iframe Hlb
  ipureintro
  obtain ⟨t, ht⟩ := Hw.1
  have hr : r < L.length := (List.getElem?_eq_some_iff.mp h).1
  rw [← ht, List.getElem?_append_left hr]
  exact h

/-- **The chain of a watch's batches** at a model whose steps are of watchkv logs (`wkSteps`;
watchkv's `chain_gen`). -/
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
    obtain ⟨e0, rfl⟩ : ∃ e0, b = [e0] := by
      have hlen : b.length = 1 := by rw [Hml.1]; rfl
      match b, hlen with
      | [e0], _ => exact ⟨e0, rfl⟩
    obtain ⟨hty, hkey, hrev⟩ := Hml.2 0 e0 _ rfl rfl
    ihave #Hval := Hmv $$ %0 %e0 %_ %rfl %rfl
    simp only [txn.changeEv, txn.putNv_key, putNv_modRev] at hty hkey hrev
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

/-- **A progress step** at a model whose steps are of watchkv logs stays at the position or,
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

/-- **One response of a watch** at a model whose steps are of watchkv logs (watchkv's
`resp_gen`): its events are puts of the plan at the revisions after the position's, which becomes
the last's. -/
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

/-- **One response of a watch at the adapter** (`resp_gen` at `wkSteps_km`). -/
theorem resp_km (γ : client.KMNames) (P : List (GoString × GoString)) (hW : γ.W = wkW P)
    (hpk : ∀ kv ∈ P, wkPfx <+: kv.1) (n : Nat) (c c' : w64)
    (v : go_etcd_io.etcd.client.v3.WatchResponse) (r : RespModel) (hne : ¬ watchErr v)
    (hcur : Cur n c) :
    ⊢ client.kmInv (GF := GF) γ -∗
      watchRespOk (EM := client.etcdModelOfKV γ) wkPfx c c' v r ={⊤}=∗
      ⌜Cur (n + r.events.length) c'⌝ ∗
      □ ∀ (j : Nat) (e : EvModel), ⌜r.events[j]? = some e⌝ -∗
        common.evFactR (revAtK γ) P (2 + n + j) e := by
  iintro #Hinv Hok
  ihave #HS := wkSteps_km γ P hW $$ Hinv
  iapply resp_gen _ P (revAtK γ) hpk n c c' v r hne hcur $$ HS Hok

/-- **A writer's update for the put of `k ↦ v` of the plan** (fired at most once): the adapter's
write update, the plan's property kept (`wkW_put`). -/
theorem km_put_au (γ : client.KMNames) (P : List (GoString × GoString)) (hW : γ.W = wkW P)
    (k v : GoString) (hkv : (k, v) ∈ P) :
    client.kmInv (GF := GF) γ ∗ monoListLbOwn γ.ch ([] : List (List mvcc.Change)) ⊢
      kvOpAu1 γ.kv (.put (client.putKeyOp k v))
        (client.kmWriteQ γ [] (.put (client.putKeyOp k v))) :=
  client.km_write_au γ [] _ (fun σ h => by
    rw [hW] at h ⊢; exact wkW_put P k v hkv σ h)

/-- **What the program knows of a successful put it logged** (persistent): its revision, from
`2` on, is the put of its key and value in a state the client saw. -/
def okFactK (γ : client.KMNames) (p : wrec) : IProp GF :=
  iprop(⌜2 ≤ sint.Z p.Rev'⌝ ∗ revAtK γ (sint.Z p.Rev').toNat p.Key' p.Val')

instance okFactK_persistent (γ : client.KMNames) (p : wrec) :
    Persistent (okFactK (GF := GF) γ p) := by
  unfold okFactK; infer_instance

/-- **A put's update result gives `okFactK`** at the revision after the state it met (a state of
no compaction, revision `1` or more, below `2 ^ 63`). -/
theorem okFactK_of_put (γ : client.KMNames) (k v : GoString) (σ : KVState)
    (hc : σ.compacted = 0) (h1 : 1 ≤ σ.rev) (hb : σ.rev + 4 < 2 ^ 63) :
    client.kmWriteQ (GF := GF) γ [] (.put (client.putKeyOp k v)) σ ⊢
      okFactK γ ⟨W64 ((σ.rev + 1 : Nat) : Int), k, v⟩ := by
  unfold client.kmWriteQ
  rw [kvOpStep_putKeyOp]
  iintro ⟨#Hlb, -⟩
  have hz : sint.Z (W64 ((σ.rev + 1 : Nat) : Int)) = σ.rev + 1 := by word
  have hr : σ.rev = σ.changes.length := by simp [KVState.rev, hc]
  unfold okFactK revAtK
  simp only
  rw [hz]
  isplitr
  · ipureintro; omega
  iexists _
  iframe Hlb
  ipureintro
  simp only [KVState.commit, List.cons_ne_nil, ↓reduceIte]
  rw [show ((σ.rev : Int) + 1).toNat = σ.changes.length + 1 by omega]
  simp

end facts

end linkv3p
end EtcdGrove
end Perennial
