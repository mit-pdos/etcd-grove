/-
**What a cache watch of a prefix delivers, the KV's changes the plan's puts** (2026-10-20). Lean-first
(no Rocq counterpart).

The cache's `Watch` contract (`Cache.Watch.spec`, `cache/v3/Results.lean`'s
`cache_Watch_delivery`) says a log `L` of responses received on the watch's channel is a
`cacheWatchLog`: the demux's delivery to the watch (its events exactly the key filter's part of
etcd's batches `bs`, each batch certified by etcd's step from at most the previous one,
`certChain (etcdStepCert pfx) p₀ bs`, and for a start `sr ≠ 0`, `p₀ < sr`), or such a delivery
followed by a compaction's cancel, or a rejection's single cancel. For a log with no cancel and a
start at revision `2`, at the clients' model of etcd over its KV state (`client.etcdModelOfKV γ`)
with the plan's fact (`γ.W = watchkv.wkW P`; `km_step_log`: each step's log is a watchkv
log, every revision from `2` on one put of the plan):

* `step_ck`: a step from `p` at most the watch's position `last` after `n` events (`CurI n last`:
  `last ≤ 1` before the first event, then the last event's revision `1 + n`), to a revision with
  events, is to revision `2 + n`, with its put's one event (`watchkv.step_wk` for a step that may
  start below the position: `certChain`'s, where `watchkv`'s client watch has `watchChain`'s);
* `km_step_log` (watchkv's until 2026-10-26, when watchkv stopped using the adapter): a step of the
  adapter's model is of a watchkv log (`StepFacts`), its puts `common.kmRevAt γ`'s (`evFact`);
* `certChain_ck`: such a chain is one event per batch, the `j`-th the put at revision `2 + n + j`
  (`evFact`);
* `log_ck`: so a log of the cache's watch from revision `2` with no cancel has, as its `j`-th event,
  the put at revision `2 + j` (the key filter keeps every put of the plan, `hkeys`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.cachekv.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.common.WritesKM
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.ClientLaws
public import Proof.go_etcd_io.etcd.cache.v3.InvCache

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cachekv

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section pure
variable [GooseExts]

/-- Revisions `0` and `1` of a watchkv log have no event. -/
theorem revEvs_low {P : List (GoString × GoString)} {L : mvcc.Log} (h : watchkv.WkLog P L)
    (pfx : GoString) (x : Nat) (hx : x < 2) : txn.revEvs L pfx x = [] := by
  unfold txn.revEvs
  cases hL : L[x]? with
  | none => simp [txn.evsUnder]
  | some cs =>
    rw [h.1 x cs hx hL]
    simp [txn.evsUnder]

/-- A later revision of a watchkv log, whose plan's keys are under the prefix, has the one event
of its put. -/
theorem revEvs_hi {P : List (GoString × GoString)} {L : mvcc.Log} (h : watchkv.WkLog P L)
    (pfx : GoString) (hpk : ∀ kv ∈ P, pfx <+: kv.1) (x : Nat) (hx2 : 2 ≤ x)
    (hxl : x < L.length) :
    ∃ k v, (k, v) ∈ P ∧ L[x]? = some [mvcc.Change.put k v (W64 0)] ∧
      txn.revEvs L pfx x =
        [txn.changeEv (W64 (x : Int)) (mvcc.stateAt L (x - 1)) (mvcc.Change.put k v (W64 0))] := by
  have hx : L[x]? = some L[x] := List.getElem?_eq_getElem hxl
  obtain ⟨k, v, hkv, hcs⟩ := h.2 x L[x] hx2 hx
  refine ⟨k, v, hkv, by rw [hx, hcs], ?_⟩
  unfold txn.revEvs
  rw [hx, hcs]
  have hp : pfx <+: k := hpk (k, v) hkv
  simp [txn.evsUnder, mvcc.Change.key, hp]

/-- **The watch's position after `n` events** (see the file header). -/
def CurI (n : Nat) (last : Int) : Prop := (n = 0 ∧ last ≤ 1) ∨ (1 ≤ n ∧ last = 1 + n)

/-- **A step to a revision with events, from at most the position** (see the file header). -/
theorem step_ck {P : List (GoString × GoString)} {L : mvcc.Log} (h : watchkv.WkLog P L)
    (pfx : GoString) (hpk : ∀ kv ∈ P, pfx <+: kv.1) (n : Nat) (last : Int) (p r1 : w64)
    (hcur : CurI n last) (hpl : sint.Z p ≤ last) (hlt : last < sint.Z r1)
    (hr1 : sint.Z r1 < L.length)
    (hnone : ∀ x : Nat, sint.Z p < x → x < sint.Z r1 → txn.revEvs L pfx x = [])
    (hne : txn.revEvs L pfx (sint.Z r1).toNat ≠ []) :
    sint.Z r1 = 2 + n ∧ ∃ k v, (k, v) ∈ P ∧ L[2 + n]? = some [mvcc.Change.put k v (W64 0)] ∧
      txn.revEvs L pfx (sint.Z r1).toNat =
        [txn.changeEv (W64 ((2 + n : Nat) : Int)) (mvcc.stateAt L (1 + n))
          (mvcc.Change.put k v (W64 0))] := by
  -- `r1 ≥ 2`: revisions below have no event
  have h2 : 2 ≤ sint.Z r1 := by
    refine Classical.byContradiction fun hc => hne ?_
    exact revEvs_low h pfx _ (by omega)
  -- nothing at `2 ≤ x < r1` above `p`
  have hle : ∀ x : Nat, 2 ≤ x → (x : Int) < sint.Z r1 → (x : Int) ≤ sint.Z p := by
    intro x hx2 hx
    refine Classical.byContradiction fun hc => ?_
    obtain ⟨k, v, -, -, he⟩ := revEvs_hi h pfx hpk x hx2 (by omega)
    have := hnone x (by omega) hx
    rw [he] at this
    simp at this
  have hr : sint.Z r1 = 2 + n := by
    rcases hcur with ⟨rfl, hl⟩ | ⟨hn, hl⟩
    · refine Classical.byContradiction fun hc => ?_
      have := hle 2 (Nat.le_refl _) (by omega)
      omega
    · refine Classical.byContradiction fun hc => ?_
      have := hle (2 + n) (by omega) (by omega)
      omega
  refine ⟨hr, ?_⟩
  obtain ⟨k, v, hkv, hL, he⟩ := revEvs_hi h pfx hpk (2 + n) (by omega) (by omega)
  refine ⟨k, v, hkv, hL, ?_⟩
  rw [show (sint.Z r1).toNat = 2 + n by omega, he]
  simp only [show 2 + n - 1 = 1 + n by omega]

end pure

section facts
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- **An event's facts at revision `r`** at the adapter's names `γ` (`common.evFactR` at
`common.kmRevAt γ`). -/
abbrev evFact (γ : client.KMNames) (P : List (GoString × GoString)) (r : Nat) (e : EvModel) :
    IProp GF :=
  common.evFactR (common.kmRevAt γ) P r e

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

/-- **A step of the adapter's model is of a watchkv log** at the plan's fact (`γ.W = wkW P`), under
any prefix: its log is a prefix of the log of a state the client saw (`client.kmLog`), whose
changes are a prefix of the invariant's state's, a watchkv log; its puts are
`common.kmRevAt γ`'s. -/
theorem km_step_log (γ : client.KMNames) (P : List (GoString × GoString)) (hW : γ.W = watchkv.wkW P)
    (r0 r1 : w64) (pfx : GoString) (evs : List EtcdEv) :
    ⊢ client.kmInv (GF := GF) γ -∗ client.kmStep γ r0 r1 pfx evs ={⊤}=∗
      ∃ L : mvcc.Log, ⌜watchkv.WkLog P L ∧ StepFacts L r0 r1 pfx evs⌝ ∗
        □ ∀ (r : Nat) (k v : GoString), ⌜L[r]? = some [mvcc.Change.put k v (W64 0)]⌝ -∗
          common.kmRevAt γ r k v := by
  iintro #Hinv #Hstep
  icases client.kmStep_elim _ _ _ _ _ $$ Hstep with ⟨%L, #HL, %Hs⟩
  imod client.kmLog_W γ L $$ Hinv HL with %HW
  obtain ⟨cs, hcs, hLcs⟩ := HW
  have hwk : watchkv.WkLog P L :=
    watchkv.wkW_prefix (by rw [← hW]; exact hcs) (List.prefix_refl _) hLcs
  imodintro
  iexists L
  isplitr
  · ipureintro; exact ⟨hwk, Hs⟩
  iapply common.kmRevAt_of_log γ L $$ HL

/-- **The certificate chain of a cache watch's batches at a watchkv server** (see the file
header). -/
theorem certChain_ck (γ : client.KMNames) (P : List (GoString × GoString))
    (hW : γ.W = watchkv.wkW P) (hpk : ∀ kv ∈ P, ckPfx <+: kv.1) :
    ∀ (bs : List Batch) (last : Int) (n : Nat), CurI n last → (∀ b ∈ bs, BatchOk b) →
      ⊢ client.kmInv (GF := GF) γ -∗
        certChain (etcdStepCert (EM := client.etcdModelOfKV γ) ckPfx) last bs ={⊤}=∗
        □ ∀ (j : Nat) (e : EvModel), ⌜bs.flatten[j]? = some e⌝ -∗
          evFact γ P (2 + n + j) e
  | [], _, _, _, _ => by
    iintro #Hinv -
    imodintro
    iintro !> %j %e %h
    simp at h
  | b :: bs, last, n, hcur, hok => by
    iintro #Hinv Hch
    rw [certChain_cons]
    icases Hch with ⟨⟨%p, %Hp, #Hcert⟩, Hrest⟩
    have hcb : (etcdStepCert (EM := client.etcdModelOfKV (GF := GF) γ) ckPfx).cert p b =
        etcdStepCertBody (EM := client.etcdModelOfKV (GF := GF) γ) ckPfx p b := rfl
    irevert Hcert
    rw [hcb]
    iintro #Hcert'
    iunfold etcdStepCertBody at Hcert'
    icases Hcert' with ⟨%cs, #Hm, #Hstep, -, -⟩
    ihave #Hstep' : client.kmStep γ p (batchRev b) ckPfx cs $$ []
    · iexact Hstep
    iclear Hstep
    imod km_step_log γ P hW p (batchRev b) ckPfx cs $$ Hinv Hstep' with ⟨%L, %HL, #HR⟩
    obtain ⟨Hwk, -, -, hr1, hnone, hcs⟩ := HL
    iunfold evsMatch at Hm
    icases Hm with ⟨%Hml, #Hmv⟩
    obtain ⟨hbne, hbrev⟩ := hok b (List.mem_cons_self ..)
    have hcsne : txn.revEvs L ckPfx (sint.Z (batchRev b)).toNat ≠ [] := by
      rw [hcs]; intro h; rw [h] at Hml; exact hbne (List.length_eq_zero_iff.mp Hml.1)
    obtain ⟨hr, k, v, hkv, hL, he⟩ :=
      step_ck Hwk ckPfx hpk n last p (batchRev b) hcur Hp.1 Hp.2 hr1 hnone hcsne
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
    have hcur' : CurI (n + 1) (sint.Z (batchRev [e0])) := Or.inr ⟨by omega, by omega⟩
    imod certChain_ck γ P hW hpk bs (sint.Z (batchRev [e0])) (n + 1) hcur'
      (fun b' hb' => hok b' (List.mem_cons_of_mem _ hb')) $$ Hinv Hrest with #Hrest
    imodintro
    iintro !> %j %e %hj
    cases j with
    | zero =>
      simp only [List.flatten_cons, List.singleton_append, List.getElem?_cons_zero,
        Option.some.injEq] at hj
      subst hj
      iunfold evFact
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

/-- **A log of a cache watch from revision `2`, with no cancel, at a watchkv server** (see the
file header): its `j`-th event is the put at revision `2 + j`. -/
theorem log_ck (γ : client.KMNames) (P : List (GoString × GoString))
    (hW : γ.W = watchkv.wkW P) (hpk : ∀ kv ∈ P, ckPfx <+: kv.1) (rangeEnd : GoString)
    (hkeys : ∀ kv ∈ P, keyPredForRange ckPfx rangeEnd kv.1 = true) (L : List RespModel)
    (hc : ∀ r ∈ L, r.canceled = false) :
    ⊢ client.kmInv (GF := GF) γ -∗
      cacheWatchLog (etcdStepCert (EM := client.etcdModelOfKV γ) ckPfx)
        (some (keyPredForRange ckPfx rangeEnd)) (W64 2) L ={⊤}=∗
      □ ∀ (j : Nat) (e : EvModel), ⌜(eventsOf L)[j]? = some e⌝ -∗ evFact γ P (2 + j) e := by
  iintro #Hinv #Hlog
  iunfold cacheWatchLog at Hlog
  icases Hlog with (#Hd | ⟨%L0, %n, %HL, -⟩ | %H)
  · ihave ⟨%bs, %p₀, %Hf, #Hch, -⟩ := cacheWatch_delivery (EM := client.etcdModelOfKV γ)
      ckPfx ckPfx rangeEnd (W64 2) L $$ Hd
    obtain ⟨hev, -, hst, hsr⟩ := Hf
    obtain ⟨hp0, -⟩ := hsr (by decide)
    have hp0' : p₀ ≤ 1 := by
      have : sint.Z (W64 2) = 2 := by decide
      omega
    imod certChain_ck γ P hW hpk bs p₀ 0 (Or.inl ⟨rfl, hp0'⟩) hst.batches
      $$ Hinv Hch with #Hb
    -- the key filter keeps every event of the batches (each a put of the plan)
    ihave %Hk : ⌜∀ (j : Nat) (e : EvModel), bs.flatten[j]? = some e →
        keyPredForRange ckPfx rangeEnd e.key = true⌝ $$ []
    · iapply BI.pure_forall.2
      iintro %j
      iapply BI.pure_forall.2
      iintro %e
      by_cases hj : bs.flatten[j]? = some e
      · ihave Hf := Hb $$ %j %e %hj
        iunfold evFact at Hf
        iunfold common.evFactR at Hf
        icases Hf with ⟨-, %v, %kvv, -, %Hv, -⟩
        ipureintro; intro _; exact hkeys _ Hv.2
      · ipureintro; intro h; exact absurd h hj
    have hid : bs.flatten.filter (fun e => keyPredForRange ckPfx rangeEnd e.key) = bs.flatten := by
      rw [List.filter_eq_self]
      intro e he
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp he
      exact Hk j e hj
    rw [hev, hid]
    imodintro
    iintro !> %j %e %hj
    ihave H := Hb $$ %j %e %hj
    rw [show 2 + j = 2 + 0 + j by omega]
    iexact H
  · exfalso
    have := hc (cancelModel n) (by rw [HL]; simp)
    simp [cancelModel] at this
  · exfalso
    obtain ⟨r, hL, hcr, -⟩ := H
    have := hc r (by rw [hL]; simp)
    rw [hcr] at this
    cases this

/-- **A progress notification of a cache watch from revision `2` at a watchkv server is not past
its events** (see the file header): a log `L` with no cancel and a progress notification `r` in
it, at revision `p`, has `p ≤ 1 + (eventsOf L).length`. The delivery theorem's quiet fact
(`watchProgressQuiet`): `p` is at most the last batch at or below it, which is an event of `L`
(at revision `2 + j`), or ends a step without events under the prefix, impossible at a revision
`≥ 2` of a watchkv log (`km_step_log`, `revEvs_hi`: every such revision is a put under it). -/
theorem log_ck_progress (γ : client.KMNames) (P : List (GoString × GoString))
    (hW : γ.W = watchkv.wkW P) (hpk : ∀ kv ∈ P, ckPfx <+: kv.1) (rangeEnd : GoString)
    (hkeys : ∀ kv ∈ P, keyPredForRange ckPfx rangeEnd kv.1 = true) (L : List RespModel)
    (hc : ∀ r ∈ L, r.canceled = false) (r : RespModel) (hr : r ∈ L ∧ r.events = []) :
    ⊢ client.kmInv (GF := GF) γ -∗
      cacheWatchLog (etcdStepCert (EM := client.etcdModelOfKV γ) ckPfx)
        (some (keyPredForRange ckPfx rangeEnd)) (W64 2) L ={⊤}=∗
      ⌜sint.Z r.hdrRev ≤ 1 + (eventsOf L).length⌝ := by
  iintro #Hinv #Hlog
  iunfold cacheWatchLog at Hlog
  icases Hlog with (#Hd | ⟨%L0, %n, %HL, -⟩ | %H)
  · ihave ⟨%bs, %p₀, %Hf, #Hch, #Hpq⟩ := cacheWatch_delivery (EM := client.etcdModelOfKV γ)
      ckPfx ckPfx rangeEnd (W64 2) L $$ Hd
    obtain ⟨hev, -, hst, hsr⟩ := Hf
    obtain ⟨hp0, -⟩ := hsr (by decide)
    have hp0' : p₀ ≤ 1 := by
      have : sint.Z (W64 2) = 2 := by decide
      omega
    by_cases hpos : sint.Z r.hdrRev ≤ 0
    · imodintro; ipureintro; omega
    imod certChain_ck γ P hW hpk bs p₀ 0 (Or.inl ⟨rfl, hp0'⟩) hst.batches
      $$ Hinv Hch with #Hb
    -- the batches' events: puts of the plan (the key filter keeps them), at revisions `2 + j`
    ihave %Hk : ⌜∀ (j : Nat) (e : EvModel), bs.flatten[j]? = some e →
        keyPredForRange ckPfx rangeEnd e.key = true ∧ sint.Z e.rev = 2 + j⌝ $$ []
    · iapply BI.pure_forall.2
      iintro %j
      iapply BI.pure_forall.2
      iintro %e
      by_cases hj : bs.flatten[j]? = some e
      · ihave Hf := Hb $$ %j %e %hj
        iunfold evFact at Hf
        iunfold common.evFactR at Hf
        icases Hf with ⟨%Hr, %v, %kvv, -, %Hv, -⟩
        ipureintro; intro _; exact ⟨hkeys _ Hv.2, by rw [Hr.2]; push_cast; omega⟩
      · ipureintro; intro h; exact absurd h hj
    have hid : bs.flatten.filter (fun e => keyPredForRange ckPfx rangeEnd e.key) = bs.flatten := by
      rw [List.filter_eq_self]
      intro e he
      obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp he
      exact (Hk j e hj).1
    rw [hid] at hev
    -- the last batch at or below the notification is at most `1 + (eventsOf L).length`
    have hcle : chainEnd p₀ (bs.filter (fun b => decide (sint.Z (batchRev b) ≤ sint.Z r.hdrRev))) ≤
        1 + (eventsOf L).length := by
      unfold chainEnd
      cases hl : (bs.filter (fun b => decide (sint.Z (batchRev b) ≤ sint.Z r.hdrRev))).getLast? with
      | none => simp only; omega
      | some b =>
        simp only
        have hb : b ∈ bs := (List.mem_filter.1 (List.mem_of_getLast? hl)).1
        obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil b (hst.batches b hb).1
        have hef : e ∈ bs.flatten := List.mem_flatten.2 ⟨b, hb, he⟩
        obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hef
        have hjl : j < bs.flatten.length := (List.getElem?_eq_some_iff.1 hj).1
        rw [← (hst.batches b hb).2 e he, (Hk j e hj).2, hev]
        omega
    icases watchProgressQuiet_at (EM := client.etcdModelOfKV γ) ckPfx p₀ bs L r ⟨hr.1, hr.2, by omega⟩ $$ Hpq
      with (%hle | ⟨%q, %hq, #Hs⟩)
    · imodintro; ipureintro; omega
    · by_cases hfin : sint.Z r.hdrRev ≤ 1 + (eventsOf L).length
      · imodintro; ipureintro; exact hfin
      -- a step without events under the prefix to a revision `≥ 2` of a watchkv log: impossible
      imod km_step_log γ P hW q r.hdrRev ckPfx [] $$ Hinv Hs with ⟨%L', %HL', -⟩
      obtain ⟨hwk, -, -, hlen, -, hnil⟩ := HL'
      obtain ⟨k, v, -, -, he⟩ := revEvs_hi hwk ckPfx hpk (sint.Z r.hdrRev).toNat (by omega)
        (by omega)
      rw [he] at hnil
      cases hnil
  · exfalso
    have := hc (cancelModel n) (by rw [HL]; simp)
    simp [cancelModel] at this
  · exfalso
    obtain ⟨r, hL, hcr, -⟩ := H
    have := hc r (by rw [hL]; simp)
    rw [hcr] at this
    cases this

end facts

end cachekv
end EtcdGrove
end Perennial
