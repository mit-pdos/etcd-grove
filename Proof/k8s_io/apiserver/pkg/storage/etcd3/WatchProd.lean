/-
Lean-first (no Rocq counterpart).

# The etcd3 watcher's producer (`startWatching`, `syncPaginated`): the incoming channel's sends (k8s 7f-5a-P step 5)

`incomingEventChan` has one producer, `startWatching` (and `syncPaginated` on its goroutine). Its
element `kInElem` at index `i` carries the indices `0..i` of the ghost list `γ.raws` of the raw
events sent. `queueEvent` may drop an event (the context done), after which the producer goes on, so
the raw event must enter `γ.raws` at the send's commit, not before: the producer sends through
`spsc_send_commit_inv` over `isSpsc`'s invariant (extended with `True`, `inv_alter`), and

- `kIncTok γ` (the sender's `T`, existential so that it survives the send): the SPSC's producer
  token and half of `γ.raws`' authority, of one length;
- the producer keeps the other half (`monoListAuthOwn γ.raws ½ raws`), which tells it `raws`;
- `kInc_commit`: from the element's facts, the commit `queueEvent` takes (`S ∧ commit`, with `S` the
  two halves back on a drop).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.WatchRes
public import Proof.context.WatchCtx

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

section pure
variable [GooseExts]

/-- The ideal raw stream is its initial part (`full := []`) followed by the tail. -/
theorem kRawIdealL_app (inS : GoString → Bool) (m : KWatchMode) (σ : KVState) (st : Nat)
    (full : List KRaw) : kRawIdealL inS m σ st full = kRawIdealL inS m σ st [] ++ full := by
  unfold kRawIdealL; split <;> simp

/-- **The producer's position in the watch phase** (pure): the raw events it has queued or dropped,
`I`, are the ideal stream's initial part (the initial events and the initial-events-end bookmark,
if asked) and a segment of the watch from the start point `st` to the cursor `c` (the client watch's
position: the last revision reported), at the history `σ`. -/
def kProdAt (inS : GoString → Bool) (m : KWatchMode) (σ : KVState) (st c : Nat) (I : List KRaw) :
    Prop :=
  (m.forceInit = true → st ≤ σ.rev) ∧
  ∃ seg, KRawSeg σ inS st c seg ∧ I = kRawIdealL inS m σ st [] ++ seg

/-- **What the watch phase queues is a prefix of the ideal stream**: any prefix `J` of a segment
from the cursor. -/
theorem kProdAt_ok {inS : GoString → Bool} {m : KWatchMode} {σ : KVState} {st c c' : Nat}
    {I ch J : List KRaw} (h : kProdAt inS m σ st c I) (hch : KRawSeg σ inS c c' ch)
    (hJ : J <+: ch) : kRawStreamOk inS m σ st (I ++ J) := by
  obtain ⟨hst, seg, hs, rfl⟩ := h
  refine ⟨hst, seg ++ ch, ?_, ?_⟩
  · have := kRawSeg_tail (kRawSeg_append hs hch) (KRawTail.nil c')
    rwa [List.append_nil] at this
  · rw [kRawIdealL_app inS m σ st (seg ++ ch), List.append_assoc]
    exact (List.prefix_append_right_inj _).2 ((List.prefix_append_right_inj _).2 hJ)

/-- The cursor moves to the end of a segment. -/
theorem kProdAt_step {inS : GoString → Bool} {m : KWatchMode} {σ : KVState} {st c c' : Nat}
    {I ch : List KRaw} (h : kProdAt inS m σ st c I) (hch : KRawSeg σ inS c c' ch) :
    kProdAt inS m σ st c' (I ++ ch) := by
  obtain ⟨hst, seg, hs, rfl⟩ := h
  exact ⟨hst, seg ++ ch, kRawSeg_append hs hch, by simp⟩

/-- **The producer's position at a longer state of the history.** -/
theorem kProdAt_hist {inS : GoString → Bool} {m : KWatchMode} {σ σ' : KVState} {st c : Nat}
    {I : List KRaw} (hh : kvSameHist σ σ') (hle : σ.rev ≤ σ'.rev) (h : kProdAt inS m σ st c I) :
    kProdAt inS m σ' st c I := by
  obtain ⟨hst, seg, hs, rfl⟩ := h
  refine ⟨fun hf => by have := hst hf; omega, seg, kRawSeg_hist hh hle hs, ?_⟩
  rw [kRawIdealL_hist hh hle inS m st hst []]

/-- **The start of the watch phase**: the whole initial part queued, the cursor at the start point. -/
theorem kProdAt_start {inS : GoString → Bool} {m : KWatchMode} {σ : KVState} {st : Nat}
    (hst : m.forceInit = true → st ≤ σ.rev) :
    kProdAt inS m σ st st (kRawIdealL inS m σ st []) :=
  ⟨hst, [], KRawSeg.nil st, by simp⟩

/-- **The initial phase**: a prefix of the initial part is a prefix of the ideal stream (any tail). -/
theorem kInit_ok {inS : GoString → Bool} {m : KWatchMode} {σ : KVState} {st : Nat}
    {I : List KRaw} (hst : m.forceInit = true → st ≤ σ.rev) (h : I <+: kRawIdealL inS m σ st []) :
    kRawStreamOk inS m σ st I :=
  ⟨hst, [], KRawTail.nil st, h⟩

/-- **A dropped event leaves a subsequence**: the raw events sent, a subsequence of those queued or
dropped `I`, followed by `r`, are a subsequence of the ideal stream when `I ++ [r]` is a prefix. -/
theorem kRawStreamSub_of_ok {inS : GoString → Bool} {m : KWatchMode} {σ : KVState} {st : Nat}
    {raws I : List KRaw} {r : KRaw} (hs : List.Sublist raws I) (h : kRawStreamOk inS m σ st (I ++ [r])) :
    kRawStreamSub inS m σ st (raws ++ [r]) :=
  kRawStreamSub_sublist (hs.append (List.Sublist.refl _)) (kRawStreamOk_sub h)

end pure

section inc
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [go_etcd_io.etcd.client.v3.Assumptions]
variable [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

instance eventAt_persistent (σ : KVState) (p : Loc) (r : KRaw) :
    Persistent (eventAt (GF := GF) σ p r) := by
  unfold eventAt; infer_instance

/-- **The incoming channel's producer token** (`spsc_send_commit_inv`'s `T`): the SPSC's producer
half and half of the raw events' authority, one raw event per element sent. -/
def kIncTok (γ : KWatchNames) : IProp GF :=
  iprop(∃ (sent : List Loc) (raws : List KRaw), spscProducer γ.inc sent ∗
    monoListAuthOwn γ.raws (1 : Qp).half raws ∗ ⌜raws.length = sent.length⌝)

/-- **The producer's commit of one raw event** `r` (an `*event` at `p` holding it at `σ`): the
element `kInElem` at the next index, from the producer's raw events `raws` (its half of `γ.raws`),
the read facts and the stream facts of `raws ++ [r]`. Given as `queueEvent` takes it: the token and
the half back (a drop), or the commit, after which the half is `raws ++ [r]`. -/
theorem kInc_commit (γ : KWatchNames) (cd : context.ContextDesc (IProp GF)) (inS : GoString → Bool)
    (m : KWatchMode) (Q : Nat → KVState → IProp GF) (ch p : Loc) (r : KRaw) (raws : List KRaw)
    (lb lb0 st : Nat) (σ σ0 : KVState) (hst : kStartOk m σ0 st)
    (hsub : kRawStreamSub inS m σ st (raws ++ [r])) :
    ⊢ isSpsc γ.inc ch (kInElem γ cd inS m Q) (fun _ => iprop(False)) -∗ eventAt σ p r -∗
      □ Q lb σ -∗ □ Q lb0 σ0 -∗
      (⌜kRawStreamOk inS m σ st (raws ++ [r])⌝ ∨ kCancelled γ cd ∨ kProcExited γ) -∗
      kIncTok γ -∗ monoListAuthOwn γ.raws (1 : Qp).half raws -∗
      ((kIncTok γ ∗ monoListAuthOwn γ.raws (1 : Qp).half raws) ∧
        (£ 1 ∗ £ 1 ∗ £ 1 -∗ ∀ Φ : IProp GF,
          ▷ (kIncTok γ ∗ monoListAuthOwn γ.raws (1 : Qp).half (raws ++ [r]) -∗ Φ) -∗
          sendAu γ.inc.chanName p Φ)) := by
  iintro #Hspsc Hev #HQ #HQ0 Hok HT Hh
  isplit
  · iframe
  unfold isSpsc
  icases Hspsc with ⟨#Hchan, #Hinv⟩
  ihave #Hinv' : inv nroot iprop(spscInv γ.inc (kInElem γ cd inS m Q) (fun _ => iprop(False)) ∗
      True) $$ []
  · iapply inv_alter $$ Hinv
    inext; imodintro
    iintro H
    isplitl [H]
    · isplitl [H]; · iexact H
      itrivial
    · iintro ⟨H, -⟩; iexact H
  iapply spsc_send_commit_inv γ.inc ch (kInElem γ cd inS m Q) (fun _ => iprop(False)) iprop(True)
    (kIncTok γ) (monoListAuthOwn γ.raws (1 : Qp).half (raws ++ [r])) p $$ Hchan Hinv' [] HT
    [Hev Hok Hh]
  · iintro !> HT -
    unfold kIncTok
    icases HT with ⟨%sent, %raws', Hp, -⟩
    iexists sent
    iexact Hp
  iintro HT -
  unfold kIncTok
  icases HT with ⟨%sent, %raws', Hp, Hh', %Hlen⟩
  ihave %Hag := monoListAuthOwn_agree γ.raws _ _ raws raws' $$ Hh Hh'
  obtain ⟨-, rfl⟩ := Hag
  ihave Hfull : monoListAuthOwn γ.raws ((1 : Qp).half + (1 : Qp).half) raws $$ [Hh Hh']
  · iapply ((monoListAuthOwn_fractional (GF := GF) γ.raws raws).fractional (1 : Qp).half
      (1 : Qp).half).2
    iframe
  isimp only [Qp.half_add_half] at Hfull
  imod monoListAuthOwn_update_app [r] $$ Hfull with ⟨Hfull, #Hlb⟩
  ihave ⟨H1, H2⟩ : monoListAuthOwn (GF := GF) γ.raws (1 : Qp).half (raws ++ [r]) ∗
      monoListAuthOwn (GF := GF) γ.raws (1 : Qp).half (raws ++ [r]) $$ [Hfull]
  · iapply ((monoListAuthOwn_fractional (GF := GF) γ.raws (raws ++ [r])).fractional (1 : Qp).half
      (1 : Qp).half).1
    rw [Qp.half_add_half]; iexact Hfull
  imodintro
  iexists sent
  isplitl [Hp]
  · iexact Hp
  isplitr [H1 H2]
  · unfold kInElem
    iexists r, raws, lb, lb0, st, σ, σ0
    iframe Hev HQ HQ0 Hok
    isplitr
    · ipureintro; simp [Hlen]
    isplitr
    · iapply monoList_lb_idx_all $$ Hlb
    ipureintro; exact ⟨hst, hsub⟩
  iintro Hp
  imodintro
  isplitr
  · itrivial
  isplitl [Hp H1]
  · iexists sent ++ [p], raws ++ [r]
    iframe Hp H1
    ipureintro; simp [Hlen]
  iexact H2

/-- **The producer's raw events** (its state between two sends): the token, and its half of
`γ.raws`, a subsequence of the raw events it has queued or dropped, `I`, and all of them unless the
watch is no longer live or the processing goroutine has exited. -/
def kProdSt (γ : KWatchNames) (cd : context.ContextDesc (IProp GF)) (I : List KRaw) : IProp GF :=
  iprop(kIncTok γ ∗ ∃ raws : List KRaw, monoListAuthOwn γ.raws (1 : Qp).half raws ∗
    ⌜List.Sublist raws I⌝ ∗ (⌜raws = I⌝ ∨ kCancelled γ cd ∨ kProcExited γ))

/-- The context descriptor of `wc.ctx` the producer reads (`WithCancel`'s, keeping the parent's
`PDone`: §10 of `notes/k8s-7f5a-draft.md`), with its own Done name (`wp_WithCancel_ctx`'s `γ'`;
`notes/k8s-7f5b-draft.md` §5). -/
def kCdw (γ : KWatchNames) (cd : context.ContextDesc (IProp GF)) : context.ContextDesc (IProp GF) :=
  { cd with PDone := iprop(cd.PDone ∨ kCancelPD γ cd), Done_gn := γ.wcDone }

/-- **A drop, seen by the running producer** (`prodEx`'s fraction at `false`): `wc.ctx` is done, so
the watch is no longer live or the processing goroutine has exited. -/
theorem kProd_drop (γ : KWatchNames) (cd : context.ContextDesc (IProp GF)) (q : Qp) :
    ⊢ dghostVar (GF := GF) γ.prodEx (DFrac.own q) false -∗ □ (kCdw γ cd).PDone -∗
      dghostVar γ.prodEx (DFrac.own q) false ∗ (kCancelled γ cd ∨ kProcExited γ) := by
  iintro Hd #Hpd
  unfold kCdw
  simp only []
  icases Hpd with (#Hp | #Hk)
  · iframe Hd
    ileft; unfold kCancelled; iright; iexact Hp
  · unfold kCancelPD
    icases Hk with (#Hs | #He | #Hp | #Hp)
    · iframe Hd
      ileft; unfold kCancelled; ileft; iexact Hs
    · unfold kProdExited
      ihave %Hab := dghostVar_agree _ _ _ _ _ $$ Hd He
      exact absurd Hab (by decide)
    · iframe Hd
      iright; iexact Hp
    · iframe Hd
      ileft; unfold kCancelled; iright; iexact Hp

/-- **One queued raw event** (`queueEvent`'s premise and the producer's state after it): from the
producer's state at `I` and a raw event `r` such that `I ++ [r]` is a prefix of the ideal stream at
`σ` from `st` (`kStartOk` at `σ0`), the conjunction `queueEvent` takes, and the state at `I ++ [r]`
from either outcome (a drop with the producer's `prodEx` fraction). -/
theorem kProd_queue (γ : KWatchNames) (cd : context.ContextDesc (IProp GF)) (inS : GoString → Bool)
    (m : KWatchMode) (Q : Nat → KVState → IProp GF) (ch p : Loc) (r : KRaw) (I : List KRaw)
    (lb lb0 st : Nat) (σ σ0 : KVState) (hst : kStartOk m σ0 st)
    (hok : kRawStreamOk inS m σ st (I ++ [r])) :
    ⊢ isSpsc γ.inc ch (kInElem γ cd inS m Q) (fun _ => iprop(False)) -∗ eventAt σ p r -∗
      □ Q lb σ -∗ □ Q lb0 σ0 -∗ kProdSt γ cd I -∗
      ∃ S Qs : IProp GF, (S ∧ (£ 1 ∗ £ 1 ∗ £ 1 -∗ ∀ Φ : IProp GF, ▷ (Qs -∗ Φ) -∗
          sendAu γ.inc.chanName p Φ)) ∗
        (Qs -∗ kProdSt γ cd (I ++ [r])) ∗
        (∀ q : Qp, S -∗ □ (kCdw γ cd).PDone -∗ dghostVar γ.prodEx (DFrac.own q) false -∗
          kProdSt γ cd (I ++ [r]) ∗ dghostVar γ.prodEx (DFrac.own q) false) := by
  iintro #Hspsc #Hev #HQ #HQ0 Hst
  unfold kProdSt
  icases Hst with ⟨HT, %raws, Hh, %Hsub, #Hok⟩
  have hsub' : kRawStreamSub inS m σ st (raws ++ [r]) := kRawStreamSub_of_ok Hsub hok
  ihave Hok' : (⌜kRawStreamOk inS m σ st (raws ++ [r])⌝ ∨ kCancelled γ cd ∨ kProcExited γ :
      IProp GF) $$ []
  · icases Hok with (%He | #Hc | #Hp)
    · ileft; ipureintro; rw [He]; exact hok
    · iright; ileft; iexact Hc
    · iright; iright; iexact Hp
  iexists iprop(kIncTok γ ∗ monoListAuthOwn γ.raws (1 : Qp).half raws),
    iprop(kIncTok γ ∗ monoListAuthOwn γ.raws (1 : Qp).half (raws ++ [r]))
  isplitl [HT Hh Hok']
  · iapply kInc_commit γ cd inS m Q ch p r raws lb lb0 st σ σ0 hst hsub' $$ Hspsc Hev HQ HQ0 Hok' HT Hh
  isplitr
  · iintro ⟨HT, Hh⟩
    iframe HT
    iexists raws ++ [r]
    iframe Hh
    isplitr
    · ipureintro; exact Hsub.append (List.Sublist.refl _)
    icases Hok with (%He | #Hc | #Hp)
    · ileft; ipureintro; rw [He]
    · iright; ileft; iexact Hc
    · iright; iright; iexact Hp
  iintro %q ⟨HT, Hh⟩ #Hpd Hd
  ihave ⟨Hd, #Hc⟩ := kProd_drop γ cd q $$ Hd Hpd
  iframe Hd HT
  iexists raws
  iframe Hh
  isplitr
  · ipureintro; exact Hsub.trans (List.sublist_append_left I [r])
  iright; iexact Hc

end inc

/-! ## The producer's premises (the statements of `syncPaginated`, `sync`, `startWatching`) -/

section prod
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [go_etcd_io.etcd.client.v3.Assumptions]
variable [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable {Obj : Type} [DecidableEq Obj] [Pos.Countable Obj]

/-- **A watch-list's initial raw events** at the start point `st` (`syncPaginated`'s pages):
the key-values in scope of the store at `st`, in key order. -/
def kInitRaws (inS : GoString → Bool) (σ : KVState) (st : Nat) : List KRaw :=
  ((σ.at st).kvs.filter fun v => inS v.key).map KRaw.kv

/-- **The watch channel's fields the producer reads, and its channels** (persistent; what
`createWatchChan` and `run` set up, step 6): the watcher (the store's), the prepared key `kp`
(`c.pathPrefix ++ k`; the scope `inS` is its `kInScope`), `recursive`, `progressNotify` and
`recordTimestamps` off, `wc.ctx` (`WithCancel` of the require-leader context, with `kCdw`'s Done
proposition, grpc's outgoing metadata and client errors), `wc.cancel` (whose proposition is
`kCancelPD`), the size estimator function (the store's), the incoming channel (`kInElem`'s
SPSC) with its block logger, and `resultChan` (`kResChan`). -/
def kWcProd (wc sp : Loc) (c : StoreCfg GF Obj) (W : WatchSpec GF Obj) (γ : KWatchNames)
    (cd : context.ContextDesc (IProp GF)) (sel : Obj → Bool) (emp : Bool) (inS : GoString → Bool)
    (m : KWatchMode) (Q : Nat → KVState → IProp GF) (procd alive : GName) (ctx : GoInterfaceOk)
    (kp : GoString) (recur : Bool) : IProp GF :=
  iprop(∃ (wp chI chR lg : Loc) (cf rse : GoFunc) (γc : context.ContextNames),
    structFieldRef k8s_io.apiserver.pkg.storage.etcd3.watchChan go!"watcher" wc ↦□ wp ∗
    structFieldRef k8s_io.apiserver.pkg.storage.etcd3.store go!"watcher" sp ↦□ wp ∗
    structFieldRef k8s_io.apiserver.pkg.storage.etcd3.watchChan go!"key" wc ↦□ kp ∗
    structFieldRef k8s_io.apiserver.pkg.storage.etcd3.watchChan go!"recursive" wc ↦□ recur ∗
    structFieldRef k8s_io.apiserver.pkg.storage.etcd3.watchChan go!"progressNotify" wc ↦□ false ∗
    structFieldRef k8s_io.apiserver.pkg.storage.etcd3.watchChan go!"recordTimestamps" wc ↦□ false ∗
    structFieldRef k8s_io.apiserver.pkg.storage.etcd3.watchChan go!"ctx" wc ↦□ GoInterface.ok ctx ∗
    structFieldRef k8s_io.apiserver.pkg.storage.etcd3.watchChan go!"cancel" wc ↦□ cf ∗
    context.cancelSpec cf γc (kCancelPD γ cd) ∗
    structFieldRef k8s_io.apiserver.pkg.storage.etcd3.watchChan go!"getResourceSizeEstimator" wc
      ↦□ rse ∗
    □ (∀ Φ : val → IProp GF,
      WP (App (Val (sp @!! go.GoType.PointerType k8s_io.apiserver.pkg.storage.etcd3.store.ty @!!
        go!"getResourceSizeEstimator")) (Val #())) {{ Φ }} -∗
      WP (App (Val #rse) (Val #())) {{ Φ }}) ∗
    structFieldRef k8s_io.apiserver.pkg.storage.etcd3.watchChan go!"incomingEventChan" wc ↦□ chI ∗
    structFieldRef k8s_io.apiserver.pkg.storage.etcd3.watchChan go!"incomingEventLogger" wc ↦□ lg ∗
    blockLoggerOk lg ∗
    isSpsc γ.inc chI (kInElem γ cd inS m Q) (fun _ => iprop(False)) ∗
    structFieldRef k8s_io.apiserver.pkg.storage.etcd3.watchChan go!"resultChan" wc ↦□ chR ∗
    kResChan c W γ cd sel emp inS m Q procd alive chR ∗
    context.isContext ctx (kCdw γ cd) ∗ metadata.outgoingCtxOkC ctx ∗ ctxErrClient ctx (kCdw γ cd) ∗
    ⌜inS = kInScope kp recur ∧ kp.length ≤ opKeyMax ∧ kp ≠ []⌝)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
instance kWcProd_persistent (wc sp : Loc) (c : StoreCfg GF Obj) (W : WatchSpec GF Obj)
    (γ : KWatchNames) (cd : context.ContextDesc (IProp GF)) (sel : Obj → Bool) (emp : Bool)
    (inS : GoString → Bool) (m : KWatchMode) (Q : Nat → KVState → IProp GF) (procd alive : GName)
    (ctx : GoInterfaceOk) (kp : GoString) (recur : Bool) :
    Persistent (kWcProd wc sp c W γ cd sel emp inS m Q procd alive ctx kp recur) := by
  unfold kWcProd; infer_instance

/-- **What `initialRev` holds when the producer starts** (`Watch`'s `getStartWatchResourceVersion`
and `createWatchChan`): with initial events, the requested revision (`0` or positive, then checked
by `startWatching` against `getCurrentStorageRV`); without, a positive requested revision, or (at
`0`) the revision of a state the caller's read update fired at (`getCurrentStorageRV`'s). Its
successor is a positive `int64` when it is the watch's start (`WithRev(initialRev + 1)`). -/
def kStartPre (m : KWatchMode) (Q : Nat → KVState → IProp GF) (r0 : w64) : IProp GF :=
  if m.forceInit then iprop(⌜uint.nat r0 = m.req ∧ uint.Z r0 < 2 ^ 63⌝)
  else if 0 < m.req then iprop(⌜uint.nat r0 = m.req ∧ uint.Z r0 + 1 < 2 ^ 63⌝)
  else iprop(∃ (lb0 : Nat) (σ0 : KVState), □ Q lb0 σ0 ∗ ⌜r0 = W64 (σ0.rev : Int) ∧ kvRevFits σ0.rev⌝)

/-- The read updates at the members, as `GetCurrentResourceVersion` takes them. -/
theorem readAus_crv (c : StoreCfg GF Obj) (γk : KVNames) (Q : KVState → IProp GF) :
    readAus c γk Q ⊢ ∀ (R m' : w64), |==> □ [∧list] γv ∈ c.K.kvs,
      ⌜(fun (_ _ : w64) => Q) R m' = fun _ => iprop(True)⌝ ∨ kvReadAu γv ((fun (_ _ : w64) => Q) R m') := by
  unfold readAus
  iintro ⟨-, #H⟩ %R %m'
  imodintro
  imodintro
  iapply (BigAndL.bigAndL_intro (P := iprop(□ [∗list] γv ∈ c.K.kvs, kvReadAu γv Q))
    (fun k x hk => ?_)) $$ H
  iintro #H'
  ihave #Hx := BigSepL.bigSepL_lookup hk $$ H'
  iright
  iexact Hx

end prod

end k8s
end EtcdGrove
end Perennial
