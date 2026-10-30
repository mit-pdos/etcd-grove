/-
Lemmas the proofs of `watch.go`'s API (`watcher.Watch`, `Close`, the stream's `close`, ...)
share (the watch slice's unit W-C). Lean-first (no Rocq counterpart).
-/
module

public import Perennial.Golang.Theory.Chan.Idioms.Bag
public import Perennial.Golang.Theory.Chan.Idioms.Broadcast
public import Perennial.Golang.Theory.Chan.Idioms.Spsc
public import Proof.go_etcd_io.etcd.client.v3.InvWatch

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace client

open Iris Iris.BI Iris.ProofMode

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable {V : Type} [Pos.Countable V] [ZeroVal V] [TypedPointsto (GF := GF) V] {t : go.GoType}
  [IntoValTyped (GF := GF) V t]

/-- **A nonblocking receive on a bag**: a value, with its predicate, if one is there. -/
theorem bag_nonblocking_recv_au (γ : ChanNames) (ch : Loc) (P : V → IProp GF)
    (Φ : V → Bool → IProp GF) :
    ⊢ isChanBag γ ch P -∗ (▷ ∀ v, P v -∗ Φ v true) -∗ nonblockingRecvAuInner γ V Φ := by
  rw [isChanBag_unseal]; unfold isChanBagDef nonblockingRecvAuInner
  iintro ⟨#Hch, #Hinv⟩ HΦ
  iinv Hinv with Hi Hclose
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  unfold chanBagInv
  icases Hi with ⟨%s, Hoc0, Hi⟩
  iexists s
  iframe Hoc0
  rcases s with (_ | ⟨v0, buff'⟩) | _ | v | _ | _ | _ | _
  all_goals dsimp only
  case Buffered.cons =>
    iintro Hoc
    icases BigSepL.bigSepL_cons.1 $$ Hi with ⟨HP, Hi⟩
    imod Hmask with -
    imod Hclose $$ [Hoc Hi] with -
    · inext; iexists .Buffered buff'; iframe
    imodintro
    iapply HΦ $$ HP
  case SndPending =>
    iintro Hoc
    imod Hmask with -
    imod Hclose $$ [Hoc] with -
    · inext; iexists .RcvCommit; iframe
    imodintro
    iapply HΦ $$ Hi
  all_goals first | itrivial | (iexfalso; iexact Hi)

omit [Pos.Countable V] [ZeroVal V] [TypedPointsto (GF := GF) V] [IntoValTyped (GF := GF) V t] in
/-- A broadcast channel's owner also has its persistent `Unknown` view. -/
theorem ownBroadcastChan_dup_unknown (ch : GoChan) (γ : ChanNames) (Q : IProp GF)
    (st : Broadcast) :
    ownBroadcastChan (GF := GF) ch γ Q st ⊢ ownBroadcastChan ch γ Q st ∗ ownBroadcastChan ch γ Q .Unknown := by
  iintro H
  icases ownBroadcastChan_open _ _ _ _ $$ H with ⟨%γch, #Hi, Ht⟩
  isplitl [Ht]
  · iapply ownBroadcastChan_close _ _ _ st γch
    iframe Hi Ht
  · iapply ownBroadcastChan_close _ _ _ .Unknown γch
    iframe Hi

omit [Pos.Countable V] [ZeroVal V] [TypedPointsto (GF := GF) V] [IntoValTyped (GF := GF) V t] in
/-- **A canceled response with no events** (a fresh zero header, a close error grpc's `status`
accepts) is any position's element of a watch's channel (`outcElem`, D47: an error, at a firing
`σ0` of the read update, the second cursor standing still). -/
theorem outcElem_canceled (γ : EtcdWatchNames) (o : OpFull) (Q : KVState → IProp GF)
    (σ0 : KVState) (i : Nat) (c : w64) (v : go_etcd_io.etcd.client.v3.WatchResponse)
    (hv : v.Events' = slice.nil ∧ v.CompactRevision' = W64 0 ∧ v.Canceled' = true ∧
      v.Created' = false ∧ v.Header' ≠ null) :
    structFieldRef go_etcd_io.etcd.api.v3.etcdserverpb.ResponseHeader go!"Revision" v.Header' ↦□ W64 0 ∗
      go_etcd_io.etcd.cache.v3.statusErrOk v.closeErr' ∗ □ Q σ0 ∗
      monoListIdxOwn γ.cur2 i c ∗ monoListIdxOwn γ.cur2 (i + 1) c ⊢
    outcElem γ o Q (i : Int) v := by
  obtain ⟨he, hc, hca, hcr, hh⟩ := hv
  iintro ⟨#Hrev, #Hse, #HQ, #Hi, #Hi'⟩
  unfold outcElem watchStateElem
  iexists { events := [], compactRev := W64 0, canceled := true, created := false, hdrRev := W64 0 },
    σ0, c, c
  simp only [Int.toNat_natCast]
  iframe HQ Hi Hi'
  isplitr
  · unfold respAt
    isplitr
    · unfold eventsAt
      iexists []
      rw [he]
      isplitr
      · iapply ownSlice_nil
      isplitr
      · ipureintro; rfl
      iintro !> %j %ev %e %h; simp at h
    isplitr
    · unfold hdrAt
      iright
      iframe #
      ipureintro; exact hh
    ipureintro; exact ⟨hc, hca, hcr⟩
  isplitr
  · unfold watchStateRespOk
    ileft
    iframe Hse
    ipureintro
    exact ⟨Or.inr (Or.inr hca), rfl⟩
  iintro !> -
  itrivial

omit [Pos.Countable V] [ZeroVal V] [TypedPointsto (GF := GF) V] [IntoValTyped (GF := GF) V t] in
/-- **`Watch`'s `closeCh`** (its loop's state): not made yet, or an SPSC channel of the watch
with both sides at the start (the producer's cursor at `rev - 1`). -/
def closeChRes (o : OpFull) (Q : KVState → IProp GF) (rev : w64) (b : Bool) (cc : Loc) :
    IProp GF :=
  iprop(⌜cc = chan.nil⌝ ∨ ∃ γ : EtcdWatchNames,
    isSpsc γ.spsc cc (outcElem γ o Q) (fun _ => iprop(True)) ∗
    spscProducer γ.spsc ([] : List go_etcd_io.etcd.client.v3.WatchResponse) ∗
    monoListAuthOwn γ.cur 1 [rev - W64 1] ∗
    spscConsumer γ.spsc ([] : List go_etcd_io.etcd.client.v3.WatchResponse) ∗
    monoListIdxOwn γ.cur 0 (rev - W64 1) ∗ ⌜γ.cur2 = γ.cur ∧ γ.cpl = b⌝)

omit [Pos.Countable V] [ZeroVal V] [TypedPointsto (GF := GF) V] [IntoValTyped (GF := GF) V t] in
/-- **A fresh channel as a watch's SPSC channel**, both sides at the start, the producer's cursor
at `rev - 1` (a new mono list). -/
theorem watch_spsc_alloc (o : OpFull) (Q : KVState → IProp GF) (rev : w64)
    (b : Bool) (ch : Loc) (γc : ChanNames) :
    ⊢ isChan ch γc go_etcd_io.etcd.client.v3.WatchResponse -∗
      (ownChan γc go_etcd_io.etcd.client.v3.WatchResponse .Idle ∨
        ownChan γc go_etcd_io.etcd.client.v3.WatchResponse (.Buffered [])) ={⊤}=∗
      ∃ γ : EtcdWatchNames,
        isSpsc γ.spsc ch (outcElem γ o Q) (fun _ => iprop(True)) ∗
        spscProducer γ.spsc ([] : List go_etcd_io.etcd.client.v3.WatchResponse) ∗
        monoListAuthOwn γ.cur 1 [rev - W64 1] ∗
        spscConsumer γ.spsc ([] : List go_etcd_io.etcd.client.v3.WatchResponse) ∗
        monoListIdxOwn γ.cur 0 (rev - W64 1) ∗ monoListIdxOwn γ.cur2 0 (rev - W64 1) ∗
        ⌜γ.cur2 = γ.cur ∧ γ.cpl = b⌝ := by
  iintro #Hch Ho
  imod mono_list_own_alloc [rev - W64 1] with ⟨%γcur, Ha, #Hlb⟩
  imod start_spsc ch (outcElem ⟨⟨γc, 0, 0⟩, γcur, γcur, b⟩ o Q) (fun _ => iprop(True)) γc
    $$ Hch Ho with ⟨%γs, #Hs, Hp, Hc⟩
  imodintro
  iexists ⟨γs, γcur, γcur, b⟩
  iframe Hp Ha Hc
  have heq : outcElem (GF := GF) ⟨⟨γc, 0, 0⟩, γcur, γcur, b⟩ o Q =
      outcElem ⟨γs, γcur, γcur, b⟩ o Q := by unfold outcElem watchStateElem; rfl
  rw [← heq]
  isplitr
  · iexact Hs
  isplitr
  · iapply monoListIdxOwn_get 0 (rev - W64 1) rfl $$ Hlb
  isplitr
  · iapply monoListIdxOwn_get 0 (rev - W64 1) rfl $$ Hlb
  ipureintro; exact ⟨rfl, rfl⟩

omit [Pos.Countable V] [ZeroVal V] [TypedPointsto (GF := GF) V] [IntoValTyped (GF := GF) V t] in
/-- **`Watch`'s result** (D47): a watch's channel of `outcElem` at the names `γ`, the consumer's
side and the second cursor at the start, is the triple's (`watchStateElem`) at `γ` with its second
cursor as the cursor. -/
theorem watch_post (γ : EtcdWatchNames) (o : OpFull) (Q : KVState → IProp GF) (ch : Loc) (rev : w64) :
    isSpsc γ.spsc ch (outcElem γ o Q) (fun _ => iprop(True)) ∗
      spscConsumer γ.spsc ([] : List go_etcd_io.etcd.client.v3.WatchResponse) ∗
      monoListIdxOwn γ.cur2 0 (rev - W64 1) ⊢
    isSpsc ({ γ with cur := γ.cur2 } : EtcdWatchNames).spsc ch
        (watchStateElem { γ with cur := γ.cur2 } o Q iprop(True)) (fun _ => iprop(True)) ∗
      spscConsumer ({ γ with cur := γ.cur2 } : EtcdWatchNames).spsc
        ([] : List go_etcd_io.etcd.client.v3.WatchResponse) ∗
      monoListIdxOwn ({ γ with cur := γ.cur2 } : EtcdWatchNames).cur 0 (rev - W64 1) := by
  iintro ⟨#Hs, Hc, #Hi⟩
  iunfold outcElem at Hs
  iframe Hs Hc Hi

end lemmas

end client
end EtcdGrove
end Perennial
