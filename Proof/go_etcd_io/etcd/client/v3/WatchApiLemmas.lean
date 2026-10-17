/-
Lemmas the proofs of `watch.go`'s API (`watcher.Watch`, `Close`, the stream's `close`, ...)
share (the watch slice's unit W-C). Lean-first (no Rocq counterpart).
-/
module

public import Perennial.Golang.Theory.Chan.Idioms.Bag
public import Perennial.Golang.Theory.Chan.Idioms.Broadcast
public import Perennial.Golang.Theory.Chan.Idioms.Spsc
public import Proof.go_etcd_io.etcd.cache.v3.InvEtcdTxn

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace client

open Iris Iris.BI Iris.ProofMode

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
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
accepts) is any position's element of a range watch, the cursor standing still. -/
theorem rangeWatchElem_canceled [EM : EtcdModel GF]
    (γ : EtcdWatchNames) (pfx : GoString) (o : OpFull)
    (rev : w64) (i : Nat) (c : w64) (v : go_etcd_io.etcd.client.v3.WatchResponse)
    (hv : v.Events' = slice.nil ∧ v.CompactRevision' = W64 0 ∧ v.Canceled' = true ∧
      v.Created' = false ∧ v.Header' ≠ null) (hc2 : γ.cpl = false ∨ γ.cur2 = γ.cur) :
    structFieldRef go_etcd_io.etcd.api.v3.etcdserverpb.ResponseHeader go!"Revision" v.Header' ↦□ W64 0 ∗
      go_etcd_io.etcd.cache.v3.statusErrOk v.closeErr' ∗
      monoListIdxOwn γ.cur i c ∗ monoListIdxOwn γ.cur (i + 1) c ⊢
    rangeWatchElem γ pfx o rev (i : Int) v := by
  obtain ⟨he, hc, hca, hcr, hh⟩ := hv
  iintro ⟨#Hrev, #Hse, #Hi, #Hi'⟩
  unfold rangeWatchElem
  iexists { events := [], compactRev := W64 0, canceled := true, created := false, hdrRev := W64 0 }, c, c
  simp only [Int.toNat_natCast]
  iframe #
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
  · unfold watchHdrOwn hdrAt
    simp only [↓reduceIte]
    iright
    iframe #
    ipureintro; exact hh
  isplitr
  · ipureintro; exact ⟨hc, hca, hcr⟩
  isplitr
  · unfold rangeWatchRespOk
    isplitr
    · ipureintro
      refine ⟨List.Pairwise.nil, fun e he => by simp at he, rfl⟩
    iintro !> %j %e %h; simp at h
  rcases hc2 with h2 | h2
  · ileft; ipureintro; exact h2
  iright
  iexists c, c
  rw [h2]
  iframe Hi Hi'
  unfold watchRespOk
  isplitr
  · ipureintro; decide
  ileft
  iframe Hse
  ipureintro
  exact ⟨Or.inr (Or.inr hca), rfl⟩

omit [Pos.Countable V] [ZeroVal V] [TypedPointsto (GF := GF) V] [IntoValTyped (GF := GF) V t] in
/-- **`Watch`'s `closeCh`** (its loop's state): not made yet, or an SPSC channel of the watch
with both sides at the start (the producer's cursor at `rev - 1`). -/
def closeChRes [EM : EtcdModel GF] (pfx : GoString) (o : OpFull) (rev : w64) (cc : Loc) :
    IProp GF :=
  iprop(⌜cc = chan.nil⌝ ∨ ∃ γ : EtcdWatchNames,
    isSpsc γ.spsc cc (rangeWatchElem γ pfx o rev) (fun _ => iprop(True)) ∗
    spscProducer γ.spsc ([] : List go_etcd_io.etcd.client.v3.WatchResponse) ∗
    monoListAuthOwn γ.cur 1 [rev - W64 1] ∗
    spscConsumer γ.spsc ([] : List go_etcd_io.etcd.client.v3.WatchResponse) ∗
    monoListIdxOwn γ.cur 0 (rev - W64 1) ∗ ⌜γ.cur2 = γ.cur⌝)

omit [Pos.Countable V] [ZeroVal V] [TypedPointsto (GF := GF) V] [IntoValTyped (GF := GF) V t] in
/-- **A fresh channel as a watch's SPSC channel**, both sides at the start, the producer's cursor
at `rev - 1` (a new mono list). -/
theorem watch_spsc_alloc [EM : EtcdModel GF] (pfx : GoString) (o : OpFull) (rev : w64)
    (ch : Loc) (γc : ChanNames) :
    ⊢ isChan ch γc go_etcd_io.etcd.client.v3.WatchResponse -∗
      (ownChan γc go_etcd_io.etcd.client.v3.WatchResponse .Idle ∨
        ownChan γc go_etcd_io.etcd.client.v3.WatchResponse (.Buffered [])) ={⊤}=∗
      ∃ γ : EtcdWatchNames,
        isSpsc γ.spsc ch (rangeWatchElem γ pfx o rev) (fun _ => iprop(True)) ∗
        spscProducer γ.spsc ([] : List go_etcd_io.etcd.client.v3.WatchResponse) ∗
        monoListAuthOwn γ.cur 1 [rev - W64 1] ∗
        spscConsumer γ.spsc ([] : List go_etcd_io.etcd.client.v3.WatchResponse) ∗
        monoListIdxOwn γ.cur 0 (rev - W64 1) ∗ ⌜γ.cur2 = γ.cur⌝ := by
  iintro #Hch Ho
  imod mono_list_own_alloc [rev - W64 1] with ⟨%γcur, Ha, #Hlb⟩
  imod start_spsc ch (rangeWatchElem ⟨⟨γc, 0, 0⟩, γcur, γcur, false⟩ pfx o rev) (fun _ => iprop(True)) γc
    $$ Hch Ho with ⟨%γs, #Hs, Hp, Hc⟩
  imodintro
  iexists ⟨γs, γcur, γcur, false⟩
  iframe Hp Ha Hc
  have heq : rangeWatchElem (GF := GF) ⟨⟨γc, 0, 0⟩, γcur, γcur, false⟩ pfx o rev =
      rangeWatchElem ⟨γs, γcur, γcur, false⟩ pfx o rev := by unfold rangeWatchElem; rfl
  rw [← heq]
  isplitr
  · iexact Hs
  isplitr
  · iapply monoListIdxOwn_get 0 (rev - W64 1) rfl $$ Hlb
  ipureintro; rfl

end lemmas

end client
end EtcdGrove
end Perennial
