/-
The stream's close of its channel, from the store's channel invariant (`InvWatchStore.lean`):
the triple `isWatchStream`'s `Hclose` asks of the store (`storeWatchParams`). Lean-first.

With the close right (`CR`: the stream's half of the registered watchers `L`) and every
registered watcher cancelled (`WC`), the channel is not closed yet (a closed channel's invariant
holds the close right's half: `Hcl`), so `close` succeeds; the invariant then holds the closed
state, every registered watcher's entry cancelled, and the close right's half.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvWatchStore

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- A cancelled watcher's entry holds in a closed channel. -/
theorem chanWatcher_close (γ : WsNames) (γc : WatchChanNames) (b : Bool) (sent : List RespM)
    (w : Loc) (γw' : WatcherNames) :
    chanWatcher (GF := GF) γ γc b sent w ∗ watcherMeta γ w γw' ∗ cancelled γw' ⊢
      chanWatcher γ γc true sent w := by
  unfold chanWatcher
  iintro ⟨⟨%γw, %r, %fcs, %evsw, %D, %d, #Hm, %Hγc, #Hf, Hevs, %HD, #HDs, #Hwf, Hlive⟩, #Hm', #Hc⟩
  unfold watcherMeta
  ihave %Heq := ghostMapElem_agree w γ.wmeta _ _ _ _ $$ Hm Hm'
  subst Heq
  iexists γw, r, fcs, evsw, D, d
  iframe Hm Hf Hevs HDs Hwf
  isplitr
  · ipureintro; exact Hγc
  isplitr
  · ipureintro; exact HD
  iright
  icases Hlive with (⟨-, Hl⟩ | #Hc0)
  · unfold cancelled
    ihave %H := dghostVar_agree _ _ _ _ _ $$ Hl Hc
    cases H
  · iexact Hc0

theorem chanWatchers_close (γ : WsNames) (γc : WatchChanNames) (b : Bool) (sent : List RespM)
    (L : List Loc) :
    ([∗list] w ∈ L, chanWatcher (GF := GF) γ γc b sent w) ∗
      □ (∀ w : Loc, ⌜w ∈ L⌝ -∗ ∃ γw : WatcherNames, watcherMeta γ w γw ∗ cancelled γw) ⊢
      [∗list] w ∈ L, chanWatcher γ γc true sent w := by
  iintro ⟨H, #HWC⟩
  iapply (BigSepL.bigSepL_impl (Φ := fun _ w => chanWatcher (GF := GF) γ γc b sent w)) $$ H
  imodintro
  iintro %k %w %Hk Hw
  icases HWC $$ %w %(List.mem_of_getElem? Hk) with ⟨%γw', #Hm, #Hc⟩
  iapply chanWatcher_close $$ [$Hw $Hm $Hc]

/-- **The stream's close of its channel** (`isWatchStream`'s `Hclose`, for the store's
`storeWatchParams`). -/
theorem wp_watch_close (s st : Loc) (γ : WsNames) (ch : Loc) (L : List Loc) :
    {{ (storeWatchParams (GF := GF) s st γ).CR ch L ∗
        □ (∀ w : Loc, ⌜w ∈ L⌝ -∗ (storeWatchParams (GF := GF) s st γ).WC w) }}
      (App (Val #(functions go.close
        [go.GoType.ChannelType go.ChanDir.sendrecv WatchResponse.ty])) (Val #ch))
    {{ RET #(); True }} := by
  wp_start_folded as ⟨HCR, #HWC⟩
  simp only [storeWatchParams]
  icases HCR with ⟨%γc, #Hch, #Hinv, Hregl0⟩
  iapply (chan.wp_close (V := WatchResponse) ch γc.ch) $$ Hch
  iintro -
  unfold closeAu
  iinv Hinv with Hi Hclose
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  unfold watchChanInv
  iNamed Hi
  ihave %Hag := ghostVar_valid_2 γc.regl _ _ _ _ $$ Hregl0 Hregl
  obtain ⟨-, HL⟩ := Hag
  subst HL
  iexists s
  iframe Hch
  rcases s with (_ | ⟨b0, bs⟩) | _ | _ | _ | _ | _ | (_ | ⟨b0, bs⟩)
  all_goals dsimp only
  case SndPending => itrivial
  case RcvPending => itrivial
  case SndCommit => itrivial
  case RcvCommit => itrivial
  case Closed.nil =>
    simp only [chanIsClosed, ↓reduceIte]
    icombine Hregl0 Hregl as H2
    ihave %Hv := ghostVar_valid_2 γc.regl _ _ _ _ $$ H2 Hcl
    exfalso
    obtain ⟨Hv, -⟩ := Hv
    simp only [Qp.le_iff, Qp.val_add, Qp.val_one, Qp.val_half] at Hv
    grind
  case Closed.cons =>
    simp only [chanIsClosed, ↓reduceIte]
    icombine Hregl0 Hregl as H2
    ihave %Hv := ghostVar_valid_2 γc.regl _ _ _ _ $$ H2 Hcl
    exfalso
    obtain ⟨Hv, -⟩ := Hv
    simp only [Qp.le_iff, Qp.val_add, Qp.val_one, Qp.val_half] at Hv
    grind
  all_goals
    iintro Hch
    ihave Hws := chanWatchers_close γ γc _ sent L $$ [$Hws $HWC]
    imod Hmask with -
    imod Hclose $$ [Hch Hrecv Hregl Hregl0 Hreg Hws] with -
    · inext
      iexists _, sent, recv, vs, L
      simp only [named]
      iframe Hch
      simp only [chanIsClosed, ↓reduceIte]
      iframe Hrecv Hregl Hregl0 Hreg Hws
      iframe #
      ipureintro
      simp_all [chanInflight]
    imodintro
    iapply HΦ
    itrivial

end proof

end mvcc
end EtcdGrove
end Perennial
