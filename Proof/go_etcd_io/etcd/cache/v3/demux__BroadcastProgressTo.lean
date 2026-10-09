/-
Proof of `Spec/demux__BroadcastProgressTo.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.demux__BroadcastProgressTo
public import Spec.go_etcd_io.etcd.cache.v3.watcher__enqueueResponse

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3 go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- A progress notification at `maxRev` to a watcher owed nothing keeps the delivery facts
(next revision unchanged). -/
theorem demuxBPT_progress {pred : Option (GoString → Bool)} {s : w64} {v : View}
    {sent sent' : List RespModel} {ok : Bool} (hD : Delivered pred s v sent)
    (hup : ∀ b ∈ v.stream, sint.Z (batchRev b) < sint.Z v.n)
    (henq : enqueueResult pred (progressResp v.maxRev) sent ok sent') :
    Delivered pred s v sent' := by
  have key : Delivered pred s v (sent ++ [progressResp v.maxRev]) := by
    have hev : ∀ a ∈ sent, ∀ e ∈ a.events, sint.Z e.rev ≤ sint.Z v.maxRev := by
      intro a ha e he
      have h1 : e ∈ eventsOf sent := by
        unfold eventsOf; rw [List.mem_flatten]; exact ⟨a.events, List.mem_map_of_mem ha, he⟩
      rw [hD.events] at h1
      have h2 := (List.mem_filter.1 h1).1
      obtain ⟨b, hb, heb⟩ := List.mem_flatten.1 h2
      have hbs : b ∈ v.stream := (List.mem_filter.1 hb).1
      rw [batchRev_of_mem (hD.stream_ok.batches b hbs) heb]
      exact hD.stream_le b hbs
    refine ⟨hD.stream_ok, hD.stream_le, ?_, ?_, ?_, hD.start_le, hD.near, hD.cancel⟩
    · rw [← hD.events]; simp [eventsOf, progressResp]
    · refine ⟨List.pairwise_append.2 ⟨hD.ordered.1, List.pairwise_singleton _ _, ?_⟩, ?_⟩
      · intro a ha b hb
        rw [List.mem_singleton] at hb; subst hb
        refine ⟨fun _ _ e' he' => by simp [progressResp] at he', fun _ e' he' => by
          simp [progressResp] at he', fun _ e he => hev a ha e he⟩
      · intro r hr
        rcases List.mem_append.1 hr with hr | hr
        · exact hD.ordered.2 r hr
        · rw [List.mem_singleton] at hr; subst hr; simp [progressResp, EvRevSorted]
    · intro r hr hre
      rcases List.mem_append.1 hr with hr | hr
      · exact hD.progress r hr hre
      · rw [List.mem_singleton] at hr; subst hr
        refine ⟨by simp [progressResp], fun b hb hnb => ?_⟩
        have := hup b hb; omega
  unfold enqueueResult at henq
  have hf : filterResp pred (progressResp v.maxRev) = none ∨
      filterResp pred (progressResp v.maxRev) = some (progressResp v.maxRev) := by
    unfold filterResp
    cases pred with
    | none => simp
    | some p =>
      simp only
      split
      · simp
      · left; simp [progressResp]
  rcases hf with hf | hf <;> rw [hf] at henq
  · obtain ⟨-, rfl⟩ := henq; exact hD
  · dsimp only at henq
    split at henq <;> subst henq
    · exact key
    · exact hD

theorem demux.BroadcastProgressTo.wp_proof
    (wp_enqueueResponse : watcher.enqueueResponse.spec (GF := GF) (hG := hG)) :
    demux.BroadcastProgressTo.spec (GF := GF) (hG := hG) := by
  intro d γd cap C w γ predT s
  wp_start as ⟨#Hd, Hh, Htok⟩
  wp_apply wp_with_defer as %defer defer
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  unfold demuxHandle
  wp_apply (lc := 3) sync.RWMutex.wp_RLock $$ [$Hh] as ⟨Hrl, HP⟩
  icombine Hlc1 Hlc2 as Hlc
  imod demux_slot_borrow d γd cap w γ predT s $$ [Hd Htok HP Hlc] with ⟨%pn, %sr, #HpredT, Hr, Hloan⟩
  · iframe; iframe #
  iunfold demuxLoan at Hloan
  icases Hloan with ⟨Hwt, Hel, HR⟩
  iNamed HR
  iNamed Hr
  wp_auto
  wp_if_destruct
  · -- maxRev = 0
    ihave Hr : regRes C γd w (RegInfo.mk γ s pn sr) $$ [Hview Hwat Huniq]
    · iunfold regRes; iexists sent, v, pred; simp only [named]; iframe; iframe #; ipureintro; exact Hdel
    ihave Hloan : demuxLoan d γd cap C w (RegInfo.mk γ s pn sr)
      $$ [Hwt Hel Hcore Hregs Hviews HminRev HmaxRev HactF HlagF Hact Hlag Hhist]
    · iunfold demuxLoan; iframe; iunfold demuxLockRest; iframe; iframe #; ipureintro; exact ⟨Hinv, Hok, Hstart⟩
    imod demux_slot_return d γd cap w γ predT s pn sr $$ [Hd HpredT Hr Hloan Hlc3] with ⟨Htok, HP⟩
    · iframe; iframe #
    wp_apply sync.RWMutex.wp_RUnlock $$ [$Hrl HP] as Hh
    · inext; iexact HP
    iapply HΦ; iframe
  · have Hm0 := Hif
    wp_apply wp_map_lookup2 $$ Hact as Hact
    icombine Hviews Hview gives %Hvw
    rw [Hvw]
    by_cases hact : v.phase = .active
    · simp only [hact, Option.filter, decide_true, ↓reduceIte, Option.map_some, Option.isSome_some]
      wp_auto
      ihave %Hhnn := typedPointsto_not_null $$ «$v0»
      iStructNamed «$v0»
      ipersist Revision
      have Hmp : v.phase.mapped = true := by rw [hact]; rfl
      obtain ⟨Hst, Hmx⟩ := Hok.mapped w v Hvw Hmp
      have Hup : ∀ b ∈ v.stream, sint.Z (batchRev b) < sint.Z v.n := by
        intro b hb
        apply Hok.active_up w v Hvw hact
        rw [List.take_length, ← Hst]; exact hb
      have Hwo : v.phase.toWatcher = .opened := by rw [hact]; rfl
      iunfold RegPhase.toWatcher at Hwat
      iunfold watcherAt at Hwat
      icombine Hregs Hel gives %Hrw
      have Hst0 := Hstart.get Hrw Hvw Hmp
      have hnext : ∀ r', filterResp pred (progressResp c.maxRev) = some r' →
          ∃ n', Delivered pred s { v with n := n' } (sent ++ [r']) := by
        intro r' h
        refine ⟨v.n, ?_⟩
        exact Delivered.enqueue_progress_same Hdel Hup (by rw [Hmx]; exact enqueueResult_some sent h)
      ihave #Hcv : certChain C c.base v.stream $$ []
      · rw [Hst]; iexact Hcerts
      ihave #Hpv : □ C.prog v.maxRev $$ []
      · rw [Hmx]; iexact Hprog
      ihave #Hpub := pub_send pred sr s v sent (progressResp c.maxRev) c.base
        (Hstart.sr_ok w _ Hrw) (Hst0.active hact) hnext $$ Hcv Hpv
      ihave #Hpub' : iprop(□ (∀ r', ⌜filterResp pred (progressResp c.maxRev) = some r'⌝ -∗
          (demuxPub C pred sr).pub none (sent ++ [r']))) $$ []
      · rw [show (demuxPub C pred sr).pub = demuxPubBody C pred sr from rfl]
        imodintro; iexact Hpub
      wp_apply (lc := 1) wp_enqueueResponse w γ pred _ sent _ (progressResp c.maxRev) $$ [Hwat]
        as %ok ⟨%sent', Hwat, %Henq⟩
      · iframe Hw Hwat Hpub'
        unfold respAt eventsAt hdrAt
        isplitl
        · iexists []
          isplitl
          · iapply ownSlice_nil
          isplitl
          · ipureintro; rfl
          imodintro
          iintro %i %ev %e %Hev
          simp at Hev
        isplitl
        · iright
          isplitl
          · ipureintro; exact Hhnn
          dsimp only [progressResp]
          iexact Revision
        ipureintro; exact ⟨rfl, rfl, rfl⟩
      have Hdel' := demuxBPT_progress Hdel Hup (by rw [← Hmx] at Henq; exact Henq)
      ihave Hwat : watcherAt γ sent' v.phase.toWatcher $$ [Hwat]
      · rw [Hwo]; iunfold watcherAt; iexact Hwat
      ihave Hr : regRes C γd w (RegInfo.mk γ s pn sr) $$ [Hview Hwat Huniq]
      · iunfold regRes; iexists sent', v, pred; simp only [named]; iframe; iframe #; ipureintro; exact Hdel'
      ihave Hloan : demuxLoan d γd cap C w (RegInfo.mk γ s pn sr)
        $$ [Hwt Hel Hcore Hregs Hviews HminRev HmaxRev HactF HlagF Hact Hlag Hhist]
      · iunfold demuxLoan; iframe; iunfold demuxLockRest; iframe; iframe #; ipureintro; exact ⟨Hinv, Hok, Hstart⟩
      imod demux_slot_return d γd cap w γ predT s pn sr $$ [Hd HpredT Hr Hloan Hlc3] with ⟨Htok, HP⟩
      · iframe; iframe #
      wp_apply sync.RWMutex.wp_RUnlock $$ [$Hrl HP] as Hh
      · inext; iexact HP
      iapply HΦ; iframe
    · simp only [hact, Option.filter, decide_false]
      wp_auto
      ihave Hr : regRes C γd w (RegInfo.mk γ s pn sr) $$ [Hview Hwat Huniq]
      · iunfold regRes; iexists sent, v, pred; simp only [named]; iframe; iframe #; ipureintro; exact Hdel
      ihave Hloan : demuxLoan d γd cap C w (RegInfo.mk γ s pn sr)
        $$ [Hwt Hel Hcore Hregs Hviews HminRev HmaxRev HactF HlagF Hact Hlag Hhist]
      · iunfold demuxLoan; iframe; iunfold demuxLockRest; iframe; iframe #; ipureintro; exact ⟨Hinv, Hok, Hstart⟩
      imod demux_slot_return d γd cap w γ predT s pn sr $$ [Hd HpredT Hr Hloan Hlc3] with ⟨Htok, HP⟩
      · iframe; iframe #
      wp_apply sync.RWMutex.wp_RUnlock $$ [$Hrl HP] as Hh
      · inext; iexact HP
      iapply HΦ; iframe

end proof

end EtcdGrove
end Perennial
