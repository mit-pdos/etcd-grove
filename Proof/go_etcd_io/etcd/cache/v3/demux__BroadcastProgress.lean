/-
Proof of `Spec/demux__BroadcastProgress.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.demux__BroadcastProgress
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
theorem demuxBP_progress {pred : Option (GoString → Bool)} {s : w64} {v : View}
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

theorem demux.BroadcastProgress.wp_proof
    (wp_enqueueResponse : watcher.enqueueResponse.spec (GF := GF) (hG := hG)) :
    demux.BroadcastProgress.spec (GF := GF) (hG := hG) := by
  intro d γd cap C
  wp_start as ⟨#Hd, Hh⟩
  wp_apply wp_with_defer as %defer defer
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  unfold demuxHandle
  wp_apply (lc := 3) sync.RWMutex.wp_Lock $$ [$Hh] as ⟨Hlk, HP⟩
  icombine Hlc1 Hlc2 as Hlc
  imod demux_lock_acquire d γd cap $$ [Hd HP Hlc] with ⟨%c, %regs, %views, Hcore, Hl, %Hinv⟩
  · iframe; iframe #
  iNamed Hl
  wp_auto
  wp_if_destruct
  · -- maxRev = 0
    ihave Hl : demuxLocked d γd cap C c c.stream.length regs views
      $$ [Hregs Hviews HminRev HmaxRev HactF HlagF Hact Hlag Hhist Hres]
    · iunfold demuxLocked; iexists actP, lagP; simp only [named]; iframe; iframe #; ipureintro; exact ⟨Hok, Hstart⟩
    imod demux_lock_release d γd cap c _ _ $$ [Hd Hcore Hl Hlc3] with HP
    · iframe; iframe #; ipureintro; exact Hinv
    wp_apply sync.RWMutex.wp_Unlock $$ [$Hlk HP] as Hh
    · inext; iexact HP
    iapply HΦ; iframe
  · ihave %Hhnn := typedPointsto_not_null $$ «$v0»
    iStructNamed «$v0»
    ipersist Revision
    ipersist resp
    ihave #Hrespat : respAt (go_etcd_io.etcd.client.v3.WatchResponse.mk «$v0_ptr» slice.nil 0 false
        false GoInterface.nil []) (progressResp c.maxRev) $$ []
    · unfold respAt eventsAt hdrAt
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
    wp_func_lits
    wp_bind (App (App (Val (map.forRange _ _)) _) _)
    iapply wp_map_for_range (fun (_ : List Loc) (_ : Int) => iprop(∃ x : Loc,
        "w" ∷ w_ptr ↦ x ∗
        "Hviews" ∷ ghostMapAuth γd.views 1 views ∗
        "Hres" ∷ ([∗map] w ↦ ri ∈ regs, regRes C γd w ri))) $$ Hact
    iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
    isplitl [w Hviews Hres]
    · iexists _; iframe
    isplitr
    · imodintro
      iintro %i %key %vv ⟨%Hkey, %Hvv⟩ HP
      iNamed HP
      wp_auto
      rw [actOf_lookup] at Hvv
      obtain ⟨v0, Hv0, Hact0⟩ : ∃ v0, views !! key = some v0 ∧ v0.phase = .active := by
        cases h : views !! key with
        | none => rw [h] at Hvv; cases Hvv
        | some v0 =>
          rw [h] at Hvv
          refine ⟨v0, rfl, ?_⟩
          by_cases hne : v0.phase = .active
          · exact hne
          · simp [hne] at Hvv
      obtain ⟨ri, Hri⟩ : ∃ ri, regs !! key = some ri := by
        have := Hok.dom key; rw [Hv0] at this
        cases h : regs !! key with
        | none => rw [h] at this; cases this
        | some ri => exact ⟨ri, rfl⟩
      icases (BigSepM.bigSepM_delete (m := regs) Hri).1 $$ Hres with ⟨Hr, Hres⟩
      iNamed Hr
      icombine Hviews Hview gives %Hv'
      rw [Hv0] at Hv'
      cases Hv'
      have Hmp : v0.phase.mapped = true := by rw [Hact0]; rfl
      obtain ⟨Hst, Hmx⟩ := Hok.mapped key v0 Hv0 Hmp
      have Hup : ∀ b ∈ v0.stream, sint.Z (batchRev b) < sint.Z v0.n := by
        intro b hb
        apply Hok.active_up key v0 Hv0 Hact0
        rw [List.take_length, ← Hst]; exact hb
      have Hwo : v0.phase.toWatcher = .opened := by rw [Hact0]; rfl
      ihave Hwat' : watcherAt ri.γ sent .opened $$ [Hwat]
      · rw [← Hwo]; iexact Hwat
      iunfold watcherAt at Hwat'
      have Hst0 := Hstart.get Hri Hv0 Hmp
      have hnext : ∀ r', filterResp pred (progressResp c.maxRev) = some r' →
          ∃ n', Delivered pred ri.s { v0 with n := n' } (sent ++ [r']) := by
        intro r' h
        refine ⟨v0.n, ?_⟩
        exact Delivered.enqueue_progress_same Hdel Hup (by rw [Hmx]; exact enqueueResult_some sent h)
      ihave #Hcv : certChain C c.base v0.stream $$ []
      · rw [Hst]; iexact Hcerts
      ihave #Hpub := pub_send pred ri.sr ri.s v0 sent (progressResp c.maxRev) c.base
        (Hstart.sr_ok key ri Hri) (Hst0.active Hact0) hnext $$ Hcv
      ihave #Hpub' : iprop(□ (∀ r', ⌜filterResp pred (progressResp c.maxRev) = some r'⌝ -∗
          (demuxPub C pred ri.sr).pub none (sent ++ [r']))) $$ []
      · rw [show (demuxPub C pred ri.sr).pub = demuxPubBody C pred ri.sr from rfl]
        imodintro; iexact Hpub
      wp_apply wp_enqueueResponse key ri.γ pred _ sent _ (progressResp c.maxRev) $$ [Hwat']
        as %ok ⟨%sent', Hwat, %Henq⟩
      · iframe Hw Hwat' Hpub'; iexact Hrespat
      have Hdel' := demuxBP_progress Hdel Hup (by rw [← Hmx] at Henq; exact Henq)
      unfold forMapPostcondition
      iright; ileft
      isplitr
      · ipureintro; rfl
      iexists key
      iframe
      iapply (BigSepM.bigSepM_delete (m := regs) Hri).2
      iframe Hres
      iunfold regRes
      iexists sent', v0, pred
      simp only [named]
      iframe; iframe #
      isplitl
      · rw [Hwo]; iunfold watcherAt; iexact Hwat
      ipureintro; exact Hdel'
    iintro HP Hact
    iNamed HP
    wp_auto
    ihave Hl : demuxLocked d γd cap C c c.stream.length regs views
      $$ [Hregs Hviews HminRev HmaxRev HactF HlagF Hact Hlag Hhist Hres]
    · iunfold demuxLocked; iexists actP, lagP; simp only [named]; iframe; iframe #; ipureintro; exact ⟨Hok, Hstart⟩
    imod demux_lock_release d γd cap c _ _ $$ [Hd Hcore Hl Hlc3] with HP
    · iframe; iframe #; ipureintro; exact Hinv
    wp_apply sync.RWMutex.wp_Unlock $$ [$Hlk HP] as Hh
    · inext; iexact HP
    iapply HΦ; iframe

end proof

end EtcdGrove
end Perennial
