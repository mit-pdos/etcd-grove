/-
`inv_init`: the start satisfies every conjunct (nothing sent, no event, no instance).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.Model.Proof.Basic

@[expose] public section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos.model

open github_com.imdea_software.swiftpaxos_epaxos.kvs

namespace InitProof

theorem msgs_init (fr to : Nat) : Sys.init.msgs fr to = [] := by
  simp [Sys.msgs, Sys.intended, Sys.init]

theorem ev_init (r : Nat) (e : Event) : ¬ Sys.init.ev r e := by
  simp [Sys.ev, Sys.init]

theorem evBefore_init (r : Nat) (e : Event) (r' : Nat) (e' : Event) :
    ¬ Sys.init.evBefore r e r' e' := by
  simp [Sys.evBefore, Sys.init]

theorem committedVal_init (x : InstId) (v : Val) : ¬ Sys.init.committedVal x v := by
  simp [Sys.committedVal, ev_init, msgs_init]

theorem prepReport_init (r : Nat) (m : PrepareReply) (e : Event) : ¬ Sys.init.prepReport r m e :=
  fun h => ev_init _ _ h.1

theorem slowChosen_init (x : InstId) (b : w32) (v : Val) : ¬ Sys.init.slowChosen x b v := by
  rintro ⟨Q, -, hl, hQ⟩
  have : Q ≠ [] := by intro h; subst h; simp [nR] at hl
  obtain ⟨r, hr⟩ := List.exists_mem_of_ne_nil Q this
  exact ev_init _ _ (hQ r hr).2

theorem fastReplies_init (x : InstId) (v : Val) : ¬ Sys.init.fastReplies x v := by
  rintro ⟨Q, -, hl, hQ⟩
  have : Q ≠ [] := by intro h; subst h; simp [fR] at hl
  obtain ⟨r, hr⟩ := List.exists_mem_of_ne_nil Q this
  obtain ⟨-, -, st, -, h⟩ := hQ r hr
  exact ev_init _ _ h

theorem wf_init : Inv.wf Sys.init := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r _; rfl
  · intro r _ x w h; simp [Sys.init, RState.init] at h
  · intro r _ q _
    simp [Sys.init, RState.init, zz, toN, MAX_INSTANCE]
  · intro r _ q k p h; simp [Sys.init, RState.init] at h
  · intro r _ q _ n hn
    simp [Sys.init, RState.init, zz] at hn
    have : sint.Z (W32 (-1)) = -1 := by decide
    omega
  · intro fr to h; exact absurd (msgs_init fr to) h
  · intro fr to n h; simp [Sys.init] at h
  · intro r b h; simp [Sys.init] at h

end InitProof

open InitProof in
theorem inv0_init' : Inv0 Sys.init := by
  refine ⟨wf_init, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro fr to m hm; simp [msgs_init] at hm
  · intro fr to m x hm; simp [msgs_init] at hm
  · intro fr to m hm; simp [msgs_init] at hm
  · exact ⟨fun r _ x w h => by simp [Sys.init, RState.init] at h,
      fun r _ x b st v h => absurd h (ev_init _ _)⟩
  · refine ⟨fun r x b h => absurd h (ev_init _ _), fun r x b v h => absurd h (ev_init _ _),
      fun r x b v h => absurd h (ev_init _ _), ?_, ?_, ?_⟩ <;>
      intro r to m hm <;> simp [msgs_init] at hm
  · exact ⟨fun r r' x b v v' h => absurd h (ev_init _ _), fun r r' x b v v' h => absurd h (ev_init _ _),
      fun r r' x b v v' h => absurd h (ev_init _ _)⟩
  · exact ⟨fun r x b st v h => absurd h (ev_init _ _), fun r x b v h => absurd h (ev_init _ _)⟩
  · refine ⟨fun r m e h => absurd h (prepReport_init _ _ _), ?_, ?_⟩ <;>
      intro a r m hm <;> simp [msgs_init] at hm
  · intro r m e h; exact absurd h (prepReport_init _ _ _)
  · intro r _ x w lb h; simp [Sys.init, RState.init] at h
  · exact ⟨fun x v v' h => absurd h (committedVal_init _ _),
      fun r _ x w h => by simp [Sys.init, RState.init] at h⟩
  · intro x v h; exact absurd h (committedVal_init _ _)
  · intro x b v h
    rcases h with h | ⟨-, h, -⟩
    · exact absurd h (slowChosen_init _ _ _)
    · exact absurd h (fastReplies_init _ _)
  · intro x y vx vy _ h; exact absurd h (committedVal_init _ _)
  · intro x v h; exact absurd h (committedVal_init _ _)
  · intro r e x cx y cy d _ _ h; exact absurd h (evBefore_init _ _ _ _)
  · intro r _
    refine ⟨by simp [Sys.init], fun x => ?_, fun x w h => by simp [Sys.init, RState.init] at h⟩
    simp [Sys.init, RState.executed, RState.init]
  · intro r _
    exact ⟨fun _ => rfl, fun h => absurd rfl h⟩
  · intro r _ i j x y _ h; simp [Sys.init] at h
  · refine ⟨fun r _ k => ?_, fun r _ k => ?_, fun r _ k pre e post h => ?_⟩
    · simp [Sys.lexec, Sys.curSlots, Sys.slotsOn, Sys.init, Sys.writes]
    · simp [Sys.lexec, Sys.curSlots, Sys.slotsOn, Sys.init, Sys.lastPut, RState.init]
    · simp [Sys.lexec, Sys.curSlots, Sys.slotsOn, Sys.init] at h
  · exact ⟨fun x v h => absurd h (committedVal_init _ _), fun x ps h => by simp [Sys.init] at h⟩
  · refine ⟨by simp [Sys.init], fun k k' e e' p p' h => by simp [Sys.init] at h,
      fun k => by simp [Sys.init], fun k e h => by simp [Sys.init] at h, fun cid o => ?_⟩
    simp [Sys.init]
  · intro fr to m hm; simp [msgs_init] at hm
  · intro r b h; simp [Sys.init] at h
  · exact ⟨fun r x b v h => absurd h (ev_init _ _), fun r x b v h => absurd h (ev_init _ _)⟩
  · refine ⟨fun r m e h => absurd h (prepReport_init _ _ _), fun r m e h => absurd h (prepReport_init _ _ _),
      fun r m e h => absurd h (prepReport_init _ _ _), fun r m e h => absurd h (prepReport_init _ _ _),
      fun r m e _ h => absurd h (prepReport_init _ _ _), fun r x b st st' v v' _ _ h => absurd h (ev_init _ _),
      fun x v m e h => absurd h (ev_init _ _), fun r x v h => absurd h (ev_init _ _),
      fun r m e h => absurd h (prepReport_init _ _ _)⟩

end Perennial.github_com.imdea_software.swiftpaxos_epaxos.model
