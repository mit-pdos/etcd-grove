/-
Ported from dsverify-lab examples/swiftpaxos/proof/Spec/swift/Model/Lin.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
L1 (decisions D7, D8; this file: change log C12, notes/prophecy-client.md): the linearization of the
client node's operations, in two independent parts.

1. **The prophecy strategy** (`Strat`, `strat_init`, `strat_step`; proved, purely about
   histories). The client node records its history `H` (invocations and acceptances, in one
   order) and prophesies its future `F` (the node-wide prophecy, resolved at each event). The
   committed prefix `G` is a prefix of a linearization `L` of `H ++ F.take k`, where `k` is the
   longest linearizable window of the prophecy. At an event `e` (the prophecy's head, by
   resolution) the strategy either keeps `L` and commits `L` up to the responding operation
   (helping: every operation it commits was invoked and has not responded), or, when `k = 0`,
   `H ++ [e]` is not linearizable: a contradiction with the protocol's fact below. Nothing about
   the protocol's future is needed: the prophesied values are checked at resolution, and a
   prophecy that is not linearizable ends in a contradiction at its first non-linearizable
   event.

2. **The protocol's fact, about the present** (`HistOk`, `lin_now`). `HistOk N fr h S`: each
   event of the history carries the protocol state at that moment (a snapshot); snapshots grow
   (`PState.le`); an invoked command was not registered before; an accepted one was possibly
   chosen, with its leader's result, at its acceptance; every registered command was invoked.
   `HistOk` is kept by every replica step (`HistOk_mono`: the step only grows the state, the
   step lemmas `le_*`), by a registration (`HistOk_register`) and by the client's events
   (`HistOk_inv`, `HistOk_resp`). `lin_now` (LinWitness.lean): a history with `HistOk` is
   linearizable. This is
   SwiftPaxos's linearizability (a property of the current state and the past snapshots, no
   future); its witness is the top ballot's leader order (puts and accepted gets), sorted by
   real time along conflict chains. Status: `lin_now` is proved from `top_witness` (the protocol
   gives a witness order; proved, the get case of `new_base` in NewBase.lean) and
   `lin_of_witness` (the sort, proved); model-checked as `lin_rt` (etc/modelcheck/check.py).
-/
module

public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.swift.Model
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.swift.Model.Steps

@[expose] public section

noncomputable section

set_option linter.unusedSimpArgs false

namespace Perennial.github_com.imdea_software.swiftpaxos

namespace sp

/-! ## Histories and linearizability -/

/-- An event of the client node: client operation `x` (`c`) invoked, or accepted with result
`v`. -/
inductive Ev where
  | inv (x : CmdId) (c : Cmd)
  | resp (x : CmdId) (v : List w8)
  deriving DecidableEq

/-- The client node's history, oldest first. -/
abbrev Hist := List Ev

/-- Real time: `x` was accepted before `y` was invoked. -/
def Hist.rtBefore (H : Hist) (x y : CmdId) : Prop :=
  ∃ (i j : Nat) (v : List w8) (c : Cmd), i < j ∧ H[i]? = some (Ev.resp x v) ∧
    H[j]? = some (Ev.inv y c)

/-- `L` is a linearization of `H`: distinct invoked operations with their commands, every
accepted operation among them with its result (`resultIn`, the sequential key-value store), in
an order that respects real time. Pending operations may be in `L` or not. -/
structure LinW (H : Hist) (L : Seq) : Prop where
  nodup : (L.map Prod.fst).Nodup
  inv : ∀ p ∈ L, Ev.inv p.1 p.2 ∈ H
  resp : ∀ x v, Ev.resp x v ∈ H → x ∈ L.map Prod.fst ∧ resultIn L x = v
  rt : ∀ x y, x ∈ L.map Prod.fst → y ∈ L.map Prod.fst → H.rtBefore x y →
    precedes (L.map Prod.fst) x y

/-- `H` is linearizable. -/
def Lin (H : Hist) : Prop := ∃ L, LinW H L

theorem Hist.rtBefore_append {H : Hist} (u : Hist) {x y : CmdId} (h : H.rtBefore x y) :
    (H ++ u).rtBefore x y := by
  obtain ⟨i, j, v, c, hij, hi, hj⟩ := h
  have hjl : j < H.length := by
    rcases Nat.lt_or_ge j H.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hj; cases hj
  exact ⟨i, j, v, c, hij, by rw [List.getElem?_append_left (by omega)]; exact hi,
    by rw [List.getElem?_append_left hjl]; exact hj⟩

/-- A linearization of a history is one of its prefixes' (real time only shrinks). -/
theorem LinW.of_append {H u : Hist} {L : Seq} (hL : LinW (H ++ u) L)
    (hinv : ∀ p ∈ L, Ev.inv p.1 p.2 ∈ H) : LinW H L :=
  ⟨hL.nodup, hinv, fun x v h => hL.resp x v (List.mem_append_left _ h),
    fun x y hx hy h => hL.rt x y hx hy (Hist.rtBefore_append u h)⟩

theorem lin_nil : Lin [] :=
  ⟨[], ⟨by simp, by simp, by simp, fun x y hx => by simp at hx⟩⟩

/-! ## Results along a prefix -/

theorem resultIn_append_mem (s u : Seq) (x : CmdId) (h : x ∈ s.map Prod.fst) :
    resultIn (s ++ u) x = resultIn s x := by
  unfold resultIn putsBefore
  obtain ⟨h1, h2⟩ := before_append_of_mem s u x h
  rw [h1, h2]

theorem resultIn_of_prefix {s t : Seq} {x : CmdId} (hst : s <+: t) (h : x ∈ s.map Prod.fst) :
    resultIn t x = resultIn s x := by
  obtain ⟨u, rfl⟩ := hst
  exact resultIn_append_mem s u x h

/-! ## The prophecy strategy -/

/-- The committed prefix `G`, after the history `H`, with the prophesied future `F`: for a
window `k` of `F`, `G` is a prefix of a linearization `L` of `H ++ F.take k`, and the window is
maximal (one more event is not linearizable); every operation accepted in `H` is committed. -/
def Strat (H F : Hist) (G : Seq) : Prop :=
  ∃ k L, k ≤ F.length ∧ LinW (H ++ F.take k) L ∧ G <+: L ∧
    (k < F.length → ¬ Lin (H ++ F.take (k + 1))) ∧
    ∀ x v, Ev.resp x v ∈ H → x ∈ G.map Prod.fst

theorem exists_window_aux (H F : Hist) : ∀ d k, k + d = F.length → Lin (H ++ F.take k) →
    ∃ k', k' ≤ F.length ∧ Lin (H ++ F.take k') ∧
      (k' < F.length → ¬ Lin (H ++ F.take (k' + 1)))
  | 0, k, hd, hk => ⟨k, by omega, hk, fun h => by omega⟩
  | d + 1, k, hd, hk => by
    by_cases h : Lin (H ++ F.take (k + 1))
    · exact exists_window_aux H F d (k + 1) (by omega) h
    · exact ⟨k, by omega, hk, fun _ => h⟩

/-- The longest linearizable window exists (from the empty one). -/
theorem exists_window (H F : Hist) (h0 : Lin H) :
    ∃ k, k ≤ F.length ∧ Lin (H ++ F.take k) ∧ (k < F.length → ¬ Lin (H ++ F.take (k + 1))) :=
  exists_window_aux H F F.length 0 (by omega) (by simpa using h0)

/-- **The start**: no history, nothing committed, any prophecy. -/
theorem strat_init (F : Hist) : Strat [] F [] := by
  obtain ⟨k, hk, ⟨L, hL⟩, hmax⟩ := exists_window [] F lin_nil
  exact ⟨k, L, hk, hL, List.nil_prefix, hmax, fun x v h => by simp at h⟩

theorem mem_take_idxOf {l : List CmdId} {x : CmdId} (h : x ∈ l) : x ∈ l.take (l.idxOf x + 1) := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    by_cases hax : a = x
    · subst hax; simp
    · have hl : x ∈ l := by simp at h; rcases h with h | h; exact absurd h.symm hax; exact h
      have hb : (a == x) = false := by simpa using hax
      rw [List.idxOf_cons, hb]
      simp only [Bool.false_eq_true, ite_false, List.take_succ_cons]
      exact List.mem_cons_of_mem _ (ih hl)

theorem idxOf_lt_of_precedes {O : List CmdId} {a b : CmdId} (h : precedes O a b) :
    O.idxOf a < O.idxOf b := ((precedes_iff O a b).mp h).2

/-- What an event's step commits: `G` grows by `D`, operations invoked by now that had not been
accepted, none committed before. -/
structure StepCommits (H : Hist) (e : Ev) (G D : Seq) : Prop where
  fresh : ∀ p ∈ D, p.1 ∉ G.map Prod.fst
  nodup : (D.map Prod.fst).Nodup
  invoked : ∀ p ∈ D, Ev.inv p.1 p.2 ∈ H ++ [e]
  pending : ∀ p ∈ D, ∀ v, Ev.resp p.1 v ∉ H

/-- **The step** at the event `e` (the prophecy's head, which the resolution says is the actual
event), given that the history with `e` is linearizable (`lin_now`): the committed prefix grows
by operations invoked and not yet accepted, and if `e` accepts `x` with `v`, `x` is committed with
result `v`. -/
theorem strat_step {H F : Hist} {G : Seq} {e : Ev} (hS : Strat H (e :: F) G)
    (hlin : Lin (H ++ [e])) :
    ∃ D, Strat (H ++ [e]) F (G ++ D) ∧ StepCommits H e G D ∧
      ∀ x v, e = .resp x v → x ∈ (G ++ D).map Prod.fst ∧ resultIn (G ++ D) x = v := by
  classical
  obtain ⟨k, L, hk, hL, hGL, hmax, hresp⟩ := hS
  rcases k with _ | k
  · exact absurd (by simpa using hlin) (hmax (by simp))
  -- the same linearization, one event less in the window
  have hwin : H ++ (e :: F).take (k + 1) = (H ++ [e]) ++ F.take k := by simp
  rw [hwin] at hL
  have hkF : k ≤ F.length := by simp at hk; omega
  have hmax' : k < F.length → ¬ Lin ((H ++ [e]) ++ F.take (k + 1)) := fun h => by
    have := hmax (by simp; omega)
    have e2 : H ++ (e :: F).take (k + 1 + 1) = (H ++ [e]) ++ F.take (k + 1) := by simp
    rwa [e2] at this
  obtain ⟨u, rfl⟩ := hGL
  have hndL := hL.nodup
  -- a member of `L` up to an accepted `x` was invoked before `x`'s acceptance
  cases e with
  | inv y c =>
    refine ⟨[], ⟨k, G ++ u, hkF, hL, by simp, hmax', fun x v h => ?_⟩,
      ⟨by simp, by simp, by simp, by simp⟩, fun x v h => by cases h⟩
    simp only [List.mem_append, List.mem_singleton] at h
    rcases h with h | h
    · simpa using hresp x v h
    · cases h
  | resp x v =>
    obtain ⟨hxL, hxv⟩ := hL.resp x v (by simp)
    by_cases hxG : x ∈ G.map Prod.fst
    · refine ⟨[], ⟨k, G ++ u, hkF, hL, by simp, hmax', fun z w h => ?_⟩,
        ⟨by simp, by simp, by simp, by simp⟩, fun x' v' h => ?_⟩
      · simp only [List.mem_append, List.mem_singleton] at h
        rcases h with h | h
        · simpa using hresp z w h
        · cases h; simpa using hxG
      · cases h
        refine ⟨by simpa using hxG, ?_⟩
        rw [List.append_nil, ← resultIn_of_prefix ⟨u, rfl⟩ hxG]; exact hxv
    · -- commit `u` up to `x`
      have hxu : x ∈ u.map Prod.fst := by
        simp only [List.map_append, List.mem_append] at hxL
        exact hxL.resolve_left hxG
      let n := (u.map Prod.fst).idxOf x
      let D := u.take (n + 1)
      have hn : n < u.length := by
        have := List.idxOf_lt_length_of_mem hxu; simpa using this
      have hxD : x ∈ D.map Prod.fst := by
        rw [List.map_take]; exact mem_take_idxOf hxu
      have hDu : D <+: u := List.take_prefix _ _
      have hGD : G ++ D <+: G ++ u := (List.prefix_append_right_inj G).mpr hDu
      refine ⟨D, ⟨k, G ++ u, hkF, hL, hGD, hmax', fun z w h => ?_⟩, ⟨?_, ?_, ?_, ?_⟩,
        fun x' v' h => ?_⟩
      · simp only [List.mem_append, List.mem_singleton] at h
        rcases h with h | h
        · have := hresp z w h; simp only [List.map_append, List.mem_append]; exact Or.inl this
        · cases h; simp only [List.map_append, List.mem_append]; exact Or.inr hxD
      · intro p hp hpG
        have hnd : (G.map Prod.fst ++ D.map Prod.fst).Nodup := by
          have := hndL; rw [List.map_append] at this
          exact (List.nodup_append.mpr ⟨(List.nodup_append.mp this).1,
            ((List.nodup_append.mp this).2.1).sublist (List.map_take ▸ (List.take_sublist _ _)),
            fun a ha b hb => (List.nodup_append.mp this).2.2 a ha b
              (by rw [List.map_take] at hb; exact List.mem_of_mem_take hb)⟩)
        exact (List.nodup_append.mp hnd).2.2 _ hpG _ (List.mem_map_of_mem hp) rfl
      · have := hndL; rw [List.map_append] at this
        rw [List.map_take]
        exact ((List.nodup_append.mp this).2.1).sublist (List.take_sublist _ _)
      · intro p hp
        have hpL : p ∈ G ++ u := List.mem_append_right _ (List.mem_of_mem_take hp)
        have hinv := hL.inv p hpL
        rw [List.mem_append] at hinv
        rcases hinv with hinv | hinv
        · exact hinv
        · -- invoked in the window's future: after `x`'s acceptance, so after `x` in `L`
          exfalso
          obtain ⟨j, hjp⟩ := List.mem_iff_getElem?.mp hinv
          have hrt : ((H ++ [Ev.resp x v]) ++ F.take k).rtBefore x p.1 :=
            ⟨H.length, H.length + 1 + j, v, p.2, by omega,
              by simp,
              by rw [List.getElem?_append_right (by simp)]; simpa using hjp⟩
          have hpre := hL.rt x p.1 hxL (List.mem_map_of_mem hpL) hrt
          have hlt := idxOf_lt_of_precedes hpre
          -- but `p` is in `L` up to `x`
          have hpD : p.1 ∈ D.map Prod.fst := List.mem_map_of_mem hp
          rw [List.map_take] at hpD
          obtain ⟨i, hi, hie⟩ := List.mem_iff_getElem.mp hpD
          simp at hi
          have hi' : i < (u.map Prod.fst).length := by simp; omega
          have hie' : (u.map Prod.fst)[i] = p.1 := by
            rw [← hie]; simp [List.getElem_take]
          have hndu : (u.map Prod.fst).Nodup := by
            have := hndL; rw [List.map_append] at this; exact (List.nodup_append.mp this).2.1
          have hidx : (u.map Prod.fst).idxOf p.1 = i := by
            rw [← hie']; exact List.Nodup.idxOf_getElem hndu i hi'
          have hidxL : ((G ++ u).map Prod.fst).idxOf p.1 = G.length + i := by
            rw [List.map_append, List.idxOf_append, if_neg]
            · simp [hidx]; omega
            · intro hpG
              exact (List.nodup_append.mp (by have := hndL; rwa [List.map_append] at this)).2.2
                _ hpG _ (by rw [← hie']; exact List.getElem_mem _) rfl
          have hidxx : ((G ++ u).map Prod.fst).idxOf x = G.length + n := by
            rw [List.map_append, List.idxOf_append, if_neg hxG]; simp; omega
          omega
      · intro p hp w hw
        have hpu := List.mem_of_mem_take hp
        have := hresp p.1 w hw
        have hnd := hndL; rw [List.map_append] at hnd
        exact (List.nodup_append.mp hnd).2.2 _ this _ (List.mem_map_of_mem hpu) rfl
      · cases h
        have hxGD : x ∈ (G ++ D).map Prod.fst := by
          rw [List.map_append, List.mem_append]; exact Or.inr hxD
        refine ⟨hxGD, ?_⟩
        rw [← resultIn_of_prefix hGD hxGD]
        exact hxv

/-! ## The protocol state only grows -/

namespace PState

/-- `S'` extends `S`: every persistent fact of `S` (a registration, a replica's sequence as a
prefix, an `MSync`, an acceptance, a pre-acceptance, a path, a commit, a report) holds in `S'`.
Every step of the model, under its own premises (the ghost maps' fresh keys), is an extension
(`le_*` below), and so is a registration. -/
structure le (S S' : PState) : Prop where
  cmds : ∀ x c, S.cmds x = some c → S'.cmds x = some c
  loc : ∀ r b, S.loc r b <+: S'.loc r b
  sync : ∀ b M, S.sync b = some M → S'.sync b = some M
  acc : ∀ r b x, S.acc r b x → S'.acc r b x
  pre : ∀ r b x D, S.pre r b x = some D → S'.pre r b x = some D
  path : ∀ r b x P, S.path r b x = some P → S'.path r b x = some P
  com : ∀ r b x, S.com r b x → S'.com r b x
  rep : ∀ r b R, S.rep r b = some R → S'.rep r b = some R

theorem le_refl (S : PState) : S.le S :=
  ⟨fun _ _ h => h, fun _ _ => List.prefix_refl _, fun _ _ h => h, fun _ _ _ h => h,
    fun _ _ _ _ h => h, fun _ _ _ _ h => h, fun _ _ _ h => h, fun _ _ _ h => h⟩

theorem le_trans {S1 S2 S3 : PState} (h1 : S1.le S2) (h2 : S2.le S3) : S1.le S3 :=
  ⟨fun x c h => h2.cmds x c (h1.cmds x c h), fun r b => (h1.loc r b).trans (h2.loc r b),
    fun b M h => h2.sync b M (h1.sync b M h), fun r b x h => h2.acc r b x (h1.acc r b x h),
    fun r b x D h => h2.pre r b x D (h1.pre r b x D h),
    fun r b x P h => h2.path r b x P (h1.path r b x P h),
    fun r b x h => h2.com r b x (h1.com r b x h), fun r b R h => h2.rep r b R (h1.rep r b R h)⟩

variable {S S' : PState} {N : Nat} {fr : Bool}

theorem seqOf_le (hle : S.le S') {l : List CmdId} (hreg : ∀ y ∈ l, S.cmds y ≠ none) :
    S'.seqOf l = S.seqOf l := by
  induction l with
  | nil => rfl
  | cons y l ih =>
    obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.mp (hreg y (List.mem_cons_self ..))
    have ih := ih (fun z hz => hreg z (List.mem_cons_of_mem _ hz))
    unfold seqOf at ih ⊢
    rw [List.filterMap_cons, List.filterMap_cons, hc, hle.cmds y c hc, ih]

theorem ordSeq_le (hI : S.PInv N fr) (hle : S.le S') (b : Nat) :
    S.ordSeq N b <+: S'.ordSeq N b := by
  obtain ⟨t, ht⟩ := hle.loc (leaderOf N b) b
  unfold ordSeq ord
  rw [← ht]
  unfold seqOf
  rw [List.filterMap_append]
  have := seqOf_le hle (l := S.loc (leaderOf N b) b) (hI.loc_ok _ _).2.1
  unfold seqOf at this
  rw [this]
  exact List.prefix_append _ _

theorem base_le (hle : S.le S') (b : Nat) (hs : S.sync b ≠ none) : S'.base b = S.base b := by
  obtain ⟨M, hM⟩ := Option.ne_none_iff_exists'.mp hs
  unfold base; rw [hM, hle.sync b M hM]

/-- A possibly chosen command stays possibly chosen, with the same leader result. -/
theorem possiblyChosen_le (hI : S.PInv N fr) (hle : S.le S') {b : Nat} {x : CmdId}
    (h : S.possiblyChosen N b x) :
    S'.possiblyChosen N b x ∧ resultIn (S'.ordSeq N b) x = resultIn (S.ordSeq N b) x := by
  have hxo := h.1
  have hxs : x ∈ (S.ordSeq N b).map Prod.fst :=
    seqOf_mem_fst S _ x hxo ((hI.loc_ok _ _).2.1 x hxo)
  obtain ⟨u, hu⟩ := ordSeq_le hI hle (N := N) b
  have hdeps : depsIn (S'.ordSeq N b) x = depsIn (S.ordSeq N b) x := by
    rw [← hu]; exact depsIn_append_of_mem _ _ _ hxs
  refine ⟨⟨(hle.loc _ _).subset hxo, ?_, lexec_le' hle.sync hle.pre h.2.2⟩,
    by rw [← hu]; exact resultIn_append_mem _ _ _ hxs⟩
  rcases h.2.1 with ⟨Q, hQ, hacc⟩ | ⟨PL, hPL, hall⟩
  · exact Or.inl ⟨Q, hQ, fun r hr => (hacc r hr).imp_right (hle.acc r b x)⟩
  · refine Or.inr ⟨PL, hle.path _ _ _ _ hPL, fun r hr hrl => ?_⟩
    obtain ⟨D, hD, hDp, hP⟩ := hall r hr hrl
    exact ⟨D, hle.pre _ _ _ _ hD, by rw [hdeps]; exact hDp, hle.path _ _ _ _ hP⟩

/-! ### Every step is an extension -/

theorem le_handle (r b : Nat) (x : CmdId) : S.le (S.handle r b x) := by
  refine ⟨fun _ _ h => h, fun r' b' => ?_, fun _ _ h => h, fun _ _ _ h => h, fun _ _ _ _ h => h,
    fun _ _ _ _ h => h, fun _ _ _ h => h, fun _ _ _ h => h⟩
  obtain ⟨t, ht⟩ := handle_loc (S := S) r b x r' b'
  rw [ht]; exact List.prefix_append _ _

theorem le_accept (r b : Nat) (y : CmdId) : S.le (S.accept r b y) :=
  ⟨fun _ _ h => h, fun _ _ => List.prefix_refl _, fun _ _ h => h, fun _ _ _ h => Or.inl h,
    fun _ _ _ _ h => h, fun _ _ _ _ h => h, fun _ _ _ h => h, fun _ _ _ h => h⟩

theorem le_commit (r b : Nat) (y : CmdId) : S.le (S.commit r b y) :=
  ⟨fun _ _ h => h, fun _ _ => List.prefix_refl _, fun _ _ h => h, fun _ _ _ h => h,
    fun _ _ _ _ h => h, fun _ _ _ _ h => h, fun _ _ _ h => Or.inl h, fun _ _ _ h => h⟩

theorem le_preaccept (r b : Nat) (y : CmdId) (D P : List CmdId) (hpre : S.pre r b y = none)
    (hpath : S.path r b y = none) : S.le (S.preaccept r b y D P) := by
  refine ⟨fun _ _ h => h, fun _ _ => List.prefix_refl _, fun _ _ h => h, fun _ _ _ h => h,
    fun r' b' y' D' h => ?_, fun r' b' y' P' h => ?_, fun _ _ _ h => h, fun _ _ _ h => h⟩
  · show (if r' = r ∧ b' = b ∧ y' = y then some D else S.pre r' b' y') = some D'
    rw [if_neg]; exact h
    rintro ⟨rfl, rfl, rfl⟩; rw [hpre] at h; cases h
  · show (if r' = r ∧ b' = b ∧ y' = y then some P else S.path r' b' y') = some P'
    rw [if_neg]; exact h
    rintro ⟨rfl, rfl, rfl⟩; rw [hpath] at h; cases h

theorem le_newBallot (r b' : Nat) : S.le (S.newBallot r b') :=
  ⟨fun _ _ h => h, fun _ _ => List.prefix_refl _, fun _ _ h => h, fun _ _ _ h => h,
    fun _ _ _ _ h => h, fun _ _ _ _ h => h, fun _ _ _ h => h, fun _ _ _ h => h⟩

theorem le_report (r b' : Nat) (R : Report) (hnone : S.rep r b' = none) :
    S.le (S.report r b' R) := by
  refine ⟨fun _ _ h => h, fun _ _ => List.prefix_refl _, fun _ _ h => h, fun _ _ _ h => h,
    fun _ _ _ _ h => h, fun _ _ _ _ h => h, fun _ _ _ h => h, fun r' b R' h => ?_⟩
  show (if r' = r ∧ b = b' then some R else S.rep r' b) = some R'
  rw [if_neg]; exact h
  rintro ⟨rfl, rfl⟩; rw [hnone] at h; cases h

theorem le_computeSync (b' : Nat) (M : SyncMsg) (hnone : S.sync b' = none)
    (hloc : S.loc (leaderOf N b') b' = []) : S.le (S.computeSync N b' M) := by
  refine ⟨fun _ _ h => h, fun r b => ?_, fun b M' h => ?_, fun _ _ _ h => h,
    fun _ _ _ _ h => h, fun _ _ _ _ h => h, fun _ _ _ h => h, fun _ _ _ h => h⟩
  · show S.loc r b <+: (if r = leaderOf N b' ∧ b = b' then syncOrder M else S.loc r b)
    split
    · rename_i h; obtain ⟨rfl, rfl⟩ := h; rw [hloc]; exact List.nil_prefix
    · exact List.prefix_refl _
  · show (if b = b' then some M else S.sync b) = some M'
    rw [if_neg]; exact h
    rintro rfl; rw [hnone] at h; cases h

/-- `le_computeSync` with its row premise from the invariant (`PInv_computeSync`'s premises). -/
theorem le_computeSync' (hI : S.PInv N fr) (b' : Nat) (M : SyncMsg) (hb : 0 < b')
    (hnone : S.sync b' = none) : S.le (S.computeSync N b' M) := by
  apply le_computeSync b' M hnone
  apply Classical.byContradiction; intro hne
  exact (((hI.loc_ok _ b').2.2 hne).2.2 hb).1 hnone

/-- A state that differs only in the replicas' states is an extension (the switch from
`sp.inv`'s empty disjunct, `PInv_emptyInit`). -/
theorem le_rs (f : Nat → RState) : S.le { S with rs := f } :=
  ⟨fun _ _ h => h, fun _ _ => List.prefix_refl _, fun _ _ h => h, fun _ _ _ h => h,
    fun _ _ _ _ h => h, fun _ _ _ _ h => h, fun _ _ _ h => h, fun _ _ _ h => h⟩

theorem le_takeSync (r b' : Nat) (hloc : S.loc r b' = [] ∨ S.loc r b' = S.base b') :
    S.le (S.takeSync r b') := by
  refine ⟨fun _ _ h => h, fun r' b => ?_, fun _ _ h => h, fun _ _ _ h => Or.inl h,
    fun _ _ _ _ h => h, fun _ _ _ _ h => h, fun _ _ _ h => h, fun _ _ _ h => h⟩
  show S.loc r' b <+: (if r' = r ∧ b = b' then S.base b' else S.loc r' b)
  split
  · rename_i h; obtain ⟨rfl, rfl⟩ := h
    rcases hloc with h | h <;> rw [h]
    · exact List.nil_prefix
    · exact List.prefix_refl _
  · exact List.prefix_refl _

theorem le_register (x : CmdId) (c : Cmd) (hx : S.cmds x = none) : S.le (S.register x c) := by
  refine ⟨fun y c' h => ?_, fun _ _ => List.prefix_refl _, fun _ _ h => h, fun _ _ _ h => h,
    fun _ _ _ _ h => h, fun _ _ _ _ h => h, fun _ _ _ h => h, fun _ _ _ h => h⟩
  show (if y = x then some c else S.cmds y) = some c'
  rw [if_neg]; exact h
  rintro rfl; rw [hx] at h; cases h

end PState

/-! ## The protocol's side: the history with snapshots (`HistOk`) -/

/-- The client node's history, each event with the protocol state at that moment. -/
abbrev SHist := List (Ev × PState)

def SHist.hist (h : SHist) : Hist := h.map Prod.fst

/-- **The history invariant** (a conjunct of `sp.inv`'s body, change log C12), for the protocol
state `S` now: the snapshots grow up to `S`; an operation is invoked before it is registered
(at most once); an accepted operation was possibly chosen at its acceptance, with its leader's
result, after its invocation; every registered command was invoked. -/
structure HistOk (N : Nat) (fr : Bool) (h : SHist) (S : PState) : Prop where
  mono : h.Pairwise (fun a b => a.2.le b.2)
  le_now : ∀ p ∈ h, p.2.le S
  fresh : ∀ x c S', (Ev.inv x c, S') ∈ h → S'.cmds x = none
  inv_once : ∀ (i j : Nat) (x : CmdId) (c c' : Cmd) (S1 S2 : PState),
    h[i]? = some (Ev.inv x c, S1) →
    h[j]? = some (Ev.inv x c', S2) → i = j
  resp : ∀ x v S', (Ev.resp x v, S') ∈ h →
    S'.PInv N fr ∧ ∃ b, S'.possiblyChosen N b x ∧ resultIn (S'.ordSeq N b) x = v
  resp_inv : ∀ (i : Nat) (x : CmdId) (v : List w8) (S' : PState),
    h[i]? = some (Ev.resp x v, S') →
    ∃ (j : Nat) (c : Cmd) (S'' : PState), j < i ∧ h[j]? = some (Ev.inv x c, S'')
  reg : ∀ x c, S.cmds x = some c → Ev.inv x c ∈ SHist.hist h
  /-- the client node invokes puts and gets only (`SendWrite`, `SendRead`) -/
  pg : ∀ x c S', (Ev.inv x c, S') ∈ h → c.isPut = true ∨ c.isGet = true

theorem HistOk.nil (N : Nat) (fr : Bool) (S : PState) (hS : ∀ x, S.cmds x = none) :
    HistOk N fr [] S :=
  ⟨List.Pairwise.nil, by simp, by simp, by simp, by simp, by simp,
    fun x c h => (by rw [hS x] at h; cases h), by simp⟩

/-- **A replica step** (any step of the model: an extension that registers nothing) keeps the
history invariant. This is the replicas' one obligation towards the linearization (MR5). -/
theorem HistOk_mono {N : Nat} {fr : Bool} {h : SHist} {S S' : PState} (hH : HistOk N fr h S)
    (hle : S.le S') (hc : S'.cmds = S.cmds) : HistOk N fr h S' :=
  ⟨hH.mono, fun p hp => PState.le_trans (hH.le_now p hp) hle, hH.fresh, hH.inv_once, hH.resp,
    hH.resp_inv, fun x c h => hH.reg x c (by rw [← hc]; exact h), hH.pg⟩

/-- A client's registration of an invoked command keeps it. -/
theorem HistOk_register {N : Nat} {fr : Bool} {h : SHist} {S : PState} {x : CmdId} {c : Cmd}
    (hH : HistOk N fr h S) (hx : S.cmds x = none) (hinv : Ev.inv x c ∈ SHist.hist h) :
    HistOk N fr h (S.register x c) := by
  refine ⟨hH.mono, fun p hp => PState.le_trans (hH.le_now p hp) (PState.le_register x c hx),
    hH.fresh, hH.inv_once, hH.resp, hH.resp_inv, fun y c' hy => ?_, hH.pg⟩
  by_cases e : y = x
  · subst e
    have : (S.register y c).cmds y = some c := by simp [PState.register]
    rw [this] at hy; cases hy; exact hinv
  · exact hH.reg y c' (by simpa [PState.register, e] using hy)

theorem SHist.mem_hist {h : SHist} {e : Ev} : e ∈ SHist.hist h ↔ ∃ S, (e, S) ∈ h := by
  unfold SHist.hist; simp

/-- **An invocation** (the client's ghost event before it registers the command). -/
theorem HistOk_inv {N : Nat} {fr : Bool} {h : SHist} {S : PState} {x : CmdId} {c : Cmd}
    (hH : HistOk N fr h S) (hx : S.cmds x = none)
    (hnew : ∀ c' S', (Ev.inv x c', S') ∉ h) (hpg : c.isPut = true ∨ c.isGet = true) :
    HistOk N fr (h ++ [(Ev.inv x c, S)]) S := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [List.pairwise_append]
    exact ⟨hH.mono, List.pairwise_singleton _ _, fun a ha b hb => by
      simp at hb; subst hb; exact hH.le_now a ha⟩
  · intro p hp; simp at hp; rcases hp with hp | hp
    · exact hH.le_now p hp
    · subst hp; exact PState.le_refl S
  · intro y c' S' hp; simp at hp; rcases hp with hp | ⟨⟨rfl, rfl⟩, rfl⟩
    · exact hH.fresh y c' S' hp
    · exact hx
  · intro i j y c1 c2 S1 S2 hi hj
    have hlen : ∀ k e, (h ++ [(Ev.inv x c, S)])[k]? = some e →
        (k < h.length ∧ h[k]? = some e) ∨ (k = h.length ∧ e = (Ev.inv x c, S)) := by
      intro k e hk
      rcases Nat.lt_or_ge k h.length with hl | hl
      · left; rw [List.getElem?_append_left hl] at hk; exact ⟨hl, hk⟩
      · right; rw [List.getElem?_append_right hl] at hk
        have : k - h.length = 0 := by
          rcases Nat.eq_zero_or_pos (k - h.length) with e | e
          · exact e
          · rw [List.getElem?_eq_none (by simp; omega)] at hk; cases hk
        rw [this] at hk; simp at hk; exact ⟨by omega, hk.symm⟩
    rcases hlen i _ hi with ⟨hi1, hi2⟩ | ⟨hi1, hi2⟩ <;>
      rcases hlen j _ hj with ⟨hj1, hj2⟩ | ⟨hj1, hj2⟩
    · exact hH.inv_once i j y c1 c2 S1 S2 hi2 hj2
    · simp at hj2; obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hj2
      exact absurd (List.mem_of_getElem? hi2) (hnew _ _)
    · simp at hi2; obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hi2
      exact absurd (List.mem_of_getElem? hj2) (hnew _ _)
    · omega
  · intro y v S' hp; rw [List.mem_append, List.mem_singleton] at hp; rcases hp with hp | hp
    · exact hH.resp y v S' hp
    · simp at hp
  · intro i y v S' hi
    rcases Nat.lt_or_ge i h.length with hl | hl
    · rw [List.getElem?_append_left hl] at hi
      obtain ⟨j, c', S'', hj, hj'⟩ := hH.resp_inv i y v S' hi
      exact ⟨j, c', S'', hj, by rw [List.getElem?_append_left (by omega)]; exact hj'⟩
    · rw [List.getElem?_append_right hl] at hi
      rcases Nat.eq_zero_or_pos (i - h.length) with e | e
      · rw [e] at hi; simp at hi
      · rw [List.getElem?_eq_none (by simp; omega)] at hi; cases hi
  · intro y c' hy
    unfold SHist.hist; rw [List.map_append, List.mem_append]
    exact Or.inl (hH.reg y c' hy)
  · intro y c' S' hp; simp at hp; rcases hp with hp | ⟨⟨rfl, rfl⟩, rfl⟩
    · exact hH.pg y c' S' hp
    · exact hpg

/-- **An acceptance** (the client's ghost event after it got `x`'s result `v`, which a quorum's
messages show possibly chosen with the leader's result: the laws `accept_fast`/`accept_slow`). -/
theorem HistOk_resp {N : Nat} {fr : Bool} {h : SHist} {S : PState} {x : CmdId} {v : List w8}
    {b : Nat} (hH : HistOk N fr h S) (hI : S.PInv N fr) (hpc : S.possiblyChosen N b x)
    (hv : resultIn (S.ordSeq N b) x = v) : HistOk N fr (h ++ [(Ev.resp x v, S)]) S := by
  have hreg : S.cmds x ≠ none := (hI.loc_ok _ _).2.1 x hpc.1
  obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.mp hreg
  obtain ⟨S0, hinv⟩ := SHist.mem_hist.mp (hH.reg x c hc)
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hinv
  have hjl : j < h.length := by
    rcases Nat.lt_or_ge j h.length with e | e
    · exact e
    · rw [List.getElem?_eq_none e] at hj; cases hj
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [List.pairwise_append]
    exact ⟨hH.mono, List.pairwise_singleton _ _, fun a ha b hb => by
      simp at hb; subst hb; exact hH.le_now a ha⟩
  · intro p hp; simp at hp; rcases hp with hp | hp
    · exact hH.le_now p hp
    · subst hp; exact PState.le_refl S
  · intro y c' S' hp; rw [List.mem_append, List.mem_singleton] at hp; rcases hp with hp | hp
    · exact hH.fresh y c' S' hp
    · simp at hp
  · intro i k y c1 c2 S1 S2 hi hk
    have ok : ∀ (m : Nat) (e : Ev × PState), (h ++ [(Ev.resp x v, S)])[m]? = some e →
        (∃ (y : CmdId) (c : Cmd) (S' : PState), e = (Ev.inv y c, S')) →
        h[m]? = some e := by
      intro m e hm he
      rcases Nat.lt_or_ge m h.length with hl | hl
      · rw [List.getElem?_append_left hl] at hm; exact hm
      · rw [List.getElem?_append_right hl] at hm
        rcases Nat.eq_zero_or_pos (m - h.length) with e0 | e0
        · rw [e0] at hm; simp at hm; obtain ⟨_, _, _, rfl⟩ := he; cases hm
        · rw [List.getElem?_eq_none (by simp; omega)] at hm; cases hm
    exact hH.inv_once i k y c1 c2 S1 S2 (ok i _ hi ⟨_, _, _, rfl⟩) (ok k _ hk ⟨_, _, _, rfl⟩)
  · intro y w S' hp; simp at hp; rcases hp with hp | ⟨⟨rfl, rfl⟩, rfl⟩
    · exact hH.resp y w S' hp
    · exact ⟨hI, b, hpc, hv⟩
  · intro i y w S' hi
    rcases Nat.lt_or_ge i h.length with hl | hl
    · rw [List.getElem?_append_left hl] at hi
      obtain ⟨j', c', S'', hj', hj''⟩ := hH.resp_inv i y w S' hi
      exact ⟨j', c', S'', hj', by rw [List.getElem?_append_left (by omega)]; exact hj''⟩
    · rw [List.getElem?_append_right hl] at hi
      rcases Nat.eq_zero_or_pos (i - h.length) with e | e
      · rw [e] at hi; simp at hi; obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hi
        exact ⟨j, c, S0, by omega, by rw [List.getElem?_append_left hjl]; exact hj⟩
      · rw [List.getElem?_eq_none (by simp; omega)] at hi; cases hi
  · intro y c' hy
    unfold SHist.hist; rw [List.map_append, List.mem_append]
    exact Or.inl (hH.reg y c' hy)
  · intro y c' S' hp; rw [List.mem_append, List.mem_singleton] at hp; rcases hp with hp | hp
    · exact hH.pg y c' S' hp
    · simp at hp


end sp

end Perennial.github_com.imdea_software.swiftpaxos

end
