/-
Ported from dsverify-lab examples/swiftpaxos/proof/Spec/swift/Model/Trace.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
L2 (notes/l2-design.md §5, notes/prove-s2-d.md): the predicted nodes' events as steps of the
protocol state, and their **locality** (risk R1).

* `Nd`: a predicted node (`cl k`: client node `k`, whose commands are those with `clOf x = k`;
  `rep r`: replica `r`), the same shape as `Inv.lean`'s `PNode`.
* `PEv`: a node's event. A replica's: its PState steps (`handle`, `preaccept` (the path is not
  predicted: the cut uses the canonical `keyPrefix`), `accept`, `commit`, `newBallot`, `report`,
  `computeSync` (with the reporters' ids, in the order `recoverSync` takes them), `takeSync`). A
  client's: `inv x c` (registers `x`), `resp x v` (no effect on the protocol state).
* `okE N S n e`: the event's guard in the cut (the premises of its `PInv_*` lemma and the fresh
  keys of its `le_*` lemma); for `resp`, `True` (notes/prove-s2-d.md: the real acceptance keeps
  its real guard, `possiblyChosen`, which reads paths; the cut must not). `apE N S n e`: its
  effect.
* The slices: `Agree N n S T` (node `n`'s part of the state is the same in `S` and `T`). An event
  changes only its node's slice (`apE_frame`); its guard holds in any extension with the same
  slice (`okE_mono`: **every premise is monotone under the other nodes' events**), and its effect
  on the slice is the same there (`apE_agree`). Hence `diamond`: two different nodes' events
  commute (`Cut.Diamond` with the invariant `PInv`).
* The real pre-acceptance's path (`apR`, `setPath`): it changes no guard and commutes with every
  event (`setPath_okE`, `setPath_apE`).
-/
module

public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.swift.Model.Lin
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.swift.Model.Cut

@[expose] public section

noncomputable section

set_option linter.unusedSimpArgs false

namespace Perennial.github_com.imdea_software.swiftpaxos

namespace sp

/-- A predicted node: client node `k`, replica `r`. -/
inductive Nd where
  | cl (k : Nat)
  | rep (r : Nat)
  deriving DecidableEq

/-- The client node of a command (client node `k` has client id `k + 1`). -/
def clOf (x : CmdId) : Nat := x.cl.toNat - 1

/-- A predicted event. -/
inductive PEv where
  | handle (b : Nat) (x : CmdId) (c : Cmd)
  | preaccept (b : Nat) (y : CmdId) (D : List CmdId)
  | accept (b : Nat) (y : CmdId)
  | commit (b : Nat) (y : CmdId)
  | newBallot (b' : Nat)
  | report (b' : Nat) (R : Report)
  | computeSync (b' : Nat) (ids : List Nat)
  | takeSync (b' : Nat)
  | inv (x : CmdId) (c : Cmd)
  | resp (x : CmdId) (v : List w8)

/-- The reports of `ids` for `b'` (`computeSync`'s input). -/
def repsOf (S : PState) (b' : Nat) (ids : List Nat) : List (Nat × Report) :=
  ids.filterMap (fun p => (S.rep p b').map (p, ·))

/-- An event's guard in the cut. -/
def okE (N : Nat) (S : PState) : Nd → PEv → Prop
  | .rep r, .handle b x c => S.cmds x = some c ∧ x ∉ S.loc r b ∧ r < N ∧ (S.rs r).ballot = b ∧
      (b > 0 → S.sync b ≠ none ∧ S.base b <+: S.loc r b)
  | .rep r, .preaccept b y D => r ∈ AQ N b ∧ (S.rs r).ballot = b ∧ y ∈ S.loc r b ∧
      D = depsIn (S.seqOf (S.loc r b)) y ∧ y ∉ S.base b ∧ S.pre r b y = none ∧
      S.path r b y = none
  | .rep r, .accept b y => r < N ∧ (S.rs r).ballot = b ∧ y ∈ S.loc r b ∧ y ∈ S.ord N b ∧
      (r ≠ leaderOf N b → ∀ d ∈ depsIn (S.ordSeq N b) y, S.acc r b d ∨ S.com r b d)
  | .rep r, .commit b y => r < N ∧ (S.rs r).ballot = b ∧ y ∈ S.loc r b ∧
      (r = leaderOf N b ∨ S.acc r b y ∨ y ∈ S.base b)
  | .rep r, .newBallot b' => (S.rs r).ballot ≤ b'
  | .rep r, .report b' R => S.rep r b' = none ∧ S.repOk N r b' R
  | .rep r, .computeSync b' ids => r = leaderOf N b' ∧ 0 < b' ∧ S.sync b' = none ∧
      (S.rs r).ballot = b' ∧ ¬ (S.rs r).normal ∧ isMajority N ids ∧ ∀ p ∈ ids, S.rep p b' ≠ none
  | .rep r, .takeSync b' => r < N ∧ S.sync b' ≠ none ∧ (S.rs r).ballot ≤ b' ∧
      (S.loc r b' = [] ∨ S.loc r b' = S.base b')
  | .cl k, .inv x c => S.cmds x = none ∧ clOf x = k ∧ (c.isPut = true ∨ c.isGet = true)
  | .cl _, .resp _ _ => True
  | _, _ => False

/-- An event's effect (a predicted pre-acceptance with the canonical path). -/
def apE (N : Nat) (S : PState) : Nd → PEv → PState
  | .rep r, .handle b x _ => S.handle r b x
  | .rep r, .preaccept b y D => S.preaccept r b y D (S.keyPrefix r b y)
  | .rep r, .accept b y => S.accept r b y
  | .rep r, .commit b y => S.commit r b y
  | .rep r, .newBallot b' => S.newBallot r b'
  | .rep r, .report b' R => S.report r b' R
  | .rep _, .computeSync b' ids => S.computeSync N b' (recoverSync N (repsOf S b' ids))
  | .rep r, .takeSync b' => S.takeSync r b'
  | .cl _, .inv x c => S.register x c
  | _, _ => S

/-- The real effect: a pre-acceptance with the path `P` the replica sent; every other event as
predicted. -/
def apR (N : Nat) (S : PState) (n : Nd) (e : PEv) (P : List CmdId) : PState :=
  match n, e with
  | .rep r, .preaccept b y D => S.preaccept r b y D P
  | n, e => apE N S n e

/-- The real guard of a replica event: `okE`, and for a pre-acceptance the path premises of
`PInv_preaccept` for `P`. -/
def okR (N : Nat) (S : PState) (n : Nd) (e : PEv) (P : List CmdId) : Prop :=
  okE N S n e ∧ match n, e with
    | .rep r, .preaccept b y _ => P.getLast? = some y ∧
        (r = leaderOf N b → P = S.keyPrefix r b y) ∧ (∀ z ∈ S.keyPrefix r b y, z ∈ P)
    | _, _ => True

/-! ## Slices -/

/-- Replica `r`'s slice is the same in `S` and `T` (its rows, its state, the `MSync`s of the
ballots it leads). -/
structure AgreeR (N r : Nat) (S T : PState) : Prop where
  loc : S.loc r = T.loc r
  sync : ∀ b, leaderOf N b = r → S.sync b = T.sync b
  rs : S.rs r = T.rs r
  acc : S.acc r = T.acc r
  pre : S.pre r = T.pre r
  path : S.path r = T.path r
  com : S.com r = T.com r
  rep : S.rep r = T.rep r

/-- Node `n`'s slice is the same in `S` and `T` (a client's: the registrations of its
commands). -/
def Agree (N : Nat) : Nd → PState → PState → Prop
  | .cl k, S, T => ∀ x, clOf x = k → S.cmds x = T.cmds x
  | .rep r, S, T => AgreeR N r S T

/-- `T` differs from `S` only in node `n`'s slice. -/
def Frame (N : Nat) (n : Nd) (S T : PState) : Prop :=
  (∀ m, m ≠ n → Agree N m S T) ∧ S.G = T.G

theorem Agree.refl (N : Nat) (n : Nd) (S : PState) : Agree N n S S := by
  cases n with
  | cl k => exact fun _ _ => rfl
  | rep r => exact ⟨rfl, fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem Agree.symm {N : Nat} {n : Nd} {S T : PState} (h : Agree N n S T) : Agree N n T S := by
  cases n with
  | cl k => exact fun x hx => (h x hx).symm
  | rep r =>
    obtain ⟨a, b, c, d, e, f, g, i⟩ := h
    exact ⟨a.symm, fun x hx => (b x hx).symm, c.symm, d.symm, e.symm, f.symm, g.symm, i.symm⟩

theorem Agree.trans {N : Nat} {n : Nd} {S T U : PState} (h1 : Agree N n S T)
    (h2 : Agree N n T U) : Agree N n S U := by
  cases n with
  | cl k => exact fun x hx => (h1 x hx).trans (h2 x hx)
  | rep r =>
    obtain ⟨a, b, c, d, e, f, g, i⟩ := h1
    obtain ⟨a', b', c', d', e', f', g', i'⟩ := h2
    exact ⟨a.trans a', fun x hx => (b x hx).trans (b' x hx), c.trans c', d.trans d', e.trans e',
      f.trans f', g.trans g', i.trans i'⟩

/-- Two states with every slice and `G` the same are equal. -/
theorem PState.eq_of_agree {N : Nat} {S T : PState} (h : ∀ n, Agree N n S T) (hG : S.G = T.G) :
    S = T := by
  have hc : S.cmds = T.cmds := funext fun x => h (.cl (clOf x)) x rfl
  have hr : ∀ r, AgreeR N r S T := fun r => h (.rep r)
  obtain ⟨c1, l1, s1, rs1, a1, p1, pa1, co1, re1, G1⟩ := S
  obtain ⟨c2, l2, s2, rs2, a2, p2, pa2, co2, re2, G2⟩ := T
  simp only at hc hG
  subst hc hG
  have el : l1 = l2 := funext fun r => (hr r).loc
  have es : s1 = s2 := funext fun b => (hr (leaderOf N b)).sync b rfl
  have ers : rs1 = rs2 := funext fun r => (hr r).rs
  have ea : a1 = a2 := funext fun r => (hr r).acc
  have ep : p1 = p2 := funext fun r => (hr r).pre
  have epa : pa1 = pa2 := funext fun r => (hr r).path
  have eco : co1 = co2 := funext fun r => (hr r).com
  have ere : re1 = re2 := funext fun r => (hr r).rep
  subst el es ers ea ep epa eco ere
  rfl

/-! ## Each event changes only its node's slice -/

section frame
variable {S : PState} {N r r' : Nat}

theorem cmds_agree_cl (k : Nat) {T : PState} (h : S.cmds = T.cmds) : Agree N (.cl k) S T :=
  fun x _ => congrFun h x

theorem handle_agreeR (h : r' ≠ r) (b : Nat) (x : CmdId) : AgreeR N r' S (S.handle r b x) := by
  refine ⟨?_, fun _ _ => rfl, ?_, rfl, rfl, rfl, rfl, rfl⟩
  · funext b'; simp [PState.handle, h]
  · simp only [PState.handle, h, if_false]

theorem accept_agreeR (h : r' ≠ r) (b : Nat) (y : CmdId) : AgreeR N r' S (S.accept r b y) := by
  refine ⟨rfl, fun _ _ => rfl, ?_, ?_, rfl, rfl, rfl, rfl⟩
  · simp only [PState.accept, h, if_false]
  · funext b' y'; simp [PState.accept, h]

theorem commit_agreeR (h : r' ≠ r) (b : Nat) (y : CmdId) : AgreeR N r' S (S.commit r b y) := by
  refine ⟨rfl, fun _ _ => rfl, ?_, rfl, rfl, rfl, ?_, rfl⟩
  · simp only [PState.commit, h, if_false]
  · funext b' y'; simp [PState.commit, h]

theorem preaccept_agreeR (h : r' ≠ r) (b : Nat) (y : CmdId) (D P : List CmdId) :
    AgreeR N r' S (S.preaccept r b y D P) := by
  refine ⟨rfl, fun _ _ => rfl, ?_, rfl, ?_, ?_, rfl, rfl⟩
  · simp only [PState.preaccept, h, if_false]
  · funext b' y'; simp [PState.preaccept, h]
  · funext b' y'; simp [PState.preaccept, h]

theorem newBallot_agreeR (h : r' ≠ r) (b' : Nat) : AgreeR N r' S (S.newBallot r b') := by
  refine ⟨rfl, fun _ _ => rfl, ?_, rfl, rfl, rfl, rfl, rfl⟩
  simp only [PState.newBallot, h, if_false]

theorem report_agreeR (h : r' ≠ r) (b' : Nat) (R : Report) : AgreeR N r' S (S.report r b' R) := by
  refine ⟨rfl, fun _ _ => rfl, ?_, rfl, rfl, rfl, rfl, ?_⟩
  · simp only [PState.report, h, if_false]
  · funext b; simp [PState.report, h]

theorem computeSync_agreeR (h : r' ≠ leaderOf N b') (M : SyncMsg) :
    AgreeR N r' S (S.computeSync N b' M) := by
  refine ⟨?_, fun b hb => ?_, ?_, rfl, rfl, rfl, rfl, rfl⟩
  · funext b; simp [PState.computeSync, h]
  · have : b ≠ b' := by rintro rfl; exact h hb.symm
    simp [PState.computeSync, this]
  · simp only [PState.computeSync, h, if_false]

theorem takeSync_agreeR (h : r' ≠ r) (b' : Nat) : AgreeR N r' S (S.takeSync r b') := by
  refine ⟨?_, fun _ _ => rfl, ?_, ?_, rfl, rfl, rfl, rfl⟩
  · funext b; simp [PState.takeSync, h]
  · simp only [PState.takeSync, h, if_false]
  · funext b x; simp [PState.takeSync, h]

theorem register_agreeR (x : CmdId) (c : Cmd) : AgreeR N r' S (S.register x c) :=
  ⟨rfl, fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end frame

/-- **An event changes only its node's slice.** -/
theorem apE_frame {N : Nat} {S : PState} {n : Nd} {e : PEv} (hok : okE N S n e) :
    Frame N n S (apE N S n e) := by
  refine ⟨fun m hm => ?_, ?_⟩
  · cases n with
    | rep r =>
      cases m with
      | cl k =>
        cases e <;> first
          | exact cmds_agree_cl k rfl
          | exact hok.elim
      | rep r' =>
        have h : r' ≠ r := fun e => hm (by rw [e])
        cases e with
        | handle b x c => exact handle_agreeR h b x
        | preaccept b y D => exact preaccept_agreeR h b y D _
        | accept b y => exact accept_agreeR h b y
        | commit b y => exact commit_agreeR h b y
        | newBallot b' => exact newBallot_agreeR h b'
        | report b' R => exact report_agreeR h b' R
        | computeSync b' ids => exact computeSync_agreeR (by rw [← hok.1]; exact h) _
        | takeSync b' => exact takeSync_agreeR h b'
        | inv x c => exact hok.elim
        | resp x v => exact hok.elim
    | cl k =>
      cases e with
      | inv x c =>
        cases m with
        | cl k' =>
          intro y hy
          have : y ≠ x := by
            rintro rfl; exact hm (by rw [← hy, hok.2.1])
          simp [apE, PState.register, this]
        | rep r' => exact register_agreeR x c
      | resp x v => exact Agree.refl N m S
      | _ => exact hok.elim
  · cases n <;> cases e <;> rfl

/-! ## The guards are monotone (R1) -/

section mono
variable {S T : PState} {N : Nat} {fr : Bool}

theorem ord_le (hle : S.le T) {b : Nat} {y : CmdId} (h : y ∈ S.ord N b) : y ∈ T.ord N b :=
  (hle.loc _ _).subset h

theorem depsIn_ord_le (hI : S.PInv N fr) (hle : S.le T) {b : Nat} {y : CmdId}
    (hy : y ∈ S.ord N b) : depsIn (T.ordSeq N b) y = depsIn (S.ordSeq N b) y := by
  have hys : y ∈ (S.ordSeq N b).map Prod.fst :=
    seqOf_mem_fst S _ y hy ((hI.loc_ok _ _).2.1 y hy)
  obtain ⟨u, hu⟩ := PState.ordSeq_le hI hle (N := N) b
  rw [← hu]; exact depsIn_append_of_mem _ _ _ hys

theorem seqOf_loc_le (hI : S.PInv N fr) (hle : S.le T) (r b : Nat) :
    T.seqOf (S.loc r b) = S.seqOf (S.loc r b) := PState.seqOf_le hle (hI.loc_ok r b).2.1

theorem base_zero (hI : S.PInv N fr) : S.base 0 = [] := by
  unfold PState.base; cases hs : S.sync 0 with
  | none => rfl
  | some M => have := (hI.sync_ok 0 M hs).1; omega

/-- A ballot's base is fixed once set, and empty at ballot 0. -/
theorem base_le' (hI : S.PInv N fr) (hIT : T.PInv N fr) (hle : S.le T) {b : Nat}
    (h : S.sync b ≠ none ∨ b = 0) : T.base b = S.base b := by
  rcases h with h | rfl
  · exact PState.base_le hle b h
  · rw [base_zero hI, base_zero hIT]

/-- A ballot with a non-empty sequence of some replica has its `MSync` (or is ballot 0). -/
theorem sync_of_mem (hI : S.PInv N fr) {r b : Nat} {y : CmdId} (hy : y ∈ S.loc r b) :
    S.sync b ≠ none ∨ b = 0 := by
  rcases Nat.eq_zero_or_pos b with h | h
  · exact .inr h
  · have hne : S.loc r b ≠ [] := fun e => by rw [e] at hy; simp at hy
    exact .inl (((hI.loc_ok r b).2.2 hne).2.2 h).1

theorem sync_of_base {b : Nat} {y : CmdId} (hy : y ∈ S.base b) : S.sync b ≠ none := by
  intro h; unfold PState.base at hy; rw [h] at hy; simp at hy

theorem keyPrefix_le (hI : S.PInv N fr) (hIT : T.PInv N fr) (hle : S.le T) {r b : Nat}
    {y : CmdId} (hloc : T.loc r b = S.loc r b) (hy : y ∈ S.loc r b) :
    T.keyPrefix r b y = S.keyPrefix r b y := by
  have hB := base_le' hI hIT hle (sync_of_mem hI hy)
  obtain ⟨cy, hcy⟩ := Option.ne_none_iff_exists'.mp ((hI.loc_ok r b).2.1 y hy)
  have hcy' := hle.cmds y cy hcy
  unfold PState.keyPrefix
  rw [hcy, hcy', hloc, hB]
  have : T.seqOf ((S.loc r b).drop (S.base b).length) =
      S.seqOf ((S.loc r b).drop (S.base b).length) :=
    PState.seqOf_le hle (fun z hz => (hI.loc_ok r b).2.1 z (List.mem_of_mem_drop hz))
  rw [this]

theorem entryOk_mono (hI : S.PInv N fr) (hle : S.le T) {r c : Nat} (hA : AgreeR N r S T)
    {e : RepEntry} (h : S.entryOk N r c e) : T.entryOk N r c e := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  have hacc : ∀ x, T.acc r c x = S.acc r c x := fun x => by rw [hA.acc]
  have hcom : ∀ x, T.com r c x = S.com r c x := fun x => by rw [hA.com]
  refine ⟨hle.cmds _ _ h1, by rw [← hA.loc]; exact h2, h3, fun hp => ?_, fun hp => ?_,
    fun hp d hd => ?_⟩
  · obtain ⟨a1, a2, a3⟩ := h4 hp
    exact ⟨by rw [hacc, hcom]; exact a1, ord_le hle a2, by rw [depsIn_ord_le hI hle a2]; exact a3⟩
  · rcases h5 hp with ⟨a1, a2, a3⟩ | a
    · exact .inl ⟨a1, ord_le hle a2, by rw [depsIn_ord_le hI hle a2]; exact a3⟩
    · exact .inr (by rw [← hA.pre]; exact a)
  · rw [← hA.loc, seqOf_loc_le hI hle]; exact h6 hp d hd

theorem repOk_mono (hI : S.PInv N fr) (hIT : T.PInv N fr) (hle : S.le T) {r b' : Nat}
    (hA : AgreeR N r S T) {R : Report} (h : S.repOk N r b' R) : T.repOk N r b' R := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  have hB : T.base R.cbal = S.base R.cbal := by
    apply base_le' hI hIT hle
    rcases Nat.eq_zero_or_pos R.cbal with e | e
    · exact .inr e
    · obtain ⟨M, hM, -⟩ := h3 e; exact .inl (by rw [hM]; simp)
  refine ⟨by rw [← hA.rs]; exact h1, h2, fun hc => ?_, fun c' x a b => ?_, fun x hx => ?_,
    fun x D hx => ?_, fun hl x hx => ?_, ?_, fun e he => entryOk_mono hI hle hA (h9 e he)⟩
  · obtain ⟨M, hM, hall⟩ := h3 hc; exact ⟨M, hle.sync _ _ hM, hall⟩
  · rw [← hA.acc, ← hA.pre, ← hA.com, ← hA.loc]; exact h4 c' x a b
  · rw [← hA.acc, ← hA.com] at hx; exact h5 x hx
  · rw [← hA.pre] at hx; exact h6 x D hx
  · apply h7 hl x
    unfold PState.ord at hx ⊢; rw [← hl] at hx ⊢; rw [hA.loc]; exact hx
  · obtain ⟨B, hBp, hBe⟩ := h8; exact ⟨B, by rw [hB]; exact hBp, by rw [hB, ← hA.loc]; exact hBe⟩

/-- **The guards are monotone**: an event ok in `S` is ok in any extension `T` (with `PInv`)
where its node's slice is the same; so (with `apE_frame`, `apE_le`) it stays ok after any other
node's event. -/
theorem okE_mono (hI : S.PInv N fr) (hIT : T.PInv N fr) (hle : S.le T) {n : Nd} {e : PEv}
    (hA : Agree N n S T) (h : okE N S n e) : okE N T n e := by
  cases n with
  | cl k =>
    cases e with
    | inv x c => exact ⟨by rw [← hA x h.2.1]; exact h.1, h.2⟩
    | resp x v => trivial
    | _ => exact h.elim
  | rep r =>
    have hA : AgreeR N r S T := hA
    have hrs := hA.rs
    cases e with
    | handle b x c =>
      obtain ⟨h1, h2, h3, h4, h5⟩ := h
      refine ⟨hle.cmds _ _ h1, by rw [← hA.loc]; exact h2, h3, by rw [← hrs]; exact h4,
        fun hb => ?_⟩
      obtain ⟨a1, a2⟩ := h5 hb
      exact ⟨fun e => a1 (by cases e' : S.sync b with
        | none => rfl
        | some M => rw [hle.sync _ _ e'] at e; cases e),
        by rw [PState.base_le hle b a1, ← hA.loc]; exact a2⟩
    | preaccept b y D =>
      obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
      refine ⟨h1, by rw [← hrs]; exact h2, by rw [← hA.loc]; exact h3, ?_, ?_,
        by rw [← hA.pre]; exact h6, by rw [← hA.path]; exact h7⟩
      · rw [← hA.loc, seqOf_loc_le hI hle]; exact h4
      · rw [base_le' hI hIT hle (sync_of_mem hI h3)]; exact h5
    | accept b y =>
      obtain ⟨h1, h2, h3, h4, h5⟩ := h
      refine ⟨h1, by rw [← hrs]; exact h2, by rw [← hA.loc]; exact h3, ord_le hle h4,
        fun hl d hd => ?_⟩
      rw [depsIn_ord_le hI hle h4] at hd
      rw [← hA.acc, ← hA.com]; exact h5 hl d hd
    | commit b y =>
      obtain ⟨h1, h2, h3, h4⟩ := h
      refine ⟨h1, by rw [← hrs]; exact h2, by rw [← hA.loc]; exact h3, ?_⟩
      rcases h4 with a | a | a
      · exact .inl a
      · exact .inr (.inl (by rw [← hA.acc]; exact a))
      · exact .inr (.inr (by rw [PState.base_le hle b (sync_of_base a)]; exact a))
    | newBallot b' => show (T.rs r).ballot ≤ b'; rw [← hrs]; exact h
    | report b' R =>
      exact ⟨by rw [← hA.rep]; exact h.1, repOk_mono hI hIT hle hA h.2⟩
    | computeSync b' ids =>
      obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
      refine ⟨h1, h2, by rw [← hA.sync b' h1.symm]; exact h3, by rw [← hrs]; exact h4,
        by rw [← hrs]; exact h5, h6, fun p hp e => h7 p hp ?_⟩
      cases e' : S.rep p b' with
      | none => rfl
      | some R => rw [hle.rep _ _ _ e'] at e; cases e
    | takeSync b' =>
      obtain ⟨h1, h2, h3, h4⟩ := h
      refine ⟨h1, fun e => h2 ?_, by rw [← hrs]; exact h3, ?_⟩
      · cases e' : S.sync b' with
        | none => rfl
        | some M => rw [hle.sync _ _ e'] at e; cases e
      · rw [← hA.loc, PState.base_le hle b' h2]; exact h4
    | inv x c => exact h.elim
    | resp x v => exact h.elim

end mono

/-! ## The effects: extensions, `PInv`, and the same new slice in an extension -/

section effects
variable {S T : PState} {N : Nat} {fr : Bool}

theorem repsOf_congr {S T : PState} {b' : Nat} {ids : List Nat}
    (h : ∀ p ∈ ids, S.rep p b' = T.rep p b') : repsOf S b' ids = repsOf T b' ids := by
  unfold repsOf
  induction ids with
  | nil => rfl
  | cons p l ih =>
    rw [List.filterMap_cons, List.filterMap_cons, h p (by simp),
      ih (fun q hq => h q (List.mem_cons_of_mem _ hq))]

theorem repsOf_fst {b' : Nat} {ids : List Nat} (h : ∀ p ∈ ids, S.rep p b' ≠ none) :
    (repsOf S b' ids).map Prod.fst = ids := by
  unfold repsOf
  induction ids with
  | nil => rfl
  | cons p l ih =>
    obtain ⟨R, hR⟩ := Option.ne_none_iff_exists'.mp (h p (by simp))
    rw [List.filterMap_cons, hR]
    simp only [Option.map_some, List.map_cons]
    rw [ih (fun q hq => h q (List.mem_cons_of_mem _ hq))]

theorem repsOf_mem {b' : Nat} {ids : List Nat} {p : Nat × Report} (h : p ∈ repsOf S b' ids) :
    S.rep p.1 b' = some p.2 := by
  unfold repsOf at h
  obtain ⟨q, -, hq⟩ := List.mem_filterMap.mp h
  cases e : S.rep q b' with
  | none => rw [e] at hq; cases hq
  | some R => rw [e] at hq; simp at hq; subst hq; exact e

theorem keyPrefix_getLast (r b : Nat) (y : CmdId) : (S.keyPrefix r b y).getLast? = some y := by
  unfold PState.keyPrefix
  cases S.cmds y <;> simp

/-- An ok event keeps `PInv`. -/
theorem apE_pinv (hI : S.PInv N fr) {n : Nd} {e : PEv} (h : okE N S n e) :
    (apE N S n e).PInv N fr := by
  cases n with
  | cl k =>
    cases e with
    | inv x c => exact PState.PInv_register hI x c h.1
    | resp x v => exact hI
    | _ => exact h.elim
  | rep r =>
    cases e with
    | handle b x c =>
      obtain ⟨h1, h2, h3, h4, h5⟩ := h
      exact PState.PInv_handle hI r b x (by rw [h1]; simp) h2 h3 h4 h5
    | preaccept b y D =>
      obtain ⟨h1, h2, h3, h4, h5, -, -⟩ := h
      exact PState.PInv_preaccept hI r b y D _ h1 h2 h3 h4 h5 (keyPrefix_getLast r b y)
        (fun _ => rfl) (fun _ h => h)
    | accept b y =>
      obtain ⟨h1, h2, h3, h4, h5⟩ := h
      exact PState.PInv_accept hI r b y h1 h2 h3 h4 h5
    | commit b y =>
      obtain ⟨h1, h2, h3, h4⟩ := h
      exact PState.PInv_commit hI r b y h1 h2 h3 h4
    | newBallot b' => exact PState.PInv_newBallot hI r b' h
    | report b' R => exact PState.PInv_report hI r b' R h.1 h.2
    | computeSync b' ids =>
      obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
      subst h1
      exact PState.PInv_computeSync hI b' _ (repsOf S b' ids) h2 h3 ⟨h4, h5⟩
        (by rw [repsOf_fst h7]; exact h6) (fun p hp => repsOf_mem hp) rfl
    | takeSync b' =>
      obtain ⟨h1, h2, h3, h4⟩ := h
      obtain ⟨M, hM⟩ := Option.ne_none_iff_exists'.mp h2
      exact PState.PInv_takeSync hI r b' M h1 hM h3 h4
    | inv x c => exact h.elim
    | resp x v => exact h.elim

/-- An ok event extends the state. -/
theorem apE_le (hI : S.PInv N fr) {n : Nd} {e : PEv} (h : okE N S n e) : S.le (apE N S n e) := by
  cases n with
  | cl k =>
    cases e with
    | inv x c => exact PState.le_register x c h.1
    | resp x v => exact PState.le_refl S
    | _ => exact h.elim
  | rep r =>
    cases e with
    | handle b x c => exact PState.le_handle r b x
    | preaccept b y D => exact PState.le_preaccept r b y D _ h.2.2.2.2.2.1 h.2.2.2.2.2.2
    | accept b y => exact PState.le_accept r b y
    | commit b y => exact PState.le_commit r b y
    | newBallot b' => exact PState.le_newBallot r b'
    | report b' R => exact PState.le_report r b' R h.1
    | computeSync b' ids => exact PState.le_computeSync' hI b' _ h.2.1 h.2.2.1
    | takeSync b' => exact PState.le_takeSync r b' h.2.2.2
    | inv x c => exact h.elim
    | resp x v => exact h.elim

/-- A replica's event registers nothing. -/
theorem apE_cmds_rep {r : Nat} {e : PEv} (h : okE N S (.rep r) e) :
    (apE N S (.rep r) e).cmds = S.cmds := by
  cases e <;> first | rfl | exact h.elim

/-- **The effect on the node's slice is the same in an extension with the same slice.** -/
theorem apE_agree (hI : S.PInv N fr) (hIT : T.PInv N fr) (hle : S.le T) {n : Nd} {e : PEv}
    (hA : Agree N n S T) (h : okE N S n e) : Agree N n (apE N S n e) (apE N T n e) := by
  cases n with
  | cl k =>
    cases e with
    | inv x c =>
      intro y hy
      show (if y = x then some c else S.cmds y) = (if y = x then some c else T.cmds y)
      by_cases e : y = x
      · simp [e]
      · simp only [e, if_false]; exact hA y hy
    | resp x v => exact hA
    | _ => exact h.elim
  | rep r =>
    have hA : AgreeR N r S T := hA
    obtain ⟨hl, hs, hrs, ha, hp, hpa, hc, hre⟩ := hA
    cases e with
    | handle b x c =>
      refine ⟨?_, fun b' hb' => hs b' hb', ?_, ha, hp, hpa, hc, hre⟩
      · funext b'; simp [apE, PState.handle, hl]
      · simp [apE, PState.handle, hl, hrs]
    | preaccept b y D =>
      have hk := keyPrefix_le hI hIT hle (b := b) (y := y) (r := r) (by rw [hl]) h.2.2.1
      refine ⟨hl, fun b' hb' => hs b' hb', ?_, ha, ?_, ?_, hc, hre⟩
      · simp [apE, PState.preaccept, hrs, hk]
      · funext b' y'; simp [apE, PState.preaccept, hp]
      · funext b' y'; simp [apE, PState.preaccept, hpa, hk]
    | accept b y =>
      refine ⟨hl, fun b' hb' => hs b' hb', ?_, ?_, hp, hpa, hc, hre⟩
      · simp [apE, PState.accept, hrs]
      · funext b' y'; simp [apE, PState.accept, ha]
    | commit b y =>
      refine ⟨hl, fun b' hb' => hs b' hb', ?_, ha, hp, hpa, ?_, hre⟩
      · simp [apE, PState.commit, hrs]
      · funext b' y'; simp [apE, PState.commit, hc]
    | newBallot b' =>
      refine ⟨hl, fun b hb => hs b hb, ?_, ha, hp, hpa, hc, hre⟩
      simp [apE, PState.newBallot, hrs]
    | report b' R =>
      refine ⟨hl, fun b hb => hs b hb, ?_, ha, hp, hpa, hc, ?_⟩
      · simp [apE, PState.report, hrs]
      · funext b; simp [apE, PState.report, hre]
    | computeSync b' ids =>
      obtain ⟨h1, -, -, -, -, -, h7⟩ := h
      have hR : repsOf T b' ids = repsOf S b' ids := by
        apply repsOf_congr; intro p hp'
        obtain ⟨R, hR⟩ := Option.ne_none_iff_exists'.mp (h7 p hp')
        rw [hR, hle.rep _ _ _ hR]
      subst h1
      refine ⟨?_, fun b hb => ?_, ?_, ha, hp, hpa, hc, hre⟩
      · funext b; simp [apE, PState.computeSync, hl, hR]
      · simp only [apE, PState.computeSync, hR]; split
        · rfl
        · exact hs b hb
      · simp [apE, PState.computeSync, hrs, hR]
    | takeSync b' =>
      have hB : T.base b' = S.base b' := PState.base_le hle b' h.2.1
      refine ⟨?_, fun b hb => hs b hb, ?_, ?_, hp, hpa, hc, hre⟩
      · funext b; simp [apE, PState.takeSync, hl, hB]
      · simp [apE, PState.takeSync, hrs, hB]
      · funext b x; simp [apE, PState.takeSync, ha, hB]
    | inv x c => exact h.elim
    | resp x v => exact h.elim

end effects

/-! ## Locality: the diamond -/

/-- The cut's invariant. -/
def CutInv (N : Nat) (fr : Bool) (S : PState) : Prop := S.PInv N fr

/-- **Locality (R1)**: two ok events of different nodes stay ok after each other and commute. -/
theorem diamond (N : Nat) (fr : Bool) : Cut.Diamond (okE N) (apE N) (CutInv N fr) := by
  refine ⟨fun s n e hI h => apE_pinv hI h, fun s n1 e1 n2 e2 hI hne h1 h2 => ?_,
    fun s n1 e1 n2 e2 hI hne h1 h2 => ?_⟩
  · have hIT := apE_pinv hI h1
    exact okE_mono hI hIT (apE_le hI h1) ((apE_frame h1).1 n2 (Ne.symm hne)) h2
  · -- the two orders agree on every slice
    have hI1 := apE_pinv (fr := fr) hI h1
    have hI2 := apE_pinv (fr := fr) hI h2
    have hA12 : Agree N n2 s (apE N s n1 e1) := (apE_frame h1).1 n2 (Ne.symm hne)
    have hA21 : Agree N n1 s (apE N s n2 e2) := (apE_frame h2).1 n1 hne
    have ok12 := okE_mono hI hI1 (apE_le hI h1) hA12 h2
    have ok21 := okE_mono hI hI2 (apE_le hI h2) hA21 h1
    have F12 := apE_frame ok12
    have F21 := apE_frame ok21
    have F1 := apE_frame h1
    have F2 := apE_frame h2
    apply PState.eq_of_agree (N := N)
    · intro m
      by_cases m1 : m = n1
      · subst m1
        -- X agrees with apE s n1 e1 at n1 (frame of n2); so does Y (the same new slice)
        have a := (F12.1 m hne).symm
        have b := apE_agree hI hI2 (apE_le hI h2) hA21 h1
        exact a.trans b
      · by_cases m2 : m = n2
        · subst m2
          exact (apE_agree hI hI1 (apE_le hI h1) hA12 h2).symm.trans (F21.1 m (Ne.symm hne))
        · have a := (F12.1 m m2).symm.trans ((F1.1 m m1).symm)
          have b := (F21.1 m m1).symm.trans ((F2.1 m m2).symm)
          exact a.trans b.symm
    · rw [← F12.2, ← F1.2, F2.2, F21.2]

/-! ## The real pre-acceptance's path -/

namespace PState

/-- `S` with replica `r`'s path of `y` in `b` set to `P`. -/
def setPath (S : PState) (r b : Nat) (y : CmdId) (P : List CmdId) : PState :=
  { S with
    path := fun r' b' y' => if r' = r ∧ b' = b ∧ y' = y then some P else S.path r' b' y'
    rs := fun r' => { S.rs r' with
      pathR := if r' = r then (S.rs r').pathR.map (fun q => if q.1 = (b, y) then (q.1, P) else q)
        else (S.rs r').pathR } }

end PState

theorem PState.ext' {S T : PState} (h1 : S.cmds = T.cmds) (h2 : S.loc = T.loc)
    (h3 : S.sync = T.sync) (h4 : S.rs = T.rs) (h5 : S.acc = T.acc) (h6 : S.pre = T.pre)
    (h7 : S.path = T.path) (h8 : S.com = T.com) (h9 : S.rep = T.rep) (h10 : S.G = T.G) :
    S = T := by
  cases S; cases T; simp only at *; subst_vars; rfl

/-- The real pre-acceptance is the predicted one with its path changed. -/
theorem preaccept_setPath {S : PState} {N : Nat} {fr : Bool} (hI : S.PInv N fr) {r b : Nat}
    {y : CmdId} {D P Q : List CmdId} (hpath : S.path r b y = none) :
    S.preaccept r b y D P = (S.preaccept r b y D Q).setPath r b y P := by
  have hnone : ((S.rs r).pathR.find? (·.1 == (b, y))) = none := by
    have := (hI.rows_ok r b).2.2.2.1 y
    rw [hpath] at this; unfold RState.pathAt at this
    cases e : (S.rs r).pathR.find? (·.1 == (b, y)) with
    | none => rfl
    | some q => rw [e] at this; simp at this
  have hmap : (S.rs r).pathR.map (fun q => if q.1 = (b, y) then (q.1, P) else q) =
      (S.rs r).pathR := by
    rw [List.map_congr_left (g := id) ?_, List.map_id]
    intro q hq
    have := List.find?_eq_none.mp hnone q hq
    have hq' : q.1 ≠ (b, y) := fun e => this (by simp [e])
    simp [hq']
  refine PState.ext' rfl rfl rfl ?_ rfl rfl ?_ rfl rfl rfl
  · funext r'
    simp only [PState.setPath, PState.preaccept]
    by_cases e : r' = r
    · subst e; simp [hmap]
    · simp [e]
  · funext r' b' y'
    simp only [PState.setPath, PState.preaccept]
    by_cases e : r' = r ∧ b' = b ∧ y' = y <;> simp [e]

theorem setPath_keyPrefix (S : PState) (r b : Nat) (y : CmdId) (P : List CmdId) :
    (S.setPath r b y P).keyPrefix = S.keyPrefix := rfl

/-- Changing an existing path changes no guard. -/
theorem setPath_okE {S : PState} {N r b : Nat} {y : CmdId} {P : List CmdId}
    (hp : S.path r b y ≠ none) (n : Nd) (e : PEv) :
    okE N (S.setPath r b y P) n e ↔ okE N S n e := by
  cases n with
  | cl k => cases e <;> exact Iff.rfl
  | rep r' =>
    cases e with
    | preaccept b' y' D =>
      have : (S.setPath r b y P).path r' b' y' = none ↔ S.path r' b' y' = none := by
        simp only [PState.setPath]
        split
        · rename_i h; obtain ⟨rfl, rfl, rfl⟩ := h; simp [hp]
        · exact Iff.rfl
      simp only [okE]; rw [this]; exact Iff.rfl
    | _ => exact Iff.rfl

/-- Changing an existing path commutes with every ok event. -/
theorem setPath_apE {S : PState} {N r b : Nat} {y : CmdId} {P : List CmdId}
    (hp : S.path r b y ≠ none) {n : Nd} {e : PEv} (h : okE N S n e) :
    apE N (S.setPath r b y P) n e = (apE N S n e).setPath r b y P := by
  cases n with
  | cl k => cases e <;> rfl
  | rep r' =>
    cases e with
    | preaccept b' y' D =>
      have hne : ¬ (r' = r ∧ b' = b ∧ y' = y) := by
        rintro ⟨rfl, rfl, rfl⟩; exact hp h.2.2.2.2.2.2
      show (S.setPath r b y P).preaccept r' b' y' D (S.keyPrefix r' b' y') =
        (S.preaccept r' b' y' D (S.keyPrefix r' b' y')).setPath r b y P
      refine PState.ext' rfl rfl rfl ?_ rfl rfl ?_ rfl rfl rfl
      · funext r''
        dsimp only [PState.setPath, PState.preaccept]
        by_cases e1 : r'' = r'
        · subst e1
          by_cases e2 : r'' = r
          · subst e2
            have : (b', y') ≠ (b, y) := by
              intro e; simp only [Prod.mk.injEq] at e; exact hne ⟨rfl, e.1, e.2⟩
            simp [this, setPath_keyPrefix]
          · simp [e2, setPath_keyPrefix]
        · simp [e1]
      · funext r'' b'' y''
        dsimp only [PState.setPath, PState.preaccept]
        by_cases e1 : r'' = r' ∧ b'' = b' ∧ y'' = y'
        · obtain ⟨rfl, rfl, rfl⟩ := e1; simp [hne, setPath_keyPrefix]
        · simp only [e1, if_false]
    | _ => rfl

end sp

end Perennial.github_com.imdea_software.swiftpaxos

end
