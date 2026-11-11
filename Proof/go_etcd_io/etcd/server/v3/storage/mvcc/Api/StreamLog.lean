/-
**A watch stream's history, and `wsRecvOk` from it** (stage 2 of the mvcc API proof, the watch
chain: `notes/mvcc-api-risk.md`, M1; 2026-11-04). Lean-first (no Rocq counterpart).

The stream's ghost history (`ι.ev`, a monotone list, `Api/StreamGhost.lean`) is the sequence of
its events: the registrations (`Watch`'s update), the cancels (`Cancel`'s, at its first check),
the close, and every response sent on its channel, each with what it records at its send
(`Api/SentInv.lean`'s `SentFact`, its filters by their saved name). Its replay (`replay`) is the
stream's state, the cancelled set and the sent facts; a registration's stamp is the number of
responses sent before it, exactly. The history is well formed (`LogWF`) when each event's
premises held when it was appended (`stepOk`: a fresh id; a send's fact true at its send, its
registry info the stream's, its cancelled ids cancelled, a `-1` response covering every watcher
registered by then). Well-formedness is what the appender proves; it is prefix-closed, so every
lower bound of the history carries it.

`sentInv_of_log`: a well-formed history's replay keeps `SentInv` (with the facts' bounds below
the store's state); `wsRecvOk_of_log`: a received prefix of its sends satisfies the guarantee.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.SentInv

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc
namespace api
namespace sent

open Iris go_etcd_io.etcd.server.v3.storage.mvcc

/-- A watcher a `-1` response covers, as the history records it (its filters by saved name). -/
abbrev CovRec := w64 × WatchRange × GName × Nat

/-- **An event of a stream's history.** A send records its response, its watcher's registry info
(its filters by saved name), the notified-log and compaction lower bounds it was sent with, and,
for a `-1` response, its covered watchers and the cancelled ids. -/
inductive SEv where
  | reg (id : w64) (rg : WatchRange) (fg : GName) (lo : Nat)
  | cancel (id : w64)
  | close
  | send (r : WResp) (fg : GName) (rg : WatchRange) (lo : Nat) (L : Log) (c0 : Int)
      (cov : List CovRec) (dead : List w64)

instance WResp.countable : Pos.Countable WResp :=
  .ofInjective (fun r => Pos.Countable.encode (r.id, r.evs, r.rev, r.compactRev))
    (by rintro ⟨a, b, c, d⟩ ⟨a', b', c', d'⟩ h; have h := Pos.encode_inj h; simp_all)

/-- The events' code, for countability. -/
def SEv.code : SEv → (w64 × WatchRange × GName × Nat) ⊕ (w64 ⊕ (Unit ⊕
    (WResp × GName × WatchRange × Nat × Log × Int × List CovRec × List w64)))
  | .reg id rg fg lo => .inl (id, rg, fg, lo)
  | .cancel id => .inr (.inl id)
  | .close => .inr (.inr (.inl ()))
  | .send r fg rg lo L c0 cov dead => .inr (.inr (.inr (r, fg, rg, lo, L, c0, cov, dead)))

instance SEv.countable : Pos.Countable SEv :=
  .ofInjective (fun e => Pos.Countable.encode e.code)
    (by
      intro a b h
      have h := Pos.encode_inj h
      cases a <;> cases b <;> simp_all [SEv.code])

/-- An event's saved filter names. -/
def SEv.fgs : SEv → List GName
  | .reg _ _ fg _ => [fg]
  | .send _ fg _ _ _ _ cov _ => fg :: cov.map (·.2.2.1)
  | _ => []

/-- A send's fact, its filters decoded by `dec`. -/
def sendFact (dec : GName → List (EvM → Bool)) (r : WResp) (fg : GName) (rg : WatchRange)
    (lo : Nat) (L : Log) (c0 : Int) (cov : List CovRec) (dead : List w64) : SentFact :=
  ⟨r, rg, dec fg, lo, L, c0, cov.map (fun c => ⟨c.1, c.2.1, dec c.2.2.1, c.2.2.2⟩), dead⟩

/-- **The replayed state**: the stream's, the cancelled set, the facts sent. -/
structure RState where
  S : StreamState
  D : List w64
  F : List SentFact

def rStart : RState := ⟨wsStart, [], []⟩

/-- An event's effect. A registration's stamp is the number of responses sent before it. -/
def RState.step (dec : GName → List (EvM → Bool)) (st : RState) : SEv → RState
  | .reg id rg fg lo => { st with S := st.S.register id ⟨rg, dec fg, lo, st.F.length, true⟩ }
  | .cancel id => ⟨st.S.cancel id, if (st.S.ws !! id).isSome then id :: st.D else st.D, st.F⟩
  | .close => { st with S := st.S.close }
  | .send r fg rg lo L c0 cov dead => { st with F := st.F ++ [sendFact dec r fg rg lo L c0 cov dead] }

def replay (dec : GName → List (EvM → Bool)) (l : List SEv) : RState :=
  l.foldl (RState.step dec) rStart

/-- **An event's premises**, at the state before it. -/
def stepOk (dec : GName → List (EvM → Bool)) (st : RState) : SEv → Prop
  | .reg id _ _ _ => st.S.ws !! id = none ∧ id ≠ W64 (-1)
  | .cancel _ => True
  | .close => True
  | .send r fg rg lo L c0 cov dead =>
      let f := sendFact dec r fg rg lo L c0 cov dead
      f.holds (st.F.map SentFact.r) ∧ factAgree st.S f ∧ (∀ id ∈ f.dead, id ∈ st.D) ∧
        stampsAt st.S st.F.length f

/-- **A well-formed history**: each event's premises held when it was appended. -/
def LogWF (dec : GName → List (EvM → Bool)) (l : List SEv) : Prop :=
  ∀ (p : Nat) (e : SEv), l[p]? = some e → stepOk dec (replay dec (l.take p)) e

/-- The responses sent. -/
def sendsOf : List SEv → List WResp
  | [] => []
  | .send r .. :: l => r :: sendsOf l
  | _ :: l => sendsOf l

/-- The number of events that are not sends (those the stream's client makes). -/
def nsCount : List SEv → Nat
  | [] => 0
  | .send .. :: l => nsCount l
  | _ :: l => nsCount l + 1

/-- The saved filter names of a history. -/
def fgsOf (l : List SEv) : List GName := l.flatMap SEv.fgs

/-! ## Lemmas -/

section lemmas
variable (dec : GName → List (EvM → Bool)) (st : RState)

theorem step_reg (id : w64) (rg : WatchRange) (fg : GName) (lo : Nat) :
    st.step dec (.reg id rg fg lo) =
      { st with S := st.S.register id ⟨rg, dec fg, lo, st.F.length, true⟩ } := rfl
theorem step_cancel (id : w64) :
    st.step dec (.cancel id) =
      ⟨st.S.cancel id, if (st.S.ws !! id).isSome then id :: st.D else st.D, st.F⟩ := rfl
theorem step_close : st.step dec .close = { st with S := st.S.close } := rfl
theorem step_send (r : WResp) (fg : GName) (rg : WatchRange) (lo : Nat) (L : Log) (c0 : Int)
    (cov : List CovRec) (dead : List w64) :
    st.step dec (.send r fg rg lo L c0 cov dead) =
      { st with F := st.F ++ [sendFact dec r fg rg lo L c0 cov dead] } := rfl
end lemmas

theorem replay_snoc (dec : GName → List (EvM → Bool)) (l : List SEv) (e : SEv) :
    replay dec (l ++ [e]) = (replay dec l).step dec e := by
  simp [replay, List.foldl_append]

theorem LogWF_snoc (dec : GName → List (EvM → Bool)) (l : List SEv) (e : SEv) :
    LogWF dec (l ++ [e]) ↔ LogWF dec l ∧ stepOk dec (replay dec l) e := by
  constructor
  · intro h
    refine ⟨fun p e' hp => ?_, ?_⟩
    · have hlt : p < l.length := (List.getElem?_eq_some_iff.1 hp).1
      have := h p e' (by rw [List.getElem?_append_left hlt]; exact hp)
      rwa [List.take_append_of_le_length (Nat.le_of_lt hlt)] at this
    · have := h l.length e (by simp)
      simpa using this
  · rintro ⟨h, he⟩ p e' hp
    rcases Nat.lt_or_ge p l.length with hlt | hge
    · rw [List.getElem?_append_left hlt] at hp
      rw [List.take_append_of_le_length (Nat.le_of_lt hlt)]
      exact h p e' hp
    · have hlen := (List.getElem?_eq_some_iff.1 hp).1
      simp only [List.length_append, List.length_singleton] at hlen
      have hpl : p = l.length := by omega
      subst hpl
      simp at hp
      subst hp
      simpa using he

theorem LogWF_prefix (dec : GName → List (EvM → Bool)) {l l' : List SEv} (hp : l <+: l')
    (h : LogWF dec l') : LogWF dec l := by
  obtain ⟨t, rfl⟩ := hp
  intro p e hpe
  have hlt : p < l.length := (List.getElem?_eq_some_iff.1 hpe).1
  have := h p e (by rw [List.getElem?_append_left hlt]; exact hpe)
  rwa [List.take_append_of_le_length (Nat.le_of_lt hlt)] at this

/-- The facts only grow. -/
theorem replay_F_snoc (dec : GName → List (EvM → Bool)) (l : List SEv) (e : SEv) :
    ∃ t, (replay dec (l ++ [e])).F = (replay dec l).F ++ t := by
  rw [replay_snoc]
  cases e with
  | reg id rg fg lo => exact ⟨[], by rw [step_reg, List.append_nil]⟩
  | cancel id => exact ⟨[], by rw [step_cancel, List.append_nil]⟩
  | close => exact ⟨[], by rw [step_close, List.append_nil]⟩
  | send r fg rg lo L c0 cov dead => exact ⟨_, by rw [step_send]⟩

theorem replay_F_prefix (dec : GName → List (EvM → Bool)) {l l' : List SEv} (hp : l <+: l') :
    (replay dec l).F <+: (replay dec l').F := by
  obtain ⟨t, rfl⟩ := hp
  refine snoc_induction (P := fun t => (replay dec l).F <+: (replay dec (l ++ t)).F) ?_ ?_ t
  · simp
  · intro t e ih
    obtain ⟨u, hu⟩ := replay_F_snoc dec (l ++ t) e
    rw [← List.append_assoc, hu]
    exact ih.trans (List.prefix_append _ _)

theorem sendsOf_append (l t : List SEv) : sendsOf (l ++ t) = sendsOf l ++ sendsOf t := by
  induction l with
  | nil => rfl
  | cons x l ih => cases x <;> simp [sendsOf, ih]

theorem sendsOf_eq (dec : GName → List (EvM → Bool)) (l : List SEv) :
    sendsOf l = (replay dec l).F.map SentFact.r := by
  refine snoc_induction (P := fun l => sendsOf l = (replay dec l).F.map SentFact.r) rfl ?_ l
  intro l e ih
  rw [sendsOf_append, replay_snoc, ih]
  cases e with
  | reg id rg fg lo => rw [step_reg]; simp [sendsOf]
  | cancel id => rw [step_cancel]; simp [sendsOf]
  | close => rw [step_close]; simp [sendsOf]
  | send r fg rg lo L c0 cov dead => rw [step_send]; simp [sendsOf, sendFact]

theorem sendsOf_prefix {l l' : List SEv} (hp : l <+: l') : sendsOf l <+: sendsOf l' := by
  obtain ⟨t, rfl⟩ := hp
  rw [sendsOf_append]; exact List.prefix_append _ _

theorem nsCount_append (l t : List SEv) : nsCount (l ++ t) = nsCount l + nsCount t := by
  induction l with
  | nil => simp [nsCount]
  | cons x l ih => cases x <;> simp [nsCount, ih] <;> omega

/-- Appending only sends leaves the stream's state and the cancelled set. -/
theorem replay_sends (dec : GName → List (EvM → Bool)) (l t : List SEv) (h : nsCount t = 0) :
    (replay dec (l ++ t)).S = (replay dec l).S ∧ (replay dec (l ++ t)).D = (replay dec l).D := by
  revert h
  refine snoc_induction (P := fun t => nsCount t = 0 →
    (replay dec (l ++ t)).S = (replay dec l).S ∧ (replay dec (l ++ t)).D = (replay dec l).D)
    (fun _ => by simp) ?_ t
  intro t e ih h
  rw [nsCount_append] at h
  have h1 : nsCount t = 0 := by omega
  have h2 : nsCount [e] = 0 := by omega
  obtain ⟨ihS, ihD⟩ := ih h1
  rw [← List.append_assoc, replay_snoc]
  cases e with
  | reg id rg fg lo => simp [nsCount] at h2
  | cancel id => simp [nsCount] at h2
  | close => simp [nsCount] at h2
  | send r fg rg lo L c0 cov dead => rw [step_send]; exact ⟨ihS, ihD⟩

theorem fgsOf_append (l t : List SEv) : fgsOf (l ++ t) = fgsOf l ++ fgsOf t := by
  simp [fgsOf, List.flatMap_append]

theorem fgsOf_prefix {l l' : List SEv} (hp : l <+: l') : ∀ fg ∈ fgsOf l, fg ∈ fgsOf l' := by
  obtain ⟨t, rfl⟩ := hp
  intro fg hfg; rw [fgsOf_append]; exact List.mem_append_left _ hfg

/-- Replay depends on the decoding only at the history's filter names. -/
theorem replay_congr (dec dec' : GName → List (EvM → Bool)) (l : List SEv)
    (h : ∀ fg ∈ fgsOf l, dec fg = dec' fg) : replay dec l = replay dec' l := by
  revert h
  refine snoc_induction (P := fun l => (∀ fg ∈ fgsOf l, dec fg = dec' fg) →
    replay dec l = replay dec' l) (fun _ => rfl) ?_ l
  intro l e ih h
  have hl : ∀ fg ∈ fgsOf l, dec fg = dec' fg := fun fg hfg =>
    h fg (by rw [fgsOf_append]; exact List.mem_append_left _ hfg)
  have he : ∀ fg ∈ e.fgs, dec fg = dec' fg := fun fg hfg =>
    h fg (by rw [fgsOf_append]; apply List.mem_append_right; simpa [fgsOf] using hfg)
  rw [replay_snoc, replay_snoc, ih hl]
  cases e with
  | reg id rg fg lo =>
    rw [step_reg, step_reg, he fg (by simp [SEv.fgs])]
  | cancel id => rw [step_cancel, step_cancel]
  | close => rw [step_close, step_close]
  | send r fg rg lo L c0 cov dead =>
    rw [step_send, step_send]
    have hcov : cov.map (fun c => (⟨c.1, c.2.1, dec c.2.2.1, c.2.2.2⟩ : CovEntry)) =
        cov.map (fun c => (⟨c.1, c.2.1, dec' c.2.2.1, c.2.2.2⟩ : CovEntry)) := by
      apply List.map_congr_left
      intro c hc
      rw [he c.2.2.1 (by simp only [SEv.fgs, List.mem_cons, List.mem_map]; exact Or.inr ⟨c, hc, rfl⟩)]
    simp only [sendFact, hcov, he fg (by simp [SEv.fgs])]

/-- **A registration in a well-formed history**: the replay has its registry info at its id, for
good (the id fresh when registered, so no later registration replaces it; a cancel changes only
`live`). What a sender's registration token gives (`factAgree`). -/
theorem replay_reg (dec : GName → List (EvM → Bool)) (l : List SEv) (hwf : LogWF dec l)
    (id : w64) (rg : WatchRange) (fg : GName) (lo : Nat) (hm : SEv.reg id rg fg lo ∈ l) :
    regAgree (replay dec l).S id rg (dec fg) lo := by
  revert hwf hm
  refine snoc_induction (P := fun l => LogWF dec l → SEv.reg id rg fg lo ∈ l →
    regAgree (replay dec l).S id rg (dec fg) lo) (fun _ h => by simp at h) ?_ l
  intro l e ih hwf hm
  obtain ⟨hwf', hstep⟩ := (LogWF_snoc dec l e).1 hwf
  rw [replay_snoc]
  rcases List.mem_append.1 hm with hm | hm
  · obtain ⟨w, hw, h1, h2, h3⟩ := ih hwf' hm
    cases e with
    | reg id' rg' fg' lo' =>
      rw [step_reg]
      have hne : id' ≠ id := by rintro rfl; rw [hstep.1] at hw; cases hw
      exact ⟨w, by simp [StreamState.register, hne, hw], h1, h2, h3⟩
    | cancel id' =>
      rw [step_cancel]
      obtain ⟨g, hg, hlk, -, -⟩ := cancel_lookup (replay dec l).S id' id
      refine ⟨g w, by rw [hlk, hw]; rfl, ?_, ?_, ?_⟩
      · rw [(hg w).1, h1]
      · rw [(hg w).2.1, h2]
      · rw [(hg w).2.2.1, h3]
    | close => rw [step_close]; exact ⟨w, hw, h1, h2, h3⟩
    | send r fg' rg' lo' L c0 cov dead => rw [step_send]; exact ⟨w, hw, h1, h2, h3⟩
  · rw [List.mem_singleton] at hm
    subst hm
    rw [step_reg]
    exact ⟨⟨rg, dec fg, lo, (replay dec l).F.length, true⟩, by simp [StreamState.register], rfl, rfl,
      rfl⟩

/-- The cancelled set only grows. -/
theorem replay_D_mono (dec : GName → List (EvM → Bool)) (l t : List SEv) :
    ∀ id ∈ (replay dec l).D, id ∈ (replay dec (l ++ t)).D := by
  refine snoc_induction (P := fun t => ∀ id ∈ (replay dec l).D, id ∈ (replay dec (l ++ t)).D)
    (fun id h => by simpa using h) ?_ t
  intro t e ih id hid
  have h := ih id hid
  rw [← List.append_assoc, replay_snoc]
  cases e with
  | reg => rw [step_reg]; exact h
  | cancel id' =>
    rw [step_cancel]
    show id ∈ (if ((replay dec (l ++ t)).S.ws !! id').isSome then id' :: _ else _)
    split
    · exact List.mem_cons_of_mem _ h
    · exact h
  | close => rw [step_close]; exact h
  | send => rw [step_send]; exact h

/-- **A cancel of a registered watcher in a well-formed history**: its id is in the replay's
cancelled set, for good. What a `-1` response's sender's cancel token gives (`deadIn`). -/
theorem replay_cancel (dec : GName → List (EvM → Bool)) (l1 l : List SEv) (hwf : LogWF dec l)
    (id : w64) (rg : WatchRange) (fg : GName) (lo : Nat) (hp : l1 ++ [.cancel id] <+: l)
    (hreg : SEv.reg id rg fg lo ∈ l1) : id ∈ (replay dec l).D := by
  obtain ⟨t, rfl⟩ := hp
  have hwf1 : LogWF dec l1 := LogWF_prefix dec (List.prefix_append _ _)
    (LogWF_prefix dec (List.prefix_append _ _) hwf)
  obtain ⟨w, hw, -⟩ := replay_reg dec l1 hwf1 id rg fg lo hreg
  refine replay_D_mono dec (l1 ++ [.cancel id]) t id ?_
  rw [replay_snoc, step_cancel]
  show id ∈ (if ((replay dec l1).S.ws !! id).isSome then id :: _ else _)
  rw [hw]; exact List.mem_cons_self ..

/-- **Which ids the replayed state has watchers of does not depend on the decoding.** -/
theorem replay_ws_isSome (dec dec' : GName → List (EvM → Bool)) (l : List SEv) (i : w64) :
    ((replay dec l).S.ws !! i).isSome = ((replay dec' l).S.ws !! i).isSome := by
  revert i
  refine snoc_induction (P := fun l => ∀ i,
    ((replay dec l).S.ws !! i).isSome = ((replay dec' l).S.ws !! i).isSome) (fun _ => rfl) ?_ l
  intro l e ih i
  rw [replay_snoc, replay_snoc]
  cases e with
  | reg id rg fg lo =>
    rw [step_reg, step_reg]
    simp only [StreamState.register, GMap.lookup_insert_eq_iff]
    split
    · rfl
    · exact ih i
  | cancel id =>
    rw [step_cancel, step_cancel]
    obtain ⟨g, -, hlk, -, -⟩ := cancel_lookup (replay dec l).S id i
    obtain ⟨g', -, hlk', -, -⟩ := cancel_lookup (replay dec' l).S id i
    show (((replay dec l).S.cancel id).ws !! i).isSome =
      (((replay dec' l).S.cancel id).ws !! i).isSome
    rw [hlk, hlk']
    have := ih i
    cases h1 : (replay dec l).S.ws !! i <;> cases h2 : (replay dec' l).S.ws !! i <;>
      simp_all
  | close => rw [step_close, step_close]; exact ih i
  | send r fg rg lo L c0 cov dead => rw [step_send, step_send]; exact ih i

/-- **A watcher of the replayed state was registered in the history.** -/
theorem replay_ws_reg (dec : GName → List (EvM → Bool)) (l : List SEv) (id : w64) (w : WInfo)
    (h : (replay dec l).S.ws !! id = some w) : ∃ rg fg lo, SEv.reg id rg fg lo ∈ l := by
  revert w h
  refine snoc_induction (P := fun l => ∀ w, (replay dec l).S.ws !! id = some w →
    ∃ rg fg lo, SEv.reg id rg fg lo ∈ l) ?_ ?_ l
  · intro w h; simp [replay, rStart, wsStart, GMap.lookup_empty] at h
  intro l e ih w h
  have up : ∀ rg fg lo, SEv.reg id rg fg lo ∈ l → SEv.reg id rg fg lo ∈ l ++ [e] :=
    fun _ _ _ hm => List.mem_append_left _ hm
  rw [replay_snoc] at h
  cases e with
  | reg id' rg fg lo =>
    rw [step_reg] at h
    by_cases hi : id' = id
    · subst hi; exact ⟨rg, fg, lo, by simp⟩
    · simp only [StreamState.register, GMap.lookup_insert_ne _ _ hi] at h
      obtain ⟨a, b, c, hm⟩ := ih w h; exact ⟨a, b, c, up _ _ _ hm⟩
  | cancel id' =>
    rw [step_cancel] at h
    obtain ⟨g, -, hlk, -, -⟩ := cancel_lookup (replay dec l).S id' id
    simp only at h
    rw [hlk] at h
    cases hw : (replay dec l).S.ws !! id with
    | none => rw [hw] at h; cases h
    | some w0 => obtain ⟨a, b, c, hm⟩ := ih w0 hw; exact ⟨a, b, c, up _ _ _ hm⟩
  | close =>
    rw [step_close] at h
    obtain ⟨a, b, c, hm⟩ := ih w h; exact ⟨a, b, c, up _ _ _ hm⟩
  | send r fg rg lo L c0 cov dead =>
    rw [step_send] at h
    obtain ⟨a, b, c, hm⟩ := ih w h; exact ⟨a, b, c, up _ _ _ hm⟩

/-! ## The bridge -/

/-- **A well-formed history keeps `SentInv`**, its facts' bounds below the store's state. -/
theorem sentInv_of_log (σ : MvccState) (dec : GName → List (EvM → Bool)) (l : List SEv)
    (hwf : LogWF dec l) (hlb : lbsOk σ (replay dec l).F) :
    SentInv σ (replay dec l).S (replay dec l).D (replay dec l).F := by
  revert hwf hlb
  refine snoc_induction (P := fun l => LogWF dec l → lbsOk σ (replay dec l).F →
    SentInv σ (replay dec l).S (replay dec l).D (replay dec l).F)
    (fun _ _ => sentInv_nil σ) ?_ l
  intro l e ih hwf hlb
  obtain ⟨hwf', hstep⟩ := (LogWF_snoc dec l e).1 hwf
  have hlb' : lbsOk σ (replay dec l).F := by
    obtain ⟨t, ht⟩ := replay_F_snoc dec l e
    intro f hf
    exact hlb f (by rw [ht]; exact List.mem_append_left _ hf)
  have IH := ih hwf' hlb'
  rw [replay_snoc] at hlb ⊢
  cases e with
  | reg id rg fg lo =>
    rw [step_reg]
    exact SentInv.register IH id _ hstep.1 hstep.2 (Nat.le_refl _)
  | cancel id => rw [step_cancel]; exact SentInv.cancel IH id
  | close => rw [step_close]; exact SentInv.close IH
  | send r fg rg lo L c0 cov dead =>
    obtain ⟨hf, hag, hdi, hst⟩ := hstep
    rw [step_send] at hlb ⊢
    exact sentFacts_snoc σ _ _ _ _ IH hf
      (hlb _ (List.mem_append_right _ (List.mem_singleton_self _))) hag hdi hst

/-- **The guarantee of a received prefix of a well-formed history's sends.** -/
theorem wsRecvOk_of_log (σ : MvccState) (dec : GName → List (EvM → Bool)) (l : List SEv)
    (rs : List WResp) (hwf : LogWF dec l) (hlb : lbsOk σ (replay dec l).F)
    (hrs : rs <+: sendsOf l) : wsRecvOk σ (replay dec l).S rs := by
  have h := (sentInv_of_log σ dec l hwf hlb).take rs.length
  have hr : ((replay dec l).F.take rs.length).map SentFact.r = rs := by
    rw [List.map_take, ← sendsOf_eq dec l]
    obtain ⟨t, ht⟩ := hrs
    rw [← ht]; simp
  rw [← hr]
  exact wsRecvOk_of_sent' σ _ _ _ h

end sent
end api
end mvcc
end EtcdGrove
end Perennial
