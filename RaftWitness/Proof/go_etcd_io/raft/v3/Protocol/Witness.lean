/-
The witness (2026-10-19, witness support, `notes/raft-witness.md`): its protocol model and its
ghost state.

The witness is not a raft node: a storage object (`WitnessStorage`, updated by compare-and-swap)
holds its state (`WState`: term, vote, and the last entry it stored, with its subterm and
replication set), and every node's witness proxy (`witness.go`) answers the leaders' and the
candidates' witness messages from its cache of the stored state (a past state) or from a state
it just read and wrote back. The ghost state of the storage is `wGhost γ st` (`st` the stored
state): the authority of the state history `γ.reWHist` (`wSt`'s lower bounds: a proxy's cache is
one), every state of it justified (`wStJust`), and the witness's half of its vote map (the other
half is in the votes table, `votesTbl`). Each path of `witness.Process` is one lemma:

- `wGhost_read`: the storage read (the state, as a cache: `wSt`);
- `wSt_app_noupd`: `handleAppendNoUpdate`, from a cache or the stored state, at its term: the
  acknowledgement of the request's index when the state has the request's `(term, subterm)`
  (shortcut replication), of its own index when its is later (`wAck`);
- `wGhost_raise`: `processMessageWithNewerTerm` (term raised, vote dropped);
- `wGhost_write`: `handleAppend`'s write of a later `(term, subterm)`, with its acknowledgement;
- `wGhost_vote`: `handleVote`'s grant, recorded in the vote map and the votes table;
- `wGhost_heartbeat`: `handleHeartbeat` at the stored state's term, read from storage (the fixed
  code, fork `edd87c489`): the response's read-index acknowledgement (`HbAckOk`) holds since the
  witness has acknowledged nothing above the stored state's term. Answered from a cache it would
  not (the stale read of `notes/raft-witness.md`); a lease read is not supported with a witness.
-/
module

public import RaftWitness.Proof.go_etcd_io.raft.v3.Protocol.Refinement

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI GMap go_etcd_io.raft.v3

/-! ### The witness's model -/

instance LexLe_decidable (t1 s1 t2 s2 : w64) : Decidable (LexLe t1 s1 t2 s2) := by
  unfold LexLe; infer_instance

theorem LexLe_refl (t s : w64) : LexLe t s t s := Or.inr ⟨rfl, Int.le_refl _⟩

theorem LexLe_trans {a b c d e f : w64} : LexLe a b c d → LexLe c d e f → LexLe a b e f := by
  unfold LexLe
  rintro (h1 | ⟨rfl, h1⟩) (h2 | ⟨rfl, h2⟩)
  · left; omega
  · left; omega
  · left; omega
  · right; exact ⟨rfl, by omega⟩

/-- `(a, b)` is not at most `(c, d)`: it is above it. -/
theorem LexLe_of_not {a b c d : w64} (h : ¬ LexLe a b c d) :
    LexLe c d a b ∧ ¬ (c = a ∧ d = b) := by
  unfold LexLe at *
  have hac : ¬ uint.Z a < uint.Z c := fun h' => h (Or.inl h')
  have hbd : a = c → ¬ uint.Z b ≤ uint.Z d := fun e h' => h (Or.inr ⟨e, h'⟩)
  refine ⟨?_, ?_⟩
  · by_cases h1 : uint.Z c < uint.Z a
    · exact Or.inl h1
    · have e : a = c := uint_Z_inj.mp (by omega)
      exact Or.inr ⟨e.symm, by have := hbd e; omega⟩
  · rintro ⟨e1, e2⟩; subst e1 e2; exact hbd rfl (Int.le_refl _)

section model
variable [GooseExts]

/-- The witness's first state (an empty storage object). -/
def wInit : WState := ⟨W64 0, W64 0, W64 0, W64 0, W64 0, []⟩

/-- `witness.handleAppendNoUpdate` from the state `st` (a proxy's cache, or the stored state), at
`st`'s term: the acknowledgement of the request's index if `st` has the request's
`(term, subterm)`, of `st`'s index if `st`'s is later; `none` (the storage is to be written) if
the request's is later. -/
def wAppNoUpd (w : w64) (st : WState) (m : Msg) : Option Msg :=
  if m.logterm = st.lt ∧ m.sub = st.ls then
    some (Msg.mk .appResp w m.src st.term false m.index (W64 0) (W64 0) (W64 0) [])
  else if LexLe m.logterm m.sub st.lt st.ls then
    some (Msg.mk .appResp w m.src st.term false st.li (W64 0) (W64 0) (W64 0) [])
  else none

/-- `witness.handleAppend`'s write: the request's entry and replication set. -/
def wAppWrite (st : WState) (m : Msg) : WState :=
  { st with lt := m.logterm, ls := m.sub, li := m.index, rs := m.voters }

/-- `witness.processMessageWithNewerTerm` (the leader is not modelled). -/
def wRaise (st : WState) (T : w64) : WState := { st with term := T, vote := W64 0 }

end model

/-! ### The witness's ghost state -/

section ghost
variable [GooseExts]
variable {GF : BundledGFunctors} [AllG GF] [ReceiptGS GF] [InvGS GF]

/-- The witness's vote map follows its state (`VoteHistOk`'s, of a `WState`). -/
def WVoteHistOk (voted : GMap w64 w64) (st : WState) : Prop :=
  (∀ t, (voted !! t).isSome → uint.Z t ≤ uint.Z st.term) ∧
  voted !! st.term = (if st.vote = W64 0 then none else some st.vote)

/-- The ghost state of the witness's storage at its state `st`. -/
def wGhost (γ : RaftNames) (st : WState) : IProp GF :=
  iprop(∃ (L : List WState) (γv : GName) (voted : GMap w64 w64),
    monoListAuthOwn γ.reWHist 1 L ∗ ⌜L.getLast? = some st ∧ wHistOk L⌝ ∗
    ([∗list] x ∈ L, wStJust γ x) ∗
    ⌜γ.reVotes !! γ.reWit = some γv ∧ WVoteHistOk voted st⌝ ∗
    ghostMapAuth γv (1 : Qp).half voted ∗ [∗map] t ↦ c ∈ voted, t ↪[γv]□ c)

omit [GooseExts] in
/-- The last state of a history is at least each of its states. -/
theorem hist_last_ge (L : List WState) (st x : WState) :
    wHistOk L → L.getLast? = some st → x ∈ L →
    uint.Z x.term ≤ uint.Z st.term ∧ LexLe x.lt x.ls st.lt st.ls := by
  intro HL Hl Hx
  rw [List.getLast?_eq_getElem?] at Hl
  obtain ⟨a, Ha⟩ := List.mem_iff_getElem?.mp Hx
  have Hal := (List.getElem?_eq_some_iff.mp Ha).1
  by_cases h : a = L.length - 1
  · subst h; rw [Ha] at Hl; cases Hl; exact ⟨Int.le_refl _, LexLe_refl _ _⟩
  · exact HL.1 a (L.length - 1) x st (by omega) Ha Hl

omit [GooseExts] in
theorem hist_push (L : List WState) (st st' : WState) :
    L.getLast? = some st → wHistOk L →
    uint.Z st.term ≤ uint.Z st'.term → LexLe st.lt st.ls st'.lt st'.ls →
    uint.Z st'.lt ≤ uint.Z st'.term →
    wHistOk (L ++ [st']) := by
  intro Hl HL H1 H2 H3
  refine ⟨fun a b x y hab ha hb => ?_, fun x hx => ?_⟩
  · by_cases hb' : b < L.length
    · rw [List.getElem?_append_left (by omega)] at ha
      rw [List.getElem?_append_left hb'] at hb
      exact HL.1 a b x y hab ha hb
    · have hbl : b = L.length := by
        have := (List.getElem?_eq_some_iff.mp hb).1; simp at this; omega
      subst hbl
      rw [List.getElem?_append_left (by omega)] at ha
      simp at hb; subst hb
      obtain ⟨h1, h2⟩ := hist_last_ge L st x HL Hl (List.mem_of_getElem? ha)
      exact ⟨by omega, LexLe_trans h2 H2⟩
  · rcases List.mem_append.mp hx with h | h
    · exact HL.2 x h
    · simp at h; subst h; exact H3

/-- The storage read: the stored state is a state of the history (a proxy caches it). -/
theorem wGhost_read (γ : RaftNames) (st : WState) :
    ⊢ wGhost (GF := GF) γ st -∗ wGhost γ st ∗ wSt γ st := by
  unfold wGhost
  iintro ⟨%L, %γv, %voted, Ha, %HL, #Hj, %Hv, Hva, #Hf⟩
  icases persistent_entails_left (monoListLbOwn_get (GF := GF) γ.reWHist 1 L) $$ Ha
    with ⟨Ha, #Hlb⟩
  isplitl [Ha Hva]
  · iexists L, γv, voted
    iframe Ha Hva Hj Hf
    ipureintro; exact ⟨HL, Hv⟩
  · unfold wSt
    iexists L
    iframe Hlb Hj
    ipureintro; exact ⟨List.mem_of_getLast? HL.1, HL.2⟩

/-- A state of the history is at most the stored one. -/
theorem wGhost_le (γ : RaftNames) (st x : WState) :
    ⊢ wGhost (GF := GF) γ st -∗ wSt γ x -∗
      ⌜uint.Z x.term ≤ uint.Z st.term ∧ LexLe x.lt x.ls st.lt st.ls⌝ := by
  unfold wGhost wSt
  iintro ⟨%L, %γv, %voted, Ha, %HL, -, -, -, -⟩ ⟨%L', #Hlb, %HL', -⟩
  icases mono_list_auth_lb_valid $$ Ha Hlb with %Hpre
  ipureintro
  exact hist_last_ge L st x HL.2 HL.1 (Hpre.2.subset HL'.1)

/-- A state's last entry is of a term at most its own. -/
theorem wSt_lt_le (γ : RaftNames) (x : WState) :
    ⊢ wSt (GF := GF) γ x -∗ ⌜uint.Z x.lt ≤ uint.Z x.term⌝ := by
  unfold wSt
  iintro ⟨%L, -, %HL, -⟩
  ipureintro; exact HL.2.2 x HL.1

/-- A new state of the storage, justified. -/
theorem wGhost_push (γ : RaftNames) (st st' : WState) :
    uint.Z st.term ≤ uint.Z st'.term → LexLe st.lt st.ls st'.lt st'.ls →
    uint.Z st'.lt ≤ uint.Z st'.term →
    (∀ voted, WVoteHistOk voted st → WVoteHistOk voted st') →
    ⊢ wStJust (GF := GF) γ st' -∗ wGhost γ st ==∗ wGhost γ st' ∗ wSt γ st' := by
  intro H1 H2 H3 H4
  unfold wGhost
  iintro #Hj' ⟨%L, %γv, %voted, Ha, %HL, #Hj, %Hv, Hva, #Hf⟩
  imod monoListAuthOwn_update_app [st'] $$ Ha with ⟨Ha, #Hlb⟩
  have HL' := hist_push L st st' HL.1 HL.2 H1 H2 H3
  ihave #Hjs : iprop([∗list] x ∈ L ++ [st'], wStJust (GF := GF) γ x) $$ []
  · iapply (BigSepL.bigSepL_append (Φ := fun _ x => wStJust (GF := GF) γ x)).2
    iframe Hj
    iapply (BigSepL.bigSepL_singleton (Φ := fun _ x => wStJust (GF := GF) γ x)).2
    iexact Hj'
  imodintro
  isplitl [Ha Hva]
  · iexists L ++ [st'], γv, voted
    iframe Ha Hva Hjs Hf
    ipureintro; exact ⟨⟨List.getLast?_concat, HL'⟩, Hv.1, H4 voted Hv.2⟩
  · unfold wSt
    iexists L ++ [st']
    iframe Hlb Hjs
    ipureintro; exact ⟨by simp, HL'⟩

/-- `processMessageWithNewerTerm`: the term raised, the vote dropped. -/
theorem wGhost_raise (γ : RaftNames) (st : WState) (T : w64) :
    uint.Z st.term < uint.Z T →
    ⊢ wGhost (GF := GF) γ st ==∗ wGhost γ (wRaise st T) ∗ wSt γ (wRaise st T) := by
  intro HT
  iintro Hg
  icases wGhost_read γ st $$ Hg with ⟨Hg, #Hst⟩
  ihave %Hlt := wSt_lt_le γ st $$ Hst
  ihave #Hj : wStJust (GF := GF) γ (wRaise st T) $$ []
  · rw [show wStJust (GF := GF) γ (wRaise st T) = wStJust γ st from rfl]
    iapply wSt_just γ st $$ Hst
  iapply wGhost_push γ st (wRaise st T) (by show uint.Z st.term ≤ uint.Z T; omega)
    (LexLe_refl _ _) (by show uint.Z st.lt ≤ uint.Z T; omega) ?_ $$ Hj Hg
  rintro voted ⟨Hk, -⟩
  refine ⟨fun t ht => by have := Hk t ht; show uint.Z t ≤ uint.Z T; omega, ?_⟩
  show voted !! T = (if W64 0 = W64 0 then none else some (W64 0))
  rw [if_pos rfl]
  cases h : voted !! T with
  | none => rfl
  | some _ => have := Hk T (by rw [h]; rfl); omega

/-- A witness request is of the leader's term, which is not `0`. -/
theorem isLeader_term_nz (γ : RaftNames) (id t : w64) :
    ⊢ isLeader (GF := GF) γ id t -∗ ⌜t ≠ W64 0⌝ := by
  unfold isLeader
  iintro ⟨%q, #Hw⟩
  icases isWin_core γ id t q $$ Hw with ⟨%c, #Hc⟩
  unfold isWinCore
  icases Hc with ⟨%γw, %F0, %k, -, #Hk, -⟩
  ihave %Hok := isCampK_ok γ id t F0 k $$ Hk
  ipureintro; exact Hok.term_nz

/-- `handleAppendNoUpdate` from a state `st` of the history at the request's term (a proxy's
cache, or the stored state): its acknowledgement is the witness's (`wAck`), within the leader's
log. -/
theorem wSt_app_noupd (γ : RaftNames) (st : WState) (m r : Msg) :
    m.ty = .wapp → m.dst = γ.reWit → γ.reWit ≠ W64 0 → m.term = st.term →
    wAppNoUpd γ.reWit st m = some r →
    ⊢ wSt (GF := GF) γ st -∗ isMessage γ m -∗ isMessage γ r := by
  intro Hty Hd Hwnz Ht Hr
  simp only [isMessage, Hty]
  rw [if_pos ⟨Hd, Hwnz⟩]
  iintro #Hst ⟨%x, %P, %c, %H, %Hm, #Hj⟩
  obtain ⟨Hlt, -, -⟩ := Hm
  ihave %Hle := wSt_lt_le γ st $$ Hst
  unfold wAppNoUpd at Hr
  by_cases He : m.logterm = st.lt ∧ m.sub = st.ls
  · rw [if_pos He] at Hr
    cases Hr
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [← Ht]
    unfold wJust
    icases Hj with ⟨%Hp, #Hl, #Hin, #Hacks⟩
    isplitr
    · unfold isAcked; iright; iright
      isplitr; · ipureintro; exact ⟨rfl, Hwnz⟩
      unfold wAck
      iexists m.sub, m.index, x, P, c, H, st
      isplitr; · ipureintro; exact ⟨Int.le_refl _, Ht.symm, by rw [← He.1, Hlt], He.2.symm⟩
      unfold wJust
      iframe Hl Hin Hacks Hst
      ipureintro; exact Hp
    · iexact Hin
  · rw [if_neg He] at Hr
    by_cases Hlx : LexLe m.logterm m.sub st.lt st.ls
    · rw [if_pos Hlx] at Hr
      cases Hr
      simp only [Bool.false_eq_true, ↓reduceIte]
      -- `st`'s last entry is the leader's of `st`'s term, of a later subterm
      have Hstl : st.lt = st.term := by
        unfold LexLe at Hlx
        rcases Hlx with h | ⟨h, -⟩
        · rw [Hlt, Ht] at h; omega
        · rw [← h, Hlt, Ht]
      have Hls : uint.Z m.sub < uint.Z st.ls := by
        unfold LexLe at Hlx
        rcases Hlx with h | ⟨h, h'⟩
        · rw [Hlt, Ht] at h; omega
        · have : m.sub ≠ st.ls := fun e => He ⟨h, e⟩
          have : uint.Z m.sub ≠ uint.Z st.ls := fun e => this (uint_Z_inj.mp e)
          omega
      ihave #Hsj := wSt_just γ st $$ Hst
      unfold wStJust
      by_cases H0 : st.lt = W64 0
      · rw [if_pos H0]
        icases Hsj with %Hs0
        iexfalso; ipureintro; rw [Hs0.1] at Hls; have := uint_Z_nonneg m.sub
        simp at Hls
      rw [if_neg H0]
      icases Hsj with ⟨%x', %P', %c', %H', -, #Hj'⟩
      rw [Hstl]
      ihave #Hin : ackIn (GF := GF) γ st.term st.li $$ []
      · unfold wJust; icases Hj' with ⟨-, -, #Hin, -⟩; iexact Hin
      isplitr
      · unfold isAcked; iright; iright
        isplitr; · ipureintro; exact ⟨rfl, Hwnz⟩
        unfold wAck
        iexists st.ls, st.li, x', P', c', H', st
        isplitr; · ipureintro; exact ⟨Int.le_refl _, rfl, Hstl, rfl⟩
        iframe Hj' Hst
      · iexact Hin
    · rw [if_neg Hlx] at Hr; cases Hr

/-- `handleAppend`'s write: the stored state takes the request's later entry, whose
acknowledgement it answers. -/
theorem wGhost_write (γ : RaftNames) (st : WState) (m : Msg) :
    m.ty = .wapp → m.dst = γ.reWit → γ.reWit ≠ W64 0 → m.term = st.term →
    ¬ LexLe m.logterm m.sub st.lt st.ls →
    ⊢ isMessage (GF := GF) γ m -∗ wGhost γ st ==∗
      wGhost γ (wAppWrite st m) ∗
      isMessage γ (Msg.mk .appResp γ.reWit m.src m.term false m.index (W64 0) (W64 0) (W64 0) []) := by
  intro Hty Hd Hwnz Ht Hnl
  have Hm' : isMessage (GF := GF) γ m = iprop(∃ (x : w64) (P : List EntryM) (c : CfgM)
      (H : GSet w64),
      ⌜m.logterm = m.term ∧ (∀ v, v ∈ m.voters ↔ v ∈ c.incoming \ ({[γ.reWit]} ∪ {[x]})) ∧
        m.voters.Nodup⌝ ∗
      wJust γ m.term m.sub m.index x P c H) := by
    simp only [isMessage, Hty]; rw [if_pos ⟨Hd, Hwnz⟩]
  rw [Hm']
  iintro ⟨%x, %P, %c, %H, %Hm, #Hj⟩ Hg
  obtain ⟨Hlt, Hvs, Hnd⟩ := Hm
  ihave %Htnz : ⌜m.term ≠ W64 0⌝ $$ []
  · unfold wJust; icases Hj with ⟨-, ⟨%ldr, #Hl, -⟩, -⟩; iapply isLeader_term_nz $$ Hl
  ihave #Hj' : wStJust (GF := GF) γ (wAppWrite st m) $$ []
  · unfold wStJust
    rw [if_neg (show (wAppWrite st m).lt ≠ W64 0 from by
      show m.logterm ≠ W64 0; rw [Hlt]; exact Htnz)]
    iexists x, P, c, H
    isplitr; · ipureintro; exact ⟨Hvs, Hnd⟩
    rw [show (wAppWrite st m).lt = m.term from Hlt, show (wAppWrite st m).ls = m.sub from rfl,
      show (wAppWrite st m).li = m.index from rfl]
    iexact Hj
  obtain ⟨Hge, -⟩ := LexLe_of_not Hnl
  imod wGhost_push γ st (wAppWrite st m) (Int.le_refl _) Hge
    (by show uint.Z m.logterm ≤ uint.Z st.term; rw [Hlt, Ht]; exact Int.le_refl _)
    (fun voted h => h) $$ Hj' Hg with ⟨Hg, #Hst⟩
  imodintro
  iframe Hg
  simp only [isMessage, Bool.false_eq_true, ↓reduceIte]
  unfold wJust
  icases Hj with ⟨%Hp, #Hl, #Hin, #Hacks⟩
  iframe Hin
  unfold isAcked; iright; iright
  isplitr; · ipureintro; exact ⟨rfl, Hwnz⟩
  unfold wAck
  iexists m.sub, m.index, x, P, c, H, wAppWrite st m
  isplitr; · ipureintro; exact ⟨Int.le_refl _, Ht.symm, Hlt, rfl⟩
  unfold wJust
  iframe Hl Hin Hacks Hst
  ipureintro; exact Hp

/-- `handleVote`'s grant at the stored state's term: the vote, in the vote map and the votes
table, justified by the state it was granted from (`wVoteJust`), at any mask where the log half
of the commit invariant can be opened (the storage's invariant's, 2026-10-20). -/
theorem wGhost_vote (γ : RaftNames) (E : CoPset) (HE : (↑raftLogN : CoPset) ⊆ E) (st : WState) (m : Msg) :
    m.ty = .wvote → m.dst = γ.reWit → γ.reWit ≠ W64 0 → m.term = st.term → m.src ≠ W64 0 →
    (st.vote = m.src ∨ st.vote = W64 0) → WGrantOk st m.logterm m.sub m.voters →
    ⊢ raftCommitInv (GF := GF) γ -∗ isMessage γ m -∗ wGhost γ st ={E}=∗
      wGhost γ { st with vote := m.src } ∗ isVote γ γ.reWit m.term m.src := by
  intro Hty Hd Hwnz Ht Hsrc Hcv Hok
  have Hm' : isMessage (GF := GF) γ m = wVoteReq γ m.src m.term m.logterm m.index m.sub m.voters := by
    simp only [isMessage, Hty]; rw [if_pos ⟨Hd, Hwnz⟩]
  rw [Hm']
  iintro #Hinv #Hreq Hg
  icases wGhost_read γ st $$ Hg with ⟨Hg, #Hst⟩
  ihave #Hsj := wSt_just γ st $$ Hst
  ihave %Hlt := wSt_lt_le γ st $$ Hst
  unfold wGhost
  icases Hg with ⟨%L, %γv, %voted, Ha, %HL, #Hj, %Hv, Hva, #Hf⟩
  obtain ⟨Hγv, Hk, Hcur⟩ := Hv
  have HL' := hist_push L st { st with vote := m.src } HL.1 HL.2 (Int.le_refl _) (LexLe_refl _ _) Hlt
  imod monoListAuthOwn_update_app [{ st with vote := m.src }] $$ Ha with ⟨Ha, -⟩
  ihave #Hjs : iprop([∗list] x ∈ L ++ [{ st with vote := m.src }], wStJust (GF := GF) γ x) $$ []
  · iapply (BigSepL.bigSepL_append (Φ := fun _ x => wStJust (GF := GF) γ x)).2
    iframe Hj
    iapply (BigSepL.bigSepL_singleton (Φ := fun _ x => wStJust (GF := GF) γ x)).2
    rw [show wStJust (GF := GF) γ { st with vote := m.src } = wStJust γ st from rfl]
    iexact Hsj
  rcases Hcv with Hcv | Hcv
  · -- the same candidate again: its vote is already recorded
    have Hl : voted !! m.term = some m.src := by
      rw [Ht, Hcur, if_neg (by rw [Hcv]; exact Hsrc), Hcv]
    ihave #Hfr := BigSepM.bigSepM_lookup (Φ := fun t c => iprop(t ↪[γv]□ c)) Hl $$ Hf
    imodintro
    isplitl [Ha Hva]
    · iexists L ++ [{ st with vote := m.src }], γv, voted
      iframe Ha Hva Hjs Hf
      ipureintro
      refine ⟨⟨List.getLast?_concat, HL'⟩, Hγv, Hk, ?_⟩
      show voted !! st.term = (if m.src = W64 0 then none else some m.src)
      rw [if_neg Hsrc, ← Ht, Hl]
    · unfold isVote; iexists γv; iframe Hfr; ipureintro; exact Hγv
  · have Hnone : voted !! m.term = none := by rw [Ht, Hcur, if_pos Hcv]
    ihave #Hvj : voteJust (GF := GF) γ γ.reWit m.term m.src $$ []
    · unfold voteJust; iright
      isplitr; · ipureintro; exact ⟨rfl, Hwnz⟩
      unfold wVoteJust
      iexists st, m.logterm, m.index, m.sub, m.voters
      iframe Hst Hreq
      ipureintro; exact ⟨Ht.symm, Hok⟩
    imod vote_insertE γ E HE γ.reWit γv voted m.term m.src Hγv Hnone $$ Hinv Hvj Hva with ⟨Hva, #Hfr⟩
    imodintro
    isplitl [Ha Hva]
    · iexists L ++ [{ st with vote := m.src }], γv, (<[m.term := m.src]> voted)
      iframe Ha Hva Hjs
      isplitr; · ipureintro; exact ⟨List.getLast?_concat, HL'⟩
      isplitr
      · ipureintro
        refine ⟨Hγv, fun t ht => ?_, ?_⟩
        · by_cases htm : t = m.term
          · rw [htm, Ht]; exact Int.le_refl _
          · rw [GMap.lookup_insert_ne _ _ (Ne.symm htm)] at ht; exact Hk t ht
        · show (<[m.term := m.src]> voted) !! st.term = (if m.src = W64 0 then none else some m.src)
          rw [if_neg Hsrc, ← Ht, GMap.lookup_insert]
      · iapply (BigSepM.bigSepM_insert (Φ := fun t c => iprop(t ↪[γv]□ c)) Hnone).2
        iframe Hfr Hf
    · unfold isVote; iexists γv; iframe Hfr; ipureintro; exact Hγv

theorem rqRecOk_some (γ : RaftNames) (T : w64) (r : RqRec) (t' : w64) (qq : GSet w64) :
    r.2 = some (t', qq) → rqRecOk (GF := GF) γ T r = doomed γ T t' qq := by
  intro h; unfold rqRecOk; rw [h]

/-- `handleHeartbeat` at the stored state's term, read from the storage: no read record of the
leader's is doomed by a quorum with the witness, which acknowledged nothing above the term. -/
theorem wGhost_heartbeat (γ : RaftNames) (st : WState) (m : Msg) :
    m.ty = .heartbeat → m.term = st.term → γ.reWit ≠ W64 0 →
    ⊢ isMessage (GF := GF) γ m -∗ wGhost γ st -∗ wGhost γ st ∗
      isMessage γ (Msg.mkV .heartbeatResp γ.reWit m.src st.term false (W64 0) (W64 0) (W64 0)
        (W64 0) [] [] m.ctx) := by
  intro Hty Ht Hwnz
  simp only [isMessage, Hty]
  iintro ⟨-, -, -, -, Hctx⟩ Hg
  icases Hctx with (%H0 | ⟨%q, %recs, %Hq, #Hlb, #Hrecs⟩)
  · iframe Hg; ileft; ipureintro; exact H0
  by_cases Hok : ∀ r ∈ recs.take (uint.nat q), ∀ t' qq, r.2 = some (t', qq) → γ.reWit ∉ qq
  · iframe Hg; iright
    iexists q, recs
    rw [← Ht]
    iframe Hlb
    ipureintro; exact ⟨Hq.1, Hq.2, Hok⟩
  · iexfalso
    simp only [Classical.not_forall, Classical.not_imp, Classical.not_not] at Hok
    obtain ⟨r, Hr, t', qq, Hr2, Hin⟩ := Hok
    obtain ⟨k, Hk⟩ := List.mem_iff_getElem?.mp (List.mem_of_mem_take Hr)
    ihave #Hrr := BigSepL.bigSepL_lookup (Φ := fun _ r => rqRecOk (GF := GF) γ m.term r) Hk
      $$ Hrecs
    rw [rqRecOk_some γ m.term r t' qq Hr2]
    unfold doomed
    icases Hrr with ⟨%n, %G, %a, %c, %qd, %Hd, -, #Hall, -⟩
    ihave Hu := Hall $$ %γ.reWit %Hin
    icases Hu with ⟨%t'', %i'', %Hti, #Hack⟩
    unfold isAcked
    icases Hack with (%H0 | #Hreg | ⟨-, #Hw⟩)
    · ipureintro; omega
    · ihave %Hn := ackReg_not_wit γ γ.reWit t'' i'' $$ Hreg
      ipureintro; exact Hn ⟨rfl, Hwnz⟩
    · unfold wAck
      icases Hw with ⟨%σ, %idx, %x, %P, %c, %H, %st'', %Hst, -, #Hst''⟩
      icases wGhost_le γ st st'' $$ Hg Hst'' with %Hle
      ipureintro
      rw [Hst.2.1] at Hle
      have := Hti.1; rw [Ht] at this; omega

end ghost

end EtcdGrove
end Perennial
