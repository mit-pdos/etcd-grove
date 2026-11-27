/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/proto/Install.lean (241f27e).
-/
/-
`proto` (stage 3) — snapshots and installs: the new step's preservation and the pure laws the code
uses (notes/stage3-plan.md "Interface design", as repaired after the review: notes/review/stage3.md,
D31).

With fix `5894fa2` (the sender stops if its term moved on after opening the snapshot), an
InstallSnapshot of term `T` for `(s, st)` is valid exactly as an AppendEntries of `T` with previous
entry `(s, st)`, no entries and commit index `s` (`AEok σ T s st [] s`). A follower whose log holds the
entry `(s, st)` learns the commit of `s` (`learnCommit`); one whose log does not discards it for the
committed prefix (`installDiscard`). The stage-2 invariant keeps its form; `dur ≥ s` afterwards, so
the FSM's position (`lastApplied`) stays within the durable prefix.

Proved by the PROTO prover (stage 3); helpers `inst_*` are internal.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.proto.Read

@[expose] public section

set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace github_com.hashicorp.raft
namespace proto

/-! ### Helpers (internal to PROTO) -/

/-- A valid install's prefix is the committed log's. -/
theorem inst_C_agree {σ : PState} {T s st : Nat} (h : PInv σ) (hs : 1 ≤ s)
    (hae : AEok σ T s st [] s) : agree σ.C (σ.llog T) s := by
  rcases hae.2.2.2.2.2 with hz | ⟨⟨T', k', p', hT', hk', hc, hag⟩, _⟩
  · omega
  · have hCo := (h.2.2.2.2.2.2.2.2.1.1 _ _ _ hc).2.2
    exact agree_trans (agree_mono hCo hk') (agree_symm hag)
  /- stage-3 proof:
  := by
  rcases hae.2.2.2.2.2 with hz | ⟨⟨T', k', hT', hk', hc, hag⟩, _⟩
  · omega
  · have hCo := (h.2.2.2.2.2.2.2.2.1.1 _ _ hc).2
    exact agree_trans (agree_mono hCo hk') (agree_symm hag)
  -/

/-- Two logs agree up to some `p` and not up to `p + 1`. -/
theorem inst_split (A B : RLog) : ∃ p, agree A B p ∧ ¬ agree A B (p + 1) := by
  have key : ∀ n, agree A B n ∨ ∃ p, p < n ∧ agree A B p ∧ ¬ agree A B (p + 1) := by
    intro n
    induction n with
    | zero => exact Or.inl (agree_zero _ _)
    | succ n ih =>
      rcases ih with h | ⟨p, hp, h1, h2⟩
      · by_cases h' : agree A B (n + 1)
        · exact Or.inl h'
        · exact Or.inr ⟨n, by omega, h, h'⟩
      · exact Or.inr ⟨p, by omega, h1, h2⟩
  rcases key (A.length + 1) with h | ⟨p, _, h1, h2⟩
  · exact absurd h.1 (by omega)
  · exact ⟨p, h1, h2⟩

theorem inst_setLog_self (σ : PState) (i : SID) : setLog σ i (σ.log i) = σ := by
  have hupd : upd σ.srv i (σ.srv i) = σ.srv := by
    funext j; unfold upd; split <;> simp_all
  show ({ σ with srv := upd σ.srv i (σ.srv i) } : PState) = σ
  rw [hupd]

/-- **installDiscard** keeps the invariant. -/
theorem installDiscard_inv (σ : PState) (i : SID) (s st T' : Nat) :
    PInv σ → installDiscardPre σ i s st T' →
      PInv (installDiscard σ i s T') ∧ Grows σ (installDiscard σ i s T') := by
  intro h hp
  obtain ⟨hi, hs, hae, hnpm, ⟨ℓ, hℓi, hℓ⟩, hT', hc', hagT'⟩ := hp
  have hag := inst_C_agree h hs hae
  have hsLL : s ≤ (σ.llog (σ.term i)).length := hag.2.1
  have hst : termAt (σ.llog (σ.term i)) s = st := hae.2.2.2.1 hs
  -- the durable prefix is below `s` (else the log would hold `(s, st)`)
  have hd : (σ.srv i).dur.1 < s := by
    apply Classical.byContradiction; intro hn
    apply hnpm; right
    obtain ⟨hsC, hent⟩ := dur_C σ i s h hi hs (by omega)
    have hdl := dur_le_log σ i h hi
    refine ⟨by omega, ?_⟩
    have e1 : termAt (σ.log i) s = termAt σ.C s := by simp only [termAt, hent]
    rw [e1, agree_termAt hag (Nat.le_refl _), hst]
  -- the agreement point `p` of the log with the leader log
  obtain ⟨p, hpa, hpn⟩ := inst_split (σ.log i) (σ.llog (σ.term i))
  have hps : p < s := by
    apply Classical.byContradiction; intro hn
    apply hnpm; right
    have a := agree_mono hpa (show s ≤ p by omega)
    exact ⟨a.1, by rw [agree_termAt a (Nat.le_refl _), hst]⟩
  have hLM := (h.2.2.1.1 i hi).1
  have hLLM := h.2.2.1.2.1 (σ.term i)
  have hconf : p = (σ.log i).length ∨ (p + 1 ≤ (σ.log i).length ∧
      termAt (σ.log i) (p + 1) ≠ termAt (σ.llog (σ.term i)) (p + 1)) := by
    by_cases hpl : p + 1 ≤ (σ.log i).length
    · exact Or.inr ⟨hpl, fun ht => hpn (LMok_agree hLM hLLM (by omega) hpl (by omega) ht)⟩
    · left; have := hpa.1; omega
  -- the request it amounts to: previous entry `p`, entries `p+1..s`, commit index `s`
  have hlen : (((σ.llog (σ.term i)).drop p).take (s - p)).length = s - p := by
    simp; omega
  have haeP : AEok σ (σ.term i) p (termAt (σ.llog (σ.term i)) p)
      (((σ.llog (σ.term i)).drop p).take (s - p)) s := by
    refine ⟨hae.1, by rw [hlen]; omega, fun h0 => by subst h0; simp [termAt], fun _ => rfl,
      by rw [hlen], hae.2.2.2.2.2⟩
  have hpm : prevMatch (σ.log i) p (termAt (σ.llog (σ.term i)) p) :=
    Or.inr ⟨hpa.1, agree_termAt hpa (Nat.le_refl _)⟩
  have hm0 : ∀ L, matchedUpTo L p (((σ.llog (σ.term i)).drop p).take (s - p)) 0 :=
    fun L => ⟨Nat.zero_le _, fun j' hj' => absurd hj' (Nat.not_lt_zero _)⟩
  -- step 1: truncate at `p + 1` (or nothing)
  have step1 : PInv (setLog σ i ((σ.log i).take p)) ∧ Grows σ (setLog σ i ((σ.log i).take p)) := by
    rcases hconf with hpl | ⟨hpl, hne⟩
    · have e : setLog σ i ((σ.log i).take p) = σ := by
        rw [hpl, List.take_length]; exact inst_setLog_self σ i
      rw [e]; exact ⟨h, grows_refl' σ⟩
    · have := truncate_inv' σ i p _ _ s 0 h ⟨hi, haeP, hpm, hm0 _, by rw [hlen]; omega, by omega, ?_⟩
      · unfold truncate at this
        rw [show p + 1 + 0 - 1 = p by omega] at this
        exact this
      · rw [ae_slice_term haeP (by omega) (by rw [hlen]; omega)]
        simpa using hne
  -- step 2: store the entries `p+1..s`
  have hl1 : (setLog σ i ((σ.log i).take p)).log i = (σ.log i).take p := by
    rw [setSrv_log]; simp
  have hl1len : ((σ.log i).take p).length = p := by simp; have := hpa.1; omega
  have hp2 : followerStorePre (setLog σ i ((σ.log i).take p)) i p (termAt (σ.llog (σ.term i)) p)
      (((σ.llog (σ.term i)).drop p).take (s - p)) s 0 := by
    refine ⟨hi, ?_, ?_, hm0 _, by rw [hlen]; omega, by rw [hl1, hl1len, Nat.add_zero]⟩
    · rw [setLog_term]; exact AEok_grows _ _ _ _ _ _ _ step1.2 haeP
    · rw [hl1]; refine Or.inr ⟨by omega, ?_⟩
      rw [termAt_take _ _ _ (Nat.le_refl _)]
      exact agree_termAt hpa (Nat.le_refl _)
  have step2 := followerStore_inv' step1.1 hp2
  have hl2 := fs_log_eq step1.1 hp2
  rw [hlen, setLog_term, show p + (s - p) = s by omega] at hl2
  -- step 3: learn the commit of `s` (the durable prefix `(s, T')`)
  have hterm2 : (followerStore (setLog σ i ((σ.log i).take p)) i
      ((((σ.llog (σ.term i)).drop p).take (s - p)).drop 0)).term i = σ.term i := by
    show (setLog _ i _).term i = _
    rw [setLog_term, setLog_term]
  have hlog2 : (followerStore (setLog σ i ((σ.log i).take p)) i
      ((((σ.llog (σ.term i)).drop p).take (s - p)).drop 0)).log i = (σ.llog (σ.term i)).take s := by
    show (setLog _ i _).log i = _
    rw [setSrv_log, if_pos rfl]; exact hl2
  have hp3 : learnCommitPre (followerStore (setLog σ i ((σ.log i).take p)) i
      ((((σ.llog (σ.term i)).drop p).take (s - p)).drop 0)) i s T' := by
    rcases hae.2.2.2.2.2 with hz | ⟨_, T'', k'', hT'', hk'', hpb⟩
    · omega
    refine ⟨hi, by rw [hterm2]; exact hT', hc', ?_, T'', k'', by rw [hterm2]; exact hT'', hk'', hpb⟩
    rw [hlog2]
    exact agree_take_left _ hagT' (Nat.le_refl _)
  have step3 := learnCommit_inv' _ i s T' step2.1 hp3
  have heq : installDiscard σ i s T' = learnCommit (followerStore (setLog σ i ((σ.log i).take p)) i
      ((((σ.llog (σ.term i)).drop p).take (s - p)).drop 0)) i s T' := by
    unfold installDiscard learnCommit followerStore
    simp only [setSrv]
    congr 1
    funext j
    by_cases hj : j = i
    · subst hj
      simp only [upd_same]
      have e2 : (σ.srv j).log.take p ++ (((σ.llog (σ.term j)).drop p).take (s - p)).drop 0 =
          (σ.llog (σ.term j)).take s := by
        have := hl2; rw [hl1] at this; exact this
      simp only [PState.log, upd_same] at e2 ⊢
      rw [e2, if_pos hd]
    · simp [upd_ne _ _ _ _ hj]
  rw [heq]
  exact ⟨step3.1, grows_trans' (grows_trans' step1.2 step2.2) step3.2⟩

/-- The discarded log: the committed prefix up to `s`, of length `s` and last term `st`, durable. -/
theorem installDiscard_log (σ : PState) (i : SID) (s st T' : Nat) :
    PInv σ → installDiscardPre σ i s st T' →
      ((installDiscard σ i s T').log i).length = s ∧
      lastTerm ((installDiscard σ i s T').log i) = st ∧
      (∀ k, 1 ≤ k → k ≤ s → ent ((installDiscard σ i s T').log i) k = ent σ.C k) := by
  intro h hp
  obtain ⟨hi, hs, hae, _⟩ := hp
  have hag := inst_C_agree h hs hae
  have hl : (installDiscard σ i s T').log i = (σ.llog (σ.term i)).take s := by
    show (setSrv σ i _).log i = _
    rw [setSrv_log]; simp
  rw [hl]
  refine ⟨by simp only [List.length_take]; exact Nat.min_eq_left hag.2.1, ?_, fun k hk1 hk2 => ?_⟩
  · rw [lastTerm_take _ _ hag.2.1]; exact hae.2.2.2.1 hs
  · rw [ent_take _ _ _ hk2, agree_ent hag hk2]

/-- **Keep**: a follower whose log holds `(s, st)` (the previous-entry check of the install request)
may learn the commit of `s` (`ae_learn` with no entries and `lci = v = s`). -/
theorem install_keep (σ : PState) (i : SID) (s st : Nat) :
    PInv σ → i ∈ σ.srvs → 1 ≤ s → AEok σ (σ.term i) s st [] s → prevMatch (σ.log i) s st →
      ∃ T', learnCommitPre σ i s T' := by
  intro h hi hs hae hpm
  have hag := ae_agree σ i s st [] s h hi hae hpm
    ⟨Nat.le_refl _, fun j' hj' => absurd hj' (Nat.not_lt_zero _)⟩
  simp only [List.length_nil, Nat.add_zero] at hag
  have := ae_learn σ i s st [] s s h hi hae hag (by rw [Nat.min_self]; omega)
  rw [Nat.min_self] at this
  exact this

/-- **A valid install is committed**: its last entry is the committed log's. -/
theorem AEok_install_C (σ : PState) (T s st : Nat) :
    PInv σ → 1 ≤ s → AEok σ T s st [] s → ∃ e, ent σ.C s = some e ∧ e.term = st := by
  intro h hs hae
  have hag := inst_C_agree h hs hae
  obtain ⟨e, he⟩ := ent_isSome σ.C s hs hag.1
  refine ⟨e, he, ?_⟩
  rw [← termAt_of_ent he, agree_termAt hag (Nat.le_refl _)]
  exact hae.2.2.2.1 hs

/-- **The sender's snapshot** (its own: at most its durable prefix; `sendLatestSnapshot`,
`setPreviousLog` with `lastSnapshot`): if `i` leads its term, a committed index `x ≥ 1` within its
durable prefix is a valid install of its term. -/
theorem dur_install (σ : PState) (i : SID) (x : Nat) (e : Entry) :
    PInv σ → i ∈ σ.srvs → σ.leader (σ.term i) = some i → 1 ≤ x → x ≤ (σ.srv i).dur.1 →
      ent σ.C x = some e → AEok σ (σ.term i) x e.term [] x := by
  intro h hi hl hx1 hx2 he
  have hcur := h.2.2.2.1 i hi hl
  have hdl := dur_le_log σ i h hi
  obtain ⟨hxC, hent⟩ := dur_C σ i x h hi hx1 hx2
  obtain ⟨hd, -⟩ := h.2.2.2.2.2.2.2.2.2.1 i hi
  rcases hd with hd | ⟨hT, ⟨k', p', hk', hck⟩, hag⟩
  · omega
  rcases h.2.2.2.2.2.2.2.2.2.2.2.2.1.2 i hi with hp | ⟨T'', k'', hT'', hk'', hpb⟩
  · omega
  refine ⟨by rw [hl]; simp, ?_, fun h0 => by omega, fun _ => ?_, by simp,
    Or.inr ⟨⟨_, k', p', hT, by omega, hck, ?_⟩, T'', k'', hT'', by omega, hpb⟩⟩
  · simp only [List.length_nil, Nat.add_zero]; rw [← hcur]; omega
  · rw [← hcur, termAt_of_ent (show ent (σ.log i) x = some e by rw [← hent]; exact he)]
  · rw [← hcur]; exact agree_mono hag hx2
  /- stage-3 proof:
  := by
  intro h hi hl hx1 hx2 he
  have hcur := h.2.2.2.1 i hi hl
  have hdl := dur_le_log σ i h hi
  obtain ⟨hxC, hent⟩ := dur_C σ i x h hi hx1 hx2
  obtain ⟨hd, -⟩ := h.2.2.2.2.2.2.2.2.2.1 i hi
  rcases hd with hd | ⟨hT, ⟨k', hk', hck⟩, hag⟩
  · omega
  rcases h.2.2.2.2.2.2.2.2.2.2.2.2.2 i hi with hp | ⟨T'', k'', hT'', hk'', hpb⟩
  · omega
  refine ⟨by rw [hl]; simp, ?_, fun h0 => by omega, fun _ => ?_, by simp,
    Or.inr ⟨⟨_, k', hT, by omega, hck, ?_⟩, T'', k'', hT'', by omega, hpb⟩⟩
  · simp only [List.length_nil, Nat.add_zero]; rw [← hcur]; omega
  · rw [← hcur, termAt_of_ent (show ent (σ.log i) x = some e by rw [← hent]; exact he)]
  · rw [← hcur]; exact agree_mono hag hx2
  -/

/-- **A valid install stays valid for a later leader** (leader completeness: the committed prefix is
in every later leader's log): the sender's installed snapshot, valid in the term `t` it followed,
is a valid install of any later term with a leader. -/
theorem AEok_install_later (σ : PState) (t T s st : Nat) :
    PInv σ → 1 ≤ s → AEok σ t s st [] s → t < T → σ.leader T ≠ none → AEok σ T s st [] s := by
  intro h hs hae htT hT
  rcases hae.2.2.2.2.2 with hz | ⟨⟨T', k', p', hT', hk', hc, hag⟩, T'', k'', hT'', hk'', hpb⟩
  · omega
  have hcm := h.2.2.2.2.2.2.2.2.1.1 _ _ _ hc
  have hnl := h.2.2.2.2.2.2.2.1 T' k' p' hcm.1 hcm.2.1 T (by omega) hT
  unfold lacks at hnl
  obtain ⟨-, hag2⟩ := Classical.not_not.mp hnl
  have hagT : agree (σ.llog T) (σ.llog t) s := agree_trans (agree_mono hag2 hk') (agree_symm hag)
  refine ⟨hT, by simpa using hagT.1, fun h0 => by omega, fun _ => ?_, by simp,
    Or.inr ⟨⟨T', k', p', by omega, hk', hc, agree_mono hag2 hk'⟩, T'', k'', by omega, hk'', hpb⟩⟩
  rw [agree_termAt hagT (Nat.le_refl _)]; exact hae.2.2.2.1 hs
  /- stage-3 proof:
  := by
  intro h hs hae htT hT
  rcases hae.2.2.2.2.2 with hz | ⟨⟨T', k', hT', hk', hc, hag⟩, T'', k'', hT'', hk'', hpb⟩
  · omega
  have hcm := (h.2.2.2.2.2.2.2.2.1.1 _ _ hc).1
  have hnl := h.2.2.2.2.2.2.2.1 T' k' hcm T (by omega) hT
  unfold lacks at hnl
  obtain ⟨-, hag2⟩ := Classical.not_not.mp hnl
  have hagT : agree (σ.llog T) (σ.llog t) s := agree_trans (agree_mono hag2 hk') (agree_symm hag)
  refine ⟨hT, by simpa using hagT.1, fun h0 => by omega, fun _ => ?_, by simp,
    Or.inr ⟨⟨T', k', by omega, hk', hc, agree_mono hag2 hk'⟩, T'', k'', by omega, hk'', hpb⟩⟩
  rw [agree_termAt hagT (Nat.le_refl _)]; exact hae.2.2.2.1 hs
  -/

/-- **The commitment counts an install** (`commitment.match(peer, meta.Index)`): a match index `m`
covered as an install's commit index of `T` (`AEok`'s commit clause), past `T`'s election part, is
covered by a recorded commit of `T` itself. -/
theorem install_commit (σ : PState) (T m k : Nat) :
    PInv σ → AEok σ T m (termAt (σ.llog T) m) [] m → σ.len0 T < k → k ≤ m →
      ∃ k' p, k ≤ k' ∧ σ.commits T k' p := by
  intro h hae hk hkm
  rcases hae.2.2.2.2.2 with hz | ⟨⟨T', k', p', hT', hk', hc, hag⟩, _⟩
  · omega
  rcases Nat.lt_or_eq_of_le hT' with hlt | heq
  · exfalso
    obtain ⟨ℓ, hℓ⟩ := Option.ne_none_iff_exists'.mp hae.1
    have hkT : k ≤ (σ.llog T).length := by have := hag.1; omega
    obtain ⟨e, he⟩ := ent_isSome _ k (by omega) hkT
    have h1 := (h.2.1.1 T ℓ hℓ).2.2.2.2.2.2.1 k e hk he
    have h2 := llog_term_le h.1 h.2.1 (t := T') (k := k) (by omega) (by have := hag.2.1; omega)
    rw [← agree_termAt hag hkm, termAt_of_ent he, h1] at h2
    omega
  · exact ⟨k', p', by omega, by rw [← heq]; exact hc⟩
  /- stage-3 proof:
  := by
  intro h hae hk hkm
  rcases hae.2.2.2.2.2 with hz | ⟨⟨T', k', hT', hk', hc, hag⟩, _⟩
  · omega
  rcases Nat.lt_or_eq_of_le hT' with hlt | heq
  · exfalso
    obtain ⟨ℓ, hℓ⟩ := Option.ne_none_iff_exists'.mp hae.1
    have hkT : k ≤ (σ.llog T).length := by have := hag.1; omega
    obtain ⟨e, he⟩ := ent_isSome _ k (by omega) hkT
    have h1 := ((h.2.1.1 T ℓ hℓ).2.2.2.2.2.2.1 k e hk he).1
    have h2 := llog_term_le h.1 h.2.1 (t := T') (k := k) (by omega) (by have := hag.2.1; omega)
    rw [← agree_termAt hag hkm, termAt_of_ent he, h1] at h2
    omega
  · exact ⟨k', by omega, by rw [← heq]; exact hc⟩
  -/

/-- The committed log's terms do not decrease (the snapshot store keeps the newer by term, then
index). -/
theorem C_term_mono (σ : PState) (x s : Nat) (e1 e2 : Entry) :
    PInv σ → x ≤ s → ent σ.C x = some e1 → ent σ.C s = some e2 → e1.term ≤ e2.term := by
  intro h hxs he1 he2
  have hx1 := (ent_le_length he1).1
  have hsl := ent_le_length he2
  have a := h.2.2.1.2.2.2.1 s hsl.1 hsl.2
  rw [termAt_of_ent he2] at a
  have := llog_term_le h.1 h.2.1 (t := e2.term) hx1 (by have := a.2.1; omega)
  rw [← agree_termAt a hxs, termAt_of_ent he1] at this
  exact this

end proto
end github_com.hashicorp.raft
end Perennial
