/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/gprot/Install.lean (241f27e).
-/
/-
`gprot` (stage 3) — snapshots and installs as laws of the ghost layer (notes/stage3-plan.md, as
repaired after the review, D31).

An InstallSnapshot of term `T` for `(s, st)` is valid as `aeValid γ T s st [] s` (an AppendEntries of
`T` with previous entry `(s, st)`, no entries, commit index `s`). The receiver either learns the commit
of `s` (its log holds the entry: `learnCommitFollower` with no entries and `lci = v = s`) or discards
its log (`installDiscard_upd`). The sender's laws: `snapValid_or_left` (its own snapshot, within its
durable prefix), `snapValid_follow` (a snapshot it installed as a follower of an earlier term);
`commit_or_snap` (the commitment counts an install).

Proved by the PROTO prover (stage 3); the helpers before the laws are internal.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.gprot.Snap
public import Dsverify.Proof.github_com.hashicorp.raft.proto.Install

@[expose] public section

set_option linter.unusedVariables false
set_option linter.deprecated false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace github_com.hashicorp.raft
namespace gprot

open proto

section install
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [hRB : ReceiptBoundLe GF (2 ^ 62)]
variable (γ : GNames)

/-! ### Helpers (internal) -/

theorem H_C_get_list (σ : PState) (L : RLog) :
    ∀ key : Nat → Nat, (∀ (j : Nat) (e : Entry), L[j]? = some e → ent σ.C (key j) = some e) →
      HistG (GF := GF) γ σ ⊢ HistG γ σ ∗ ([∗list] j ↦ e ∈ L, CIdx γ (key j) e) := by
  induction L with
  | nil =>
    intro key _
    iintro H; isplitl [H]; · iexact H
    iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2; iempintro
  | cons e es ih =>
    intro key h
    iintro H
    ihave ⟨H, #Hf⟩ := H_C_get γ σ (key 0) e (h 0 e rfl) $$ H
    ihave ⟨H, Hfs⟩ := ih (fun j => key (j + 1)) (fun j e' hj => h (j + 1) e' (by simpa using hj))
      $$ H
    isplitl [H]; · iexact H
    iapply BigSepL.bigSepL_cons.2
    isplitr; · iexact Hf
    iexact Hfs

/-- A valid install (as `AEok`) gives its `aeValid`. -/
theorem H_aeValid_install (σ : PState) (T x pt : Nat) (hx : 1 ≤ x) (hae : AEok σ T x pt [] x) :
    HistG (GF := GF) γ σ ⊢ HistG γ σ ∗ aeValid γ T x pt [] x := by
  obtain ⟨ℓ, hℓ⟩ := Option.ne_none_iff_exists'.mp hae.1
  have hxl : x ≤ (σ.llog T).length := by have := hae.2.1; simpa using this
  obtain ⟨e, he⟩ := proto.ent_isSome (σ.llog T) x hx hxl
  have het : e.term = pt := by rw [← termAt_of_ent he]; exact hae.2.2.2.1 hx
  rcases hae.2.2.2.2.2 with hz | ⟨⟨T', k', p', hT', hk', hcm, hag⟩, T'', k'', hT'', hk'', hpb⟩
  · omega
  iintro H
  ihave ⟨H, #Hl⟩ := H_leader_get γ σ T ℓ hℓ $$ H
  ihave ⟨H, #He⟩ := H_llog_get γ σ T x e he $$ H
  ihave ⟨H, #Hcm⟩ := H_commit_get γ σ T' k' p' hcm $$ H
  ihave ⟨H, #Hpb⟩ := H_pub_get γ σ T'' k'' hpb $$ H
  ihave ⟨H, #Hes1⟩ := H_llog_get_list γ σ T ((σ.llog T).take x) (fun j => j + 1) (by
      intro j e hj
      rw [ent_succ]; rw [List.getElem?_take] at hj
      split at hj
      · exact hj
      · cases hj) $$ H
  ihave ⟨H, #Hes2⟩ := H_llog_get_list γ σ T' ((σ.llog T).take x) (fun j => j + 1) (by
      intro j e hj
      rw [ent_succ]; rw [hag.2.2, List.getElem?_take] at hj
      split at hj
      · exact hj
      · cases hj) $$ H
  isplitl [H]; · iexact H
  unfold aeValid lciOk
  isplitr; · iexists ℓ; iexact Hl
  isplitr
  · iright; iexists e
    isplitr; · ipureintro; exact ⟨hx, het⟩
    iexact He
  isplitr; · iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2; iempintro
  iright
  isplitr
  · iexists T', k', p', ((σ.llog T).take x)
    isplitr
    · ipureintro; refine ⟨hT', hk', ?_⟩; rw [List.length_take]; have := hag.1; omega
    isplitr; · iexact Hcm
    iapply BigSepL.bigSepL_sep_eqv.2
    isplitr; · iexact Hes1
    iexact Hes2
  · iexists T'', k''
    isplitr; · ipureintro; exact ⟨hT'', hk''⟩
    iexact Hpb

/-- `lciOk`, read in the history. -/
theorem H_lciOk (σ : PState) (T lci : Nat) :
    HistG (GF := GF) γ σ ∗ lciOk γ T lci ⊢ HistG γ σ ∗ ⌜lci = 0 ∨ ((∃ (T' k' p' : Nat) (es : List Entry),
      T' ≤ T ∧ lci ≤ k' ∧ lci = es.length ∧ σ.commits T' k' p' ∧ ∀ (j : Nat) (e : Entry), es[j]? = some e →
        ent (σ.llog T) (j + 1) = some e ∧ ent (σ.llog T') (j + 1) = some e) ∧
      ∃ T'' k'', T'' ≤ T ∧ lci ≤ k'' ∧ σ.pubs T'' k'')⌝ := by
  unfold lciOk
  iintro ⟨H, #Hc⟩
  icases Hc with (%h | ⟨⟨%T', %k', %p', %es, %h, #Hcm, #Hes⟩, ⟨%T'', %k'', %h'', #Hpb⟩⟩)
  · iframe; ipureintro; left; exact h
  · ihave ⟨H, %hcm⟩ := H_commit_lookup γ σ T' k' p' $$ [H]
    · isplitl [H]; iexact H; iexact Hcm
    ihave ⟨Hes1, Hes2⟩ := BigSepL.bigSepL_sep_eqv.1 $$ Hes
    ihave ⟨H, %h1⟩ := H_llog_lookup_list γ σ T es (fun j => j + 1) $$ [H Hes1]
    · isplitl [H]; iexact H; iexact Hes1
    ihave ⟨H, %h2⟩ := H_llog_lookup_list γ σ T' es (fun j => j + 1) $$ [H Hes2]
    · isplitl [H]; iexact H; iexact Hes2
    ihave ⟨H, %hpb⟩ := H_pub_lookup γ σ T'' k'' $$ [H]
    · isplitl [H]; iexact H; iexact Hpb
    iframe; ipureintro; right
    exact ⟨⟨T', k', p', es, h.1, h.2.1, h.2.2, hcm, fun j e hj => ⟨h1 j e hj, h2 j e hj⟩⟩,
      T'', k'', h''.1, h''.2, hpb⟩

/-- A quorum of matches: all acknowledgements, or one is an install's commit index. -/
theorem acks_or_lci (T k : Nat) (Q : List SID) :
    ([∗list] j ∈ Q, ∃ m, ⌜k ≤ m⌝ ∗ (ackIs (GF := GF) γ j T m ∨ lciOk γ T m)) ⊢
      ([∗list] j ∈ Q, ∃ m, ackIs γ j T m ∗ ⌜k ≤ m⌝) ∨ (∃ m, ⌜k ≤ m⌝ ∗ lciOk γ T m) := by
  induction Q with
  | nil =>
    iintro -; ileft; iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2; iempintro
  | cons a Q ih =>
    iintro Hl
    ihave ⟨⟨%m, %hm, #Hx⟩, Hfs⟩ := BigSepL.bigSepL_cons.1 $$ Hl
    ihave Hr := ih $$ Hfs
    icases Hx with (#Ha | #Hc)
    · icases Hr with (Hr | Hr)
      · ileft; iapply BigSepL.bigSepL_cons.2
        isplitr
        · iexists m; isplitr; · iexact Ha
          ipureintro; exact hm
        · iexact Hr
      · iright; iexact Hr
    · iright; iexists m; isplitr; · ipureintro; exact hm
      iexact Hc

/-- An install's commit index past `T`'s election part is covered by a recorded commit of `T`. -/
theorem lci_commit (E : CoPset) (hE : ↑gprotN ⊆ E) (T k m n : Nat) (ℓ : SID) (hk : n < k)
    (hm : k ≤ m) :
    Inv (GF := GF) γ ∗ leaderIs γ T ℓ ∗ len0Is γ T n ∗ lciOk γ T m ⊢ |={E}=>
      ∃ k' p', ⌜k ≤ k'⌝ ∗ commitIs γ T k' p' := by
  apply Inv_read γ E hE
  intro σ
  unfold InvBody
  iintro ⟨⟨%hg, Hh, Hs, Hr⟩, #Hl, #Hn, #Hc⟩
  ihave ⟨Hh, %hl⟩ := H_leader_lookup γ σ T ℓ $$ [Hh]
  · isplitl [Hh]; iexact Hh; iexact Hl
  ihave ⟨Hh, %hn⟩ := H_len0_lookup γ σ T n $$ [Hh]
  · isplitl [Hh]; iexact Hh; iexact Hn
  ihave ⟨Hh, %hc⟩ := H_lciOk γ σ T m $$ [Hh]
  · isplitl [Hh]; iexact Hh; iexact Hc
  have hn' : σ.len0 T = n := by
    unfold len0F at hn; rw [if_pos (Or.inl (by rw [hl]; simp))] at hn; cases hn; rfl
  have hae : AEok σ T m (termAt (σ.llog T) m) [] m := by
    apply AEok_of σ T m _ [] m (by rw [hl]; simp) _ (fun j e hj => by simp at hj) hc
    rcases hc with h0 | ⟨⟨T', k', p', es, _, _, hes, _, h5⟩, _⟩
    · omega
    · right
      have hj : es[m - 1]? = some es[m - 1] := List.getElem?_eq_getElem (by omega)
      have he := (h5 _ _ hj).1
      rw [show m - 1 + 1 = m by omega] at he
      exact ⟨_, by omega, (termAt_of_ent he).symm, he⟩
  obtain ⟨k', p', hk', hcm⟩ := install_commit σ T m k hg.1 hae (by omega) hm
  ihave ⟨Hh, #Hcm⟩ := H_commit_get γ σ T k' p' hcm $$ Hh
  isplitl [Hh Hs Hr]
  · iframe; ipureintro; exact hg
  iexists k', p'; isplitr; · ipureintro; exact hk'
  iexact Hcm


/-- **installDiscard** (`installSnapshot`'s `DeleteRange(1, lastLogIdx)`, `setLastLog(x, st)`): a
follower of its term (whose leader `ℓ ≠ i` sent the valid install `(x, st)`) whose log does not hold
the entry `(x, st)`: the log becomes the committed prefix up to `x` (length `x`, last term `st`, each
entry committed), and the durable prefix `x`. -/
theorem installDiscard_upd (E : CoPset) (hE : ↑gprotN ⊆ E) (i : SID) (s : SState) (x st : Nat)
    (ℓ : SID) (hℓ : ℓ ≠ i) (hx : 1 ≤ x) (hn : ¬ prevMatch s.log x st) :
    Inv (GF := GF) γ ∗ srvOwn γ i s ∗ logCouple γ i s.log ∗ durView γ i (1 : Qp).half s.dur.1 ∗
      aeValid γ s.term x st [] x ∗ leaderIs γ s.term ℓ ⊢ |={E}=>
      ∃ (L' : RLog) (d : Nat × Nat), srvOwn γ i { s with log := L', dur := d } ∗ logCouple γ i L' ∗
        durView γ i (1 : Qp).half d.1 ∗ durLb γ i x ∗
        ⌜L'.length = x ∧ lastTerm L' = st ∧ d.1 = x⌝ ∗ ([∗list] k ↦ e ∈ L', CIdx γ (k + 1) e) := by
  apply Inv_upd γ E hE
  intro σ
  unfold InvBody
  iintro ⟨⟨%hg, Hh, Hs, Hr, Hcc⟩, Ho, Hlc, Hdv, #Hae, #Hl⟩
  ihave ⟨Hh, %hae⟩ := H_AEok γ σ s.term x st [] x $$ [Hh]
  · isplitl [Hh]; iexact Hh; iexact Hae
  ihave ⟨Hh, %hl⟩ := H_leader_lookup γ σ s.term ℓ $$ [Hh]
  · isplitl [Hh]; iexact Hh; iexact Hl
  ihave ⟨Hh, Hi, Hcl, Ho, %hh⟩ := srvOwn_open γ σ hg i s $$ [Hh Hs Ho]
  · iframe
  obtain ⟨hi, hs⟩ := hh
  subst hs
  have hi' : i ∈ σ.srvs := by rw [hg.2.1]; exact hi
  have hP := hg.1
  obtain ⟨T', hpre⟩ : ∃ T', installDiscardPre σ i x st T' := by
    rcases hae.2.2.2.2.2 with hz | ⟨⟨T', k', p', hT', hk', hc, hag⟩, _⟩
    · omega
    exact ⟨T', hi', hx, hae, hn, ⟨ℓ, hℓ, hl⟩, hT', ⟨k', p', hk', hc⟩, hag⟩
  obtain ⟨hP', hGr⟩ := installDiscard_inv σ i x st T' hP hpre
  obtain ⟨hlen, hlt, hents⟩ := installDiscard_log σ i x st T' hP hpre
  have hL' : (installDiscard σ i x T').log i = (σ.llog (σ.term i)).take x := by
    show (setSrv σ i _).log i = _; rw [setSrv_log]; simp
  rw [hL'] at hlen hlt hents
  have hd1 : (σ.srv i).dur.1 ≤ x := by
    have := hGr.2.2.2.2.2.2.2.2.2.2.1 i
    simpa [installDiscard, upd] using this
  ihave ⟨Ht, Hd, Hsv, Hlg, Hc⟩ := (srvG_eq γ i (σ.srv i)).1 $$ Hi
  unfold logCouple
  icases Hlc with ⟨Hlc, #Hv⟩
  imod ghostVar_update_halves ((σ.llog (σ.term i)).take x) (γ.slog i) _ _ $$ Hlg Hlc
    with ⟨Hlg, Hlc⟩
  unfold durView durLb
  imod monoNat_update_halves (γ.dur i) (σ.srv i).dur.1 (σ.srv i).dur.1 x hd1 $$ [Hd Hdv]
    with ⟨Hd, Hdv, #Hlb⟩
  · iframe
  imod srvOwn_update γ i (σ.srv i) (σ.srv i)
    { σ.srv i with log := (σ.llog (σ.term i)).take x, dur := (x, T') } $$ [Ho Hsv] with ⟨Ho, Hsv⟩
  · iframe
  ihave Hi := (srvG_eq γ i { σ.srv i with log := (σ.llog (σ.term i)).take x, dur := (x, T') }).2
    $$ [Ht Hd Hsv Hlg Hc]
  · iframe
  ihave Hs := Hcl $$ %{ σ.srv i with log := (σ.llog (σ.term i)).take x, dur := (x, T') } Hi
  imod HistG_grow γ σ _ hP hGr (fun T k e h _ => ⟨T, h⟩) [] (fun _ _ => rfl) [] (fun _ _ => rfl)
    [] (fun _ _ => rfl) [] (fun _ _ => rfl) [] (fun _ _ => rfl) [] (fun _ _ => rfl)
    [] (fun _ _ => rfl) $$ Hh with Hh
  ihave ⟨Hh, Hcs⟩ := H_C_get_list γ (installDiscard σ i x T') ((σ.llog (σ.term i)).take x)
    (fun j => j + 1) (by
      intro j e hj
      have hjl : j < x := by
        have := (List.getElem?_eq_some_iff.mp hj).1; rw [hlen] at this; exact this
      show ent σ.C (j + 1) = some e
      rw [← hents (j + 1) (by omega) (by omega), ent_succ]; exact hj) $$ Hh
  imodintro
  isplitl [Hh Hs Hr Hcc]
  · iapply InvInner_close γ (installDiscard σ i x T')
      (upd σ.srv i { σ.srv i with log := (σ.llog (σ.term i)).take x, dur := (x, T') })
      (σ.maxT + σ.maxI) rfl (Nat.le_refl _) (GInv_step hg hP' hGr hg.2.2.2.2.1)
    iframe
    iapply CcfgG_congr γ σ (installDiscard σ i x T') rfl rfl rfl $$ Hcc
  iexists ((σ.llog (σ.term i)).take x), (x, T')
  isplitl [Ho]; · iexact Ho
  isplitl [Hlc]; · iframe; iexact Hv
  isplitl [Hdv]; · iexact Hdv
  isplitr; · iexact Hlb
  isplitr; · ipureintro; exact ⟨hlen, hlt, rfl⟩
  iexact Hcs

/-- **A valid install is committed** (the restore's last entry; the snapshot store's facts). -/
theorem aeValid_install_CIdx (E : CoPset) (hE : ↑gprotN ⊆ E) (T x st : Nat) (hx : 1 ≤ x) :
    Inv (GF := GF) γ ∗ aeValid γ T x st [] x ⊢ |={E}=> ∃ e, CIdx γ x e ∗ ⌜e.term = st⌝ := by
  apply Inv_read γ E hE
  intro σ
  unfold InvBody
  iintro ⟨⟨%hg, Hh, Hs, Hr⟩, #Hae⟩
  ihave ⟨Hh, %hae⟩ := H_AEok γ σ T x st [] x $$ [Hh]
  · isplitl [Hh]; iexact Hh; iexact Hae
  obtain ⟨e, he, het⟩ := AEok_install_C σ T x st hg.1 hx hae
  ihave ⟨Hh, #Hc⟩ := H_C_get γ σ x e he $$ Hh
  isplitl [Hh Hs Hr]
  · iframe; ipureintro; exact hg
  iexists e; isplitr; · iexact Hc
  ipureintro; exact het

/-- **The sender's own snapshot** (`sendLatestSnapshot`, `setPreviousLog` with `lastSnapshot`): a
committed index `x ≥ 1` within `i`'s durable prefix is a valid install of `T` while `i` leads `T`, or
`i` has left `T` (the D12 shape; the sender's term check refutes the right side). -/
theorem snapValid_or_left (E : CoPset) (hE : ↑gprotN ⊆ E) (i : SID) (T x : Nat) (e : Entry)
    (hx : 1 ≤ x) :
    Inv (GF := GF) γ ∗ isSrv γ i ∗ durLb γ i x ∗ CIdx γ x e ∗ leaderIs γ T i ∗ termLb γ i T ⊢
      |={E}=> aeValid γ T x e.term [] x ∨ termLb γ i (T + 1) := by
  apply Inv_read γ E hE
  intro σ
  unfold InvBody
  iintro ⟨⟨%hg, Hh, Hs, Hr⟩, #Hv, #Hd, #Hc, #Hl, #Ht⟩
  unfold isSrv
  ihave ⟨Hh, %hv⟩ := H_voter_lookup γ σ i $$ [Hh]
  · isplitl [Hh]; iexact Hh; iexact Hv
  ihave ⟨Hh, %hC⟩ := H_C_lookup γ σ x e $$ [Hh]
  · isplitl [Hh]; iexact Hh; iexact Hc
  ihave ⟨Hh, %hl⟩ := H_leader_lookup γ σ T i $$ [Hh]
  · isplitl [Hh]; iexact Hh; iexact Hl
  have hi : i ∈ γ.srvs := by rw [← hg.2.1]; exact hv
  ihave ⟨Hi, Hcl⟩ := srvs_peek γ σ i hi $$ Hs
  ihave ⟨Hi, %hT⟩ := srvG_term_lb γ i (σ.srv i) T $$ [Hi]
  · isplitl [Hi]; iexact Hi; iexact Ht
  ihave ⟨Hi, %hdx⟩ := srvG_dur_lb γ i (σ.srv i) x $$ [Hi]
  · isplitl [Hi]; iexact Hi; iexact Hd
  ihave ⟨Hi, #Hlb2⟩ := srvG_term_get_lb γ i (σ.srv i) $$ Hi
  ihave Hs := Hcl $$ Hi
  by_cases hTe : (σ.srv i).term = T
  · have hl' : σ.leader (σ.term i) = some i := by
      show σ.leader (σ.srv i).term = _; rw [hTe]; exact hl
    have hae := dur_install σ i x e hg.1 hv hl' hx hdx hC
    have hae' : AEok σ T x e.term [] x := by
      have e1 : σ.term i = T := hTe
      rw [e1] at hae; exact hae
    ihave ⟨Hh, #Hae⟩ := H_aeValid_install γ σ T x e.term hx hae' $$ Hh
    isplitl [Hh Hs Hr]
    · iframe; ipureintro; exact hg
    ileft; iexact Hae
  · isplitl [Hh Hs Hr]
    · iframe; ipureintro; exact hg
    iright
    iapply termLb_mono γ i (σ.srv i).term (T + 1) (by omega) $$ Hlb2

/-- **The sender's installed snapshot** (one `i` received as a follower of the term `t`, whose leader
`ℓ ≠ i` sent it, `aeValid γ t …`): a valid install of any term `T` `i` leads (then `t < T`: `t = T`
would make `i` the leader of `t`; leader completeness carries it to `T`), or `i` has left `T`
(`T < t`). -/
theorem snapValid_follow (E : CoPset) (hE : ↑gprotN ⊆ E) (i ℓ : SID) (t T x st : Nat) (hℓ : ℓ ≠ i)
    (hx : 1 ≤ x) :
    Inv (GF := GF) γ ∗ aeValid γ t x st [] x ∗ leaderIs γ t ℓ ∗ termLb γ i t ∗ leaderIs γ T i ⊢
      |={E}=> aeValid γ T x st [] x ∨ termLb γ i (T + 1) := by
  apply Inv_read γ E hE
  intro σ
  unfold InvBody
  iintro ⟨⟨%hg, Hh, Hs, Hr⟩, #Hae, #Hl, #Ht, #HlT⟩
  ihave ⟨Hh, %hae⟩ := H_AEok γ σ t x st [] x $$ [Hh]
  · isplitl [Hh]; iexact Hh; iexact Hae
  ihave ⟨Hh, %hl⟩ := H_leader_lookup γ σ t ℓ $$ [Hh]
  · isplitl [Hh]; iexact Hh; iexact Hl
  ihave ⟨Hh, %hlT⟩ := H_leader_lookup γ σ T i $$ [Hh]
  · isplitl [Hh]; iexact Hh; iexact HlT
  rcases Nat.lt_trichotomy t T with hlt | heq | hgt
  · have hae' := AEok_install_later σ t T x st hg.1 hx hae hlt (by rw [hlT]; simp)
    ihave ⟨Hh, #Hv⟩ := H_aeValid_install γ σ T x st hx hae' $$ Hh
    isplitl [Hh Hs Hr]
    · iframe; ipureintro; exact hg
    ileft; iexact Hv
  · subst heq
    exfalso
    exact hℓ (Option.some.inj (hl.symm.trans hlT))
  · isplitl [Hh Hs Hr]
    · iframe; ipureintro; exact hg
    iright
    iapply termLb_mono γ i t (T + 1) (by omega) $$ Ht

/-- **The commitment counts an install** (`commitment.match(peer, meta.Index)` after a successful
InstallSnapshot of `T`; `recalculate`): a quorum (stage 4: of the configuration the commitment
counts, the entry `e` at `p` of `llog T`, `ccfgOwn`) match index `k` past `T`'s election part, each
member's match an acknowledgement or a valid install's commit index (`lciOk γ T m`), is covered by a
recorded commit of `T` (a new one at `p`, `commit_upd`, if all are acknowledgements; an existing
one, `proto.install_commit`, otherwise). -/
theorem commit_or_snap (E : CoPset) (hE : ↑gprotN ⊆ E) (T k n p : Nat) (ℓ : SID) (e : Entry)
    (Q : List SID) (hQ : isQuorumOf (γ.cv e.data) Q) (hk : n < k) :
    Inv (GF := GF) γ ∗ leaderIs γ T ℓ ∗ len0Is γ T n ∗ ccfgOwn γ ℓ T p ∗ llogIdx γ T p e ∗
      ([∗list] j ∈ Q, ∃ m, ⌜k ≤ m⌝ ∗ (ackIs γ j T m ∨ lciOk γ T m)) ⊢ |={E}=>
      ccfgOwn γ ℓ T p ∗ ∃ k' p', ⌜k ≤ k'⌝ ∗ commitIs γ T k' p' := by
  iintro ⟨#Hinv, #Hl, #Hn, Hk, #He, Hq⟩
  ihave Hq := acks_or_lci γ T k Q $$ Hq
  icases Hq with (Hq | ⟨%m, %hm, #Hc⟩)
  · imod commit_upd γ E hE T k n p ℓ e Q hQ hk $$ [$Hinv $Hl $Hn $Hk $He $Hq] with ⟨Hk, #Hcm⟩
    imodintro
    isplitl [Hk]; · iexact Hk
    iexists k, p; isplitr; · ipureintro; exact Nat.le_refl _
    iexact Hcm
  · imod lci_commit γ E hE T k m n ℓ hk hm $$ [$Hinv $Hl $Hn $Hc] with Hc
    imodintro
    isplitl [Hk]; · iexact Hk
    iexact Hc

/-- The committed log's terms do not decrease (`snapstore` keeps the newer by term, then index: a
snapshot at a smaller index is not newer). -/
theorem CIdx_term_mono (E : CoPset) (hE : ↑gprotN ⊆ E) (x s : Nat) (e1 e2 : Entry) (h : x ≤ s) :
    Inv (GF := GF) γ ∗ CIdx γ x e1 ∗ CIdx γ s e2 ⊢ |={E}=> ⌜e1.term ≤ e2.term⌝ := by
  apply Inv_read γ E hE
  intro σ
  unfold InvBody
  iintro ⟨⟨%hg, Hh, Hs, Hr⟩, #H1, #H2⟩
  ihave ⟨Hh, %h1⟩ := H_C_lookup γ σ x e1 $$ [Hh]
  · isplitl [Hh]; iexact Hh; iexact H1
  ihave ⟨Hh, %h2⟩ := H_C_lookup γ σ s e2 $$ [Hh]
  · isplitl [Hh]; iexact Hh; iexact H2
  isplitl [Hh Hs Hr]
  · iframe; ipureintro; exact hg
  ipureintro; exact C_term_mono σ x s e1 e2 hg.1 h h1 h2

/-- A durable index is below the bound on log lengths (`compactLogs`' `DeleteRange` needs its range
end `< 2^64 - 1`). -/
theorem durLb_lt (E : CoPset) (hE : ↑gprotN ⊆ E) (i : SID) (x : Nat) :
    Inv (GF := GF) γ ∗ isSrv γ i ∗ durLb γ i x ⊢ |={E}=> ⌜x < 2 ^ 62⌝ := by
  apply Inv_read γ E hE
  intro σ
  unfold InvBody
  iintro ⟨⟨%hg, Hh, Hs, Hr⟩, #Hv, #Hd⟩
  unfold isSrv
  ihave ⟨Hh, %hv⟩ := H_voter_lookup γ σ i $$ [Hh]
  · isplitl [Hh]; iexact Hh; iexact Hv
  have hi : i ∈ γ.srvs := by rw [← hg.2.1]; exact hv
  ihave ⟨Hi, Hcl⟩ := srvs_peek γ σ i hi $$ Hs
  ihave ⟨Hi, %hx⟩ := srvG_dur_lb γ i (σ.srv i) x $$ [Hi]
  · isplitl [Hi]; iexact Hi; iexact Hd
  ihave Hs := Hcl $$ Hi
  ihave ⟨Hr, Hcc⟩ := Hr
  ihave ⟨Hr, %hb⟩ := receipt_bound _ $$ Hr
  isplitl [Hh Hs Hr Hcc]
  · iframe; ipureintro; exact hg
  ipureintro
  have h1 : (σ.srv i).dur.1 ≤ (σ.srv i).log.length := dur_le_log σ i hg.1 hv
  have h2 : (σ.srv i).log.length ≤ σ.maxI := log_le_maxI σ i hg.1 hv
  omega

end install

end gprot
end github_com.hashicorp.raft

end Perennial
