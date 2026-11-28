/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/gprot/Internal.lean (241f27e).
-/
/-
`gprot` internals — opening and re-closing the invariant, per-voter access, growing the
history's ghost maps along a step, and pure helpers. Used only by `Laws.lean`.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.gprot.Defs
public import Perennial.ProgramLogic.Bounds

@[expose] public section

set_option linter.unusedVariables false
set_option linter.deprecated false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace github_com.hashicorp.raft
namespace gprot

open proto

/-! ## Pure helpers -/

theorem ent_prefix {L L' : RLog} {k : Nat} {e : Entry} (h : L <+: L') (he : ent L k = some e) :
    ent L' k = some e := by
  unfold ent at *
  split at he
  · cases he
  · rw [if_neg (by assumption)]; exact prefix_getElem? h he

theorem ent_pos {L : RLog} {k : Nat} {e : Entry} (he : ent L k = some e) : 1 ≤ k := by
  unfold ent at he; split at he
  · cases he
  · omega

theorem ent_le_length {L : RLog} {k : Nat} {e : Entry} (he : ent L k = some e) : k ≤ L.length := by
  unfold ent at he; split at he
  · cases he
  · have := (List.getElem?_eq_some_iff.mp he).1; omega

theorem ent_succ (L : RLog) (j : Nat) : ent L (j + 1) = L[j]? := by
  unfold ent; simp

theorem ent_eq_getElem? (L : RLog) (k : Nat) (hk : 1 ≤ k) : ent L k = L[k - 1]? := by
  unfold ent; rw [if_neg (by omega)]

theorem agree_mono {A B : RLog} {k k' : Nat} (h : agree A B k) (hk : k' ≤ k) : agree A B k' := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨by omega, by omega, ?_⟩
  have := congrArg (List.take k') h3
  rwa [List.take_take, List.take_take, Nat.min_eq_left hk] at this

theorem agree_ent {A B : RLog} {k x : Nat} (h : agree A B k) (hx : x ≤ k) : ent A x = ent B x := by
  obtain ⟨h1, h2, h3⟩ := h
  unfold ent
  split
  · rfl
  · have ha : A[x - 1]? = (A.take k)[x - 1]? := by rw [List.getElem?_take]; rw [if_pos (by omega)]
    have hb : B[x - 1]? = (B.take k)[x - 1]? := by rw [List.getElem?_take]; rw [if_pos (by omega)]
    rw [ha, hb, h3]

theorem list_of_ents {L es : RLog} {base : Nat}
    (h : ∀ (j : Nat) (e : Entry), es[j]? = some e → L[base + j]? = some e) :
    (es = [] ∨ base + es.length ≤ L.length) ∧ es = (L.drop base).take es.length := by
  constructor
  · cases hes : es.length with
    | zero => left; exact List.length_eq_zero_iff.mp hes
    | succ n =>
      right
      have hj : es[n]? = some es[n] := List.getElem?_eq_getElem (by omega)
      have := (List.getElem?_eq_some_iff.mp (h n _ hj)).1
      omega
  · apply List.ext_getElem?
    intro j
    rw [List.getElem?_take, List.getElem?_drop]
    split
    · rename_i hj
      rw [h j es[j] (List.getElem?_eq_getElem hj)]
      exact List.getElem?_eq_getElem hj
    · rename_i hj
      exact List.getElem?_eq_none (by omega)

theorem agree_of_ents {L L' es : RLog}
    (h : ∀ (j : Nat) (e : Entry), es[j]? = some e → L[j]? = some e ∧ L'[j]? = some e) :
    agree L L' es.length := by
  have h1 := list_of_ents (L := L) (base := 0) (fun j e hj => by rw [Nat.zero_add]; exact (h j e hj).1)
  have h2 := list_of_ents (L := L') (base := 0) (fun j e hj => by rw [Nat.zero_add]; exact (h j e hj).2)
  simp only [List.drop_zero, Nat.zero_add] at h1 h2
  refine ⟨?_, ?_, ?_⟩
  · rcases h1.1 with h | h
    · subst h; simp
    · exact h
  · rcases h2.1 with h | h
    · subst h; simp
    · exact h
  · rw [← h1.2, ← h2.2]

theorem AEok_of (σ : PState) (T prev pt : Nat) (ents : RLog) (lci : Nat)
    (hl : σ.leader T ≠ none)
    (hp : (prev = 0 ∧ pt = 0) ∨ ∃ e : Entry, 1 ≤ prev ∧ e.term = pt ∧ ent (σ.llog T) prev = some e)
    (he : ∀ (j : Nat) (e : Entry), ents[j]? = some e → ent (σ.llog T) (prev + 1 + j) = some e)
    (hc : lci = 0 ∨ ((∃ (T' k' p' : Nat) (es : List Entry), T' ≤ T ∧ lci ≤ k' ∧ lci = es.length ∧
      σ.commits T' k' p' ∧
      ∀ (j : Nat) (e : Entry), es[j]? = some e → ent (σ.llog T) (j + 1) = some e ∧ ent (σ.llog T') (j + 1) = some e) ∧
      ∃ T'' k'', T'' ≤ T ∧ lci ≤ k'' ∧ σ.pubs T'' k'')) :
    AEok σ T prev pt ents lci := by
  have he' : ∀ (j : Nat) (e : Entry), ents[j]? = some e → (σ.llog T)[prev + j]? = some e := by
    intro j e hj
    have := he j e hj
    rw [show prev + 1 + j = (prev + j) + 1 by omega, ent_succ] at this
    exact this
  obtain ⟨hlen, htake⟩ := list_of_ents he'
  refine ⟨hl, ?_, ?_, ?_, htake, ?_⟩
  · rcases hlen with h | h
    · subst h
      rcases hp with ⟨h1, _⟩ | ⟨e, _, _, h3⟩
      · simp [h1]
      · simpa using ent_le_length h3
    · exact h
  · intro h0
    rcases hp with ⟨_, h2⟩ | ⟨e, h1, _, _⟩
    · exact h2
    · omega
  · intro h1
    rcases hp with ⟨h0, _⟩ | ⟨e, _, h2, h3⟩
    · omega
    · unfold termAt; rw [h3]; exact h2
  · rcases hc with h | ⟨⟨T', k', p', es, h1, h2, h3, h4, h5⟩, hpb⟩
    · left; exact h
    · right
      refine ⟨⟨T', k', p', h1, h2, h4, ?_⟩, hpb⟩
      rw [h3]
      apply agree_of_ents
      intro j e hj
      have := h5 j e hj
      rw [ent_succ, ent_succ] at this
      exact this

theorem ent_append_left (L es : RLog) (k : Nat) (hk : k ≤ L.length) :
    ent (L ++ es) k = ent L k := by
  unfold ent; split
  · rfl
  · rw [List.getElem?_append_left (by omega)]

theorem ent_append_right (L es : RLog) (j : Nat) :
    ent (L ++ es) (L.length + 1 + j) = es[j]? := by
  rw [show L.length + 1 + j = (L.length + j) + 1 by omega, ent_succ,
    List.getElem?_append_right (by omega)]
  congr 1; omega

theorem ent_none_of_gt (L : RLog) (k : Nat) (hk : L.length < k) : ent L k = none := by
  unfold ent; split
  · rfl
  · exact List.getElem?_eq_none (by omega)

/-- (stage 4) A log starting with a configuration has one in each non-empty prefix. -/
theorem lastCfgIdx_take_pos {L : RLog} {n : Nat} {e : Entry} (he : ent L 1 = some e)
    (hk : e.kind = kConfig) (hn : 1 ≤ n) : 1 ≤ lastCfgIdx (L.take n) := by
  apply Nat.pos_of_ne_zero
  intro h0
  have := (lastCfgIdx_spec (L.take n)).2.2 1 e (by omega) (by rw [proto.ent_take _ _ _ hn]; exact he)
  exact this hk

/-- (stage 4) A leader's commitment counts a configuration entry, at an index `≥ 1`. -/
theorem ccfg_pos {σ : PState} (hP : PInv σ) {T : Nat} {ℓ : SID} (hl : σ.leader T = some ℓ) :
    1 ≤ σ.ccfg T := by
  obtain ⟨_, _, h0, h0l, hg1, _, _, _, _, hadm⟩ := hP.2.1.1 T ℓ hl
  have hgk := hP.1.2.1
  rcases hadm with h | ⟨h1, h2⟩
  · rw [h]; exact lastCfgIdx_take_pos hg1 hgk (by omega)
  · rw [h2]; exact lastCfgIdx_take_pos hg1 hgk (by omega)

/-- (stage 4) A positive latest configuration index of a prefix is a configuration entry of the
log. -/
theorem lastCfgIdx_take_ent {L : RLog} {n : Nat} (h : 1 ≤ lastCfgIdx (L.take n)) :
    ∃ e, ent L (lastCfgIdx (L.take n)) = some e ∧ e.kind = kConfig := by
  obtain ⟨hle, hor, _⟩ := lastCfgIdx_spec (L.take n)
  rcases hor with h0 | ⟨e, he, hk⟩
  · omega
  · have : lastCfgIdx (L.take n) ≤ n := Nat.le_trans hle (List.length_take_le _ _)
    rw [proto.ent_take _ _ _ this] at he
    exact ⟨e, he, hk⟩

/-- (stage 4) A leader's commitment counts a configuration entry of its leader log. -/
theorem ccfg_entry {σ : PState} (hP : PInv σ) {T : Nat} {ℓ : SID} (hl : σ.leader T = some ℓ) :
    ∃ e, ent (σ.llog T) (σ.ccfg T) = some e ∧ e.kind = kConfig := by
  obtain ⟨_, _, h0, h0l, hg1, _, _, _, _, hadm⟩ := hP.2.1.1 T ℓ hl
  have hgk := hP.1.2.1
  rcases hadm with h | ⟨h1, h2⟩
  · rw [h]; exact lastCfgIdx_take_ent (lastCfgIdx_take_pos hg1 hgk (by omega))
  · rw [h2]; exact lastCfgIdx_take_ent (lastCfgIdx_take_pos hg1 hgk (by omega))

/-! ## Facts about `σ` from `GInv`/`PInv` -/

theorem GInv_step {γ : GNames} {σ σ' : PState} (h : GInv γ σ) (hP : PInv σ') (hG : Grows σ σ')
    (hK : IKinds σ') : GInv γ σ' := by
  obtain ⟨_, hv, hg, hc, _, hn⟩ := h
  obtain ⟨gV, ⟨gG, gC⟩, _⟩ := hG
  exact ⟨hP, by rw [gV, hv], by rw [gG, hg], by rw [gC, hc], hK, hn⟩

/-- The operation-token facts survive a step whose new leader-log commands are copies (at the
same index) of existing ones, and whose committed log only grows. -/
theorem OpsOK_mono {σ σ' : PState} {O : GMap (List w8) Nat}
    (hL : ∀ T k e, ent (σ'.llog T) k = some e → e.kind = kCommand → ∃ T', ent (σ.llog T') k = some e)
    (hC : σ.C <+: σ'.C) (h : OpsOK σ O) : OpsOK σ' O := by
  obtain ⟨ha, hb, hc⟩ := h
  refine ⟨fun T k e he hk => ?_, fun T1 k1 e1 T2 k2 e2 h1 h2 hk1 hk2 hd => ?_,
    fun d n y hn ⟨T, e, he, hk, hd⟩ => ?_⟩
  · obtain ⟨T', he'⟩ := hL T k e he hk; exact ha T' k e he' hk
  · obtain ⟨T1', h1'⟩ := hL _ _ _ h1 hk1
    obtain ⟨T2', h2'⟩ := hL _ _ _ h2 hk2
    exact hb _ _ _ _ _ _ h1' h2' hk1 hk2 hd
  · obtain ⟨T', he'⟩ := hL T y e he hk
    rcases hc d n y hn ⟨T', e, he', hk, hd⟩ with h | ⟨e', h1, h2⟩
    · left; exact h
    · right; exact ⟨e', ent_prefix hC h1, h2⟩

theorem llogF_sub {σ σ' : PState} (hP : PInv σ) (hG : Grows σ σ') :
    ∀ p v, llogF σ p = some v → llogF σ' p = some v := by
  intro ⟨T, k⟩ v h
  unfold llogF at *
  exact ent_prefix (hG.2.2.2.1 T).1 h

theorem len0F_sub {σ σ' : PState} (hG : Grows σ σ') :
    ∀ T v, len0F σ T = some v → len0F σ' T = some v := by
  intro T v h
  unfold len0F at *
  split at h
  · rename_i hc
    have hl := (hG.2.2.2.1 T).2 hc
    have hc' : σ'.leader T ≠ none ∨ T = 1 := by
      rcases hc with hc | hc
      · left
        cases hT : σ.leader T with
        | none => exact absurd hT hc
        | some ℓ => rw [hG.2.2.1 T ℓ hT]; simp
      · right; exact hc
    rw [if_pos hc', hl]; exact h
  · cases h

theorem acksF_sub {σ σ' : PState} (hG : Grows σ σ') :
    ∀ p v, acksF σ p = some v → acksF σ' p = some v := by
  intro p v h
  unfold acksF at *
  split at h
  · rename_i hc; rw [if_pos (hG.2.2.2.2.2.2.1 _ _ _ hc)]
  · cases h

theorem commitsF_sub {σ σ' : PState} (hG : Grows σ σ') :
    ∀ p v, commitsF σ p = some v → commitsF σ' p = some v := by
  intro p v h
  unfold commitsF at *
  split at h
  · rename_i hc; rw [if_pos (hG.2.2.2.2.2.2.2.1 _ _ _ hc)]
  · cases h

theorem acksF_iff (σ : PState) (j : SID) (T m : Nat) :
    acksF σ (j, T, m) = some () ↔ σ.acked j T m := by
  unfold acksF; split <;> simp_all

theorem commitsF_iff (σ : PState) (T k p : Nat) :
    commitsF σ (T, k, p) = some () ↔ σ.commits T k p := by
  unfold commitsF; split <;> simp_all

theorem acksF_congr {σ σ' : PState} (h : σ'.acked = σ.acked) (p : SID × Nat × Nat) :
    acksF σ' p = acksF σ p := by
  unfold acksF; rw [h]

theorem commitsF_congr {σ σ' : PState} (h : σ'.commits = σ.commits) (p : Nat × Nat × Nat) :
    commitsF σ' p = commitsF σ p := by
  unfold commitsF; rw [h]

theorem acksF_of_iff {σ σ' : PState} (p : SID × Nat × Nat)
    (h : σ'.acked p.1 p.2.1 p.2.2 ↔ σ.acked p.1 p.2.1 p.2.2) : acksF σ' p = acksF σ p := by
  unfold acksF
  by_cases h1 : σ.acked p.1 p.2.1 p.2.2
  · rw [if_pos (h.2 h1), if_pos h1]
  · rw [if_neg (fun h2 => h1 (h.1 h2)), if_neg h1]

theorem commitsF_of_iff {σ σ' : PState} (p : Nat × Nat × Nat)
    (h : σ'.commits p.1 p.2.1 p.2.2 ↔ σ.commits p.1 p.2.1 p.2.2) : commitsF σ' p = commitsF σ p := by
  unfold commitsF
  by_cases h1 : σ.commits p.1 p.2.1 p.2.2
  · rw [if_pos (h.2 h1), if_pos h1]
  · rw [if_neg (fun h2 => h1 (h.1 h2)), if_neg h1]

theorem srvsF_iff (σ : PState) (i : SID) : srvsF σ i = some () ↔ i ∈ σ.srvs := by
  unfold srvsF; split <;> simp_all

theorem pubsF_iff (σ : PState) (T k : Nat) :
    pubsF σ (T, k) = some () ↔ σ.pubs T k := by
  unfold pubsF; split <;> simp_all

theorem pubsF_congr {σ σ' : PState} (h : σ'.pubs = σ.pubs) (p : Nat × Nat) :
    pubsF σ' p = pubsF σ p := by
  unfold pubsF; rw [h]

theorem PInv.gen {σ : PState} (h : PInv σ) : IGen σ := h.1
theorem PInv.leaders {σ : PState} (h : PInv σ) : ILeaders σ := h.2.1
theorem PInv.logs {σ : PState} (h : PInv σ) : ILogs σ := h.2.2.1
theorem PInv.current {σ : PState} (h : PInv σ) : ICurrent σ := h.2.2.2.1
theorem PInv.votes {σ : PState} (h : PInv σ) : IVotes σ := h.2.2.2.2.1
theorem PInv.acks {σ : PState} (h : PInv σ) : IAcks σ := h.2.2.2.2.2.1
theorem PInv.commits {σ : PState} (h : PInv σ) : ICommits σ := h.2.2.2.2.2.2.2.2.1
theorem PInv.dur {σ : PState} (h : PInv σ) : IDur σ := h.2.2.2.2.2.2.2.2.2.1
theorem PInv.bounds {σ : PState} (h : PInv σ) : IBounds σ := h.2.2.2.2.2.2.2.2.2.2.1

/-! ## The ghost layer -/

section internal
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable (γ : GNames)

instance InvInner_timeless : Timeless (InvInner (GF := GF) γ) := by
  unfold InvInner InvBody HistG OpsG srvG PubMaxG SnapG CcfgG; infer_instance

theorem InvInner_eq : InvInner (GF := GF) γ ⊣⊢ ∃ σ, InvBody γ σ := by
  unfold InvInner; exact .rfl

theorem InvInner_intro (σ : PState) : InvBody (GF := GF) γ σ ⊢ InvInner γ := by
  unfold InvInner
  iintro H; iexists σ; iexact H

/-- Every law: a ghost update of the opened invariant. -/
theorem Inv_upd (E : CoPset) (hE : ↑gprotN ⊆ E) (P Q : IProp GF)
    (h : ∀ σ, InvBody γ σ ∗ P ⊢ |==> (InvInner γ ∗ Q)) :
    Inv γ ∗ P ⊢ |={E}=> Q := by
  rw [Inv_unseal]; unfold InvDef
  iintro ⟨#Hinv, HP⟩
  imod inv_acc_timeless hE $$ Hinv with ⟨Hi, Hcl⟩
  ihave ⟨%σ, Hb⟩ := (InvInner_eq γ).1 $$ Hi
  imod h σ $$ [Hb HP] with ⟨Hi, HQ⟩
  · isplitl [Hb]
    · iexact Hb
    · iexact HP
  imod Hcl $$ Hi with -
  imodintro
  iexact HQ

/-- A law that only reads the invariant. -/
theorem Inv_read (E : CoPset) (hE : ↑gprotN ⊆ E) (P Q : IProp GF)
    (h : ∀ σ, InvBody γ σ ∗ P ⊢ InvBody γ σ ∗ Q) :
    Inv γ ∗ P ⊢ |={E}=> Q := by
  apply Inv_upd γ E hE P Q
  intro σ
  iintro H
  ihave ⟨Hb, HQ⟩ := h σ $$ H
  imodintro
  isplitl [Hb]
  · iapply InvInner_intro γ σ $$ Hb
  · iexact HQ

theorem receipt_le {m n : Nat} (h : m ≤ n) : receipt (GF := GF) n ⊢ receipt m := by
  have := (receipt_add (GF := GF) m (n - m)).1
  rw [show m + (n - m) = n by omega] at this
  exact this.trans sep_elim_left

theorem receipt_bound [hRB : ReceiptBoundLe GF (2 ^ 62)] (n : Nat) :
    receipt (GF := GF) n ⊢ receipt n ∗ ⌜n < 2 ^ 62⌝ := by
  have h1 : receipt (GF := GF) n ⊢ ⌜n < 2 ^ 62⌝ :=
    (receipt_lt n).trans (pure_mono fun h => Nat.lt_of_lt_of_le h (ReceiptBoundLe.le (2 ^ 62)))
  iintro H
  ihave %hb := h1 $$ H
  isplitl [H]
  · iexact H
  · ipureintro; exact hb

/-- Re-close the invariant at `σ'`, given its servers as `f` and receipts for its bounds. -/
theorem InvInner_close (σ' : PState) (f : SID → SState) (n : Nat) (hsrv : σ'.srv = f)
    (hn : σ'.maxT + σ'.maxI ≤ n) (hg : GInv γ σ') :
    HistG (GF := GF) γ σ' ∗ ([∗list] j ∈ γ.srvs, srvG γ j (f j)) ∗ receipt n ∗ CcfgG γ σ' ⊢
      InvInner γ := by
  subst hsrv
  iintro ⟨Hh, Hs, Hr, Hc⟩
  iapply InvInner_intro γ σ'
  unfold InvBody
  ihave Hr := receipt_le hn $$ Hr
  iframe; ipureintro; exact hg

/-- (stage 4) The commitments' configurations survive a step that changes no candidate, leader or
`ccfg`. -/
theorem CcfgG_congr (σ σ' : PState) (hc : σ'.cand = σ.cand) (hl : σ'.leader = σ.leader)
    (hf : σ'.ccfg = σ.ccfg) : CcfgG (GF := GF) γ σ ⊢ CcfgG γ σ' := by
  unfold CcfgG; rw [hc, hl, hf]

/-! ### Per-voter access -/

theorem srvs_congr (l : List SID) (f g : SID → SState) (h : ∀ j ∈ l, f j = g j) :
    ([∗list] j ∈ l, srvG (GF := GF) γ j (f j)) ⊢ [∗list] j ∈ l, srvG γ j (g j) := by
  induction l with
  | nil => exact .rfl
  | cons a l ih =>
    refine BigSepL.bigSepL_cons.1.trans (Entails.trans (sep_mono ?_ ?_) BigSepL.bigSepL_cons.2)
    · rw [h a List.mem_cons_self]
    · exact ih (fun j hj => h j (List.mem_cons_of_mem a hj))

theorem srvs_acc (vs : List SID) (hnd : vs.Nodup) (i : SID) (hi : i ∈ vs) (f : SID → SState) :
    ([∗list] j ∈ vs, srvG (GF := GF) γ j (f j)) ⊢
      srvG γ i (f i) ∗ ∀ s', srvG γ i s' -∗ [∗list] j ∈ vs, srvG γ j (upd f i s' j) := by
  obtain ⟨l1, l2, rfl⟩ := List.append_of_mem hi
  have h1 : i ∉ l1 := by
    intro h; have := (List.nodup_append.mp hnd).2.2 i h i List.mem_cons_self; exact this rfl
  have h2 : i ∉ l2 := (List.nodup_cons.mp (List.nodup_append.mp hnd).2.1).1
  have e : ∀ g : SID → SState, ([∗list] j ∈ l1 ++ i :: l2, srvG (GF := GF) γ j (g j)) ⊣⊢
      ([∗list] j ∈ l1, srvG γ j (g j)) ∗ srvG γ i (g i) ∗ [∗list] j ∈ l2, srvG γ j (g j) :=
    fun g => BigSepL.bigSepL_append.trans (sep_congr .rfl BigSepL.bigSepL_cons)
  rw [(e f).to_eq]
  iintro ⟨H1, Hi, H2⟩
  isplitl [Hi]
  · iexact Hi
  iintro %s' Hs
  rw [(e (upd f i s')).to_eq]
  have hu : upd f i s' i = s' := by simp [upd]
  rw [hu]
  isplitl [H1]
  · iapply srvs_congr γ l1 f (upd f i s') ?_ $$ H1
    intro j hj; have : j ≠ i := fun h => h1 (h ▸ hj); simp [upd, this]
  isplitl [Hs]
  · iexact Hs
  · iapply srvs_congr γ l2 f (upd f i s') ?_ $$ H2
    intro j hj; have : j ≠ i := fun h => h2 (h ▸ hj); simp [upd, this]

theorem upd_self (f : SID → SState) (i : SID) : upd f i (f i) = f := by
  funext j; by_cases h : j = i <;> simp [upd, h]

/-! ### Growing the history -/

/-- The publications' bounds survive a step that adds no candidate and no publication. -/
theorem PubMaxG_grow (σ σ' : PState) (hGr : Grows σ σ') (hPub : σ'.pubs = σ.pubs)
    (hCand : ∀ c T, σ'.cand c T ≠ none → σ.cand c T ≠ none) :
    PubMaxG (GF := GF) γ σ ⊢ PubMaxG γ σ' := by
  unfold PubMaxG
  iintro ⟨%PM, Ha, %h⟩
  iexists PM
  isplitl [Ha]; · iexact Ha
  ipureintro
  refine ⟨fun c T => ?_, fun T k hk => ?_⟩
  · rw [h.1 c T]
    constructor
    · intro hn hn'
      obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.mp hn
      rw [hGr.2.2.2.2.1 c T x hx] at hn'; cases hn'
    · exact hCand c T
  · rw [hPub] at hk
    obtain ⟨ℓ, m, hl, hpm, hkm⟩ := h.2 T k hk
    exact ⟨ℓ, m, hGr.2.2.1 T ℓ hl, hpm, hkm⟩

/-- A new candidate `(c, T)` gets its publications' bound `0`. -/
theorem PubMaxG_alloc (σ σ' : PState) (c : SID) (T : Nat) (hGr : Grows σ σ')
    (hPub : σ'.pubs = σ.pubs) (hfresh : σ.cand c T = none)
    (hCand : ∀ c' T', σ'.cand c' T' ≠ none ↔ (σ.cand c' T' ≠ none ∨ (c' = c ∧ T' = T))) :
    PubMaxG (GF := GF) γ σ ⊢ |==> (PubMaxG γ σ' ∗ pubOwn γ c T 0) := by
  unfold PubMaxG pubOwn
  iintro ⟨%PM, Ha, %h⟩
  have hnone : PM.lookup (c, T) = none := by
    cases hx : PM.lookup (c, T) with
    | none => rfl
    | some x =>
      have := (h.1 c T).1 (by rw [hx]; rfl)
      exact absurd hfresh this
  imod ghost_map_insert (c, T) 0 hnone $$ Ha with ⟨Ha, Hk⟩
  imodintro
  isplitl [Ha]
  · iexists (PM.insert (c, T) 0)
    isplitl [Ha]; · iexact Ha
    ipureintro
    refine ⟨fun c' T' => ?_, fun T1 k hk => ?_⟩
    · show (if (c, T) = (c', T') then some 0 else PM.lookup (c', T')).isSome = true ↔ _
      rw [hCand c' T']
      by_cases he : (c, T) = (c', T')
      · rw [if_pos he]; simp only [Prod.mk.injEq] at he
        simp [he.1, he.2]
      · rw [if_neg he, h.1 c' T']
        constructor
        · exact Or.inl
        · rintro (h' | ⟨rfl, rfl⟩)
          · exact h'
          · exact absurd rfl he
    · rw [hPub] at hk
      obtain ⟨ℓ, m, hl, hpm, hkm⟩ := h.2 T1 k hk
      refine ⟨ℓ, m, hGr.2.2.1 T1 ℓ hl, ?_, hkm⟩
      show (if (c, T) = (ℓ, T1) then some 0 else PM.lookup (ℓ, T1)) = some m
      rw [if_neg]; · exact hpm
      intro he
      rw [← he] at hpm; rw [hnone] at hpm; cases hpm
  · iexact Hk

/-- (stage 4) A new candidacy `(c, T)` gets both halves of its commitment's configuration, `0`. -/
theorem CcfgG_alloc (σ σ' : PState) (c : SID) (T : Nat) (hfresh : σ.cand c T = none)
    (hCand : ∀ c' T', σ'.cand c' T' ≠ none ↔ (σ.cand c' T' ≠ none ∨ (c' = c ∧ T' = T)))
    (hlead : ∀ T' ℓ, σ'.leader T' = some ℓ → σ.leader T' = some ℓ ∧ σ'.ccfg T' = σ.ccfg T')
    (hnl : σ'.leader T ≠ some c) :
    CcfgG (GF := GF) γ σ ⊢ |==> (CcfgG γ σ' ∗ ccfgOwn γ c T 0 ∗ ccfgOwn γ c T 0) := by
  unfold CcfgG ccfgOwn
  iintro ⟨%CM, Ha, %h⟩
  have hnone : CM.lookup (c, T) = none := by
    cases hx : CM.lookup (c, T) with
    | none => rfl
    | some x =>
      have := (h.1 c T).1 (by rw [hx]; rfl)
      exact absurd hfresh this
  imod ghost_map_insert (c, T) 0 hnone $$ Ha with ⟨Ha, Hk⟩
  ihave ⟨Hk1, Hk2⟩ := (ghostMapElem_halves γ.ccfg (c, T) (0 : Nat)).1 $$ Hk
  imodintro
  isplitl [Ha]
  · iexists (CM.insert (c, T) 0)
    isplitl [Ha]; · iexact Ha
    ipureintro
    refine ⟨fun c' T' => ?_, fun c' T' p hp hl => ?_⟩
    · show (if (c, T) = (c', T') then some 0 else CM.lookup (c', T')).isSome = true ↔ _
      rw [hCand c' T']
      by_cases he : (c, T) = (c', T')
      · rw [if_pos he]; simp only [Prod.mk.injEq] at he
        simp [he.1, he.2]
      · rw [if_neg he, h.1 c' T']
        constructor
        · exact Or.inl
        · rintro (h' | ⟨rfl, rfl⟩)
          · exact h'
          · exact absurd rfl he
    · have hp' : (if (c, T) = (c', T') then some 0 else CM.lookup (c', T')) = some p := hp
      by_cases he : (c, T) = (c', T')
      · simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        exact absurd hl hnl
      · rw [if_neg he] at hp'
        obtain ⟨h1, h2⟩ := hlead T' c' hl
        rw [h2]; exact h.2 c' T' p hp' h1
  · isplitl [Hk1]; · iexact Hk1
    iexact Hk2

/-- (stage 4) A half of a commitment's configuration: the candidacy exists, and the value is
`ccfg T` if `c` leads `T`. -/
theorem CcfgG_lookup (σ : PState) (c : SID) (T p : Nat) :
    CcfgG (GF := GF) γ σ ∗ ccfgOwn γ c T p ⊢
      CcfgG γ σ ∗ ccfgOwn γ c T p ∗ ⌜σ.cand c T ≠ none ∧ (σ.leader T = some c → σ.ccfg T = p)⌝ := by
  unfold CcfgG ccfgOwn
  iintro ⟨⟨%CM, Ha, %h⟩, Hk⟩
  ihave %hl := ghost_map_lookup $$ Ha Hk
  isplitl [Ha]
  · iexists CM; isplitl [Ha]; · iexact Ha
    ipureintro; exact h
  isplitl [Hk]; · iexact Hk
  ipureintro
  exact ⟨(h.1 c T).1 (by rw [hl]; rfl), fun hl' => h.2 c T p hl hl'⟩

/-- (stage 4) Both halves of a commitment's configuration set it to `p`, for a step that changes
`T`'s leader and `ccfg` only to `c` and `p`. -/
theorem CcfgG_set (σ σ' : PState) (c : SID) (T p1 p2 p : Nat) (hc : σ'.cand = σ.cand)
    (hl : ∀ T', T' ≠ T → σ'.leader T' = σ.leader T' ∧ σ'.ccfg T' = σ.ccfg T')
    (hT : ∀ c', σ'.leader T = some c' → c' = c ∧ σ'.ccfg T = p) :
    CcfgG (GF := GF) γ σ ∗ ccfgOwn γ c T p1 ∗ ccfgOwn γ c T p2 ⊢
      |==> (CcfgG γ σ' ∗ ccfgOwn γ c T p ∗ ccfgOwn γ c T p) := by
  unfold CcfgG ccfgOwn
  iintro ⟨⟨%CM, Ha, %h⟩, Hk1, Hk2⟩
  ihave %he := ghostMapElem_agree (c, T) γ.ccfg _ _ p1 p2 $$ Hk1 Hk2
  subst he
  ihave %hl0 := ghost_map_lookup $$ Ha Hk1
  ihave Hk := (ghostMapElem_halves γ.ccfg (c, T) p1).2 $$ [Hk1 Hk2]
  · isplitl [Hk1]; iexact Hk1; iexact Hk2
  imod ghost_map_update p $$ Ha Hk with ⟨Ha, Hk⟩
  ihave ⟨Hk1, Hk2⟩ := (ghostMapElem_halves γ.ccfg (c, T) p).1 $$ Hk
  imodintro
  isplitl [Ha]
  · iexists (CM.insert (c, T) p)
    isplitl [Ha]; · iexact Ha
    ipureintro
    refine ⟨fun c' T' => ?_, fun c' T' q hq hl' => ?_⟩
    · show (if (c, T) = (c', T') then some p else CM.lookup (c', T')).isSome = true ↔ _
      rw [hc]
      by_cases he : (c, T) = (c', T')
      · rw [if_pos he]; simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        have := (h.1 c T).1 (by rw [hl0]; rfl)
        simp [this]
      · rw [if_neg he, h.1 c' T']
    · have hq' : (if (c, T) = (c', T') then some p else CM.lookup (c', T')) = some q := hq
      by_cases hTT : T' = T
      · subst hTT
        obtain ⟨rfl, h2⟩ := hT c' hl'
        rw [if_pos rfl] at hq'; cases hq'; exact h2
      · have he : ¬ (c, T) = (c', T') := by
          intro he; simp only [Prod.mk.injEq] at he; exact hTT he.2.symm
        rw [if_neg he] at hq'
        obtain ⟨h1, h2⟩ := hl T' hTT
        rw [h2]; rw [h1] at hl'; exact h.2 c' T' q hq' hl'
  · isplitl [Hk1]; · iexact Hk1
    iexact Hk2

/-- (stage 4) No candidacy yet: the empty map of commitments' configurations. -/
theorem CcfgG_init (srvs : List SID) (g : Entry) (cv : List w8 → List SID) :
    ghostMapAuth (GF := GF) γ.ccfg 1 (∅ : GMap (SID × Nat) Nat) ⊢ CcfgG γ (init srvs g cv) := by
  unfold CcfgG
  iintro H
  iexists ∅
  isplitl [H]; · iexact H
  ipureintro
  refine ⟨fun c T => ?_, fun c T p h => by simp at h⟩
  show ((∅ : GMap (SID × Nat) Nat).lookup (c, T)).isSome = true ↔ (none : Option (Nat × Nat)) ≠ none
  simp

/-- The snapshots stay known after any step. -/
theorem SnapG_grow (σ σ' : PState) (hP : PInv σ) (hGr : Grows σ σ') :
    SnapG (GF := GF) γ σ ⊢ SnapG γ σ' := by
  unfold SnapG
  iintro ⟨%L, Ha, %h⟩
  iexists L
  isplitl [Ha]; · iexact Ha
  ipureintro
  exact ⟨fun n s hn => ⟨(h.1 n s hn).1, snapOK_grows σ σ' s hP hGr (h.1 n s hn).2⟩, h.2⟩

/-- A publication `(T, k)` by `T`'s leader `ℓ`, which holds its bound: the bound grows to `k`. -/
theorem PubMaxG_publish (σ σ' : PState) (ℓ : SID) (T k m : Nat) (hGr : Grows σ σ')
    (hl : σ.leader T = some ℓ)
    (hPub : ∀ T' k', σ'.pubs T' k' ↔ (σ.pubs T' k' ∨ (T' = T ∧ k' = k)))
    (hCand : ∀ c T, σ'.cand c T ≠ none → σ.cand c T ≠ none) :
    PubMaxG (GF := GF) γ σ ∗ pubOwn γ ℓ T m ⊢ |==> (PubMaxG γ σ' ∗ pubOwn γ ℓ T (Max.max m k)) := by
  unfold PubMaxG pubOwn
  iintro ⟨⟨%PM, Ha, %h⟩, Hk⟩
  icombine Ha Hk gives %hlk
  imod ghost_map_update (Max.max m k) $$ Ha Hk with ⟨Ha, Hk⟩
  imodintro
  isplitl [Ha]
  · iexists (PM.insert (ℓ, T) (Max.max m k))
    isplitl [Ha]; · iexact Ha
    ipureintro
    refine ⟨fun c T1 => ?_, fun T1 k1 hk => ?_⟩
    · have e : (if (ℓ, T) = (c, T1) then some (Max.max m k) else PM.lookup (c, T1)).isSome =
          (PM.lookup (c, T1)).isSome := by
        split
        · rename_i he; rw [← he, hlk]; rfl
        · rfl
      show (if (ℓ, T) = (c, T1) then some (Max.max m k) else PM.lookup (c, T1)).isSome = true ↔ _
      rw [e, h.1 c T1]
      constructor
      · intro hs hn
        obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.mp hs
        rw [hGr.2.2.2.2.1 c T1 x hx] at hn; cases hn
      · exact hCand c T1
    · rcases (hPub T1 k1).1 hk with hk | ⟨rfl, rfl⟩
      · obtain ⟨ℓ', m', hl', hpm, hkm⟩ := h.2 T1 k1 hk
        by_cases he : (ℓ, T) = (ℓ', T1)
        · refine ⟨ℓ', Max.max m k, hGr.2.2.1 T1 ℓ' hl', ?_, ?_⟩
          · show (if (ℓ, T) = (ℓ', T1) then some (Max.max m k) else PM.lookup (ℓ', T1)) = _
            rw [if_pos he]
          · rw [← he, hlk] at hpm; cases hpm; omega
        · refine ⟨ℓ', m', hGr.2.2.1 T1 ℓ' hl', ?_, hkm⟩
          show (if (ℓ, T) = (ℓ', T1) then some (Max.max m k) else PM.lookup (ℓ', T1)) = _
          rw [if_neg he]; exact hpm
      · refine ⟨ℓ, Max.max m k1, hGr.2.2.1 T1 ℓ hl, ?_, by omega⟩
        show (if (ℓ, T1) = (ℓ, T1) then some (Max.max m k1) else PM.lookup (ℓ, T1)) = _
        rw [if_pos rfl]
  · iexact Hk

/-- Grow the history's ghost state, with the publications and their bounds updated by `hPP`
(which may take some of the caller's resources `R0` and give it `R`). -/
theorem HistG_grow_with (σ σ' : PState) (hP : PInv σ) (hGr : Grows σ σ')
    (hLc : ∀ T k e, ent (σ'.llog T) k = some e → e.kind = kCommand →
      ∃ T', ent (σ.llog T') k = some e)
    (kL : List Nat) (oL : ∀ T, T ∉ kL → σ'.leader T = σ.leader T)
    (kLl : List (Nat × Nat)) (oLl : ∀ p, p ∉ kLl → llogF σ' p = llogF σ p)
    (kL0 : List Nat) (oL0 : ∀ T, T ∉ kL0 → len0F σ' T = len0F σ T)
    (kC : List (SID × Nat)) (oC : ∀ p, p ∉ kC → candF σ' p = candF σ p)
    (kV : List (SID × Nat)) (oV : ∀ p, p ∉ kV → votesF σ' p = votesF σ p)
    (kA : List (SID × Nat × Nat)) (oA : ∀ p, p ∉ kA → acksF σ' p = acksF σ p)
    (kCm : List (Nat × Nat × Nat)) (oCm : ∀ p, p ∉ kCm → commitsF σ' p = commitsF σ p)
    (R0 R : IProp GF)
    (hPP : GMapOf γ.pubs (pubsF σ) ∗ PubMaxG (GF := GF) γ σ ∗ R0 ⊢
      |==> (GMapOf γ.pubs (pubsF σ') ∗ PubMaxG γ σ' ∗ R)) :
    HistG (GF := GF) γ σ ∗ R0 ⊢ |==> (HistG γ σ' ∗ R) := by
  have hGr0 := hGr
  obtain ⟨gV, gG, gL, gLl, gC, gVo, gA, gCm, gCC, gT, gD, gMT, gMI, gP⟩ := hGr
  unfold HistG
  iintro ⟨⟨Hl, Hll, Hl0, Hc, Hv, Ha, Hcm, Hvs, HO, HC, Hp, Hpm, Hs⟩, HR0⟩
  imod GMapOf_grow γ.leader kL σ.leader σ'.leader gL oL $$ Hl with Hl
  imod GMapOf_grow γ.llog kLl (llogF σ) (llogF σ') (llogF_sub hP hGr0) oLl $$ Hll with Hll
  imod GMapOf_grow γ.len0 kL0 (len0F σ) (len0F σ') (len0F_sub hGr0) oL0 $$ Hl0 with Hl0
  imod GMapOf_grow γ.cand kC (candF σ) (candF σ') (fun p v h => gC p.1 p.2 v h) oC $$ Hc with Hc
  imod GMapOf_grow γ.votes kV (votesF σ) (votesF σ') (fun p v h => gVo p.1 p.2 v h) oV $$ Hv
    with Hv
  imod GMapOf_grow γ.acks kA (acksF σ) (acksF σ') (acksF_sub hGr0) oA $$ Ha with Ha
  imod GMapOf_grow γ.commits kCm (commitsF σ) (commitsF σ') (commitsF_sub hGr0) oCm $$ Hcm with Hcm
  imod monoListAuthOwn_update σ'.C gCC $$ HC with ⟨HC, -⟩
  ihave Hvs := GMapOf_congr γ.srvSet (srvsF σ) (srvsF σ')
    (fun i => by unfold srvsF; rw [gV]) $$ Hvs
  imod hPP $$ [Hp Hpm HR0] with ⟨Hp, Hpm, HR⟩
  · iframe
  ihave Hs := SnapG_grow γ σ σ' hP hGr0 $$ Hs
  unfold OpsG
  icases HO with ⟨%O, %hO, HO⟩
  imodintro
  isplitr [HR]
  · iframe
    ipureintro; exact OpsOK_mono hLc gCC hO
  · iexact HR

theorem HistG_grow (σ σ' : PState) (hP : PInv σ) (hGr : Grows σ σ')
    (hLc : ∀ T k e, ent (σ'.llog T) k = some e → e.kind = kCommand →
      ∃ T', ent (σ.llog T') k = some e)
    (kL : List Nat) (oL : ∀ T, T ∉ kL → σ'.leader T = σ.leader T)
    (kLl : List (Nat × Nat)) (oLl : ∀ p, p ∉ kLl → llogF σ' p = llogF σ p)
    (kL0 : List Nat) (oL0 : ∀ T, T ∉ kL0 → len0F σ' T = len0F σ T)
    (kC : List (SID × Nat)) (oC : ∀ p, p ∉ kC → candF σ' p = candF σ p)
    (kV : List (SID × Nat)) (oV : ∀ p, p ∉ kV → votesF σ' p = votesF σ p)
    (kA : List (SID × Nat × Nat)) (oA : ∀ p, p ∉ kA → acksF σ' p = acksF σ p)
    (kCm : List (Nat × Nat × Nat)) (oCm : ∀ p, p ∉ kCm → commitsF σ' p = commitsF σ p)
    (hPub : σ'.pubs = σ.pubs := by first | rfl | (simp only [becomeLeader]; split <;> rfl))
    (hCand : ∀ c T, σ'.cand c T ≠ none → σ.cand c T ≠ none := by
      first | (intro _ _ h; exact h) | (intro _ _ h; simp only [becomeLeader] at h; split at h <;> exact h)) :
    HistG (GF := GF) γ σ ⊢ |==> HistG γ σ' := by
  iintro H
  imod HistG_grow_with γ σ σ' hP hGr hLc kL oL kLl oLl kL0 oL0 kC oC kV oV kA oA kCm oCm emp emp
    (by iintro ⟨Hp, H, -⟩; imodintro
        isplitl [Hp]; · iapply GMapOf_congr γ.pubs (pubsF σ) (pubsF σ') (fun p => (pubsF_congr hPub p).symm) $$ Hp
        isplitl [H]; · iapply PubMaxG_grow γ σ σ' hGr hPub hCand $$ H
        iempintro) $$ [H] with ⟨H, -⟩
  · isplitl [H]; iexact H; iempintro
  imodintro; iexact H

/-! ### Reading the history -/

section hist
variable (σ : PState)

theorem H_leader_lookup (T : Nat) (ℓ : SID) :
    HistG (GF := GF) γ σ ∗ leaderIs γ T ℓ ⊢ HistG γ σ ∗ ⌜σ.leader T = some ℓ⌝ := by
  unfold HistG leaderIs
  iintro ⟨⟨H, Hr⟩, #Hf⟩
  ihave ⟨H, %h⟩ := GMapOf_lookup γ.leader σ.leader T ℓ $$ [H]
  · isplitl [H]; iexact H; iexact Hf
  isplitl [H Hr]; · isplitl [H]; iexact H; iexact Hr
  ipureintro; exact h

theorem H_leader_get (T : Nat) (ℓ : SID) (h : σ.leader T = some ℓ) :
    HistG (GF := GF) γ σ ⊢ HistG γ σ ∗ leaderIs γ T ℓ := by
  unfold HistG leaderIs
  iintro ⟨H, Hr⟩
  ihave ⟨H, #Hf⟩ := GMapOf_get γ.leader σ.leader T ℓ h $$ H
  isplitl [H Hr]; · isplitl [H]; iexact H; iexact Hr
  iexact Hf

theorem H_llog_lookup (T k : Nat) (e : Entry) :
    HistG (GF := GF) γ σ ∗ llogIdx γ T k e ⊢ HistG γ σ ∗ ⌜ent (σ.llog T) k = some e⌝ := by
  unfold HistG llogIdx
  iintro ⟨⟨H0, H, Hr⟩, %hk, #Hf⟩
  ihave ⟨H, %h⟩ := GMapOf_lookup γ.llog (llogF σ) (T, k) e $$ [H]
  · isplitl [H]; iexact H; iexact Hf
  isplitl [H0 H Hr]; · iframe
  ipureintro; exact h

theorem H_llog_get (T k : Nat) (e : Entry) (h : ent (σ.llog T) k = some e) :
    HistG (GF := GF) γ σ ⊢ HistG γ σ ∗ llogIdx γ T k e := by
  unfold HistG llogIdx
  iintro ⟨H0, H, Hr⟩
  ihave ⟨H, #Hf⟩ := GMapOf_get γ.llog (llogF σ) (T, k) e h $$ H
  isplitl [H0 H Hr]; · iframe
  isplitr
  · ipureintro; exact ent_pos h
  · iexact Hf

theorem H_len0_lookup (T n : Nat) :
    HistG (GF := GF) γ σ ∗ len0Is γ T n ⊢ HistG γ σ ∗ ⌜len0F σ T = some n⌝ := by
  unfold HistG len0Is
  iintro ⟨⟨H0, H1, H, Hr⟩, #Hf⟩
  ihave ⟨H, %h⟩ := GMapOf_lookup γ.len0 (len0F σ) T n $$ [H]
  · isplitl [H]; iexact H; iexact Hf
  isplitl [H0 H1 H Hr]; · iframe
  ipureintro; exact h

theorem H_len0_get (T n : Nat) (h : len0F σ T = some n) :
    HistG (GF := GF) γ σ ⊢ HistG γ σ ∗ len0Is γ T n := by
  unfold HistG len0Is
  iintro ⟨H0, H1, H, Hr⟩
  ihave ⟨H, #Hf⟩ := GMapOf_get γ.len0 (len0F σ) T n h $$ H
  isplitl [H0 H1 H Hr]; · iframe
  iexact Hf

theorem H_cand_lookup (c : SID) (T li lt : Nat) :
    HistG (GF := GF) γ σ ∗ candIs γ c T li lt ⊢ HistG γ σ ∗ ⌜σ.cand c T = some (li, lt)⌝ := by
  unfold HistG candIs
  iintro ⟨⟨H0, H1, H2, H, Hr⟩, #Hf⟩
  ihave ⟨H, %h⟩ := GMapOf_lookup γ.cand (candF σ) (c, T) (li, lt) $$ [H]
  · isplitl [H]; iexact H; iexact Hf
  isplitl [H0 H1 H2 H Hr]; · iframe
  ipureintro; exact h

theorem H_cand_get (c : SID) (T li lt : Nat) (h : σ.cand c T = some (li, lt)) :
    HistG (GF := GF) γ σ ⊢ HistG γ σ ∗ candIs γ c T li lt := by
  unfold HistG candIs
  iintro ⟨H0, H1, H2, H, Hr⟩
  ihave ⟨H, #Hf⟩ := GMapOf_get γ.cand (candF σ) (c, T) (li, lt) h $$ H
  isplitl [H0 H1 H2 H Hr]; · iframe
  iexact Hf

theorem H_vote_lookup (j : SID) (T : Nat) (c : SID) :
    HistG (GF := GF) γ σ ∗ voteIs γ j T c ⊢
      HistG γ σ ∗ ⌜∃ L b, σ.votes j T = some (c, L, b)⌝ := by
  unfold HistG voteIs
  iintro ⟨⟨H0, H1, H2, H3, H, Hr⟩, %L, %b, #Hf⟩
  ihave ⟨H, %h⟩ := GMapOf_lookup γ.votes (votesF σ) (j, T) (c, L, b) $$ [H]
  · isplitl [H]; iexact H; iexact Hf
  isplitl [H0 H1 H2 H3 H Hr]; · iframe
  ipureintro; exact ⟨L, b, h⟩

theorem H_vote_get (j : SID) (T : Nat) (c : SID) (L : RLog) (b : Bool)
    (h : σ.votes j T = some (c, L, b)) :
    HistG (GF := GF) γ σ ⊢ HistG γ σ ∗ voteIs γ j T c := by
  unfold HistG voteIs
  iintro ⟨H0, H1, H2, H3, H, Hr⟩
  ihave ⟨H, #Hf⟩ := GMapOf_get γ.votes (votesF σ) (j, T) (c, L, b) h $$ H
  isplitl [H0 H1 H2 H3 H Hr]; · iframe
  iexists L, b; iexact Hf

theorem H_ack_lookup (j : SID) (T m : Nat) :
    HistG (GF := GF) γ σ ∗ ackIs γ j T m ⊢ HistG γ σ ∗ ⌜σ.acked j T m⌝ := by
  unfold HistG ackIs
  iintro ⟨⟨H0, H1, H2, H3, H4, H, Hr⟩, #Hf⟩
  ihave ⟨H, %h⟩ := GMapOf_lookup γ.acks (acksF σ) (j, T, m) () $$ [H]
  · isplitl [H]; iexact H; iexact Hf
  isplitl [H0 H1 H2 H3 H4 H Hr]; · iframe
  ipureintro; exact (acksF_iff σ j T m).mp h

theorem H_ack_get (j : SID) (T m : Nat) (h : σ.acked j T m) :
    HistG (GF := GF) γ σ ⊢ HistG γ σ ∗ ackIs γ j T m := by
  unfold HistG ackIs
  iintro ⟨H0, H1, H2, H3, H4, H, Hr⟩
  ihave ⟨H, #Hf⟩ := GMapOf_get γ.acks (acksF σ) (j, T, m) () ((acksF_iff σ j T m).mpr h) $$ H
  isplitl [H0 H1 H2 H3 H4 H Hr]; · iframe
  iexact Hf

theorem H_commit_lookup (T k p : Nat) :
    HistG (GF := GF) γ σ ∗ commitIs γ T k p ⊢ HistG γ σ ∗ ⌜σ.commits T k p⌝ := by
  unfold HistG commitIs
  iintro ⟨⟨H0, H1, H2, H3, H4, H5, H, Hr⟩, #Hf⟩
  ihave ⟨H, %h⟩ := GMapOf_lookup γ.commits (commitsF σ) (T, k, p) () $$ [H]
  · isplitl [H]; iexact H; iexact Hf
  isplitl [H0 H1 H2 H3 H4 H5 H Hr]; · iframe
  ipureintro; exact (commitsF_iff σ T k p).mp h

theorem H_commit_get (T k p : Nat) (h : σ.commits T k p) :
    HistG (GF := GF) γ σ ⊢ HistG γ σ ∗ commitIs γ T k p := by
  unfold HistG commitIs
  iintro ⟨H0, H1, H2, H3, H4, H5, H, Hr⟩
  ihave ⟨H, #Hf⟩ := GMapOf_get γ.commits (commitsF σ) (T, k, p) () ((commitsF_iff σ T k p).mpr h)
    $$ H
  isplitl [H0 H1 H2 H3 H4 H5 H Hr]; · iframe
  iexact Hf

theorem H_voter_lookup (i : SID) :
    HistG (GF := GF) γ σ ∗ i ↪[γ.srvSet]□ () ⊢ HistG γ σ ∗ ⌜i ∈ σ.srvs⌝ := by
  unfold HistG
  iintro ⟨⟨H0, H1, H2, H3, H4, H5, H6, H, Hr⟩, #Hf⟩
  ihave ⟨H, %h⟩ := GMapOf_lookup γ.srvSet (srvsF σ) i () $$ [H]
  · isplitl [H]; iexact H; iexact Hf
  isplitl [H0 H1 H2 H3 H4 H5 H6 H Hr]; · iframe
  ipureintro; exact (srvsF_iff σ i).mp h

theorem H_voter_get (i : SID) (h : i ∈ σ.srvs) :
    HistG (GF := GF) γ σ ⊢ HistG γ σ ∗ isSrv γ i := by
  unfold HistG isSrv
  iintro ⟨H0, H1, H2, H3, H4, H5, H6, H, Hr⟩
  ihave ⟨H, #Hf⟩ := GMapOf_get γ.srvSet (srvsF σ) i () ((srvsF_iff σ i).mpr h) $$ H
  isplitl [H0 H1 H2 H3 H4 H5 H6 H Hr]; · iframe
  iexact Hf

theorem H_C_lookup (k : Nat) (e : Entry) :
    HistG (GF := GF) γ σ ∗ CIdx γ k e ⊢ HistG γ σ ∗ ⌜ent σ.C k = some e⌝ := by
  unfold HistG CIdx
  iintro ⟨⟨H0, H1, H2, H3, H4, H5, H6, H7, HO, H, Hr⟩, %hk, #Hf⟩
  ihave %h := mono_list_auth_idx_lookup γ.C 1 σ.C (k - 1) e $$ H Hf
  isplitl [H0 H1 H2 H3 H4 H5 H6 H7 HO H Hr]; · iframe
  ipureintro; rw [ent_eq_getElem? _ _ hk]; exact h

theorem H_C_lb :
    HistG (GF := GF) γ σ ⊢ HistG γ σ ∗ CLb γ σ.C := by
  unfold HistG CLb
  iintro ⟨H0, H1, H2, H3, H4, H5, H6, H7, HO, H, Hr⟩
  ihave #Hlb := monoListLbOwn_get γ.C 1 σ.C $$ H
  isplitl [H0 H1 H2 H3 H4 H5 H6 H7 HO H Hr]; · iframe
  iexact Hlb

theorem H_pub_lookup (T k : Nat) :
    HistG (GF := GF) γ σ ∗ pubIs γ T k ⊢ HistG γ σ ∗ ⌜σ.pubs T k⌝ := by
  unfold HistG pubIs
  iintro ⟨⟨H0, H1, H2, H3, H4, H5, H6, H7, HO, HC, H, Hr⟩, #Hf⟩
  ihave ⟨H, %h⟩ := GMapOf_lookup γ.pubs (pubsF σ) (T, k) () $$ [H]
  · isplitl [H]; iexact H; iexact Hf
  isplitl [H0 H1 H2 H3 H4 H5 H6 H7 HO HC H Hr]; · iframe
  ipureintro; exact (pubsF_iff σ T k).mp h

theorem H_pub_get (T k : Nat) (h : σ.pubs T k) :
    HistG (GF := GF) γ σ ⊢ HistG γ σ ∗ pubIs γ T k := by
  unfold HistG pubIs
  iintro ⟨H0, H1, H2, H3, H4, H5, H6, H7, HO, HC, H, Hr⟩
  ihave ⟨H, #Hf⟩ := GMapOf_get γ.pubs (pubsF σ) (T, k) () ((pubsF_iff σ T k).mpr h) $$ H
  isplitl [H0 H1 H2 H3 H4 H5 H6 H7 HO HC H Hr]; · iframe
  iexact Hf

end hist

/-! ### Per-server pieces -/

theorem srvG_srv_agree (i : SID) (s0 s : SState) :
    srvG (GF := GF) γ i s0 ∗ ghostVar (γ.srv i) (1 : Qp).half s ⊢
      srvG γ i s0 ∗ ghostVar (γ.srv i) (1 : Qp).half s ∗ ⌜s = s0⌝ := by
  unfold srvG
  iintro ⟨⟨Ht, Hd, Hs, Hl, Hc⟩, Hg⟩
  icombine Hg Hs gives %h
  iframe; ipureintro; exact h.2

theorem srvG_term_lb (i : SID) (s : SState) (t : Nat) :
    srvG (GF := GF) γ i s ∗ termLb γ i t ⊢ srvG γ i s ∗ ⌜t ≤ s.term⌝ := by
  unfold srvG termLb
  iintro ⟨⟨Ht, Hd, Hs, Hl, Hc⟩, #Hlb⟩
  ihave %h := monoNatLbOwn_valid (γ.term i) _ s.term t $$ Ht Hlb
  iframe; ipureintro; exact h.2

theorem srvG_dur_lb (i : SID) (s : SState) (k : Nat) :
    srvG (GF := GF) γ i s ∗ durLb γ i k ⊢ srvG γ i s ∗ ⌜k ≤ s.dur.1⌝ := by
  unfold srvG durLb
  iintro ⟨⟨Ht, Hd, Hs, Hl, Hc⟩, #Hlb⟩
  ihave %h := monoNatLbOwn_valid (γ.dur i) _ s.dur.1 k $$ Hd Hlb
  iframe; ipureintro; exact h.2

theorem srvG_log_agree (i : SID) (s : SState) (L : RLog) :
    srvG (GF := GF) γ i s ∗ logCouple γ i L ⊢ srvG γ i s ∗ logCouple γ i L ∗ ⌜L = s.log⌝ := by
  unfold srvG logCouple
  iintro ⟨⟨Ht, Hd, Hs, Hl, Hc⟩, Hg, #Hv⟩
  icombine Hg Hl gives %h
  iframe; isplitr; · iexact Hv
  ipureintro; exact h.2

theorem srvG_cidx_agree (i : SID) (s : SState) (c : Nat) :
    srvG (GF := GF) γ i s ∗ cidxCouple γ i c ⊢ srvG γ i s ∗ cidxCouple γ i c ∗ ⌜c = s.cidx⌝ := by
  unfold srvG cidxCouple
  iintro ⟨⟨Ht, Hd, Hs, Hl, Hc⟩, Hg⟩
  icombine Hg Hc gives %h
  iframe; ipureintro; exact h.2

theorem srvG_term_agree (i : SID) (s : SState) (t : Nat) :
    srvG (GF := GF) γ i s ∗ termCouple γ i t ⊢ srvG γ i s ∗ termCouple γ i t ∗ ⌜t = s.term⌝ := by
  unfold srvG termCouple
  iintro ⟨⟨Ht, Hd, Hs, Hl, Hc⟩, Hg⟩
  ihave %h := monoNatAuthOwn_agree (γ.term i) _ _ t s.term $$ Hg Ht
  iframe; ipureintro; exact h.2

theorem srvG_dur_agree (i : SID) (s : SState) (q : Qp) (d : Nat) :
    srvG (GF := GF) γ i s ∗ durView γ i q d ⊢ srvG γ i s ∗ durView γ i q d ∗ ⌜d = s.dur.1⌝ := by
  unfold srvG durView
  iintro ⟨⟨Ht, Hd, Hs, Hl, Hc⟩, Hg⟩
  ihave %h := monoNatAuthOwn_agree (γ.dur i) _ _ d s.dur.1 $$ Hg Hd
  iframe; ipureintro; exact h.2

/-- Open server `i`'s pieces from its `srvOwn`. -/
theorem srvOwn_open (σ : PState) (hg : GInv γ σ) (i : SID) (s : SState) :
    HistG (GF := GF) γ σ ∗ ([∗list] j ∈ γ.srvs, srvG γ j (σ.srv j)) ∗ srvOwn γ i s ⊢
      HistG γ σ ∗ srvG γ i s ∗
      (∀ s', srvG γ i s' -∗ [∗list] j ∈ γ.srvs, srvG γ j (upd σ.srv i s' j)) ∗
      srvOwn γ i s ∗ ⌜i ∈ γ.srvs ∧ σ.srv i = s⌝ := by
  have hnd : γ.srvs.Nodup := hg.2.1 ▸ hg.1.1.2.2.1
  iintro ⟨Hh, Hs, Ho⟩
  unfold srvOwn
  icases Ho with ⟨Hg, #Hv⟩
  ihave ⟨Hh, %hv⟩ := H_voter_lookup γ σ i $$ [Hh]
  · isplitl [Hh]; iexact Hh; iexact Hv
  have hv' : i ∈ γ.srvs := hg.2.1 ▸ hv
  ihave ⟨Hi, Hcl⟩ := srvs_acc γ γ.srvs hnd i hv' σ.srv $$ Hs
  ihave ⟨Hi, Hg, %he⟩ := srvG_srv_agree γ i (σ.srv i) s $$ [Hi Hg]
  · isplitl [Hi]; iexact Hi; iexact Hg
  subst he
  iframe
  isplitr
  · iexact Hv
  · ipureintro; exact ⟨hv', rfl⟩

/-- Access voter `i`'s pieces. -/
theorem srvs_open (σ : PState) (hg : GInv γ σ) (i : SID) (hi : i ∈ γ.srvs) :
    ([∗list] j ∈ γ.srvs, srvG (GF := GF) γ j (σ.srv j)) ⊢
      srvG γ i (σ.srv i) ∗ (∀ s', srvG γ i s' -∗ [∗list] j ∈ γ.srvs, srvG γ j (upd σ.srv i s' j)) :=
  srvs_acc γ γ.srvs (hg.2.1 ▸ hg.1.1.2.2.1) i hi σ.srv

theorem srvs_peek (σ : PState) (i : SID) (hi : i ∈ γ.srvs) :
    ([∗list] j ∈ γ.srvs, srvG (GF := GF) γ j (σ.srv j)) ⊢
      srvG γ i (σ.srv i) ∗ (srvG γ i (σ.srv i) -∗ [∗list] j ∈ γ.srvs, srvG γ j (σ.srv j)) :=
  BigSepL.bigSepL_mem_acc (Φ := fun j => srvG (GF := GF) γ j (σ.srv j)) hi

theorem srvOwn_update (i : SID) (s s0 s' : SState) :
    srvOwn (GF := GF) γ i s ∗ ghostVar (γ.srv i) (1 : Qp).half s0 ⊢
      |==> (srvOwn γ i s' ∗ ghostVar (γ.srv i) (1 : Qp).half s') := by
  unfold srvOwn
  iintro ⟨⟨Hg, #Hv⟩, Hs⟩
  imod ghostVar_update_halves s' (γ.srv i) s s0 $$ Hg Hs with ⟨Hg, Hs⟩
  imodintro
  iframe; iexact Hv

theorem srvG_eq (i : SID) (s : SState) : srvG (GF := GF) γ i s ⊣⊢
    monoNatAuthOwn (γ.term i) (1 : Qp).half s.term ∗
    monoNatAuthOwn (γ.dur i) (1 : Qp).half s.dur.1 ∗
    ghostVar (γ.srv i) (1 : Qp).half s ∗
    ghostVar (γ.slog i) (1 : Qp).half s.log ∗
    ghostVar (γ.cidx i) (1 : Qp).half s.cidx := by
  unfold srvG; exact .rfl

theorem monoNat_halves (γn : GName) (n : Nat) :
    monoNatAuthOwn (GF := GF) γn 1 n ⊣⊢
      monoNatAuthOwn γn (1 : Qp).half n ∗ monoNatAuthOwn γn (1 : Qp).half n := by
  have h := (monoNatAuthOwn_fractional (GF := GF) γn n).fractional (1 : Qp).half (1 : Qp).half
  rw [Qp.half_add_half] at h
  exact h

theorem monoNat_update_halves (γn : GName) (n n' m : Nat) (h : n ≤ m) :
    monoNatAuthOwn (GF := GF) γn (1 : Qp).half n ∗ monoNatAuthOwn γn (1 : Qp).half n' ⊢
      |==> (monoNatAuthOwn γn (1 : Qp).half m ∗ monoNatAuthOwn γn (1 : Qp).half m ∗
        monoNatLbOwn γn m) := by
  iintro ⟨H1, H2⟩
  ihave %he := monoNatAuthOwn_agree γn _ _ n n' $$ H1 H2
  obtain ⟨_, he⟩ := he
  subst he
  ihave H := (monoNat_halves γn n).2 $$ [H1 H2]
  · isplitl [H1]; iexact H1; iexact H2
  imod mono_nat_own_update m h $$ H with ⟨H, #Hlb⟩
  ihave ⟨H1, H2⟩ := (monoNat_halves γn m).1 $$ H
  imodintro
  iframe; iexact Hlb

/-- Open server `i`'s pieces from its `srvOwn`, to put them back unchanged. -/
theorem srvOwn_peek (σ : PState) (hg : GInv γ σ) (i : SID) (s : SState) :
    HistG (GF := GF) γ σ ∗ ([∗list] j ∈ γ.srvs, srvG γ j (σ.srv j)) ∗ srvOwn γ i s ⊢
      HistG γ σ ∗ srvG γ i s ∗
      (srvG γ i s -∗ [∗list] j ∈ γ.srvs, srvG γ j (σ.srv j)) ∗
      srvOwn γ i s ∗ ⌜i ∈ γ.srvs ∧ σ.srv i = s⌝ := by
  iintro H
  ihave ⟨Hh, Hi, Hcl, Ho, %hh⟩ := srvOwn_open γ σ hg i s $$ H
  obtain ⟨hi, hs⟩ := hh
  subst hs
  iframe
  isplitl [Hcl]
  · iintro Hi; ihave Hs := Hcl $$ %(σ.srv i) Hi
    rw [upd_self]; iexact Hs
  · ipureintro; exact ⟨hi, rfl⟩

theorem Inv_read0 (E : CoPset) (hE : ↑gprotN ⊆ E) (Q : IProp GF)
    (h : ∀ σ, InvBody γ σ ⊢ InvBody γ σ ∗ Q) :
    Inv γ ⊢ |={E}=> Q := by
  refine (sep_emp (PROP := IProp GF)).2.trans (Inv_read γ E hE emp Q ?_)
  intro σ; exact sep_emp.1.trans (h σ)

theorem Inv_upd0 (E : CoPset) (hE : ↑gprotN ⊆ E) (Q : IProp GF)
    (h : ∀ σ, InvBody γ σ ⊢ |==> (InvInner γ ∗ Q)) :
    Inv γ ⊢ |={E}=> Q := by
  refine (sep_emp (PROP := IProp GF)).2.trans (Inv_upd γ E hE emp Q ?_)
  intro σ; exact sep_emp.1.trans (h σ)

theorem logCouple_voter (i : SID) (L : RLog) :
    logCouple (GF := GF) γ i L ⊢ logCouple γ i L ∗ i ↪[γ.srvSet]□ () := by
  unfold logCouple
  iintro ⟨H, #Hv⟩
  isplitl [H]
  · isplitl [H]; iexact H; iexact Hv
  · iexact Hv

theorem srvG_term_get_lb (i : SID) (s : SState) :
    srvG (GF := GF) γ i s ⊢ srvG γ i s ∗ termLb γ i s.term := by
  unfold srvG termLb
  iintro ⟨Ht, Hd, Hs, Hl, Hc⟩
  ihave #Hlb := monoNatLbOwn_get (γ.term i) _ s.term $$ Ht
  iframe; iexact Hlb

theorem H_C_get (σ : PState) (x : Nat) (e : Entry) (h : ent σ.C x = some e) :
    HistG (GF := GF) γ σ ⊢ HistG γ σ ∗ CIdx γ x e := by
  iintro H
  ihave ⟨H, #Hlb⟩ := H_C_lb γ σ $$ H
  iframe
  unfold CLb CIdx
  have hx := ent_pos h
  isplitr
  · ipureintro; exact hx
  · iapply monoListIdxOwn_get (x - 1) e (by rw [← ent_eq_getElem? _ _ hx]; exact h) $$ Hlb

theorem H_vote_lookup_list (σ : PState) (T : Nat) (c : SID) (Q : List SID) :
    HistG (GF := GF) γ σ ∗ ([∗list] j ∈ Q, voteIs γ j T c) ⊢
      HistG γ σ ∗ ⌜∀ j ∈ Q, ∃ L b, σ.votes j T = some (c, L, b)⌝ := by
  induction Q with
  | nil => iintro ⟨H, -⟩; iframe; ipureintro; intro j hj; simp at hj
  | cons a Q ih =>
    iintro ⟨H, Hl⟩
    ihave ⟨#Hf, Hfs⟩ := BigSepL.bigSepL_cons.1 $$ Hl
    ihave ⟨H, %h0⟩ := H_vote_lookup γ σ a T c $$ [H]
    · isplitl [H]; iexact H; iexact Hf
    ihave ⟨H, %hs⟩ := ih $$ [H Hfs]
    · isplitl [H]; iexact H; iexact Hfs
    iframe; ipureintro
    intro j hj
    rcases List.mem_cons.mp hj with h | h
    · subst h; exact h0
    · exact hs j h

theorem H_ack_lookup_list (σ : PState) (T k : Nat) (Q : List SID) :
    HistG (GF := GF) γ σ ∗ ([∗list] j ∈ Q, ∃ m, ackIs γ j T m ∗ ⌜k ≤ m⌝) ⊢
      HistG γ σ ∗ ⌜∀ j ∈ Q, ∃ m, k ≤ m ∧ σ.acked j T m⌝ := by
  induction Q with
  | nil => iintro ⟨H, -⟩; iframe; ipureintro; intro j hj; simp at hj
  | cons a Q ih =>
    iintro ⟨H, Hl⟩
    ihave ⟨⟨%m, #Hf, %hm⟩, Hfs⟩ := BigSepL.bigSepL_cons.1 $$ Hl
    ihave ⟨H, %h0⟩ := H_ack_lookup γ σ a T m $$ [H]
    · isplitl [H]; iexact H; iexact Hf
    ihave ⟨H, %hs⟩ := ih $$ [H Hfs]
    · isplitl [H]; iexact H; iexact Hfs
    iframe; ipureintro
    intro j hj
    rcases List.mem_cons.mp hj with h | h
    · subst h; exact ⟨m, hm, h0⟩
    · exact hs j h

/-! ### Lists of leader-log entries -/

theorem H_llog_lookup_list (σ : PState) (T : Nat) (es : List Entry) :
    ∀ key : Nat → Nat, HistG (GF := GF) γ σ ∗ ([∗list] j ↦ e ∈ es, llogIdx γ T (key j) e) ⊢
      HistG γ σ ∗ ⌜∀ (j : Nat) (e : Entry), es[j]? = some e → ent (σ.llog T) (key j) = some e⌝ := by
  induction es with
  | nil =>
    intro key
    iintro ⟨H, -⟩
    iframe; ipureintro; intro j e h; simp at h
  | cons e es ih =>
    intro key
    iintro ⟨H, Hl⟩
    ihave ⟨#Hf, Hfs⟩ := BigSepL.bigSepL_cons.1 $$ Hl
    ihave ⟨H, %h0⟩ := H_llog_lookup γ σ T (key 0) e $$ [H]
    · isplitl [H]; iexact H; iexact Hf
    ihave ⟨H, %hs⟩ := ih (fun j => key (j + 1)) $$ [H Hfs]
    · isplitl [H]; iexact H; iexact Hfs
    iframe; ipureintro
    intro j e' hj
    cases j with
    | zero => simp at hj; subst hj; exact h0
    | succ j => exact hs j e' (by simpa using hj)


/-- (stage 4) A known prefix of a leader log is one. -/
theorem H_llogPre_lookup (σ : PState) (T : Nat) (L : RLog) :
    HistG (GF := GF) γ σ ∗ llogPre γ T L ⊢ HistG γ σ ∗ ⌜L = (σ.llog T).take L.length⌝ := by
  unfold llogPre
  iintro ⟨H, Hl⟩
  ihave ⟨H, %h⟩ := H_llog_lookup_list γ σ T L (fun j => j + 1) $$ [H Hl]
  · isplitl [H]; iexact H; iexact Hl
  iframe; ipureintro
  have := (list_of_ents (L := σ.llog T) (es := L) (base := 0)
    (fun j e hj => by rw [Nat.zero_add, ← ent_succ]; exact h j e hj)).2
  simpa using this

theorem H_llog_get_list (σ : PState) (T : Nat) (es : List Entry) :
    ∀ key : Nat → Nat, (∀ (j : Nat) (e : Entry), es[j]? = some e → ent (σ.llog T) (key j) = some e) →
      HistG (GF := GF) γ σ ⊢ HistG γ σ ∗ ([∗list] j ↦ e ∈ es, llogIdx γ T (key j) e) := by
  induction es with
  | nil =>
    intro key _
    iintro H; isplitl [H]; · iexact H
    iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2; iempintro
  | cons e es ih =>
    intro key h
    iintro H
    ihave ⟨H, #Hf⟩ := H_llog_get γ σ T (key 0) e (h 0 e rfl) $$ H
    ihave ⟨H, Hfs⟩ := ih (fun j => key (j + 1)) (fun j e' hj => h (j + 1) e' (by simpa using hj))
      $$ H
    isplitl [H]; · iexact H
    iapply BigSepL.bigSepL_cons.2
    isplitr; · iexact Hf
    iexact Hfs

theorem H_AEok (σ : PState) (T prev pt : Nat) (ents : RLog) (lci : Nat) :
    HistG (GF := GF) γ σ ∗ aeValid γ T prev pt ents lci ⊢
      HistG γ σ ∗ ⌜AEok σ T prev pt ents lci⌝ := by
  unfold aeValid lciOk
  iintro ⟨H, ⟨%ℓ, #Hl⟩, #Hp, #He, #Hc⟩
  ihave ⟨H, %hl⟩ := H_leader_lookup γ σ T ℓ $$ [H]
  · isplitl [H]; iexact H; iexact Hl
  ihave ⟨H, %he⟩ := H_llog_lookup_list γ σ T ents (fun j => prev + 1 + j) $$ [H]
  · isplitl [H]; iexact H; iexact He
  ihave ⟨H, %hp⟩ : HistG γ σ ∗ ⌜(prev = 0 ∧ pt = 0) ∨
      ∃ e : Entry, 1 ≤ prev ∧ e.term = pt ∧ ent (σ.llog T) prev = some e⌝ $$ [H]
  · icases Hp with (%h | ⟨%e, %h, #Hf⟩)
    · iframe; ipureintro; left; exact h
    · ihave ⟨H, %h2⟩ := H_llog_lookup γ σ T prev e $$ [H]
      · isplitl [H]; iexact H; iexact Hf
      iframe; ipureintro; right; exact ⟨e, h.1, h.2, h2⟩
  ihave ⟨H, %hc⟩ : HistG γ σ ∗ ⌜lci = 0 ∨ ((∃ (T' k' p' : Nat) (es : List Entry), T' ≤ T ∧ lci ≤ k' ∧
      lci = es.length ∧ σ.commits T' k' p' ∧ ∀ (j : Nat) (e : Entry), es[j]? = some e →
        ent (σ.llog T) (j + 1) = some e ∧ ent (σ.llog T') (j + 1) = some e) ∧
      ∃ T'' k'', T'' ≤ T ∧ lci ≤ k'' ∧ σ.pubs T'' k'')⌝ $$ [H]
  · icases Hc with (%h | ⟨⟨%T', %k', %p', %es, %h, #Hcm, #Hes⟩, ⟨%T'', %k'', %h'', #Hpb⟩⟩)
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
  iframe; ipureintro
  exact AEok_of σ T prev pt ents lci (by rw [hl]; simp) hp he hc

/-- A term from `termOk` is at most `maxT`. -/
theorem H_termOk (σ : PState) (hg : GInv γ σ) (t : Nat) :
    HistG (GF := GF) γ σ ∗ ([∗list] j ∈ γ.srvs, srvG γ j (σ.srv j)) ∗ termOk γ t ⊢
      HistG γ σ ∗ ([∗list] j ∈ γ.srvs, srvG γ j (σ.srv j)) ∗ ⌜t ≤ σ.maxT⌝ := by
  unfold termOk
  iintro ⟨H, Hs, (⟨%j, %t', Hv, #Hlb, %ht⟩ | ⟨%c, %li, %lt, #Hc⟩ | ⟨%ℓ, #Hl⟩)⟩
  · unfold isSrv
    ihave ⟨H, %hv⟩ := H_voter_lookup γ σ j $$ [H Hv]
    · isplitl [H]; iexact H; iexact Hv
    have hv' : j ∈ γ.srvs := hg.2.1 ▸ hv
    ihave ⟨Hj, Hcl⟩ := srvs_peek γ σ j hv' $$ Hs
    ihave ⟨Hj, %h⟩ := srvG_term_lb γ j (σ.srv j) t' $$ [Hj]
    · isplitl [Hj]; iexact Hj; iexact Hlb
    ihave Hs := Hcl $$ Hj
    iframe; ipureintro
    exact Nat.le_trans ht (Nat.le_trans h (term_le_maxT σ j hg.1 hv))
  · ihave ⟨H, %h⟩ := H_cand_lookup γ σ c t li lt $$ [H]
    · isplitl [H]; iexact H; iexact Hc
    iframe; ipureintro; exact cand_le_maxT σ c t _ hg.1 h
  · ihave ⟨H, %h⟩ := H_leader_lookup γ σ t ℓ $$ [H]
    · isplitl [H]; iexact H; iexact Hl
    iframe; ipureintro; exact leader_le_maxT σ t hg.1 (by rw [h]; simp)

/-! ### Allocation -/

theorem bigSepL_congr_mem {A : Type} (l : List A) (F F' : A → IProp GF) (h : ∀ j ∈ l, F j = F' j) :
    ([∗list] j ∈ l, F j) ⊢ [∗list] j ∈ l, F' j := by
  induction l with
  | nil => exact .rfl
  | cons a l ih =>
    refine BigSepL.bigSepL_cons.1.trans (Entails.trans (sep_mono ?_ ?_) BigSepL.bigSepL_cons.2)
    · rw [h a List.mem_cons_self]
    · exact ih (fun j hj => h j (List.mem_cons_of_mem a hj))

theorem GMapOf_get_all {K V : Type} [DecidableEq K] [Pos.Countable K] [Pos.Countable V]
    (γn : GName) (f : K → Option V) (v : V) (l : List K) (h : ∀ k ∈ l, f k = some v) :
    GMapOf (GF := GF) γn f ⊢ GMapOf γn f ∗ [∗list] k ∈ l, k ↪[γn]□ v := by
  induction l with
  | nil => iintro H; isplitl [H]; · iexact H
           iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2; iempintro
  | cons a l ih =>
    iintro H
    ihave ⟨H, #Ha⟩ := GMapOf_get γn f a v (h a List.mem_cons_self) $$ H
    ihave ⟨H, Hl⟩ := ih (fun k hk => h k (List.mem_cons_of_mem a hk)) $$ H
    isplitl [H]; · iexact H
    iapply BigSepL.bigSepL_cons.2
    isplitr; · iexact Ha
    iexact Hl

/-- A server's freshly allocated per-server state (stage 4: its initial state `s`, the bootstrap
voters' or the empty one). -/
def fullG (s : SState) (n : GName × GName × GName × GName × GName) : IProp GF := iprop(
  monoNatAuthOwn n.1 1 s.term ∗ monoNatAuthOwn n.2.1 1 0 ∗
  ghostVar n.2.2.1 1 s ∗ ghostVar n.2.2.2.1 1 s.log ∗
  ghostVar n.2.2.2.2 1 (0 : Nat))

theorem alloc_srvs (f : SID → SState) (vs : List SID) (hnd : vs.Nodup) :
    ⊢ |==> ∃ N : SID → GName × GName × GName × GName × GName,
      [∗list] i ∈ vs, fullG (GF := GF) (f i) (N i) := by
  induction vs with
  | nil =>
    iexists (fun _ => (0, 0, 0, 0, 0))
    imodintro
    iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2; iempintro
  | cons j rest ih =>
    rw [List.nodup_cons] at hnd
    obtain ⟨hj, hrest⟩ := hnd
    imod mono_nat_own_alloc (GF := GF) (f j).term with ⟨%a, Ha, -⟩
    imod mono_nat_own_alloc (GF := GF) 0 with ⟨%b, Hb, -⟩
    imod ghostVar_alloc (GF := GF) (f j) with ⟨%c, Hc⟩
    imod ghostVar_alloc (GF := GF) (f j).log with ⟨%d, Hd⟩
    imod ghostVar_alloc (GF := GF) (0 : Nat) with ⟨%e, He⟩
    imod (ih hrest) with ⟨%N, HN⟩
    iexists (fun y => if y = j then (a, b, c, d, e) else N y)
    imodintro
    iapply BigSepL.bigSepL_cons.2
    isplitl [Ha Hb Hc Hd He]
    · simp only [if_true]; unfold fullG; iframe
    · iapply bigSepL_congr_mem rest (fun i => fullG (GF := GF) (f i) (N i)) _ ?_ $$ HN
      intro i hi
      have : i ≠ j := fun h => hj (h ▸ hi)
      simp only [if_neg this]

theorem alloc_split (γ : GNames) (i : SID) (s : SState) (hs : s.dur.1 = 0 ∧ s.cidx = 0) :
    fullG (GF := GF) s (γ.term i, γ.dur i, γ.srv i, γ.slog i, γ.cidx i) ∗ i ↪[γ.srvSet]□ () ⊢
      srvG γ i s ∗
      (isSrv γ i ∗ srvOwn γ i s ∗ durView γ i (1 : Qp).half 0 ∗
        termCouple γ i s.term ∗ logCouple γ i s.log ∗ cidxCouple γ i 0) := by
  unfold fullG srvG isSrv srvOwn durView termCouple logCouple cidxCouple
  iintro ⟨⟨Ht, Hd, Hs, Hl, Hc⟩, #Hv⟩
  ihave ⟨Ht1, Ht2⟩ := (monoNat_halves (γ.term i) s.term).1 $$ Ht
  ihave ⟨Hd1, Hd2⟩ := (monoNat_halves (γ.dur i) 0).1 $$ Hd
  ihave ⟨Hs1, Hs2⟩ := (ghostVar_split_half (γ.srv i) 1 _).1 $$ Hs
  ihave ⟨Hl1, Hl2⟩ := (ghostVar_split_half (γ.slog i) 1 _).1 $$ Hl
  ihave ⟨Hc1, Hc2⟩ := (ghostVar_split_half (γ.cidx i) 1 _).1 $$ Hc
  isplitl [Ht1 Hd1 Hs1 Hl1 Hc1]
  · rw [hs.1, hs.2]; iframe
  isplitr; · iexact Hv
  isplitl [Hs2]; · iframe; iexact Hv
  isplitl [Hd2]; · iexact Hd2
  isplitl [Ht2]; · iexact Ht2
  isplitl [Hl2]; · iframe; iexact Hv
  iexact Hc2

theorem H_voters_all (σ : PState) :
    HistG (GF := GF) γ σ ⊢ HistG γ σ ∗ [∗list] i ∈ σ.srvs, i ↪[γ.srvSet]□ () := by
  unfold HistG
  iintro ⟨H0, H1, H2, H3, H4, H5, H6, H, Hr⟩
  ihave ⟨H, Hl⟩ := GMapOf_get_all γ.srvSet (srvsF σ) () σ.srvs
    (fun i hi => (srvsF_iff σ i).mpr hi) $$ H
  isplitl [H0 H1 H2 H3 H4 H5 H6 H Hr]; · iframe
  iexact Hl

theorem alloc_core (E : CoPset) (hnd : γ.srvs.Nodup) (hne : ∀ j ∈ γ.srvs, j ≠ [])
    (hg1 : γ.g.term = 1) (hgk : γ.g.kind = kConfig) (hcv : cfgValid γ.srvs (γ.cv γ.g.data)) :
    HistG (GF := GF) γ (init γ.srvs γ.g γ.cv) ∗
      ([∗list] i ∈ γ.srvs, fullG (initSrv γ.cv γ.g i)
        (γ.term i, γ.dur i, γ.srv i, γ.slog i, γ.cidx i)) ∗
      receipt 2 ∗ CcfgG γ (init γ.srvs γ.g γ.cv) ⊢ |={E}=> Inv γ ∗
      [∗list] i ∈ γ.srvs, isSrv γ i ∗ srvOwn γ i (initSrv γ.cv γ.g i) ∗
        durView γ i (1 : Qp).half 0 ∗ termCouple γ i (initSrv γ.cv γ.g i).term ∗
        logCouple γ i (initSrv γ.cv γ.g i).log ∗ cidxCouple γ i 0 := by
  iintro ⟨Hh, HN, Hr, Hcc⟩
  ihave ⟨Hh, Hvs⟩ := H_voters_all γ (init γ.srvs γ.g γ.cv) $$ Hh
  rw [show (init γ.srvs γ.g γ.cv).srvs = γ.srvs from rfl]
  ihave H := BigSepL.bigSepL_sep_eqv.2 $$ [HN Hvs]
  · isplitl [HN]; iexact HN; iexact Hvs
  ihave H := BigSepL.bigSepL_mono (fun {k i} _ => alloc_split γ i (initSrv γ.cv γ.g i)
    (by unfold initSrv; split <;> exact ⟨rfl, rfl⟩)) $$ H
  ihave ⟨Hsrvs, Hcl⟩ := BigSepL.bigSepL_sep_eqv.1 $$ H
  imod inv_alloc gprotN E (InvInner γ) $$ [Hh Hsrvs Hr Hcc] with Hinv
  · inext
    iapply InvInner_close γ (init γ.srvs γ.g γ.cv) (initSrv γ.cv γ.g) 2 rfl
      (by simp [init]) ⟨init_inv γ.srvs γ.g γ.cv hnd hg1 hgk hcv, rfl, rfl, rfl,
        init_kinds γ.srvs γ.g γ.cv hgk, hne⟩
    iframe
  imodintro
  isplitl [Hinv]
  · rw [Inv_unseal]; unfold InvDef; iexact Hinv
  · iexact Hcl

/-! ### Snapshots (stage 2) -/

theorem snapLe_of_prefix {L1 L2 : List Snap} (hp : L1 <+: L2) (hpw : L2.Pairwise snapLe)
    {a b : Snap} (ha : L1.getLast? = some a) (hb : L2.getLast? = some b) : snapLe a b := by
  obtain ⟨t, rfl⟩ := hp
  by_cases ht : t = []
  · subst ht; rw [List.append_nil, ha] at hb; cases hb; exact snapLe_refl _
  · have hb' : t.getLast? = some b := by
      rw [List.getLast?_append] at hb
      cases h : t.getLast? with
      | none => simp_all
      | some x => rw [h] at hb; simpa using hb
    have hbm : b ∈ t := List.mem_of_getLast? hb'
    have ham : a ∈ L1 := List.mem_of_getLast? ha
    exact (List.pairwise_append.1 hpw).2.2 a ham b hbm

theorem getElem?_append_one {L : List Snap} {s x : Snap} {n : Nat} (h : (L ++ [s])[n]? = some x) :
    (n < L.length ∧ L[n]? = some x) ∨ (n = L.length ∧ x = s) := by
  rw [List.getElem?_append] at h
  split at h
  · left; exact ⟨by omega, h⟩
  · right; rw [List.getElem?_singleton] at h; split at h <;> simp_all <;> omega

/-- The snapshots' authority of the opened history. -/
theorem H_snapG_open (σ : PState) :
    HistG (GF := GF) γ σ ⊢ ∃ L : List Snap, monoListAuthOwn γ.hist 1 L ∗
      ⌜(∀ (n : Nat) (s : Snap), L[n]? = some s → s.idx = n ∧ SnapOK σ s) ∧ L.Pairwise snapLe⌝ ∗
      (∀ L' : List Snap, monoListAuthOwn γ.hist 1 L' -∗
        ⌜(∀ (n : Nat) (s : Snap), L'[n]? = some s → s.idx = n ∧ SnapOK σ s) ∧ L'.Pairwise snapLe⌝ -∗
        HistG γ σ) := by
  unfold HistG SnapG
  iintro ⟨H0, H1, H2, H3, H4, H5, H6, H7, HO, HC, Hp, Hpm, ⟨%L, Ha, %h⟩⟩
  iexists L
  isplitl [Ha]; · iexact Ha
  isplitr; · ipureintro; exact h
  iintro %L' Ha' %h'
  iframe
  ipureintro; exact h'

theorem snapG_lb_mem (L : List Snap) (s : Snap) :
    monoListAuthOwn (GF := GF) γ.hist 1 L ∗ histLb γ s ⊢ monoListAuthOwn γ.hist 1 L ∗ ⌜s ∈ L⌝ := by
  unfold histLb
  iintro ⟨Ha, %L0, #Hlb, %h⟩
  ihave %hp := mono_list_auth_lb_valid γ.hist 1 L L0 $$ Ha Hlb
  iframe
  ipureintro
  exact hp.2.subset (List.mem_of_getLast? h.1)

theorem snapG_lbs_mem (L : List Snap) (S : List Snap) :
    monoListAuthOwn (GF := GF) γ.hist 1 L ∗ ([∗list] s0 ∈ S, histLb γ s0) ⊢
      monoListAuthOwn γ.hist 1 L ∗ ⌜∀ s0 ∈ S, s0 ∈ L⌝ := by
  induction S with
  | nil => iintro ⟨Ha, -⟩; iframe; ipureintro; intro s0 h; simp at h
  | cons a S ih =>
    iintro ⟨Ha, Hl⟩
    ihave ⟨#Hf, Hfs⟩ := BigSepL.bigSepL_cons.1 $$ Hl
    ihave ⟨Ha, %h0⟩ := snapG_lb_mem γ L a $$ [Ha]
    · isplitl [Ha]; iexact Ha; iexact Hf
    ihave ⟨Ha, %hs⟩ := ih $$ [Ha Hfs]
    · isplitl [Ha]; iexact Ha; iexact Hfs
    iframe; ipureintro
    intro s0 hs0
    rcases List.mem_cons.mp hs0 with h | h
    · subst h; exact h0
    · exact hs s0 h

theorem srvs_durLbs (σ : PState) (ds : List (SID × Nat)) :
    ([∗list] j ∈ γ.srvs, srvG (GF := GF) γ j (σ.srv j)) ∗ ([∗list] p ∈ ds, durLb γ p.1 p.2) ⊢
      ([∗list] j ∈ γ.srvs, srvG γ j (σ.srv j)) ∗
        ⌜∀ p ∈ ds, p.1 ∈ γ.srvs → p.2 ≤ (σ.srv p.1).dur.1⌝ := by
  induction ds with
  | nil => iintro ⟨Hs, -⟩; iframe; ipureintro; intro p h; simp at h
  | cons a ds ih =>
    iintro ⟨Hs, Hl⟩
    ihave ⟨#Hf, Hfs⟩ := BigSepL.bigSepL_cons.1 $$ Hl
    ihave ⟨Hs, %hs⟩ := ih $$ [Hs Hfs]
    · isplitl [Hs]; iexact Hs; iexact Hfs
    by_cases ha : a.1 ∈ γ.srvs
    · ihave ⟨Hi, Hcl⟩ := srvs_peek γ σ a.1 ha $$ Hs
      ihave ⟨Hi, %h0⟩ := srvG_dur_lb γ a.1 (σ.srv a.1) a.2 $$ [Hi]
      · isplitl [Hi]; iexact Hi; iexact Hf
      ihave Hs := Hcl $$ Hi
      iframe; ipureintro
      intro p hp hv
      rcases List.mem_cons.mp hp with h | h
      · subst h; exact h0
      · exact hs p h hv
    · iframe; ipureintro
      intro p hp hv
      rcases List.mem_cons.mp hp with h | h
      · subst h; exact absurd hv ha
      · exact hs p h hv

/-- A snapshot of the opened history's state, after every held snapshot. -/
theorem H_snap_take (σ : PState) (hg : GInv γ σ) (S : List Snap) :
    HistG (GF := GF) γ σ ∗ ([∗list] s0 ∈ S, histLb γ s0) ⊢
      |==> (HistG γ σ ∗ ∃ n, histLb γ (snapOf σ n) ∗ ⌜∀ s0 ∈ S, snapLe s0 (snapOf σ n)⌝) := by
  iintro ⟨Hh, HS⟩
  ihave ⟨%L, Ha, %hL, Hcl⟩ := H_snapG_open γ σ $$ Hh
  ihave ⟨Ha, %hS⟩ := snapG_lbs_mem γ L S $$ [Ha HS]
  · isplitl [Ha]; iexact Ha; iexact HS
  have hP := hg.1
  have hmemL : ∀ x ∈ L, x.idx < L.length ∧ SnapOK σ x := by
    intro x hx
    obtain ⟨n, hn⟩ := List.mem_iff_getElem?.1 hx
    have := hL.1 n x hn
    refine ⟨?_, this.2⟩
    rw [this.1]; exact (List.getElem?_eq_some_iff.1 hn).1
  have hle : ∀ x ∈ L, snapLe x (snapOf σ L.length) := fun x hx =>
    snapLe_now σ x L.length hP (hmemL x hx).2 (Nat.le_of_lt (hmemL x hx).1)
  have hidx : ∀ (n : Nat) (x : Snap), (L ++ [snapOf σ L.length])[n]? = some x →
      x.idx = n ∧ SnapOK σ x := by
    intro n x hn
    rcases getElem?_append_one hn with ⟨_, h⟩ | ⟨rfl, rfl⟩
    · exact hL.1 n x h
    · exact ⟨rfl, snapOK_now σ _ hP⟩
  have hpw : (L ++ [snapOf σ L.length]).Pairwise snapLe := by
    rw [List.pairwise_append]
    refine ⟨hL.2, List.pairwise_singleton _ _, fun a ha b hb => ?_⟩
    rw [List.mem_singleton] at hb; subst hb; exact hle a ha
  have hnew := And.intro hidx hpw
  imod monoListAuthOwn_update_app [snapOf σ L.length] $$ Ha with ⟨Ha, #Hlb⟩
  ihave Hh := Hcl $$ %(L ++ [snapOf σ L.length]) Ha %hnew
  imodintro
  isplitl [Hh]; · iexact Hh
  iexists L.length
  isplitr
  · unfold histLb
    iexists (L ++ [snapOf σ L.length])
    isplitr; · iexact Hlb
    ipureintro
    refine ⟨by simp, fun n x hn => (hidx n x hn).1, hpw, ?_, fun x hx => ?_⟩
    · rw [← hg.2.1]; exact hP.1.2.2.1
    · obtain ⟨n, hn⟩ := List.mem_iff_getElem?.1 hx
      have hok := (hidx n x hn).2
      rw [← hg.2.1]; exact ⟨hok.1, hok.2.1⟩
  · ipureintro
    intro s0 hs0; exact hle s0 (hS s0 hs0)

/-- A held snapshot is known to the current state. -/
theorem H_histLb_ok (σ : PState) (s : Snap) :
    HistG (GF := GF) γ σ ∗ histLb γ s ⊢ HistG γ σ ∗ ⌜SnapOK σ s⌝ := by
  iintro ⟨Hh, #Hs0⟩
  ihave ⟨%L, Ha, %hL, Hcl⟩ := H_snapG_open γ σ $$ Hh
  ihave ⟨Ha, %hm⟩ := snapG_lb_mem γ L s $$ [Ha]
  · isplitl [Ha]; iexact Ha; iexact Hs0
  ihave Hh := Hcl $$ %L Ha %hL
  iframe
  ipureintro
  obtain ⟨n, hn⟩ := List.mem_iff_getElem?.1 hm
  exact (hL.1 n s hn).2

/-- The leader's bound on its publications. -/
theorem H_pubOwn_bound (σ : PState) (j : SID) (T k : Nat) :
    HistG (GF := GF) γ σ ∗ pubOwn γ j T k ⊢
      HistG γ σ ∗ pubOwn γ j T k ∗ ⌜∀ k', σ.pubs T k' → σ.leader T = some j → k' ≤ k⌝ := by
  unfold HistG PubMaxG pubOwn
  iintro ⟨⟨H0, H1, H2, H3, H4, H5, H6, H7, HO, HC, Hp, ⟨%PM, Ha, %h⟩, Hs⟩, Hk⟩
  icombine Ha Hk gives %hlk
  isplitl [H0 H1 H2 H3 H4 H5 H6 H7 HO HC Hp Ha Hs]
  · iframe; ipureintro; exact h
  isplitl [Hk]; · iexact Hk
  ipureintro
  intro k' hk' hl
  obtain ⟨ℓ, m, hl', hpm, hkm⟩ := h.2 T k' hk'
  rw [hl] at hl'; cases hl'
  rw [hlk] at hpm; cases hpm; exact hkm

end internal

end gprot
end github_com.hashicorp.raft

end Perennial
