/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/proto/Misc.lean (241f27e).
-/
/-
`proto` — the remaining steps: `setTerm`, `newTerm`, `recordCand`, `grantVote`, `commit`,
`learnCommit`, `setCidx`; the initial state; `Grows` is a preorder.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.proto.SrvFrame

@[expose] public section

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

noncomputable section

namespace Perennial
namespace github_com.hashicorp.raft
namespace proto

/-! ### `Grows` -/

theorem grows_refl' (σ : PState) : Grows σ σ :=
  ⟨rfl, ⟨rfl, rfl⟩, fun _ _ x => x, fun _ => ⟨List.prefix_refl _, fun _ => rfl⟩, fun _ _ _ x => x,
    fun _ _ _ x => x, fun _ _ _ x => x, fun _ _ _ x => x, List.prefix_refl _,
    fun _ => Nat.le_refl _, fun _ => Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, fun _ _ x => x,
    fun _ _ _ _ x => Or.inl x⟩

theorem grows_trans' {σ1 σ2 σ3 : PState} (h1 : Grows σ1 σ2) (h2 : Grows σ2 σ3) : Grows σ1 σ3 := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩ := h1
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15⟩ := h2
  refine ⟨b1.trans a1, ⟨b2.1.trans a2.1, b2.2.trans a2.2⟩, fun T ℓ h => b3 T ℓ (a3 T ℓ h),
    fun T => ⟨(a4 T).1.trans (b4 T).1,
    fun hT => ?_⟩, fun c T x h => b5 c T x (a5 c T x h), fun j T x h => b6 j T x (a6 j T x h),
    fun j T m h => b7 j T m (a7 j T m h), fun T k p h => b8 T k p (a8 T k p h), a9.trans b9,
    fun i => Nat.le_trans (a10 i) (b10 i), fun i => Nat.le_trans (a11 i) (b11 i),
    Nat.le_trans a12 b12, Nat.le_trans a13 b13, fun T k h => b14 T k (a14 T k h), ?_⟩
  · rw [(b4 T).2 ?_, (a4 T).2 hT]
    rcases hT with hT | hT
    · left
      obtain ⟨ℓ, hℓ⟩ := Option.ne_none_iff_exists'.mp hT
      rw [a3 T ℓ hℓ]; simp
    · exact Or.inr hT
  · intro j T c L hv
    rcases b15 j T c L hv with h | h
    · exact a15 j T c L h
    · right
      cases h1 : σ1.leader T with
      | none => rfl
      | some ℓ => rw [a3 T ℓ h1] at h; cases h

/-! ### Steps that keep every server's log and term -/

theorem srvKeep_inv {σ : PState} {i : SID} {s : SState} (h : PInv σ)
    (hl : s.log = (σ.srv i).log) (ht : s.term = (σ.srv i).term) (hvt : s.vterm = (σ.srv i).vterm)
    (hvc : s.vcand = (σ.srv i).vcand) (hdur : (σ.srv i).dur.1 ≤ s.dur.1)
    (hD' : IDur (setSrv σ i s)) (hP' : IPub (setSrv σ i s)) :
    PInv (setSrv σ i s) ∧ Grows σ (setSrv σ i s) := by
  have elog : ∀ j, (setSrv σ i s).log j = σ.log j := by
    intro j; rw [setSrv_log]; split
    · subst_vars; exact hl
    · rfl
  have eterm : ∀ j, (setSrv σ i s).term j = σ.term j := by
    intro j; rw [setSrv_term]; split
    · subst_vars; exact ht
    · rfl
  have hg : HG σ (setSrv σ i s) := HG.refl_llog rfl rfl rfl rfl rfl
  obtain ⟨hG, hL, hLo, hC, hV, hA, hVA, hLC, hCo, hD, hB, hX, hP, hR⟩ := h
  obtain ⟨l1, l2, l3, l4, l5⟩ := hLo
  obtain ⟨b1, b2, b3, b4, b5⟩ := hB
  refine ⟨⟨hG, hL, ⟨fun j hj => ?_, l2, l3, l4, l5⟩, fun j hj hl' => ?_, ?_,
    IAcks_grow hg hL (fun j _ => by rw [elog]; exact List.prefix_refl _)
      (fun j _ => by rw [eterm]; exact Nat.le_refl _) (fun _ _ _ x => x) hA,
    hVA, hLC, hCo, hD', ⟨fun j hj => ?_, b2, b3, b4, b5⟩, fun j hj => ?_, hP', hR⟩, ?_⟩
  · rw [elog]; exact l1 j hj
  · rw [eterm] at hl' ⊢; rw [elog]; exact hC j hj hl'
  · refine IVotes_srv (σ := σ) rfl rfl rfl rfl (fun j => ?_) (fun j => by rw [eterm]; exact Nat.le_refl _) hV
    rw [setSrv_srv]; split
    · subst_vars; exact ⟨hvt, hvc⟩
    · exact ⟨rfl, rfl⟩
  · rw [elog, eterm]; exact b1 j hj
  · rw [elog, eterm]; exact hX j hj
  · refine ⟨rfl, ⟨rfl, rfl⟩, fun _ _ x => x, fun T => ⟨List.prefix_refl _, fun _ => rfl⟩,
      fun _ _ _ x => x, fun _ _ _ x => x, fun _ _ _ x => x, fun _ _ _ x => x, List.prefix_refl _,
      fun j => by rw [eterm]; exact Nat.le_refl _, fun j => ?_, Nat.le_refl _, Nat.le_refl _,
      fun _ _ x => x, fun _ _ _ _ x => Or.inl x⟩
    rw [setSrv_srv]; split
    · subst_vars; exact hdur
    · exact Nat.le_refl _

theorem setCidx_inv' (σ : PState) (i : SID) (c : Nat) (h : PInv σ) (hp : setCidxPre σ i c) :
    PInv (setCidx σ i c) ∧ Grows σ (setCidx σ i c) := by
  show PInv (setSrv σ i { σ.srv i with cidx := c }) ∧ Grows σ (setSrv σ i { σ.srv i with cidx := c })
  refine srvKeep_inv (s := { σ.srv i with cidx := c }) h rfl rfl rfl rfl (Nat.le_refl _) ?_ ?_
  rotate_left
  · refine IPub_grow (σ := σ) (HG.refl_llog rfl rfl rfl rfl rfl) (fun j _ => ?_) (fun j _ => ?_) (fun _ _ _ x => x) rfl
      h.2.2.2.2.2.2.2.2.2.2.2.2.1
    · rw [setSrv_term]; split <;> (subst_vars; exact Nat.le_refl _)
    · rw [setSrv_srv]; split <;> (subst_vars; rfl)
  intro j hj
  rw [setSrv_srv, setSrv_log, setSrv_term]
  have hD := h.2.2.2.2.2.2.2.2.2.1
  split
  · subst_vars; exact ⟨(hD j hj).1, hp.2⟩
  · exact hD j hj

theorem learnCommit_inv' (σ : PState) (i : SID) (k T' : Nat) (h : PInv σ)
    (hp : learnCommitPre σ i k T') :
    PInv (learnCommit σ i k T') ∧ Grows σ (learnCommit σ i k T') := by
  show PInv (setSrv σ i { σ.srv i with dur := if (σ.srv i).dur.1 < k then (k, T') else (σ.srv i).dur })
    ∧ Grows σ (setSrv σ i { σ.srv i with dur := if (σ.srv i).dur.1 < k then (k, T') else (σ.srv i).dur })
  refine srvKeep_inv
    (s := { σ.srv i with dur := if (σ.srv i).dur.1 < k then (k, T') else (σ.srv i).dur })
    h rfl rfl rfl rfl ?_ ?_ ?_
  rotate_left 2
  · have hP := h.2.2.2.2.2.2.2.2.2.2.2.2.1
    obtain ⟨_, _, _, _, ⟨T'', k'', hT'', hk'', hpk⟩⟩ := hp
    refine ⟨fun T k1 hp1 => hP.1 T k1 hp1, fun j hj => ?_⟩
    rw [setSrv_srv, setSrv_term]
    by_cases hji : j = i
    · subst hji
      rw [if_pos rfl, if_pos rfl]
      show ((if (σ.srv j).dur.1 < k then (k, T') else (σ.srv j).dur).1 = 0 ∨ _)
      split
      · exact Or.inr ⟨T'', k'', hT'', hk'', hpk⟩
      · exact hP.2 j hj
    · rw [if_neg hji, if_neg hji]; exact hP.2 j hj
  · show (σ.srv i).dur.1 ≤ (if (σ.srv i).dur.1 < k then (k, T') else (σ.srv i).dur).1
    split
    · simp; omega
    · exact Nat.le_refl _
  intro j hj
  rw [setSrv_srv, setSrv_log, setSrv_term]
  have hD := h.2.2.2.2.2.2.2.2.2.1
  split
  · subst_vars
    obtain ⟨hi, hT, hc, hag, _⟩ := hp
    obtain ⟨hd, hcx⟩ := hD j hj
    show ((if (σ.srv j).dur.1 < k then (k, T') else (σ.srv j).dur).1 = 0 ∨ _) ∧ _
    split
    · exact ⟨Or.inr ⟨hT, hc, hag⟩, by simp; omega⟩
    · exact ⟨hd, hcx⟩
  · exact hD j hj

/-! ### setTerm and newTerm -/

theorem setTerm_inv' (σ : PState) (i : SID) (t : Nat) (h : PInv σ) (hp : setTermPre σ i t) :
    PInv (setTerm σ i t) ∧ Grows σ (setTerm σ i t) := by
  obtain ⟨hi, hle, hmx⟩ := hp
  have elog : ∀ j, (setTerm σ i t).log j = σ.log j := by
    intro j; show (setSrv σ i _).log j = _; rw [setSrv_log]; split
    · subst_vars; rfl
    · rfl
  have eterm : ∀ j, (setTerm σ i t).term j = if j = i then t else σ.term j := by
    intro j; show (setSrv σ i _).term j = _; rw [setSrv_term]
  have hterm : ∀ j, σ.term j ≤ (setTerm σ i t).term j := by
    intro j; rw [eterm]; split
    · subst_vars; exact hle
    · exact Nat.le_refl _
  have hsrv : ∀ j, ((setTerm σ i t).srv j).vterm = (σ.srv j).vterm ∧
      ((setTerm σ i t).srv j).vcand = (σ.srv j).vcand ∧
      ((setTerm σ i t).srv j).dur = (σ.srv j).dur ∧ ((setTerm σ i t).srv j).cidx = (σ.srv j).cidx := by
    intro j; show ((setSrv σ i _).srv j).vterm = _ ∧ ((setSrv σ i _).srv j).vcand = _ ∧
      ((setSrv σ i _).srv j).dur = _ ∧ ((setSrv σ i _).srv j).cidx = _
    rw [setSrv_srv]; split <;> (subst_vars; exact ⟨rfl, rfl, rfl, rfl⟩)
  have hg : HG σ (setTerm σ i t) := HG.refl_llog rfl rfl rfl rfl rfl
  obtain ⟨hG, hL, hLo, hC, hV, hA, hVA, hLC, hCo, hD, hB, hX, hP, hR⟩ := h
  obtain ⟨l1, l2, l3, l4, l5⟩ := hLo
  obtain ⟨b1, b2, b3, b4, b5⟩ := hB
  refine ⟨⟨hG, hL, ⟨fun j hj => ?_, l2, l3, l4, l5⟩, fun j hj hl' => ?_,
    IVotes_srv (σ := σ) rfl rfl rfl rfl (fun j => ⟨(hsrv j).1, (hsrv j).2.1⟩) hterm hV,
    IAcks_grow hg hL (fun j _ => by rw [elog]; exact List.prefix_refl _)
      (fun j _ => hterm j) (fun _ _ _ x => x) hA,
    hVA, hLC, hCo,
    IDur_grow hg (fun j _ => by rw [elog]; exact List.prefix_refl _) (fun j _ => hterm j)
      (fun j _ => ⟨(hsrv j).2.2.1, (hsrv j).2.2.2⟩) (fun _ _ _ x => x) hD,
    ⟨fun j hj => ?_, b2, b3, b4, b5⟩, fun j hj => ?_,
    IPub_grow hg (fun j _ => hterm j) (fun j _ => by rw [(hsrv j).2.2.1]) (fun _ _ _ x => x) rfl hP,
    hR⟩, ?_⟩
  · rw [elog]; exact l1 j hj
  · rw [elog]
    have hl'' : σ.leader ((setTerm σ i t).term j) = some j := hl'
    rw [eterm] at hl'' ⊢
    split
    · subst_vars
      rw [if_pos' rfl] at hl''
      have hcand := (hL.1 t j hl'').2.2.2.2.2.2.2.1
      have := (hV.2.2 j t _ hcand).2.2
      have e : t = σ.term j := by omega
      subst e
      exact hC j hj hl''
    · rw [if_neg' (by assumption)] at hl''
      exact hC j hj hl''
  · rw [elog, eterm]; split
    · subst_vars; exact ⟨hmx, (b1 j hj).2⟩
    · exact b1 j hj
  · rw [elog]
    refine ⟨fun hne => Nat.le_trans ((hX j hj).1 hne) (hterm j), fun k h1 h2 => ?_⟩
    exact Nat.le_trans ((hX j hj).2 k h1 h2) (hterm j)
  · refine ⟨rfl, ⟨rfl, rfl⟩, fun _ _ x => x, fun T => ⟨List.prefix_refl _, fun _ => rfl⟩,
      fun _ _ _ x => x, fun _ _ _ x => x, fun _ _ _ x => x, fun _ _ _ x => x, List.prefix_refl _,
      hterm, fun j => by rw [(hsrv j).2.2.1]; exact Nat.le_refl _, Nat.le_refl _, Nat.le_refl _,
      fun _ _ x => x, fun _ _ _ _ x => Or.inl x⟩

/-- `newTerm` is `setTerm` after raising `maxT`. -/
theorem newTerm_eq (σ : PState) (i : SID) :
    newTerm σ i = setTerm { σ with maxT := max σ.maxT (σ.term i + 1) } i (σ.term i + 1) := rfl

theorem newTerm_inv' (σ : PState) (i : SID) (h : PInv σ) (hp : newTermPre σ i) :
    PInv (newTerm σ i) ∧ Grows σ (newTerm σ i) := by
  let σ1 : PState := { σ with maxT := max σ.maxT (σ.term i + 1) }
  have h1 : PInv σ1 := by
    obtain ⟨hG, hL, hLo, hC, hV, hA, hVA, hLC, hCo, hD, hB, hX, hP, hR⟩ := h
    obtain ⟨b1, b2, b3, b4, b5⟩ := hB
    refine ⟨hG, hL, hLo, hC, hV, hA, hVA, hLC, hCo, hD, ⟨fun j hj => ?_, b2, fun T hT => ?_, ?_, b5⟩, hX, hP, hR⟩
    · have := b1 j hj; exact ⟨by show σ.term j ≤ max _ _; omega, this.2⟩
    · have hT' : max σ.maxT (σ.term i + 1) < T := hT
      exact b3 T (by omega)
    · show 1 ≤ max _ _; omega
  have g1 : Grows σ σ1 := by
    refine ⟨rfl, ⟨rfl, rfl⟩, fun _ _ x => x, fun T => ⟨List.prefix_refl _, fun _ => rfl⟩,
      fun _ _ _ x => x, fun _ _ _ x => x, fun _ _ _ x => x, fun _ _ _ x => x, List.prefix_refl _,
      fun _ => Nat.le_refl _, fun _ => Nat.le_refl _, ?_, Nat.le_refl _, fun _ _ x => x,
      fun _ _ _ _ x => Or.inl x⟩
    show σ.maxT ≤ max _ _; omega
  have hp1 : setTermPre σ1 i (σ.term i + 1) :=
    ⟨hp, Nat.le_succ _, by show _ ≤ max _ _; omega⟩
  rw [newTerm_eq]
  have := setTerm_inv' σ1 i _ h1 hp1
  exact ⟨this.1, grows_trans' g1 this.2⟩

/-! ### recordCand -/

theorem recordCand_inv' (σ : PState) (c : SID) (h : PInv σ) (hp : recordCandPre σ c) :
    PInv (recordCand σ c) ∧ Grows σ (recordCand σ c) := by
  obtain ⟨hc, hT2, hltT, hnone⟩ := hp
  have hext : ∀ c' T x, σ.cand c' T = some x → (recordCand σ c).cand c' T = some x := by
    intro c' T x hx
    show updST σ.cand c (σ.term c) _ c' T = _
    rw [updST_apply, if_neg']
    · exact hx
    · rintro ⟨rfl, rfl⟩; rw [hnone] at hx; cases hx
  obtain ⟨hG, hL, hLo, hC, hV, hA, hVA, hLC, hCo, hD, hB, hX, hP, hR⟩ := h
  refine ⟨⟨hG, ⟨fun T ℓ hl => ?_, hL.2⟩, hLo, hC, ⟨fun j T c' L b hv => ?_, hV.2.1, fun c' T x hx => ?_⟩,
    hA, hVA, hLC, hCo, hD, hB, hX, hP, hR⟩, ?_⟩
  · obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := hL.1 T ℓ hl
    exact ⟨a1, a2, a3, a4, a5, a6, a7, hext _ _ _ a8, a9, a10⟩
  · obtain ⟨a1, a2, a3, ⟨li, lt, a4, a4'⟩, a5⟩ := hV.1 j T c' L b hv
    exact ⟨a1, a2, a3, ⟨li, lt, hext _ _ _ a4, a4'⟩, a5⟩
  · have hx' : updST σ.cand c (σ.term c) _ c' T = some x := hx
    rw [updST_apply] at hx'
    split at hx'
    · obtain ⟨rfl, rfl⟩ := ‹c' = c ∧ T = σ.term c›
      cases hx'
      refine ⟨hc, hT2, Nat.le_refl _, fun h1 => ?_, hltT⟩
      have hlt : lastTerm (σ.log c') < σ.term c' := hltT
      have hl1 : σ.log c' = [] := by
        apply Classical.byContradiction; intro hne
        have hx1 : 1 ≤ (σ.log c').length := by
          cases hh : σ.log c' with
          | nil => exact absurd hh hne
          | cons _ _ => simp
        have := (LMok_last_pos hG hL (hLo.1 c' hc).1 hx1).1
        omega
      show (σ.log c').length = 0
      rw [hl1]; rfl
    · exact hV.2.2 c' T x hx'
  · exact ⟨rfl, ⟨rfl, rfl⟩, fun _ _ x => x, fun T => ⟨List.prefix_refl _, fun _ => rfl⟩,
      hext, fun _ _ _ x => x, fun _ _ _ x => x, fun _ _ _ x => x, List.prefix_refl _,
      fun _ => Nat.le_refl _, fun _ => Nat.le_refl _, Nat.le_refl _, Nat.le_refl _,
      fun _ _ x => x, fun _ _ _ _ x => Or.inl x⟩

/-! ### grantVote -/

theorem grantVote_inv' (σ : PState) (j c : SID) (h : PInv σ) (hp : grantVotePre σ j c) :
    PInv (grantVote σ j c) ∧ Grows σ (grantVote σ j c) := by
  obtain ⟨hj, hvt, li, lt, hcand, hu⟩ := hp
  have hvnone : σ.votes j (σ.term j) = none := by
    cases hx : σ.votes j (σ.term j) with
    | none => rfl
    | some x =>
      obtain ⟨c', L, b⟩ := x
      have := (h.2.2.2.2.1.1 j _ c' L b hx).2.2.1
      omega
  have hvotes : ∀ j' T x, (grantVote σ j c).votes j' T = some x ↔
      σ.votes j' T = some x ∨
        (j' = j ∧ T = σ.term j ∧ x = (c, σ.log j, decide (σ.leader (σ.term j) = none))) := by
    intro j' T x
    show updST σ.votes j (σ.term j) _ j' T = _ ↔ _
    rw [updST_apply]
    constructor
    · intro hx
      split at hx
      · obtain ⟨rfl, rfl⟩ := ‹j' = j ∧ T = σ.term j›
        cases hx
        exact Or.inr ⟨rfl, rfl, rfl⟩
      · exact Or.inl hx
    · rintro (hx | ⟨rfl, rfl, rfl⟩)
      · rw [if_neg']
        · exact hx
        · rintro ⟨rfl, rfl⟩; rw [hvnone] at hx; cases hx
      · rw [if_pos' ⟨rfl, rfl⟩]
  have hext : ∀ j' T x, σ.votes j' T = some x → (grantVote σ j c).votes j' T = some x :=
    fun j' T x hx => (hvotes j' T x).mpr (Or.inl hx)
  have hsrv : ∀ j', ((grantVote σ j c).srv j') =
      if j' = j then { σ.srv j with vterm := σ.term j, vcand := c } else σ.srv j' := fun _ => rfl
  have elog : ∀ j', (grantVote σ j c).log j' = σ.log j' := by
    intro j'; unfold PState.log; rw [hsrv]; split
    · subst_vars; rfl
    · rfl
  have eterm : ∀ j', (grantVote σ j c).term j' = σ.term j' := by
    intro j'; unfold PState.term; rw [hsrv]; split
    · subst_vars; rfl
    · rfl
  have hdur : ∀ j', ((grantVote σ j c).srv j').dur = (σ.srv j').dur ∧
      ((grantVote σ j c).srv j').cidx = (σ.srv j').cidx := by
    intro j'; rw [hsrv]; split
    · subst_vars; exact ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩
  have hg : HG σ (grantVote σ j c) := HG.refl_llog rfl rfl rfl rfl rfl
  obtain ⟨hG, hL, hLo, hC, hV, hA, hVA, hLC, hCo, hD, hB, hX, hP, hR⟩ := h
  obtain ⟨l1, l2, l3, l4, l5⟩ := hLo
  obtain ⟨b1, b2, b3, b4, b5⟩ := hB
  have hL' : ILeaders (grantVote σ j c) := by
    refine ⟨fun T ℓ hl => ?_, hL.2⟩
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, ⟨Q, hQ, hQv⟩, a10⟩ := hL.1 T ℓ hl
    refine ⟨a1, a2, a3, a4, a5, a6, a7, a8, ⟨Q, hQ, fun j' hj' => ?_⟩, a10⟩
    obtain ⟨L, hv⟩ := hQv j' hj'
    exact ⟨L, hext _ _ _ hv⟩
  have hLo' : ILogs (grantVote σ j c) := by
    refine ⟨fun j' hj' => by rw [elog]; exact l1 j' hj', l2, fun j' T c' L b hv => ?_, l4, l5⟩
    rcases (hvotes j' T _).mp hv with hv | ⟨rfl, rfl, hx⟩
    · exact l3 j' T c' L b hv
    · cases hx; exact (l1 _ hj).1
  have hV' : IVotes (grantVote σ j c) := by
    refine ⟨fun j' T c' L b hv => ?_, fun j' hj' => ?_, fun c' T x hx => ?_⟩
    · rcases (hvotes j' T _).mp hv with hv | ⟨rfl, rfl, hx⟩
      · obtain ⟨a1, a2, a3, a4, a5⟩ := hV.1 j' T c' L b hv
        refine ⟨a1, a2, ?_, a4, a5⟩
        rw [hsrv]; split
        · subst_vars; show T ≤ σ.term j'; omega
        · exact a3
      · cases hx
        refine ⟨hj, ?_, ?_, ⟨li, lt, hcand, hu⟩, fun hb => ?_⟩
        · have := (hV.2.2 c _ _ hcand).2.1; omega
        · rw [hsrv, if_pos' rfl]; exact Nat.le_refl _
        · intro hn
          have hn' : σ.leader (σ.term j') = none := hn
          rw [hn'] at hb; simp at hb
    · rw [hsrv, eterm]; split
      · subst_vars
        refine ⟨Nat.le_refl _, fun _ => ⟨σ.log j', decide (σ.leader (σ.term j') = none), ?_⟩⟩
        exact (hvotes _ _ _).mpr (Or.inr ⟨rfl, rfl, rfl⟩)
      · obtain ⟨a1, a2⟩ := hV.2.1 j' hj'
        refine ⟨a1, fun hp => ?_⟩
        obtain ⟨L, b, hv⟩ := a2 hp
        exact ⟨L, b, hext _ _ _ hv⟩
    · obtain ⟨a1, a2, a3, a4⟩ := hV.2.2 c' T x hx
      exact ⟨a1, a2, by rw [eterm]; exact a3, a4⟩
  have hVA' : IVoteAck (grantVote σ j c) := by
    intro j' T' c' L b T m k hv ha hkm hTT'
    rcases (hvotes j' T' _).mp hv with hv | ⟨rfl, rfl, hx⟩
    · exact hVA j' T' c' L b T m k hv ha hkm hTT'
    · cases hx
      obtain ⟨_, _, _, _, hk⟩ := hA j' T m ha
      rcases hk k hkm with hag | ⟨T'', a1, a2, a3, a4⟩
      · exact Or.inl hag
      · refine Or.inr ⟨T'', a1, ?_, a3, a4⟩
        rcases Nat.lt_or_eq_of_le a2 with a2 | a2
        · exact Or.inl a2
        · subst a2; exact Or.inr ⟨rfl, by simp [a3]⟩
  refine ⟨⟨hG, hL', hLo', fun j' hj' hl => ?_, hV',
    IAcks_grow hg hL (fun j' _ => by rw [elog]; exact List.prefix_refl _)
      (fun j' _ => by rw [eterm]; exact Nat.le_refl _) (fun _ _ _ x => x) hA,
    hVA', ILC_of (σ := grantVote σ j c) hG hL' hLo' hV' hVA' hR
      (fun T k p h => ⟨(hCo.1 T k p h).1, (hCo.1 T k p h).2.1⟩), hCo,
    IDur_grow hg (fun j' _ => by rw [elog]; exact List.prefix_refl _)
      (fun j' _ => by rw [eterm]; exact Nat.le_refl _) (fun j' _ => hdur j') (fun _ _ _ x => x) hD,
    ⟨fun j' hj' => by rw [elog, eterm]; exact b1 j' hj', b2, b3, b4, b5⟩,
    fun j' hj' => by rw [elog, eterm]; exact hX j' hj',
    IPub_grow hg (fun j' _ => by rw [eterm]; exact Nat.le_refl _) (fun j' _ => by rw [(hdur j').1])
      (fun _ _ _ x => x) rfl hP, hR⟩, ?_⟩
  · rw [eterm] at hl ⊢; rw [elog]; exact hC j' hj' hl
  · refine ⟨rfl, ⟨rfl, rfl⟩, fun _ _ x => x, fun T => ⟨List.prefix_refl _, fun _ => rfl⟩,
      fun _ _ _ x => x, hext, fun _ _ _ x => x, fun _ _ _ x => x, List.prefix_refl _,
      fun j' => by rw [eterm]; exact Nat.le_refl _,
      fun j' => by rw [(hdur j').1]; exact Nat.le_refl _, Nat.le_refl _, Nat.le_refl _,
      fun _ _ x => x, fun j' T c' L hv => ?_⟩
    rcases (hvotes j' T _).mp hv with hv | ⟨rfl, rfl, hx⟩
    · exact Or.inl hv
    · right
      simp only [Prod.mk.injEq] at hx
      obtain ⟨_, _, hb⟩ := hx
      exact of_decide_eq_true hb.symm

/-! ### commit -/

theorem commit_inv' (σ : PState) (T k : Nat) (h : PInv σ) (hp : commitPre σ T k) :
    PInv (commit σ T k) ∧ Grows σ (commit σ T k) := by
  obtain ⟨hG, hL, hLo, hC, hV, hA, hVA, hLC, hCo, hD, hB, hX, hP, hR⟩ := h
  have hk1 := hp.2.1
  have hkl := hp.2.2.1
  have hpa : cfgAdm σ T k (σ.ccfg T) := by
    obtain ⟨ℓ, hℓ⟩ := Option.ne_none_iff_exists'.mp hp.1
    exact ⟨_, hkl, Nat.le_refl _, (hL.1 T ℓ hℓ).2.2.2.2.2.2.2.2.2⟩
  have hCeq : (commit σ T k).C = if σ.C.length < k then (σ.llog T).take k else σ.C := rfl
  -- `C` is a prefix of the new committed log
  have hpre : σ.C <+: (commit σ T k).C := by
    rw [hCeq]; split
    · rcases hCo.2 with h0 | ⟨T0, p0, h0⟩
      · rw [h0]; exact List.nil_prefix
      · obtain ⟨hc0, ha0, hag0⟩ := hCo.1 _ _ _ h0
        have := committed_agree (n := k) (k := σ.C.length) hLC hp hpa hc0 ha0 (by omega)
        apply prefix_take_of_agree
        exact agree_symm (agree_take_left (n := k) (agree_trans this (agree_symm hag0)) (by omega))
    · exact List.prefix_refl _
  have hCo' : ICommits (commit σ T k) := by
    refine ⟨fun T1 k1 p1 hc => ?_, ?_⟩
    · have hc' : σ.commits T1 k1 p1 ∨ (T1 = T ∧ k1 = k ∧ p1 = σ.ccfg T) := hc
      rw [hCeq]
      rcases hc' with hc' | ⟨e1, e2, e3⟩
      · obtain ⟨hc1, ha1, hag1⟩ := hCo.1 _ _ _ hc'
        refine ⟨hc1, ha1, ?_⟩
        by_cases hlt : σ.C.length < k
        · rw [if_pos' hlt]
          have := hag1.1
          exact agree_take_left (n := k)
            (committed_agree (n := k) (k := k1) hLC hp hpa hc1 ha1 (by omega)) (by omega)
        · rw [if_neg' hlt]; exact hag1
      · rw [e1, e2, e3]
        refine ⟨hp, hpa, ?_⟩
        by_cases hlt : σ.C.length < k
        · rw [if_pos' hlt]; exact agree_take_self _ (Nat.le_refl _) hkl
        · rw [if_neg' hlt]
          rcases hCo.2 with h0 | ⟨T0, p0, h0⟩
          · have : σ.C.length = 0 := by rw [h0]; rfl
            omega
          · obtain ⟨hc0, ha0, hag0⟩ := hCo.1 _ _ _ h0
            exact agree_trans (agree_mono hag0 (by omega))
              (committed_agree (n := σ.C.length) (k := k) hLC hc0 ha0 hp hpa (by omega))
    · rw [hCeq]
      by_cases hlt : σ.C.length < k
      · rw [if_pos' hlt]
        right; refine ⟨T, σ.ccfg T, Or.inr ⟨rfl, ?_, rfl⟩⟩; simp; omega
      · rw [if_neg' hlt]
        rcases hCo.2 with h0 | ⟨T0, p0, h0⟩
        · exact Or.inl h0
        · exact Or.inr ⟨T0, p0, Or.inl h0⟩
  have hg : HG σ (commit σ T k) := HG.refl_llog rfl rfl rfl rfl rfl
  obtain ⟨l1, l2, l3, l4, l5⟩ := hLo
  have hl4 : LMok (commit σ T k) (commit σ T k).C := by
    rw [hCeq]; split
    · exact LMok_take (l2 T) _
    · exact l4
  refine ⟨⟨hG, hL, ⟨l1, l2, l3, hl4, l5⟩, hC, hV, hA, hVA, hLC, hCo',
    IDur_grow hg (fun _ _ => List.prefix_refl _) (fun _ _ => Nat.le_refl _) (fun _ _ => ⟨rfl, rfl⟩)
      (fun _ _ _ x => Or.inl x) hD, hB, hX,
    IPub_grow hg (fun _ _ => Nat.le_refl _) (fun _ _ => rfl) (fun _ _ _ x => Or.inl x) rfl hP,
    ICfgR_frame (σ := σ) (σ' := commit σ T k) rfl rfl rfl rfl (fun _ _ _ x => Or.inl x) hR⟩, ?_⟩
  exact ⟨rfl, ⟨rfl, rfl⟩, fun _ _ x => x, fun T => ⟨List.prefix_refl _, fun _ => rfl⟩,
    fun _ _ _ x => x, fun _ _ _ x => x, fun _ _ _ x => x, fun _ _ _ x => Or.inl x, hpre,
    fun _ => Nat.le_refl _, fun _ => Nat.le_refl _, Nat.le_refl _, Nat.le_refl _,
      fun _ _ x => x, fun _ _ _ _ x => Or.inl x⟩

/-! ### publish -/

theorem publish_inv' (σ : PState) (i : SID) (k : Nat) (h : PInv σ) (hp : publishPre σ i k) :
    PInv (publish σ (σ.term i) k) ∧ Grows σ (publish σ (σ.term i) k) := by
  obtain ⟨hG, hL, hLo, hC, hV, hA, hVA, hLC, hCo, hD, hB, hX, hP, hR⟩ := h
  obtain ⟨hi, hld, k', p, hk, hc⟩ := hp
  refine ⟨⟨hG, hL, hLo, hC, hV, hA, hVA, hLC, hCo, hD, hB, hX, ⟨fun T m hm => ?_, fun j hj => ?_⟩, hR⟩, ?_⟩
  · rcases hm with hm | ⟨rfl, rfl⟩
    · exact hP.1 T m hm
    · exact ⟨by show σ.leader (σ.term i) ≠ none; rw [hld]; simp, k', p, hk, hc⟩
  · rcases hP.2 j hj with h0 | ⟨T, m, a, b, c⟩
    · exact Or.inl h0
    · exact Or.inr ⟨T, m, a, b, Or.inl c⟩
  · exact ⟨rfl, ⟨rfl, rfl⟩, fun _ _ x => x, fun T => ⟨List.prefix_refl _, fun _ => rfl⟩,
      fun _ _ _ x => x, fun _ _ _ x => x, fun _ _ _ x => x, fun _ _ _ x => x, List.prefix_refl _,
      fun _ => Nat.le_refl _, fun _ => Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, fun _ _ x => Or.inl x,
      fun _ _ _ _ x => Or.inl x⟩

/-! ### The initial state -/

theorem init_inv' (srvs : List SID) (g : Entry) (cv : List w8 → List SID) (hnd : srvs.Nodup)
    (hg1 : g.term = 1) (hgk : g.kind = kConfig) (hcv : cfgValid srvs (cv g.data)) :
    PInv (init srvs g cv) := by
  have hll : ∀ t, (init srvs g cv).llog t = if t = 1 then [g] else [] := fun _ => rfl
  have hg : LMok (init srvs g cv) [g] := by
    intro k h1 h2
    simp at h2
    have : k = 1 := by omega
    subst this
    have : termAt [g] 1 = 1 := by simp [termAt, ent, hg1]
    rw [this, hll, if_pos' rfl]
    exact agree_refl _ _ (by simp)
  have hnil : LMok (init srvs g cv) [] := by
    intro k h1 h2; simp at h2; omega
  have hllok : ∀ t, LMok (init srvs g cv) ((init srvs g cv).llog t) := by
    intro t; rw [hll]; split
    · exact hg
    · exact hnil
  have hS : ∀ i, ((init srvs g cv).log i = [g] ∧ (init srvs g cv).term i = 1) ∨
      ((init srvs g cv).log i = [] ∧ (init srvs g cv).term i = 0) := by
    intro i
    show ((initSrv cv g i).log = [g] ∧ (initSrv cv g i).term = 1) ∨
      ((initSrv cv g i).log = [] ∧ (initSrv cv g i).term = 0)
    unfold initSrv; split
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩
  have hS2 : ∀ i, ((init srvs g cv).srv i).vterm = 0 ∧ ((init srvs g cv).srv i).dur = (0, 0) ∧
      ((init srvs g cv).srv i).cidx = 0 := by
    intro i
    show (initSrv cv g i).vterm = 0 ∧ (initSrv cv g i).dur = (0, 0) ∧ (initSrv cv g i).cidx = 0
    unfold initSrv; split <;> exact ⟨rfl, rfl, rfl⟩
  have hG : IGen (init srvs g cv) := ⟨hg1, hgk, hnd, hcv, rfl, rfl, rfl, rfl, rfl⟩
  have hL : ILeaders (init srvs g cv) := by
    refine ⟨fun T ℓ hl => (by cases hl), fun T hT _ => ?_⟩
    rw [hll, if_neg' hT]
  have hLo : ILogs (init srvs g cv) := by
    refine ⟨fun i _ => ?_, hllok, fun j T c L b hv => (by cases hv), hnil, ?_⟩
    · rcases hS i with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rw [h1]
      · exact ⟨hg, Or.inr (by simp [ent]; rfl)⟩
      · exact ⟨hnil, Or.inl rfl⟩
    · intro T k e he hk
      rw [hll] at he; split at he
      · have := ent_le_length he
        simp at this
        have : k = 1 := by omega
        subst this
        simp [ent] at he; subst he; exact hcv
      · simp [ent] at he
  have hV : IVotes (init srvs g cv) := by
    refine ⟨fun j T c L b hv => (by cases hv), fun j _ => ⟨?_, ?_⟩, fun c T x hx => (by cases hx)⟩
    · rw [(hS2 j).1]; exact Nat.zero_le _
    · intro h; rw [(hS2 j).1] at h; exact absurd h (Nat.lt_irrefl 0)
  have hVA : IVoteAck (init srvs g cv) := fun j T' c L b T m k hv => by cases hv
  have hR : ICfgR (init srvs g cv) := fun T p e h1 => absurd rfl h1
  refine ⟨hG, hL, hLo, fun i _ hl => (by cases hl), hV, fun j T m ha => False.elim ha, hVA,
    ILC_of (σ := init srvs g cv) hG hL hLo hV hVA hR (fun T k p hc => False.elim hc),
    ⟨fun T k p hc => False.elim hc, Or.inl rfl⟩,
    fun i _ => ⟨Or.inl (by rw [(hS2 i).2.1]), by rw [(hS2 i).2.2]; exact Nat.zero_le _⟩,
    ⟨fun i _ => ?_, fun T => ?_, fun T _ => rfl, Nat.le_refl _, Nat.le_refl _⟩, fun i _ => ?_,
    ⟨fun T k h => False.elim h, fun i _ => Or.inl (by rw [(hS2 i).2.1])⟩, hR⟩
  · rcases hS i with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> exact ⟨by simp [init], by simp [init]⟩
  · rw [hll]; split <;> simp [init]
  · rcases hS i with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
    · refine ⟨fun _ => Nat.le_refl _, fun k h1 h2 => ?_⟩
      simp at h2
      have : k = 1 := by omega
      subst this
      simp [termAt, ent, hg1]
    · refine ⟨fun h => absurd rfl h, fun k h1 h2 => ?_⟩
      simp at h2; omega

end proto
end github_com.hashicorp.raft
end Perennial
