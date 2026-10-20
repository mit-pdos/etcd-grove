/-
Port of election_proof/protocol.v, lines 4018–4494 at feb5c73d4: Leader Completeness over
the vote table, the agreement of commit facts, firing the proposal registry, committing
(`commit_extend`). (On top of `Protocol/StepGhost.lean`; the refinement obligation is
`Protocol/Refinement.lean`.)

Lean notes:
* Proofs are skeletons: every lemma's proof that is not done is `sorry`, on the line
  after a `-- PORT: proof` marker.
* No lemma here starts with a definition's name, so all keep their Rocq names
  (`lc_core`, `cq_agree`, `fire_one`, `commit_extend`, ...). Rocq `Local Lemma`s are
  public theorems.
* `lc_core`'s `uint.Z T < k` with `k : nat` is `uint.Z T < (k : Int)`; `S m` is `m + 1`.
-/
module

public import Proof.go_etcd_io.raft.v3.Protocol.StepGhost

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI GMap go_etcd_io.raft.v3

section ghost
variable [FfiSyntax]
variable {GF : BundledGFunctors} [AllG GF] [ReceiptGS GF] [InvGS GF]

/-! ### Leader Completeness, over the vote table (2026-10-05)

The pivot argument of Leader Completeness (`lc_core`) needs, of the voter in both the
commit quorum and the election quorum, its vote record and the history of its
acknowledgement at the time it voted. Since 2026-10-05 both are reachable without that
voter's ghost state: the vote record from the vote table in `raftCommitInv`
(`votesTbl_just`), the history from the two event-history facts (`ev_pair`). So
`lc_core` and the agreement of two commit facts (`cq_agree`) need only the table --
which `Step.commit` has, inside the invariant, and which is what lets the global
committed log be extended there. -/

omit [FfiSyntax] in
theorem quorums_intersect_cfg (cfg q1 q2 : GSet w64) :
    IsQuorum cfg q1 → IsQuorum cfg q2 → ∃ x, x ∈ q1 ∧ x ∈ q2 ∧ x ∈ cfg := by
  intro Hq1 Hq2
  have E1 : q1 ∩ cfg ∩ cfg = q1 ∩ cfg := by set_solver
  have E2 : q2 ∩ cfg ∩ cfg = q2 ∩ cfg := by set_solver
  obtain ⟨x, Hx1, Hx2⟩ := quorums_intersect cfg (q1 ∩ cfg) (q2 ∩ cfg)
    (by unfold IsQuorum at *; rw [E1]; exact Hq1) (by unfold IsQuorum at *; rw [E2]; exact Hq2)
  exact ⟨x, by set_solver, by set_solver, by set_solver⟩

/-- (2026-10-19, witness support) In the dynamic mode there is no witness. -/
theorem RaftNames.wit_dyn {γ : RaftNames} (h : γ.reDyn ≠ none) : γ.reWit = W64 0 := by
  rcases γ.reWit_ok with h' | ⟨-, h', -⟩
  · exact h'
  · exact absurd h' h

/-- Without a witness, a voter in both quorums is not the witness. -/
theorem meet_nowit {γ : RaftNames} {q V : GSet w64} (h : γ.reWit = W64 0) :
    (∃ v, v ∈ q ∧ v ∈ V) → ∃ v, v ∈ q ∧ v ∈ V ∧ ¬ (v = γ.reWit ∧ γ.reWit ≠ W64 0) :=
  fun ⟨v, h1, h2⟩ => ⟨v, h1, h2, fun hw => hw.2 h⟩

omit [FfiSyntax] in
/-- Two subsets of `S` with more members than `S` meet. -/
theorem gset_meet (S A B : GSet w64) (hA : A ⊆ S) (hB : B ⊆ S)
    (h : size S < size A + size B) : ∃ x, x ∈ A ∧ x ∈ B := by
  by_cases hex : ∃ x, x ∈ A ∧ x ∈ B
  · exact hex
  exfalso
  have hne' : ∀ x, x ∈ A → x ∉ B := fun x ha hb => hex ⟨x, ha, hb⟩
  have hBA : B \ A = B := GMap.set_eq (fun k => by
    rw [GMap.elem_of_difference]
    exact ⟨fun h => h.1, fun hk => ⟨hk, fun ha => hne' k ha hk⟩⟩)
  have hU : A ∪ B ⊆ S := by
    rw [GMap.elem_of_subseteq] at hA hB ⊢
    intro x hx
    rcases (GMap.elem_of_union _ _ _).1 hx with h | h
    · exact hA x h
    · exact hB x h
  have := GMap.subseteq_size hU
  rw [GMap.size_union_alt, hBA] at this
  omega

omit [FfiSyntax] in
/-- A set without two of its members has two members fewer. -/
theorem gset_size_minus2 (S : GSet w64) (w x : w64) (hw : w ∈ S) (hx : x ∈ S) (hne : x ≠ w) :
    size (S \ ({[w]} ∪ {[x]})) + 2 = size S := by
  have hsub : ({[w]} ∪ {[x]} : GSet w64) ⊆ S := by
    rw [GMap.elem_of_subseteq]
    intro y hy
    rcases (GMap.elem_of_union _ _ _).1 hy with h | h
    · rw [GMap.elem_of_singleton] at h; rw [h]; exact hw
    · rw [GMap.elem_of_singleton] at h; rw [h]; exact hx
  have h2 : size ({[w]} ∪ {[x]} : GSet w64) = 2 := by
    rw [GMap.size_union_alt, GMap.size_singleton]
    have : ({[x]} \ {[w]} : GSet w64) = {[x]} := GMap.set_eq (fun k => by
      rw [GMap.elem_of_difference, GMap.elem_of_singleton, GMap.elem_of_singleton]
      exact ⟨fun h => h.1, fun h => ⟨h, by rw [h]; exact hne⟩⟩)
    rw [this, GMap.size_singleton]
  have := GMap.size_difference hsub
  have := GMap.subseteq_size hsub
  omega

omit [FfiSyntax] in
/-- (2026-10-20, witness support in the dynamic mode, W5) The counting lemma behind the
witness case of Leader Completeness across a configuration change (`notes/raft-witness-reconfig.md`,
(Count)): the witness's write and the candidate's votes meet in a regular voter even when the
candidate's configuration differs from the entry's by one member.

`S` is the replication set without the witness and the excluded voter (`|S| + 2 = n`, the entry's
configuration's incoming size); `H` the regular members of it that acknowledged the entry
(`n/2 ≤ |H|`, the witness's write needs `quorum - 1` of `S`); `G` the candidate's incoming votes,
all in `S` (the witness checks `G ⊆ S`), with `m/2 ≤ |G|` where `m` is the candidate's incoming
size (`quorum - 1` by the readiness check). The two configurations are adjacent (`n ≤ m + 1`), so
`n/2 + m/2 = n - 1 > n - 2 = |S|` and `H`, `G` meet. -/
theorem wit_count_meet (S H G : GSet w64) (n m : Nat) (hS : size S + 2 = n)
    (hH : H ⊆ S) (hG : G ⊆ S) (hHn : n / 2 ≤ size H) (hGm : m / 2 ≤ size G)
    (hadj : n ≤ m + 1) : ∃ x, x ∈ H ∧ x ∈ G :=
  gset_meet S H G hH hG (by omega)

/-- A campaign log ends at its last entry. -/
theorem camp_last (T : w64) (F0 : List EntryM) :
    CampOk T F0 →
    plogTermAt base0 F0 (W64 (plogLastIndexZ base0 F0))
    = some (plogLast base0 F0).term' := by
  intro ⟨Hwf, _⟩
  have Hi := plogLast_index _ _ Hwf
  have Hr := PlogWf_range _ _ Hwf
  have H : W64 (plogLastIndexZ base0 F0) = (plogLast base0 F0).index' := by
    apply uint_Z_inj.mp
    rw [uint_Z_W64 _ (plogLastIndexZ_nonneg _ _) Hr, Hi]
  rw [H]; exact plogTermAt_last _ _ Hwf

/-- What the vote table says of a vote and an earlier acknowledgement of the same voter:
its log when it voted, at least as up to date as the candidate's campaign log, and the
acknowledgement's history then (`ev_pair`). Since 2026-10-05; before, the voter's own
ghost state (`own_raft_ghost_voter`, `cluster_voter`). -/
theorem tbl_voter (γ : RaftNames) (v T c t i : w64) :
    uint.Z t < uint.Z T → 0 < uint.Z i → ¬ (v = γ.reWit ∧ γ.reWit ≠ W64 0) →
    ⊢ votesTbl (GF := GF) γ -∗ isVote γ v T c -∗ isAcked γ v t i -∗
      ∃ d Fv Fc, isCamp γ c T Fc ∗ logRecs γ base0 Fv ∗
        ⌜PlogWf base0 Fv ∧ plogUpToDate base0 Fv (plogLast base0 Fc) = true⌝ ∗
        hist γ Fv t i (vbnd T d) ∗
        (if d then iprop(∃ ldr q, isWin γ ldr T q ∗ ⌜v ∉ q⌝) else iprop(True)) := by
  intro Ht Hi Hnw
  iintro Htbl #Hvote Hack
  unfold isAcked ackReg
  icases Hack with (%H0 | ⟨-, #Hev⟩ | ⟨%Hw, -⟩)
  · exact False.elim (by omega)
  rotate_left
  · exact absurd Hw Hnw
  ihave Hj := votesTbl_just γ v T c $$ Htbl Hvote
  unfold voteJust
  icases Hj with (⟨%k, %d, %Fv, %Fc, -, #Hcamp, #HrFv, %Hpure, #Hd, #Hvev, -⟩ | ⟨%Hw, -⟩)
  rotate_left
  · exact absurd Hw Hnw
  iexists d, Fv, Fc
  iframe Hcamp HrFv Hd
  isplitr
  · ipureintro; exact Hpure
  iapply ev_pair γ v t i T d Fv Ht $$ Hev Hvev

/-- The induction hypothesis of `lc_core`, below the term `T`. -/
def LcIH (γ : RaftNames) (T : w64) : Prop :=
  ∀ (T' t' n' : w64) (F' : List EntryM) (c' : w64) (F0' G' : List EntryM),
    uint.Z T' < uint.Z T → uint.Z t' < uint.Z T' →
    PlogWf base0 G' →
    plogTermAt base0 G' (W64 (plogLastIndexZ base0 F0'))
      = some (plogLast base0 F0').term' →
    ⊢ votesTbl (GF := GF) γ -∗ cq γ t' n' F' -∗ isLeader γ c' T' -∗ isCamp γ c' T' F0' -∗
      logRecs γ base0 G' -∗ ⌜plogTermAt base0 G' n' = some t'⌝

/-- (2026-10-19, witness support) A log with records with an entry of the commit fact's term
at or past its index has that term at the index: the entry is the leader's, which had the commit
fact's entry below it. -/
theorem lc_same_term (γ : RaftNames) (t n j : w64) (F G : List EntryM) :
    PlogWf base0 G → plogTermAt base0 G j = some t → 0 < uint.Z j → uint.Z n ≤ uint.Z j →
    ⊢ cq (GF := GF) γ t n F -∗ logRecs γ base0 G -∗ ⌜plogTermAt base0 G n = some t⌝ := by
  intro HwG HGj Hj0 Hnj
  iintro #Hcq #HrG
  icases cq_full γ t n F $$ Hcq with ⟨%HwF, #HrF⟩
  icases cq_base γ _ _ _ $$ Hcq with ⟨%HFn, #HFl⟩
  icases leadFull_camp γ t F $$ HFl with ⟨%ldr, %F0c, #Hl, #Hc, %Hpre⟩
  icases isCamp_ok γ ldr t F0c $$ Hc with %Hcok
  icases recs_chain γ G ldr t F0c HwG $$ Hl Hc HrG with %Hch
  obtain ⟨Hlt, -, Hall⟩ := Hch j Hj0 HGj
  -- the commit fact's index is past the campaign log, whose terms are below `t`
  have HnF0 : plogLastIndexZ base0 F0c < uint.Z n := by
    by_cases Hlt' : plogLastIndexZ base0 F0c < uint.Z n
    · exact Hlt'
    exfalso
    have Hle' : uint.Z n ≤ plogLastIndexZ base0 F0c := by omega
    have Hs : (plogTermAt base0 F0c n).isSome := by
      unfold plogTermAt; rw [base0_index]
      by_cases Hn0 : uint.Z n = 0
      · simp [Hn0]
      · have := uint_Z_nonneg n
        unfold plogLastIndexZ at Hle'; rw [base0_index] at Hle'
        simp only [Hn0, ↓reduceIte, show ¬ uint.Z n < 0 by omega]
        rw [List.getElem?_eq_getElem (by omega)]; rfl
    obtain ⟨x, Hx⟩ := Option.isSome_iff_exists.mp Hs
    have HxF := plogTermAt_prefix base0 F0c F n Hpre (by rw [Hx]; rfl)
    rw [Hx, HFn] at HxF
    cases HxF
    have := Hcok.2 n t Hx
    omega
  ipureintro
  exact Hall n ⟨HnF0, Hnj⟩

/-- (2026-10-19, witness support) The newer-term case of `lc_adj_gen` (its branch "a later last
term"): a log with records with an entry of a term `tc` in `(t, T)` has the commit fact's term at
its index, by the induction hypothesis at `tc`. -/
theorem lc_newer (γ : RaftNames) (T t n j tc : w64) (F G : List EntryM) (IH : LcIH (GF := GF) γ T) :
    uint.Z t < uint.Z tc → uint.Z tc < uint.Z T →
    PlogWf base0 G → plogTermAt base0 G j = some tc → 0 < uint.Z j →
    ⊢ votesTbl (GF := GF) γ -∗ cq γ t n F -∗ logRecs γ base0 G -∗
      ⌜plogTermAt base0 G n = some t⌝ := by
  intro Htc HtcT HwG HGj Hj0
  iintro HS #Hcq #HrG
  have HGjr := (plogTermAt_some_range _ _ _ _ HGj).2
  have HGlen : plogLastIndexZ base0 G = G.length := by
    unfold plogLastIndexZ; rw [base0_index]; omega
  have Hrng := uint_Z_lt j
  obtain ⟨x, Hx⟩ : ∃ x, G[(uint.Z j - 1).toNat]? = some x :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  icases logRecs_lookup γ G _ x Hx (by omega) $$ HrG with ⟨%pt, -, #Hxr⟩
  have Hjw : W64 ((((uint.Z j - 1).toNat : Nat) : Int) + 1) = j := by
    apply uint_Z_inj.mp; rw [uint_Z_W64 _ (by omega) (by omega)]; omega
  have Hxt : x.Term' = tc := by
    rw [plogTermAt_lookup base0 G _ _ x Hx (by rw [base0_index]; omega)] at HGj
    exact Option.some.inj HGj
  unfold isEntryR
  icases Hxr with (⟨%ldr, %γt, %b, %l0, %F0c, #Hlc, -, #Hcc, -, -⟩ | ⟨%Hb, -⟩)
  · rw [Hxt]
    icases recs_chain γ G ldr _ F0c HwG $$ Hlc Hcc HrG with %Hch
    obtain ⟨-, HGlc, -⟩ := Hch _ Hj0 HGj
    iapply IH _ t n F ldr F0c G HtcT Htc HwG HGlc $$ HS Hcq Hlc Hcc HrG
  · -- a boot entry, of term `1`: below every commit fact's term
    icases cq_boot γ t n F $$ Hcq with %Hbf
    have H2 := Hbf.2 (BootRec_ne _ _ _ Hb)
    have Hx1 : uint.Z tc = 1 := by rw [← Hxt, Hb.2.2.1]; rfl
    ipureintro; exfalso; omega

/-- A full log extends the campaign log of its leader, so it reaches that log's last
entry. -/
theorem prefix_camp_last (T : w64) (F0 X : List EntryM) :
    CampOk T F0 → F0 <+: X →
    plogTermAt base0 X (W64 (plogLastIndexZ base0 F0)) = some (plogLast base0 F0).term' := by
  intro Hcok Hpre
  have Hcl := camp_last T F0 Hcok
  rw [plogTermAt_prefix _ F0 X _ Hpre (by rw [Hcl]; rfl), Hcl]

/-- In `lc_core` (Rocq: the `iAssert` `"Hagree"`): logs a history may mention agree with
`F` at and below `n`, by the induction hypothesis. -/
private theorem lc_agree (γ : RaftNames) (T t n : w64) (F : List EntryM)
    (IH : LcIH (GF := GF) γ T) (j : w64) (X : List EntryM) :
    uint.Z t < uint.Z T → uint.Z j ≤ uint.Z n → (plogTermAt base0 X j).isSome →
    ⊢ votesTbl (GF := GF) γ -∗ cq γ t n F -∗ okL γ t (uint.Z T) j X -∗
      ⌜plogTermAt base0 X j = plogTermAt base0 F j⌝ := by
  intro HtT Hj HsX
  iintro HS #Hcq HX
  icases cq_full γ t n F $$ Hcq with ⟨%HwF, #HrF⟩
  icases cq_base γ _ _ _ $$ Hcq with ⟨%HFn, #HFl⟩
  unfold okL
  icases HX with (⟨%t'', %Ht12, #HX⟩ | ⟨%t'', %n'', %Htj, #Hq''⟩ | %Hb)
  · obtain ⟨Ht1, Ht2⟩ := Ht12
    icases leadFull_wf γ t'' X $$ HX with ⟨%HwX', #HrX⟩
    have HwX := HwX'.1
    have HsF : (plogTermAt base0 F j).isSome := full_term_at_some F j n (by rw [HFn]; rfl) Hj
    by_cases Hne : t'' = t
    · subst Hne
      iapply leadFull_agree γ t'' X F j HsX HsF $$ HX HFl
    · -- a later term: `X` extends its leader's campaign log
      icases leadFull_camp γ t'' X $$ HX with ⟨%ldr, %F0'', #Hl'', #Hc'', %Hpre⟩
      icases isCamp_ok γ ldr t'' F0'' $$ Hc'' with %Hcok
      have Htt : uint.Z t < uint.Z t'' := by
        have : uint.Z t ≠ uint.Z t'' := fun h => Hne (uint_Z_inj.mp h).symm
        omega
      icases IH t'' t n F ldr F0'' X Ht2 Htt HwX (prefix_camp_last t'' F0'' X Hcok Hpre)
        $$ HS Hcq Hl'' Hc'' HrX with %HXn
      icases full_match γ X F n HwX HwF (by rw [HXn]; rfl) (by rw [HXn, HFn]) $$ HrX HrF
        with %Hm
      ipureintro; exact Hm j Hj
  · -- a committed log of an earlier term: `F`'s leader has it (`IH` at `t`)
    obtain ⟨Ht'', Hjn⟩ := Htj
    icases cq_full γ t'' n'' X $$ Hq'' with ⟨%HwX, #HrX⟩
    icases cq_base γ _ _ _ $$ Hq'' with ⟨%HXn'', -⟩
    icases leadFull_camp γ t F $$ HFl with ⟨%ldr, %F0t, #Hlt, #Hct, %Hpre⟩
    icases isCamp_ok γ ldr t F0t $$ Hct with %Hcok
    icases IH t t'' n'' X ldr F0t F HtT Ht'' HwF (prefix_camp_last t F0t F Hcok Hpre)
      $$ HS Hq'' Hlt Hct HrF with %HFn''
    icases full_match γ X F n'' HwX HwF (by rw [HXn'']; rfl) (by rw [HXn'', HFn''])
      $$ HrX HrF with %Hm
    ipureintro; exact Hm j Hjn
  · -- (2026-10-16, stage R8b) the bootstrap log, which `F` starts with
    obtain ⟨-, HX⟩ := Hb
    subst HX
    icases cq_boot γ t n F $$ Hcq with %Hbf
    ipureintro
    exact (plogTermAt_prefix base0 γ.reBoot F j Hbf.1 HsX).symm

/-- `lc_agree` at the bound `T + 1`, given that the logs of `T`'s leader agree with `F` below
`n` (2026-10-14, stage B5: the `d` branch of a vote cast for a winner not yet in the table, the
paper's repair 2). -/
private theorem lc_agree_T1 (γ : RaftNames) (T t n : w64) (F : List EntryM)
    (IH : LcIH (GF := GF) γ T) (j : w64) (X : List EntryM) :
    uint.Z t < uint.Z T → uint.Z j ≤ uint.Z n → (plogTermAt base0 X j).isSome →
    ⊢ votesTbl (GF := GF) γ -∗ cq γ t n F -∗ (□ ∀ (X' : List EntryM) (j' : w64), votesTbl γ -∗ leadFull γ T X' -∗
        ⌜uint.Z j' ≤ uint.Z n ∧ (plogTermAt base0 X' j').isSome⌝ -∗
        ⌜plogTermAt base0 X' j' = plogTermAt base0 F j'⌝) -∗
      okL γ t (uint.Z T + 1) j X -∗ ⌜plogTermAt base0 X j = plogTermAt base0 F j⌝ := by
  intro HtT Hj HsX
  iintro HS #Hcq #HLT HX
  unfold okL
  icases HX with (⟨%t'', %Ht12, #HX⟩ | #HX)
  · by_cases HtTe : uint.Z t'' = uint.Z T
    · have : t'' = T := uint_Z_inj.mp HtTe
      subst this
      iapply HLT $$ %X %j HS HX %(And.intro Hj HsX)
    · iapply lc_agree γ T t n F IH j X HtT Hj HsX $$ HS Hcq
      unfold okL
      ileft; iexists t''; iframe HX; ipureintro; omega
  · iapply lc_agree γ T t n F IH j X HtT Hj HsX $$ HS Hcq
    unfold okL
    iright; iexact HX

/-- The adjacent case of Leader Completeness (`lc_adj`, the paper's section 7; 2026-10-14,
reconfiguration stage B4, split out of `lc_core`): given the induction hypothesis below `T` and
a voter `v` in both the commit quorum `q` of `t < T` and the winning quorum `V` of `T`, every
full log `G` with records that reaches the last entry of the campaign log of `T`'s leader has
term `t` at `n`.

`v`'s log `Fv` when it voted had `t` at `n` (its history of the acknowledgement, every log it
mentions agreeing with `F` below `n` by the induction hypothesis), and the campaign log of `T`
was at least as up to date. Same last term: `G` has that term down to `Fv`'s last index
(`recs_chain`), so it matches `Fv` there and below. A later last term `tc`: `G` has `tc`'s
campaign log's last entry (`recs_chain`), and the induction hypothesis at `tc` applies to `G`
itself. The vote counted in the election (the `d` branch: a vote cast knowing the leader of `T`
is not in its winning quorum) by election safety, the winners table's agreement. -/
theorem lc_adj_gen (γ : RaftNames) (T t n : w64) (F : List EntryM) (c : w64)
    (F0 G : List EntryM) (q V : GSet w64) (IH : LcIH (GF := GF) γ T) :
    uint.Z t < uint.Z T →
    PlogWf base0 G →
    plogTermAt base0 G (W64 (plogLastIndexZ base0 F0))
      = some (plogLast base0 F0).term' →
    (∃ v, v ∈ q ∧ v ∈ V ∧ ¬ (v = γ.reWit ∧ γ.reWit ≠ W64 0)) →
    ⊢ votesTbl (GF := GF) γ -∗ cq γ t n F -∗
      ([∗map] v ↦ _u ∈ toMap q, ∃ i', ⌜uint.Z n ≤ uint.Z i'⌝ ∗ isAcked γ v t i') -∗
      ([∗map] v ↦ _u ∈ toMap V, isVote γ v T c) -∗
      (□ ∀ (ldr : w64) (qd : GSet w64), isWin γ ldr T qd -∗ ⌜∃ v, v ∈ V ∧ v ∉ qd⌝ -∗
        (□ ∀ (X' : List EntryM) (j' : w64), votesTbl γ -∗ leadFull γ T X' -∗
        ⌜uint.Z j' ≤ uint.Z n ∧ (plogTermAt base0 X' j').isSome⌝ -∗
        ⌜plogTermAt base0 X' j' = plogTermAt base0 F j'⌝)) -∗
      isCamp γ c T F0 -∗
      logRecs γ base0 G -∗ ⌜plogTermAt base0 G n = some t⌝ := by
  intro HtT HwG HGl Hmeet
  iintro HS #Hcq #Hacks #Hvotes #HdB #Hc #HrG
  icases cq_full γ t n F $$ Hcq with ⟨%HwF, #HrF⟩
  icases cq_base γ _ _ _ $$ Hcq with ⟨%HFn, #HFl⟩
  -- index 0
  by_cases Hn0 : uint.Z n = 0
  · have key : ∀ L : List EntryM, plogTermAt base0 L n = some base0.term' := by
      intro L; unfold plogTermAt; rw [base0_index]; simp [Hn0]
    rw [key] at HFn
    ipureintro; rw [key]; exact HFn
  -- the voter in both quorums
  obtain ⟨v, Hvq, HvV, Hvw⟩ := Hmeet
  ihave Hackv0 := BigSepM.bigSepM_lookup
    (Φ := fun v _ => iprop(∃ i', ⌜uint.Z n ≤ uint.Z i'⌝ ∗ isAcked (GF := GF) γ v t i'))
    ((GMap.elem_of_gset _ _).mp Hvq) $$ Hacks
  icases Hackv0 with ⟨%iv, %Hiv, #Hackv⟩
  ihave #Hvotev := BigSepM.bigSepM_lookup (Φ := fun v _ => isVote (GF := GF) γ v T c)
    ((GMap.elem_of_gset _ _).mp HvV) $$ Hvotes
  icases tbl_voter γ v T c t iv HtT (by have := uint_Z_nonneg n; omega) Hvw $$ HS Hvotev Hackv
    with ⟨%d, %Fv, %Fc, #Hcv, #HrFv, %HFv, #Hh0, #Hd⟩
  obtain ⟨HwFv, Hutd⟩ := HFv
  icases isCamp_agree γ c T F0 Fc $$ Hc Hcv with %HF0
  subst HF0
  icases isCamp_ok γ c T F0 $$ Hc with %Hcok
  -- `Fv` had `t` at `n`: its history of the acknowledgement mentions logs that agree with `F`
  -- below `n`. If `v`'s vote counted in `c`'s election, it was cast before `v` knew a leader
  -- of `T`: the history is bounded by `T`. Otherwise (the `d` branch) the leader `v` knew
  -- satisfies `HdB` (a winners-table member: it is `c`, which contradicts `v ∈ V`; for a winner
  -- not yet in the table, `win_fresh`'s case "new winner older", the existing winner's
  -- `lc_core`, the paper's repair 2), and the bound is `T + 1`.
  have Hnpos : 0 < uint.Z n := by have := uint_Z_nonneg n; omega
  ihave %HFvn : ⌜plogTermAt base0 Fv n = some t⌝ $$ [HS]
  · cases d with
    | false =>
      ihave #Hh : hist γ Fv t iv (uint.Z T) $$ []
      · iapply hist_mono γ Fv t iv (vbnd T false) (uint.Z T) (by simp [vbnd]) $$ Hh0
      ieval (unfold hist) at Hh
      ihave Hhn := Hh $$ %n %(And.intro Hnpos Hiv)
      icases Hhn with (⟨%X, #HX, %HsX⟩ | ⟨%j', %X1, %X2, %Hj', #H1, #H2, %Hd'⟩)
      · obtain ⟨HsX, HXn⟩ := HsX
        icases lc_agree γ T t n F IH n X HtT (Int.le_refl _) HsX $$ HS Hcq HX with %HX'
        ipureintro; rw [← HXn, HX', HFn]
      · obtain ⟨Hs1, Hs2, Hne⟩ := Hd'
        icases lc_agree γ T t n F IH j' X1 HtT (by omega) Hs1 $$ HS Hcq H1 with %HX1
        icases lc_agree γ T t n F IH j' X2 HtT (by omega) Hs2 $$ HS Hcq H2 with %HX2
        exact absurd (HX1.trans HX2.symm) Hne
    | true =>
      simp only [↓reduceIte]
      icases Hd with ⟨%ldr, %qd, #Hwd, %Hvq'⟩
      ihave #HLT := HdB $$ %ldr %qd Hwd %(⟨v, HvV, Hvq'⟩ : ∃ v, v ∈ V ∧ v ∉ qd)
      ihave #Hh : hist γ Fv t iv (uint.Z T + 1) $$ []
      · iapply hist_mono γ Fv t iv (vbnd T true) (uint.Z T + 1) (by simp [vbnd]) $$ Hh0
      ieval (unfold hist) at Hh
      ihave Hhn := Hh $$ %n %(And.intro Hnpos Hiv)
      icases Hhn with (⟨%X, #HX, %HsX⟩ | ⟨%j', %X1, %X2, %Hj', #H1, #H2, %Hd'⟩)
      · obtain ⟨HsX, HXn⟩ := HsX
        icases lc_agree_T1 γ T t n F IH n X HtT (Int.le_refl _) HsX $$ HS Hcq HLT HX with %HX'
        ipureintro; rw [← HXn, HX', HFn]
      · obtain ⟨Hs1, Hs2, Hne⟩ := Hd'
        icases lc_agree_T1 γ T t n F IH j' X1 HtT (by omega) Hs1 $$ HS Hcq HLT H1 with %HX1
        icases lc_agree_T1 γ T t n F IH j' X2 HtT (by omega) Hs2 $$ HS Hcq HLT H2 with %HX2
        exact absurd (HX1.trans HX2.symm) Hne
  icases recs_mono γ Fv HwFv $$ HrFv with %Hmono
  obtain ⟨HwF0, HltF0⟩ := Hcok
  have Hli : uint.Z (plogLast base0 Fv).index' = plogLastIndexZ base0 Fv :=
    plogLast_index _ _ HwFv
  have HFvli := plogTermAt_last _ _ HwFv
  have Hnli := (plogTermAt_some_range _ _ _ _ HFvn).2
  rw [← Hli] at Hnli
  have Htlt : uint.Z t ≤ uint.Z (plogLast base0 Fv).term' := Hmono n _ t _ Hnli HFvn HFvli
  have Hic : uint.Z (W64 (plogLastIndexZ base0 F0)) = plogLastIndexZ base0 F0 :=
    uint_Z_W64 _ (plogLastIndexZ_nonneg _ _) (PlogWf_range _ _ HwF0)
  have HtcT : uint.Z (plogLast base0 F0).term' < uint.Z T :=
    HltF0 _ _ (camp_last T F0 ⟨HwF0, HltF0⟩)
  have Hcli : (plogLast base0 F0).index' = W64 (plogLastIndexZ base0 F0) := by
    apply uint_Z_inj.mp; rw [Hic]; exact plogLast_index _ _ HwF0
  unfold plogUpToDate at Hutd
  simp only [decide_eq_true_eq] at Hutd
  have HGic := (plogTermAt_some_range _ _ _ _ HGl).2
  have HGlen : plogLastIndexZ base0 G = G.length := by
    unfold plogLastIndexZ; rw [base0_index]; omega
  have HFvlen : plogLastIndexZ base0 Fv = Fv.length := by
    unfold plogLastIndexZ; rw [base0_index]; omega
  rcases Hutd with Hgt | ⟨Heq, Hle⟩
  · -- a later last term `tc`: the induction hypothesis at `tc`, for `G`
    have Hic0 : 0 < uint.Z (W64 (plogLastIndexZ base0 F0)) := by
      by_cases H0 : uint.Z (W64 (plogLastIndexZ base0 F0)) = 0
      · exfalso
        have Hc0 := camp_last T F0 ⟨HwF0, HltF0⟩
        unfold plogTermAt at Hc0
        rw [base0_index] at Hc0
        simp only [H0, Int.lt_irrefl, ↓reduceIte, Option.some.injEq] at Hc0
        have : uint.Z (plogLast base0 F0).term' = 0 := by rw [← Hc0]; rfl
        have := uint_Z_nonneg (plogLast base0 Fv).term'
        omega
      · have := uint_Z_nonneg (W64 (plogLastIndexZ base0 F0)); omega
    have Hrng := uint_Z_lt (W64 (plogLastIndexZ base0 F0))
    obtain ⟨x, Hx⟩ : ∃ x, G[(uint.Z (W64 (plogLastIndexZ base0 F0)) - 1).toNat]? = some x :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    icases logRecs_lookup γ G _ x Hx (by omega) $$ HrG with ⟨%pt, -, #Hxr⟩
    have Hxt : x.Term' = (plogLast base0 F0).term' := by
      rw [plogTermAt_lookup base0 G _ _ x Hx (by rw [base0_index]; omega)] at HGl
      exact Option.some.inj HGl
    unfold isEntryR
    icases Hxr with (⟨%ldr, %γt, %b, %l0, %F0c, #Hlc, -, #Hcc, -, -⟩ | ⟨%Hb, -⟩)
    · rw [Hxt]
      icases recs_chain γ G ldr _ F0c HwG $$ Hlc Hcc HrG with %Hch
      obtain ⟨-, HGlc, -⟩ := Hch _ Hic0 HGl
      iapply IH _ t n F ldr F0c G HtcT (by omega) HwG HGlc $$ HS Hcq Hlc Hcc HrG
    · -- (2026-10-16, stage R8b) a boot entry, of term `1`: below every commit fact's term
      icases cq_boot γ t n F $$ Hcq with %Hbf
      have H2 := Hbf.2 (BootRec_ne _ _ _ Hb)
      have Hx1 : uint.Z (plogLast base0 F0).term' = 1 := by rw [← Hxt, Hb.2.2.1]; rfl
      ipureintro; exfalso; omega
  · -- the same last term: `G` has it down to `Fv`'s last index
    have Hn1 : 1 ≤ uint.Z (plogLast base0 Fv).index' := by omega
    have Hrng := uint_Z_lt (plogLast base0 Fv).index'
    obtain ⟨y, Hy⟩ : ∃ y, Fv[(uint.Z (plogLast base0 Fv).index' - 1).toNat]? = some y :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    icases logRecs_lookup γ Fv _ y Hy (by omega) $$ HrFv with ⟨%pt, -, #Hyr⟩
    have Hyt : y.Term' = (plogLast base0 Fv).term' := by
      rw [plogTermAt_lookup base0 Fv _ _ y Hy (by rw [base0_index]; omega)] at HFvli
      exact Option.some.inj HFvli
    have Hyi : uint.Z y.Index' = uint.Z (plogLast base0 Fv).index' := by
      have Hw := HwFv _ _ Hy
      rw [base0_index] at Hw
      omega
    unfold isEntryR
    icases Hyr with (⟨%ldr, %γt, %b, %l0, %F0c, #Hlc, -, #Hcc, -, %Hptok, -⟩ | ⟨%Hb, -⟩)
    · have HyL := Hptok.1
      rw [Hyi] at HyL
      icases recs_chain γ G ldr _ F0c HwG $$ Hlc Hcc HrG with %Hch
      rw [Heq, ← Hyt] at HGl
      have Hlic : uint.Z (plogLast base0 Fv).index' ≤ uint.Z (W64 (plogLastIndexZ base0 F0)) := by
        rw [← Hcli]; exact Hle
      obtain ⟨-, -, Hall⟩ := Hch _ (by omega) HGl
      have HGli : plogTermAt base0 G (plogLast base0 Fv).index' = some (plogLast base0 Fv).term' := by
        rw [← Hyt]; exact Hall _ ⟨HyL, Hlic⟩
      icases full_match γ G Fv _ HwG HwFv (by rw [HGli]; rfl) (by rw [HGli, HFvli])
        $$ HrG HrFv with %Hm
      ipureintro
      rw [Hm n Hnli]; exact HFvn
    · -- (2026-10-16, stage R8b) a boot entry, of term `1`: below every commit fact's term
      icases cq_boot γ t n F $$ Hcq with %Hbf
      have H2 := Hbf.2 (BootRec_ne _ _ _ Hb)
      have Hy1 : uint.Z (plogLast base0 Fv).term' = 1 := by rw [← Hyt, Hb.2.2.1]; rfl
      ipureintro; exfalso; omega


/-- `lc_adj_gen` for a winner in the winners table: a vote cast knowing the leader of `T`, who
is the winner (the table's agreement), is not in the winning quorum. -/
theorem lc_adj (γ : RaftNames) (T t n : w64) (F : List EntryM) (c : w64)
    (F0 G : List EntryM) (q V : GSet w64) (IH : LcIH (GF := GF) γ T) :
    uint.Z t < uint.Z T →
    PlogWf base0 G →
    plogTermAt base0 G (W64 (plogLastIndexZ base0 F0))
      = some (plogLast base0 F0).term' →
    (∃ v, v ∈ q ∧ v ∈ V ∧ ¬ (v = γ.reWit ∧ γ.reWit ≠ W64 0)) →
    ⊢ votesTbl (GF := GF) γ -∗ cq γ t n F -∗
      ([∗map] v ↦ _u ∈ toMap q, ∃ i', ⌜uint.Z n ≤ uint.Z i'⌝ ∗ isAcked γ v t i') -∗
      isWin γ c T V -∗ isCamp γ c T F0 -∗
      logRecs γ base0 G -∗ ⌜plogTermAt base0 G n = some t⌝ := by
  intro HtT HwG HGl Hmeet
  iintro HS #Hcq #Hacks #Hwin #Hc #HrG
  ihave #Hvotes := isWin_votes γ c T V $$ Hwin
  iapply lc_adj_gen γ T t n F c F0 G q V IH HtT HwG HGl Hmeet $$ HS Hcq Hacks Hvotes [] Hc HrG
  imodintro
  iintro %ldr %qd #Hwd %Hex
  icases isWin_tbl_agree γ ldr c T qd V $$ Hwd Hwin with %Heq
  obtain ⟨rfl, rfl⟩ := Heq
  obtain ⟨v, h1, h2⟩ := Hex
  exact absurd h1 h2

/-- **The case of Leader Completeness the witness adds** (2026-10-19, witness support,
`notes/raft-witness.md`, "Why it is safe"): the commit quorum of `t` and the winning quorum of `T`
meet only at the witness. Its acknowledgement says that `quorum - 1` voters `H` of the
replication set of a subterm `σ` of `t` acknowledged an entry `idx ≥ n` of it, and that its state
had `(t, σ)` as last entry; its vote, that its state then -- of term `T`, so later, so at least
`(t, σ)` -- granted the request of `T`'s winner, whose campaign log ends at `(lt, ls)`:
- `lt > t`: the induction hypothesis at `lt` (`lc_newer`);
- `lt = t`, `ls > σ`: the campaign log's last entry is the leader of `t`'s, of a later subterm, so
  past `idx` (`subRec_order`): `lc_same_term`;
- `(lt, ls) = (t, σ)`: the witness's state is `(t, σ)` too, whose replication set is `H`'s (one
  excluded voter per subterm), and every responder of the request is in it. The request's
  `quorum - 1` granted votes and `H` are in the replication set without the witness, of
  `|voters| - 2` members: they meet in a node (`gset_meet`), which voted in the winning quorum
  (`grantLb_win`) and acknowledged `idx`: `lc_adj`. -/
theorem lc_wit (γ : RaftNames) (T t n : w64) (F : List EntryM) (c : w64)
    (F0 G : List EntryM) (q V : GSet w64) (IH : LcIH (GF := GF) γ T) (Hst : γ.reDyn = none) :
    uint.Z t < uint.Z T →
    PlogWf base0 G →
    plogTermAt base0 G (W64 (plogLastIndexZ base0 F0)) = some (plogLast base0 F0).term' →
    γ.reWit ∈ q → γ.reWit ∈ V → γ.reWit ≠ W64 0 →
    ⊢ votesTbl (GF := GF) γ -∗ cq γ t n F -∗
      ([∗map] v ↦ _u ∈ toMap q, ∃ i', ⌜uint.Z n ≤ uint.Z i'⌝ ∗ isAcked γ v t i') -∗
      isWin γ c T V -∗ isCamp γ c T F0 -∗
      logRecs γ base0 G -∗ ⌜plogTermAt base0 G n = some t⌝ := by
  intro HtT HwG HGl Hwq HwV Hwne
  iintro HS #Hcq #Hacks #Hwin #Hc #HrG
  icases cq_full γ t n F $$ Hcq with ⟨%HwF, #HrF⟩
  icases cq_base γ _ _ _ $$ Hcq with ⟨%HFn, #HFl⟩
  -- index 0
  by_cases Hn0 : uint.Z n = 0
  · have key : ∀ L : List EntryM, plogTermAt base0 L n = some base0.term' := by
      intro L; unfold plogTermAt; rw [base0_index]; simp [Hn0]
    rw [key] at HFn
    ipureintro; rw [key]; exact HFn
  -- `t > 0`: the leader of `t` campaigned with a log of lower terms
  icases leadFull_camp γ t F $$ HFl with ⟨%ldrF, %F0F, -, #HcF, -⟩
  icases isCamp_ok γ ldrF t F0F $$ HcF with %HcokF
  have Ht0 : 0 < uint.Z t := by
    have := HcokF.2 _ _ (camp_last t F0F HcokF)
    have := uint_Z_nonneg (plogLast base0 F0F).term'
    omega
  -- the witness's acknowledgement
  ihave Hack0 := BigSepM.bigSepM_lookup
    (Φ := fun v _ => iprop(∃ i', ⌜uint.Z n ≤ uint.Z i'⌝ ∗ isAcked (GF := GF) γ v t i'))
    ((GMap.elem_of_gset _ _).mp Hwq) $$ Hacks
  icases Hack0 with ⟨%iw, %Hiw, #Hackw⟩
  iunfold isAcked at Hackw
  icases Hackw with (%H0 | #Hreg | ⟨-, #Hwa⟩)
  · exfalso; have := uint_Z_nonneg n; omega
  · icases ackReg_not_wit γ _ _ _ $$ Hreg with %Hnw
    exact absurd ⟨rfl, Hwne⟩ Hnw
  iunfold wAck at Hwa
  icases Hwa with ⟨%σs, %idx, %x, %P, %cA, %H, %st, %Hst, #Hj, #Hstw⟩
  obtain ⟨Hiidx, Hstt, Hstlt, Hstls⟩ := Hst
  iunfold wJust at Hj
  icases Hj with ⟨%Hjp, ⟨%ldr, #Hl, #Hsr⟩, -, #HHacks⟩
  obtain ⟨-, HcA, -, HwA, Hxcfg, Hxw, HHsub, HHsize, Hidx1, Hσ0⟩ := Hjp
  -- the witness's vote, for `T`'s winner
  ihave #Hvotes := isWin_votes γ c T V $$ Hwin
  ihave #Hvw := BigSepM.bigSepM_lookup (Φ := fun v _ => isVote (GF := GF) γ v T c)
    ((GMap.elem_of_gset _ _).mp HwV) $$ Hvotes
  ihave #Hjust := votesTbl_just γ γ.reWit T c $$ HS Hvw
  iunfold voteJust at Hjust
  icases Hjust with (⟨%k, %d, %Fv, %Fc, #Hvl, -⟩ | ⟨-, #Hwv⟩)
  · -- the witness has no vote-time logs
    iunfold isVlog at Hvl
    icases Hvl with ⟨%γl, %Hγl, -⟩
    exfalso
    rcases γ.reWit_ok with h | ⟨-, -, -, h⟩
    · exact Hwne h
    · rw [h] at Hγl; cases Hγl
  iunfold wVoteJust at Hwv
  icases Hwv with ⟨%stv, %lt, %li, %ls, %resp, %Hg, #Hstv, #Hreq⟩
  obtain ⟨Hstvt, Hgrant⟩ := Hg
  iunfold wVoteReq at Hreq
  icases Hreq with ⟨%F0', %kv, %K, %G', #HcK', #HrF0, %Hrq, #Hglb, -⟩
  ihave #Hc' := isCampK_camp γ c T F0' kv $$ HcK'
  icases isCamp_agree γ c T F0 F0' $$ Hc Hc' with %HF0
  subst HF0
  obtain ⟨Hlast, Hls, HKcfg, HG'resp, HGin, -⟩ := Hrq
  icases isCamp_ok γ c T F0 $$ Hc with %Hcok
  -- the witness's state at the vote is at least the acknowledged one; the request's last entry
  -- at least that state's
  icases wSt_order γ st stv (by rw [Hstt, Hstvt]; exact HtT) $$ Hstw Hstv with %Hord
  rw [Hstlt, Hstls] at Hord
  have Hlt : (plogLast base0 F0).term' = lt := by rw [Hlast]
  have Hcl := camp_last T F0 Hcok
  have HltT : uint.Z lt < uint.Z T := by rw [← Hlt]; exact Hcok.2 _ _ Hcl
  rw [Hlt] at HGl
  have HwF0 := Hcok.1
  have HL0 := plogLastIndexZ_nonneg base0 F0
  have Hrng0 := PlogWf_range _ _ HwF0
  have HjZ : uint.Z (W64 (plogLastIndexZ base0 F0)) = plogLastIndexZ base0 F0 :=
    uint_Z_W64 _ HL0 Hrng0
  have Hcases : uint.Z t < uint.Z lt ∨ (lt = t ∧ uint.Z σs < uint.Z ls) ∨
      (lt = t ∧ ls = σs ∧ stv.lt = t ∧ stv.ls = σs) := by
    have Hcand : LexLe stv.lt stv.ls lt ls := by
      rcases Hgrant with ⟨h, -⟩ | ⟨h1, h2, -⟩
      · exact h
      · right; exact ⟨h1, by rw [h2]; exact Int.le_refl _⟩
    unfold LexLe at Hord Hcand
    rcases Hord with Hord | ⟨Hord1, Hord2⟩ <;> rcases Hcand with Hcand | ⟨Hcand1, Hcand2⟩
    · left; omega
    · left; rw [← Hcand1]; exact Hord
    · left; rw [Hord1]; exact Hcand
    · by_cases hs : uint.Z σs < uint.Z ls
      · right; left; exact ⟨Hcand1.symm.trans Hord1.symm, hs⟩
      · right; right
        refine ⟨Hcand1.symm.trans Hord1.symm, ?_, Hord1.symm, ?_⟩
        · apply uint_Z_inj.mp; omega
        · apply uint_Z_inj.mp; omega
  rcases Hcases with HA | ⟨HB1, HB2⟩ | ⟨HC1, HC2, HC3, HC4⟩
  · -- a newer last term: the induction hypothesis
    have Hj0 : 0 < uint.Z (W64 (plogLastIndexZ base0 F0)) := by
      by_cases H0 : uint.Z (W64 (plogLastIndexZ base0 F0)) = 0
      · exfalso
        unfold plogTermAt at HGl
        rw [base0_index] at HGl
        simp only [H0, Int.lt_irrefl, ↓reduceIte, Option.some.injEq] at HGl
        have : uint.Z lt = 0 := by rw [← HGl]; rfl
        omega
      · have := uint_Z_nonneg (W64 (plogLastIndexZ base0 F0)); omega
    iapply lc_newer γ T t n _ lt F G IH HA HltT HwG HGl Hj0 $$ HS Hcq HrG
  · -- the same term, a later subterm: the campaign log's last entry is past `idx`
    have Hls0 : ls ≠ W64 0 := by
      intro h; rw [h] at HB2; have := uint_Z_nonneg σs; simp at HB2
    obtain ⟨e, He, Hes⟩ : ∃ e, F0.getLast? = some e ∧ e.Subterm' = ls := by
      rcases Hls with h | h
      · exact absurd h Hls0
      · exact h
    have Hlen : 0 < F0.length := by
      cases hF : F0 with
      | nil => rw [hF] at He; simp at He
      | cons _ _ => simp
    have HeF : F0[F0.length - 1]? = some e := by
      rw [List.getLast?_eq_getElem?] at He; exact He
    have Hidx := HwF0 _ _ HeF
    rw [base0_index] at Hidx
    have HlenZ : plogLastIndexZ base0 F0 = F0.length := by
      unfold plogLastIndexZ; rw [base0_index]; omega
    have Het : e.Term' = lt := by
      unfold plogLast at Hlast; rw [He] at Hlast
      simp only [entId, entryID.mk.injEq] at Hlast; exact Hlast.1
    icases logRecs_lookup γ F0 _ e HeF (by omega) $$ HrF0 with ⟨%pt, -, #Her⟩
    iunfold isEntryR at Her
    icases Her with (⟨%ldr', %γt', %b', %l0', %F0c', #Hl', -, -, -, -, -, -, %xe, %Pe, #Hsre⟩ | ⟨%Hb, -⟩)
    · rw [show e.Term' = t from Het.trans HB1]
      icases isLeader_unique γ ldr' ldr t $$ Hl' Hl with %Hll
      subst Hll
      icases subRec_order γ ldr' t idx σs x e.Index' e.Subterm' xe P Pe $$ Hsr Hsre with %Hso
      rw [Hes] at Hso
      have Hlt' := Hso.1 HB2
      iapply lc_same_term γ t n _ F G HwG (by rw [← HB1]; exact HGl)
        (by rw [HjZ]; omega) (by rw [HjZ]; omega) $$ Hcq HrG
    · -- a boot entry, of term `1`: below every commit fact's term
      icases cq_boot γ t n F $$ Hcq with %Hbf
      have H2 := Hbf.2 (BootRec_ne _ _ _ Hb)
      have : uint.Z e.Term' = 1 := by rw [Hb.2.2.1]; rfl
      rw [Het, HB1] at this
      exfalso; omega
  · -- the same `(term, subterm)`: the witness's state's replication set is `H`'s
    have Hresp : ∀ v, v ∈ resp → v ∈ stv.rs := by
      rcases Hgrant with ⟨-, hne⟩ | ⟨-, -, h⟩
      · exact absurd ⟨by rw [HC3, HC1], by rw [HC4, HC2]⟩ hne
      · exact h
    ihave #Hsj := wSt_just γ stv $$ Hstv
    iunfold wStJust at Hsj
    have Hlt0 : stv.lt ≠ W64 0 := by
      intro h; rw [HC3] at h; rw [h] at Ht0; simp at Ht0
    rw [if_neg Hlt0]
    icases Hsj with ⟨%xv, %Pv, %cv, %Hv, %Hrs0, #Hjv⟩
    have Hrs := Hrs0.1
    iunfold wJust at Hjv
    icases Hjv with ⟨%Hjpv, ⟨%ldrv, #Hlv, #Hsrv⟩, -, -⟩
    rw [HC3, HC4]
    icases isLeader_unique γ ldrv ldr t $$ Hlv Hl with %Hll
    subst Hll
    icases subRec_order γ ldrv t idx σs x stv.li σs xv P Pv $$ Hsr Hsrv with %Hso
    obtain ⟨Hxv, HPv⟩ := Hso.2 rfl
    subst Hxv HPv
    -- (2026-10-20) the stored replication set is of the acknowledged entry's configuration
    have Hcv : cv.incoming = cA.incoming := CfgAt.incoming_eq Hjpv.2.1 HcA
    -- the request's granted votes of the campaign configuration's incoming half, and `H`, in
    -- the replication set without the witness
    have HKin : K.incoming = cA.incoming :=
      (CfgAt.static Hst HKcfg).1.trans (CfgAt.static Hst HcA).1.symm
    let S := cA.incoming \ ({[γ.reWit]} ∪ {[x]})
    let Gh := G' ∩ K.incoming
    have HGhS : Gh ⊆ S := by
      rw [GMap.elem_of_subseteq]
      intro g hg
      rw [GMap.elem_of_intersection] at hg
      have := (Hrs g).1 (Hresp g (HG'resp g hg.1))
      rw [Hcv] at this; exact this
    have Hsz := gset_size_minus2 cA.incoming γ.reWit x HwA Hxcfg Hxw
    obtain ⟨h, hH, hGh⟩ := wit_count_meet S H Gh (size cA.incoming) (size K.incoming)
      Hsz HHsub HGhS HHsize HGin (by rw [HKin]; omega)
    have hG' : h ∈ G' := by
      have := hGh; rw [GMap.elem_of_intersection] at this; exact this.1
    ihave #Hwg := isWin_grant γ c T V $$ Hwin
    icases grantLb_win γ c T G' V $$ Hglb Hwg with %HG'V
    have hV : h ∈ V := (GMap.elem_of_subseteq _ _).1 HG'V h hG'
    have hnw : ¬ (h = γ.reWit ∧ γ.reWit ≠ W64 0) := by
      intro hw
      have := (GMap.elem_of_subseteq _ _).1 HHsub h hH
      rw [GMap.elem_of_difference, GMap.elem_of_union, GMap.elem_of_singleton] at this
      exact this.2 (Or.inl hw.1)
    iapply lc_adj γ T t n F c F0 G H V IH HtT HwG (by rw [Hlt]; exact HGl) ⟨h, hH, hV, hnw⟩
      $$ HS Hcq [] Hwin Hc HrG
    iapply BigSepM.bigSepM_impl $$ HHacks
    imodintro
    iintro %v %u %Hv ⟨%i', %Hi', #Ha⟩
    iexists i'
    isplitr; · ipureintro; omega
    iunfold isAcked
    iright; ileft; iexact Ha

/-- A winner's campaign's dynamic facts, from a vote of its quorum (2026-10-14, stage B5). -/
theorem winner_campDyn (γ : RaftNames) (c T : w64) (V : GSet w64) (F0 : List EntryM)
    (k : w64) (Hdyn : γ.reDyn ≠ none) (Hne : ∃ v, v ∈ V) :
    ⊢ votesTbl (GF := GF) γ -∗ ([∗map] x ↦ _u ∈ toMap V, isVote γ x T c) -∗
      isCampK γ c T F0 k -∗
      ∃ tmc, ⌜uint.Z tmc < uint.Z T ∧ ConfI1 F0 (uint.Z k).toNat ∧ PlogWf base0 F0⌝ ∗
        logRecs γ base0 F0 ∗ commitIn γ F0 k tmc := by
  iintro HS #Hvs #HcK
  obtain ⟨v0, Hv0⟩ := Hne
  ihave #Hv0v := BigSepM.bigSepM_lookup (Φ := fun v _ => isVote (GF := GF) γ v T c)
    ((GMap.elem_of_gset _ _).mp Hv0) $$ Hvs
  ihave #Hj := votesTbl_just γ v0 T c $$ HS Hv0v
  iunfold voteJust at Hj
  icases Hj with (⟨%kj, %dj, %Fvj, %Fcj, -, -, -, -, -, -, #Hcdj⟩ | ⟨%Hwj, -⟩)
  rotate_left
  · exact absurd (RaftNames.wit_dyn Hdyn) Hwj.2
  ihave #Hcd := dynOn_elim γ _ Hdyn $$ Hcdj
  iunfold campDyn at Hcd
  icases Hcd with ⟨%kc, %tmc, %Hcp, #HcKc, #HrF0c, #HcmF0⟩
  icases isCampK_agree γ c T F0 Fcj k kc $$ HcK HcKc with %Hag
  obtain ⟨rfl, rfl⟩ := Hag
  iexists tmc
  iframe HrF0c HcmF0
  ipureintro; exact Hcp

/-! ### Two commit facts below `T`, by the induction hypothesis (2026-10-14, stage B5) -/

/-- `cq_lt_agree` below `T`, by the induction hypothesis instead of `lc_core`. -/
theorem cq_lt_agree_ih (γ : RaftNames) (T : w64) (IH : LcIH (GF := GF) γ T)
    (t1 n1 t2 n2 : w64) (G1 G2 : List EntryM) :
    uint.Z t1 < uint.Z t2 → uint.Z t2 < uint.Z T →
    ⊢ votesTbl (GF := GF) γ -∗ cq γ t1 n1 G1 -∗ cq γ t2 n2 G2 -∗
      ⌜∀ j : w64, uint.Z j ≤ uint.Z n1 → plogTermAt base0 G1 j = plogTermAt base0 G2 j⌝ := by
  intro Hlt Ht2
  iintro HS #Hq1 #Hq2
  icases cq_full γ t1 n1 G1 $$ Hq1 with ⟨%Hw1, #Hr1⟩
  icases cq_full γ t2 n2 G2 $$ Hq2 with ⟨%Hw2, #Hr2⟩
  icases cq_base γ _ _ _ $$ Hq1 with ⟨%H1n, -⟩
  icases cq_base γ _ _ _ $$ Hq2 with ⟨-, #Hfl2⟩
  icases leadFull_camp γ t2 G2 $$ Hfl2 with ⟨%ldr, %F0, #Hl, #Hc, %Hpre⟩
  icases isCamp_ok γ ldr t2 F0 $$ Hc with %Hcok
  have Hcl := camp_last t2 F0 Hcok
  have HGl : plogTermAt base0 G2 (W64 (plogLastIndexZ base0 F0))
      = some (plogLast base0 F0).term' := by
    rw [plogTermAt_prefix _ F0 G2 _ Hpre (by rw [Hcl]; rfl), Hcl]
  icases IH t2 t1 n1 G1 ldr F0 G2 Ht2 Hlt Hw2 HGl $$ HS Hq1 Hl Hc Hr2 with %H2n
  iapply full_match γ G1 G2 n1 Hw1 Hw2 (by rw [H1n]; rfl) (by rw [H1n, H2n]) $$ Hr1 Hr2

/-- `cq_agree` below `T`, by the induction hypothesis. -/
theorem cq_agree_ih (γ : RaftNames) (T : w64) (IH : LcIH (GF := GF) γ T)
    (t1 n1 t2 n2 i : w64) (G1 G2 : List EntryM) :
    uint.Z t1 < uint.Z T → uint.Z t2 < uint.Z T →
    uint.Z i ≤ uint.Z n1 → uint.Z i ≤ uint.Z n2 →
    ⊢ votesTbl (GF := GF) γ -∗ cq γ t1 n1 G1 -∗ cq γ t2 n2 G2 -∗
      ⌜∀ j : w64, uint.Z j ≤ uint.Z i → plogTermAt base0 G1 j = plogTermAt base0 G2 j⌝ := by
  intro Ht1 Ht2 Hi1 Hi2
  iintro HS #Hq1 #Hq2
  rcases Int.lt_trichotomy (uint.Z t1) (uint.Z t2) with Hlt | Heq | Hgt
  · icases cq_lt_agree_ih γ T IH t1 n1 t2 n2 G1 G2 Hlt Ht2 $$ HS Hq1 Hq2 with %H
    ipureintro; intro j Hj; exact H j (by omega)
  · have Ht : t1 = t2 := uint_Z_inj.mp Heq
    subst Ht
    icases cq_full γ t1 n1 G1 $$ Hq1 with ⟨%Hw1, #Hr1⟩
    icases cq_full γ t1 n2 G2 $$ Hq2 with ⟨%Hw2, #Hr2⟩
    icases cq_base γ _ _ _ $$ Hq1 with ⟨%H1n, #Hf1⟩
    icases cq_base γ _ _ _ $$ Hq2 with ⟨%H2n, #Hf2⟩
    have Hs1 := full_term_at_some G1 i n1 (by rw [H1n]; rfl) Hi1
    have Hs2 := full_term_at_some G2 i n2 (by rw [H2n]; rfl) Hi2
    icases leadFull_agree γ t1 G1 G2 i Hs1 Hs2 $$ Hf1 Hf2 with %Hag
    iapply full_match γ G1 G2 i Hw1 Hw2 Hs1 Hag $$ Hr1 Hr2
  · icases cq_lt_agree_ih γ T IH t2 n2 t1 n1 G2 G1 Hgt Ht1 $$ HS Hq2 Hq1 with %H
    ipureintro; intro j Hj; exact (H j (by omega)).symm

/-- The far case "older commit fact" of `lc_core` (the paper's section 7, `j_c ≥ j_m + 2`,
2026-10-14, stage B5): the campaign's commit index `k` is justified by a commit fact of a term
below `T` (the campaign's `commitIn`), which agrees with the commit fact up to the smaller of
the two indices (the induction hypothesis). If `n ≤ k`, the campaign log has `t` at `n`, and so
has every log that reaches its last entry; if `k < n`, the commit fact's log has the campaign
log's first `k` entries, two more conf entries than its own prefix at `a`: against its I1
(the paper's repair 1). -/
theorem lc_far_newer (γ : RaftNames) (T t n : w64) (F : List EntryM) (a : w64)
    (F0 G : List EntryM) (kw tmc : w64) (IH : LcIH (GF := GF) γ T) :
    uint.Z t < uint.Z T → uint.Z tmc < uint.Z T →
    PlogWf base0 G →
    plogTermAt base0 G (W64 (plogLastIndexZ base0 F0))
      = some (plogLast base0 F0).term' →
    CampOk T F0 → uint.Z kw ≤ plogLastIndexZ base0 F0 →
    ConfI1 F (uint.Z a).toNat →
    confCount (F.take (uint.Z a).toNat) + 2 ≤ confCount (F0.take (uint.Z kw).toNat) →
    ⊢ votesTbl (GF := GF) γ -∗ cq γ t n F -∗ logRecs γ base0 F0 -∗ commitIn γ F0 kw tmc -∗
      logRecs γ base0 G -∗ ⌜plogTermAt base0 G n = some t⌝ := by
  intro HtT HtmT HwG HGl Hcok Hkle HI1 Hcc
  iintro HS #Hcq #HrF0 #Hcm #HrG
  have HwF0 := Hcok.1
  icases cq_full γ t n F $$ Hcq with ⟨%HwF, #HrF⟩
  icases cq_base γ t n F $$ Hcq with ⟨%HFn, -⟩
  ihave #Hcj := commitIn_j γ F0 kw tmc $$ Hcm
  iunfold commitJ at Hcj
  icases Hcj with (%Hk0 | ⟨%tk, %nk, %Gk, #Hqk, %Hk⟩)
  · -- (2026-10-16, stage R8b) the campaign's commit index within the bootstrap log: the
    -- commit fact's log and the campaign log both start with it, against I1
    obtain ⟨Hkb, -⟩ := Hk0
    icases cq_boot γ t n F $$ Hcq with %Hbf
    icases logRecs_boot_take γ F0 HwF0 $$ HrF0 with %Htk0
    have HL0 : plogLastIndexZ base0 F0 = F0.length := by
      unfold plogLastIndexZ; rw [base0_index]; omega
    have Htk : F.take (uint.Z kw).toNat = F0.take (uint.Z kw).toNat := by
      rw [take_of_prefix Hbf.1 (by omega), Htk0 _ (by omega) (by omega)]
    exact (far_newer HI1 Htk Hcc).elim
  obtain ⟨Hkn, Htk, HGk⟩ := Hk
  icases cq_full γ tk nk Gk $$ Hqk with ⟨%HwGk, #HrGk⟩
  icases cq_base γ tk nk Gk $$ Hqk with ⟨%HGkn, -⟩
  -- the justifying fact's log agrees with the campaign log up to `k`
  have HsGk : (plogTermAt base0 Gk kw).isSome :=
    full_term_at_some Gk kw nk (by rw [HGkn]; rfl) Hkn
  icases full_match γ Gk F0 kw HwGk HwF0 HsGk HGk $$ HrGk HrF0 with %HmK
  -- every log reaching the campaign log's last entry agrees with it below
  have Hcl := camp_last T F0 Hcok
  have Hli := uint_Z_W64 (plogLastIndexZ base0 F0) (plogLastIndexZ_nonneg _ _)
    (PlogWf_range _ _ HwF0)
  icases full_match γ F0 G (W64 (plogLastIndexZ base0 F0)) HwF0 HwG (by rw [Hcl]; rfl)
    (by rw [Hcl, HGl]) $$ HrF0 HrG with %HmG
  by_cases Hnk : uint.Z n ≤ uint.Z kw
  · icases cq_agree_ih γ T IH t n tk nk n F Gk HtT (by omega) (Int.le_refl _) (by omega)
      $$ HS Hcq Hqk with %Hag
    ipureintro
    rw [← HmG n (by omega), ← HmK n Hnk, ← Hag n (Int.le_refl _), HFn]
  · icases cq_agree_ih γ T IH t n tk nk kw F Gk HtT (by omega) (by omega) Hkn
      $$ HS Hcq Hqk with %Hag
    have HsF : (plogTermAt base0 F kw).isSome :=
      full_term_at_some F kw n (by rw [HFn]; rfl) (by omega)
    icases full_take_eq γ F F0 kw HwF HwF0 HsF
      ((Hag kw (Int.le_refl _)).trans (HmK kw (Int.le_refl _))) $$ HrF HrF0 with %Htk
    exact (far_newer HI1 Htk Hcc).elim

/-- The far case "older winner" of `lc_core` (the paper's section 7, `j_c ≤ j_m - 2`,
2026-10-14, stage B5): the commit fact's witness for its conf entry `j_c + 1` (0-based) has the
configuration index just after the winner's, so its quorum meets the winning one, and the
adjacent case (`lc_adj`) puts its log, up to the entry, into the campaign log: two conf entries
past the campaign's commit index, against I1 at the campaign. -/
theorem lc_far_older (γ : RaftNames) (T t : w64) (F : List EntryM) (a : w64)
    (c : w64) (F0 : List EntryM) (kw : w64) (cW : CfgM) (V : GSet w64)
    (IH : LcIH (GF := GF) γ T) (Hdyn : γ.reDyn ≠ none) :
    uint.Z t < uint.Z T → CampOk T F0 →
    ConfI1 F0 (uint.Z kw).toNat →
    CfgAt γ (F0.take (uint.Z kw).toNat) cW → JQuorum cW V →
    confCount (F0.take (uint.Z kw).toNat) + 2 ≤ confCount (F.take (uint.Z a).toNat) →
    ⊢ votesTbl (GF := GF) γ -∗ cqDyn γ t F a -∗ isWin γ c T V -∗ isCamp γ c T F0 -∗
      logRecs γ base0 F0 -∗ isCommitted γ (F0.take (uint.Z kw).toNat) -∗ ⌜False⌝ := by
  intro HtT Hcok HI1 HcfgW HjW Hcc
  iintro HS #Hd #Hwin #Hc #HrF0 #HcF0
  have HwF0 := Hcok.1
  iunfold cqDyn at Hd
  icases Hd with ⟨-, #Hwit⟩
  obtain ⟨k2, hk2, hp2, hc2⟩ :=
    exists_confPos F (uint.Z a).toNat (confCount (F0.take (uint.Z kw).toNat) + 1) (by omega)
  ihave Hw := Hwit $$ %k2 %(And.intro hp2 hk2)
  icases Hw with ⟨%tw, %nw, %Gw, %aw, %cw, %qw, %Hwo, #Hcqw⟩
  icases cqAt_parts γ tw nw Gw aw cw qw $$ Hcqw with ⟨%Hpw, -, #HcGw, #Hackw, -⟩
  icases isCommitted_agree γ _ _ $$ HcGw HcF0 with %Hpre
  obtain ⟨Htw, Hnw, Haw, Hag, Hcw⟩ := Hwo
  have Hcw' : confCount (Gw.take (uint.Z aw).toNat) = confCount (F0.take (uint.Z kw).toNat) + 1 := by
    rw [Hcw, hc2]
  have Hov := CfgAt.overlap_adj Hpre (by omega) (by omega) Hpw.2.2.1 HcfgW
  have Hmeet := meet_nowit (RaftNames.wit_dyn Hdyn) (Hov qw V Hpw.2.2.2 HjW)
  ihave #Hcqw' := cqAt_cq γ _ _ _ _ _ _ $$ Hcqw
  icases lc_adj γ T tw nw Gw c F0 F0 qw V IH (by omega) HwF0 (camp_last T F0 Hcok) Hmeet
    $$ HS Hcqw' Hackw Hwin Hc HrF0 with %HF0nw
  icases cq_full γ tw nw Gw $$ Hcqw' with ⟨%HwGw, #HrGw⟩
  icases full_take_eq γ Gw F0 nw HwGw HwF0 (by rw [Hpw.1]; rfl) (by rw [Hpw.1, HF0nw])
    $$ HrGw HrF0 with %Htk
  ipureintro
  refine far_older HI1 ?_ hp2 hc2
  rw [take_agree_le Htk.symm (by omega), Hag]

/-- The core of Leader Completeness, by strong induction on the term `T` of the leader
(`k` bounds it). If a quorum acknowledged the leader of `t < T` up to `n`, where its log
`F` has an entry of term `t`, then every full log `G` with records that reaches the last
entry of the campaign log of `T`'s leader has term `t` at `n`.

Since 2026-10-14 (reconfiguration stage B4) structured as the paper's section 7: at `T`, the
commit quorum is a joint quorum of the committer's configuration and the winning quorum one
of the winner's (both recorded, `CfgAt`); when the two overlap, the adjacent case `lc_adj`
(with the induction hypothesis below `T`). At B4 they always overlap (`CfgAt.overlap`, the
static instance). B5 replaces that one step by the case split on the configuration indices:
adjacent, `lc_adj`; far, `j_c ≥ j_m + 2` (the commit fact's at-most-one) or `j_c ≤ j_m - 2`
(`lc_adj` at the commit fact's witness, then I1 at the campaign). -/
theorem lc_core (γ : RaftNames) (k : Nat) :
    ∀ (T t n : w64) (F : List EntryM) (c : w64) (F0 G : List EntryM),
    uint.Z T < (k : Int) → uint.Z t < uint.Z T →
    PlogWf base0 G →
    plogTermAt base0 G (W64 (plogLastIndexZ base0 F0))
      = some (plogLast base0 F0).term' →
    ⊢ votesTbl (GF := GF) γ -∗ cq γ t n F -∗ isLeader γ c T -∗ isCamp γ c T F0 -∗
      logRecs γ base0 G -∗ ⌜plogTermAt base0 G n = some t⌝ := by
  induction k with
  | zero =>
    intro T t n F c F0 G HTk
    have := uint_Z_nonneg T
    omega
  | succ k IH0 =>
  intro T t n F c F0 G HTk HtT HwG HGl
  -- the induction hypothesis, for every term below `T`
  have IH : LcIH (GF := GF) γ T := fun T' t' n' F' c' F0' G' h1 h2 h3 h4 =>
    IH0 T' t' n' F' c' F0' G' (by omega) h2 h3 h4
  iintro HS #Hcq #Hl #Hc #HrG
  -- the commit quorum and its configuration
  icases cq_cqAt γ t n F $$ Hcq with ⟨%a, %cQ, %q, #Hcqa⟩
  icases cqAt_parts γ t n F a cQ q $$ Hcqa with ⟨%Hq, -, -, #Hacks, -⟩
  -- the winning quorum and its configuration
  iunfold isLeader at Hl
  icases Hl with ⟨%V, #Hwin⟩
  icases isWin_core γ c T V $$ Hwin with ⟨%cW, #Hcore⟩
  iunfold isWinCore at Hcore
  icases Hcore with ⟨%γw, %F0w, %kw, %Hw, #HcK, -, #Hvs, -⟩
  -- Static, the two recorded configurations overlap. Dynamic (2026-10-14, stage B5), the case
  -- split on their configuration indices (`notes/reconfiguration-safety.md`, section 7).
  cases HD : γ.dyn with
  | none =>
    have Hmeet := CfgAt.overlap (RaftNames.dyn_eq_none.1 HD) Hq.2.2.1 Hw.2.2 q V Hq.2.2.2 Hw.2.1
    obtain ⟨v, Hvq, HvV⟩ := Hmeet
    -- (2026-10-19, witness support) the quorums meet at a node, or only at the witness
    by_cases Hvw : v = γ.reWit ∧ γ.reWit ≠ W64 0
    · obtain ⟨rfl, Hne⟩ := Hvw
      iapply lc_wit γ T t n F c F0 G q V IH (RaftNames.dyn_eq_none.1 HD) HtT HwG HGl Hvq HvV Hne
        $$ HS Hcq Hacks Hwin Hc HrG
    · iapply lc_adj γ T t n F c F0 G q V IH HtT HwG HGl ⟨v, Hvq, HvV, Hvw⟩ $$ HS Hcq Hacks Hwin Hc HrG
  | some D =>
  have Hdyn : γ.reDyn ≠ none := fun h => by rw [RaftNames.dyn_none h] at HD; cases HD
  icases cqAt_parts γ t n F a cQ q $$ Hcqa with ⟨-, -, #HcF, -, #HdF⟩
  ihave #HdF' := dynOn_elim γ _ Hdyn $$ HdF
  ihave #HdF2 := HdF'
  iunfold cqDyn at HdF2
  icases HdF2 with ⟨%HI1F, -⟩
  -- the winner's campaign's dynamic facts, from a vote of its quorum
  obtain ⟨v0, Hv0⟩ := CfgAt.member Hw.2.2 Hw.2.1
  ihave #Hv0v := BigSepM.bigSepM_lookup (Φ := fun v _ => isVote (GF := GF) γ v T c)
    ((GMap.elem_of_gset _ _).mp Hv0) $$ Hvs
  ihave #Hj := votesTbl_just γ v0 T c $$ HS Hv0v
  iunfold voteJust at Hj
  icases Hj with (⟨%kj, %dj, %Fvj, %Fcj, -, -, -, -, -, -, #Hcdj⟩ | ⟨%Hwj, -⟩)
  rotate_left
  · exact absurd (RaftNames.wit_dyn Hdyn) Hwj.2
  ihave #Hcd := dynOn_elim γ _ Hdyn $$ Hcdj
  iunfold campDyn at Hcd
  icases Hcd with ⟨%kc, %tmc, %Hcp, #HcKc, #HrF0c, #HcmF0⟩
  icases isCampK_agree γ c T F0w Fcj kw kc $$ HcK HcKc with %Hag
  obtain ⟨rfl, rfl⟩ := Hag
  ihave #Hc' := isCampK_camp γ c T F0w kw $$ HcK
  icases isCamp_agree γ c T F0 F0w $$ Hc Hc' with %HF0
  subst HF0
  icases isCamp_ok γ c T F0 $$ Hc with %Hcok
  icases isCampK_k_le γ c T F0 kw $$ HcK with %Hkle
  ihave #HcF0 := isCampK_committed γ c T F0 kw $$ HcK
  icases isCommitted_agree γ _ _ $$ HcF HcF0 with %Hpre
  by_cases Hadj : confCount (F.take (uint.Z a).toNat) ≤ confCount (F0.take (uint.Z kw).toNat) + 1 ∧
      confCount (F0.take (uint.Z kw).toNat) ≤ confCount (F.take (uint.Z a).toNat) + 1
  · have Hmeet := meet_nowit (RaftNames.wit_dyn Hdyn)
      (CfgAt.overlap_adj Hpre Hadj.2 Hadj.1 Hq.2.2.1 Hw.2.2 q V Hq.2.2.2 Hw.2.1)
    iapply lc_adj γ T t n F c F0 G q V IH HtT HwG HGl Hmeet $$ HS Hcq Hacks Hwin Hc HrG
  · rcases (by omega : confCount (F.take (uint.Z a).toNat) + 2 ≤ confCount (F0.take (uint.Z kw).toNat) ∨
        confCount (F0.take (uint.Z kw).toNat) + 2 ≤ confCount (F.take (uint.Z a).toNat))
      with Hfar | Hfar
    · iapply lc_far_newer γ T t n F a F0 G kw tmc IH HtT Hcp.1 HwG HGl Hcok Hkle HI1F Hfar
        $$ HS Hcq HrF0c HcmF0 HrG
    · icases lc_far_older γ T t F a c F0 kw cW V IH Hdyn HtT Hcok Hcp.2.1 Hw.2.2 Hw.2.1 Hfar
        $$ HS HdF' Hwin Hc HrF0c HcF0 with %Hf
      exact Hf.elim

/-- Two commit facts agree below the earlier one's index: same term, the leader's logs
agree; an earlier term, `lc_core` puts the earlier committed log's entry in the later
leader's log. -/
theorem cq_lt_agree (γ : RaftNames) (t1 n1 t2 n2 : w64) (G1 G2 : List EntryM) :
    uint.Z t1 < uint.Z t2 →
    ⊢ votesTbl (GF := GF) γ -∗ cq γ t1 n1 G1 -∗ cq γ t2 n2 G2 -∗
      ⌜∀ j : w64, uint.Z j ≤ uint.Z n1 → plogTermAt base0 G1 j = plogTermAt base0 G2 j⌝ := by
  intro Hlt
  iintro HS #Hq1 #Hq2
  icases cq_full γ t1 n1 G1 $$ Hq1 with ⟨%Hw1, #Hr1⟩
  icases cq_full γ t2 n2 G2 $$ Hq2 with ⟨%Hw2, #Hr2⟩
  icases cq_base γ _ _ _ $$ Hq1 with ⟨%H1n, -⟩
  icases cq_base γ _ _ _ $$ Hq2 with ⟨-, #Hfl2⟩
  icases leadFull_camp γ t2 G2 $$ Hfl2 with ⟨%ldr, %F0, #Hl, #Hc, %Hpre⟩
  icases isCamp_ok γ ldr t2 F0 $$ Hc with %Hcok
  have Hcl := camp_last t2 F0 Hcok
  have HGl : plogTermAt base0 G2 (W64 (plogLastIndexZ base0 F0))
      = some (plogLast base0 F0).term' := by
    rw [plogTermAt_prefix _ F0 G2 _ Hpre (by rw [Hcl]; rfl), Hcl]
  icases lc_core γ ((uint.Z t2).toNat + 1) t2 t1 n1 G1 ldr F0 G2
      (by have := uint_Z_nonneg t2; omega) Hlt Hw2 HGl $$ HS Hq1 Hl Hc Hr2 with %H2n
  iapply full_match γ G1 G2 n1 Hw1 Hw2 (by rw [H1n]; rfl) (by rw [H1n, H2n]) $$ Hr1 Hr2

theorem cq_agree (γ : RaftNames) (t1 n1 t2 n2 i : w64) (G1 G2 : List EntryM) :
    uint.Z i ≤ uint.Z n1 → uint.Z i ≤ uint.Z n2 →
    ⊢ votesTbl (GF := GF) γ -∗ cq γ t1 n1 G1 -∗ cq γ t2 n2 G2 -∗
      ⌜∀ j : w64, uint.Z j ≤ uint.Z i → plogTermAt base0 G1 j = plogTermAt base0 G2 j⌝ := by
  intro Hi1 Hi2
  iintro HS #Hq1 #Hq2
  rcases Int.lt_trichotomy (uint.Z t1) (uint.Z t2) with Hlt | Heq | Hgt
  · icases cq_lt_agree γ t1 n1 t2 n2 G1 G2 Hlt $$ HS Hq1 Hq2 with %H
    ipureintro; intro j Hj; exact H j (by omega)
  · have Ht : t1 = t2 := uint_Z_inj.mp Heq
    subst Ht
    icases cq_full γ t1 n1 G1 $$ Hq1 with ⟨%Hw1, #Hr1⟩
    icases cq_full γ t1 n2 G2 $$ Hq2 with ⟨%Hw2, #Hr2⟩
    icases cq_base γ _ _ _ $$ Hq1 with ⟨%H1n, #Hf1⟩
    icases cq_base γ _ _ _ $$ Hq2 with ⟨%H2n, #Hf2⟩
    have Hs1 := full_term_at_some G1 i n1 (by rw [H1n]; rfl) Hi1
    have Hs2 := full_term_at_some G2 i n2 (by rw [H2n]; rfl) Hi2
    icases leadFull_agree γ t1 G1 G2 i Hs1 Hs2 $$ Hf1 Hf2 with %Hag
    iapply full_match γ G1 G2 i Hw1 Hw2 Hs1 Hag $$ Hr1 Hr2
  · icases cq_lt_agree γ t2 n2 t1 n1 G2 G1 Hgt $$ HS Hq2 Hq1 with %H
    ipureintro; intro j Hj; exact (H j (by omega)).symm

/-! Firing the registries as the global log grows by one entry `e`, the entry at position `m`
of a full log `G` with records (2026-10-10; 2026-10-14, stage R: persistent updates fired at
every entry). The entry's record carries its data (`entData`): the entry's own update moves
the client's log (`propAu` of its data, or the standing `noopAu`), then every read slot is
fired at the new log (`readSlot_fire`); every other proposal slot keeps its results
(`propSlot_grow`). -/

/-- A position of a log grown by one entry: one of the old log's, or the new entry. -/
theorem getElem?_snoc_cases {A : Type _} {l : List A} {e e' : A} {m : Nat}
    (h : (l ++ [e])[m]? = some e') :
    (m < l.length ∧ l[m]? = some e' ∧ (l ++ [e]).take m = l.take m) ∨
    (m = l.length ∧ e' = e ∧ (l ++ [e]).take m = l) := by
  by_cases hm : m < l.length
  · left
    refine ⟨hm, ?_, List.take_append_of_le_length (Nat.le_of_lt hm)⟩
    rw [List.getElem?_append_left hm] at h; exact h
  · right
    have hle : l.length ≤ m := Nat.le_of_not_lt hm
    rw [List.getElem?_append_right hle] at h
    have h0 : m - l.length = 0 := by
      cases hk : m - l.length with
      | zero => rfl
      | succ k => rw [hk] at h; simp at h
    have hml : m = l.length := by omega
    subst hml
    refine ⟨rfl, ?_, List.take_left⟩
    rw [h0] at h; simp at h; exact h.symm

theorem take_snoc_le {A : Type _} (l : List A) (e : A) (n : Nat) (h : n ≤ l.length) :
    (l ++ [e]).take n = l.take n :=
  List.take_append_of_le_length h

/-- A committed entry with the client data `d` was deposited. -/
theorem entDataIs_deposited (γ : RaftNames) (e : EntryM) (d : List w8) :
    entDataIs (GF := GF) γ e (some d) ⊢ deposited γ d := by
  unfold entDataIs propDataIs
  iintro ⟨⟨-, #H⟩, -⟩
  iexact H

/-- A proposal slot keeps its results as the log grows by an entry whose data is not its. -/
theorem propSlot_grow (γ : RaftNames) (d : List w8) (p : PropRec) (l : List EntryM)
    (e : EntryM) (o : Option (List w8)) (Hne : o ≠ some d) :
    ⊢ entDataIs (GF := GF) γ e o -∗ propSlot γ d p l -∗ propSlot γ d p (l ++ [e]) := by
  unfold propSlot
  iintro #He ⟨%Q, #Hsp, #Hres, Hau⟩
  iexists Q
  iframe Hsp
  isplitr
  · imodintro
    iintro %m %e' %Hm #He'
    rcases getElem?_snoc_cases Hm with ⟨-, Hl, Ht⟩ | ⟨-, rfl, -⟩
    · rw [Ht]; iapply Hres $$ %m %e' %Hl He'
    · ihave %Ho := entDataIs_agree γ e' o (some d) $$ He He'
      exact absurd Ho Hne
  -- (D21 M6) the update: as it was; an occurrence stays one
  cases hb : p.2.2
  · simp only [hb, Bool.false_eq_true, ↓reduceIte]
    iexact Hau
  · simp only [hb, ↓reduceIte]
    icases Hau with (Hau | #Hocc)
    · ileft; iexact Hau
    · iright
      unfold propOcc
      icases Hocc with ⟨%m0, %e0, %Hm0, #He0⟩
      iexists m0, e0
      iframe He0
      ipureintro
      rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp Hm0).1]
      exact Hm0

/-- The new entry's own proposal slot, fired: its result at the log before is added; (D21 M6)
the update kept if persistent, else the entry's occurrence recorded. -/
theorem propSlot_fire (γ : RaftNames) (d : List w8) (p : PropRec) (l : List EntryM)
    (e : EntryM) (Q : List EntryM → IProp GF) :
    ⊢ savedPredOwn p.1 DFrac.discard Q -∗ entDataIs γ e (some d) -∗
      (if p.2.2 then iprop(emp) else propAu γ d Q) -∗ □ Q l -∗
      □ (∀ (m : Nat) (e' : EntryM), ⌜l[m]? = some e'⌝ -∗ entDataIs γ e' (some d) -∗
         □ Q (l.take m)) -∗
      propSlot γ d p (l ++ [e]) := by
  iintro #Hsp #He Hau #HQ #Hres
  unfold propSlot
  iexists Q
  iframe Hsp
  isplitr
  · imodintro
    iintro %m %e' %Hm #He'
    rcases getElem?_snoc_cases Hm with ⟨-, Hl, Ht⟩ | ⟨-, -, Ht⟩
    · rw [Ht]; iapply Hres $$ %m %e' %Hl He'
    · rw [Ht]; iexact HQ
  cases hb : p.2.2
  · simp only [hb, Bool.false_eq_true, ↓reduceIte] at *
    iexact Hau
  · simp only [hb, ↓reduceIte]
    iright
    unfold propOcc
    iexists l.length, e
    iframe He
    ipureintro; simp

/-- A read slot, fired at the log grown by one entry. -/
theorem readSlot_fire (γ : RaftNames) (r : GName × List EntryM) (l : List EntryM)
    (e : EntryM) :
    ⊢ readSlot (GF := GF) γ r l -∗ ghostVar γ.reRLog (1 : Qp).half (l ++ [e]) ={⊤ \ ↑raftN}=∗
      ghostVar γ.reRLog (1 : Qp).half (l ++ [e]) ∗ readSlot γ r (l ++ [e]) := by
  unfold readSlot
  iintro ⟨%Qr, #Hsp, #Hau, %Hpre, #Hres⟩ Hv
  imod readAu_fire γ Qr (l ++ [e]) $$ Hau Hv with ⟨Hv, #HQ⟩
  imodintro
  iframe Hv
  iexists Qr
  iframe Hsp Hau
  isplitr
  · ipureintro; exact Hpre.trans (List.prefix_append _ _)
  imodintro
  iintro %n %Hn
  by_cases hn : n ≤ l.length
  · rw [take_snoc_le l e n hn]
    iapply Hres $$ %n
    ipureintro; exact ⟨Hn.1, hn⟩
  · have : n = (l ++ [e]).length := by simp at Hn ⊢; omega
    rw [this, List.take_length]
    iexact HQ

/-- A step over a list, threading a resource `R` through the elements' updates. -/
theorem bigSepL_fupd_thread {A : Type _} (E : CoPset) (R : IProp GF) (Φ Ψ : A → IProp GF) :
    ∀ (l : List A),
    ⊢ □ (∀ x, R -∗ Φ x ={E}=∗ R ∗ Ψ x) -∗ R -∗ ([∗list] x ∈ l, Φ x) ={E}=∗
      R ∗ [∗list] x ∈ l, Ψ x
  | [] => by
    iintro #_ HR _
    imodintro
    iframe HR
    iapply (BigSepL.bigSepL_nil (Φ := fun _ x => Ψ x)).2
    iempintro
  | x :: xs => by
    iintro #Hstep HR Hl
    icases (BigSepL.bigSepL_cons (Φ := fun _ x => Φ x)).1 $$ Hl with ⟨Hx, Hl⟩
    imod Hstep $$ %x HR Hx with ⟨HR, Hx⟩
    imod bigSepL_fupd_thread E R Φ Ψ xs $$ Hstep HR Hl with ⟨HR, Hl⟩
    imodintro
    iframe HR
    iapply (BigSepL.bigSepL_cons (Φ := fun _ x => Ψ x)).2
    iframe Hx Hl

/-- The same over a map. -/
theorem bigSepM_fupd_thread {K V : Type} [DecidableEq K] [Pos.Countable K] (E : CoPset)
    (R : IProp GF) (Φ Ψ : K → V → IProp GF) (M : GMap K V) :
    ⊢ □ (∀ k v, R -∗ Φ k v ={E}=∗ R ∗ Ψ k v) -∗ R -∗ ([∗map] k ↦ v ∈ M, Φ k v) ={E}=∗
      R ∗ [∗map] k ↦ v ∈ M, Ψ k v := by
  iintro #Hstep HR HM
  ihave HM := (BigSepM.bigSepM_toList (Φ := Φ) (m := M)).1 $$ HM
  imod bigSepL_fupd_thread E R (fun kv : K × V => Φ kv.1 kv.2) (fun kv => Ψ kv.1 kv.2)
    (Std.toList M) $$ [] HR HM with ⟨HR, HM⟩
  · imodintro
    iintro %kv HR Hx
    iapply Hstep $$ %kv.1 %kv.2 HR Hx
  imodintro
  iframe HR
  iapply (BigSepM.bigSepM_toList (Φ := Ψ) (m := M)).2 $$ HM

/-- Every read slot, fired at the log grown by one entry. -/
theorem readsReg_fire (γ : RaftNames) (l : List EntryM) (e : EntryM)
    (RR : GMap (List w8) (GName × List EntryM)) :
    ⊢ readsReg (GF := GF) γ l RR -∗ ghostVar γ.reRLog (1 : Qp).half (l ++ [e]) ={⊤ \ ↑raftN}=∗
      ghostVar γ.reRLog (1 : Qp).half (l ++ [e]) ∗ readsReg γ (l ++ [e]) RR := by
  unfold readsReg
  iintro ⟨Ha, Hs⟩ Hv
  imod bigSepM_fupd_thread (⊤ \ ↑raftN) iprop(ghostVar γ.reRLog (1 : Qp).half (l ++ [e]))
    (fun c r => iprop(readSlot γ r l ∗ rdFresh γ c))
    (fun c r => iprop(readSlot γ r (l ++ [e]) ∗ rdFresh γ c)) RR $$ [] Hv Hs with ⟨Hv, Hs⟩
  · imodintro
    iintro %c %r Hv ⟨Hsl, Hfr⟩
    imod readSlot_fire γ r l e $$ Hsl Hv with ⟨Hv, Hsl⟩
    imodintro
    iframe Hv Hsl Hfr
  imodintro
  iframe Hv Ha Hs

/-- What the commit moves, at the global committed log `l`: its authority, its entries' data,
the invariant's half of `reRLog` and the registries. -/
def commitSt (γ : RaftNames) (l : List EntryM) : IProp GF :=
  iprop(ownCommitted γ l ∗ entsData γ l ∗ ghostVar γ.reRLog (1 : Qp).half l ∗ regsAt γ l)

theorem fire_one (γ : RaftNames) (G : List EntryM) (m : Nat) (e : EntryM) :
    PlogWf base0 G → G[m]? = some e →
    ⊢ logRecs (GF := GF) γ base0 G -∗ commitSt γ (G.take m) ={⊤ \ ↑raftN}=∗
      commitSt γ (G.take (m + 1)) := by
  intro Hwf He
  iintro #Hr Hst
  unfold commitSt
  icases Hst with ⟨HP, #Hds, Hv, Hregs⟩
  have Hei := Hwf _ _ He
  rw [base0_index] at Hei
  push_cast at Hei
  have Hrng := uint_Z_lt e.Index'
  have Hlt := (List.getElem?_eq_some_iff.mp He).1
  icases logRecs_lookup γ G m e He (by omega) $$ Hr with ⟨%pt, -, #Her⟩
  ihave #Hed := isEntryR_data γ e pt $$ Her
  unfold entData
  icases Hed with ⟨%o, #Ho⟩
  have Htk : G.take (m + 1) = G.take m ++ [e] := by rw [List.take_add_one, He]; rfl
  have Hidx : uint.Z e.Index' = ((G.take m).length : Int) + 1 := by
    rw [List.length_take]; push_cast; omega
  rw [Htk]
  imod ownCommitted_extend γ (G.take m) (G.take m ++ [e]) (List.prefix_append _ _) $$ HP
    with ⟨HP, -⟩
  ihave #Hds' : entsData γ (G.take m ++ [e]) $$ []
  · unfold entsData
    icases Hds with ⟨%ods, #Hds⟩
    iexists ods ++ [o]
    iapply (BigSepL2.bigSepL2_snoc (Φ := fun _ e o => entDataIs (GF := GF) γ e o)).2
    iframe Hds Ho
  unfold regsAt
  icases Hregs with ⟨%R, %RR, Hprops, Hreads, #Hnoop⟩
  unfold propsOwn
  icases Hprops with ⟨Hra, Hs⟩
  -- the entry's own update moves the log; the other proposal slots keep their results
  ihave Hfire : |={⊤ \ ↑raftN}=> ghostVar γ.reRLog (1 : Qp).half (G.take m ++ [e]) ∗
      ghostMapAuth γ.reProps 1 R ∗
      [∗map] d ↦ p ∈ R, propSlot γ d p (G.take m ++ [e]) ∗ propFresh γ d $$ [Hv Hra Hs]
  · cases o with
    | none =>
      imod noopAu_fire γ (G.take m) e Hidx $$ Hnoop Ho Hv with Hv
      imodintro
      iframe Hv Hra
      iapply BigSepM.bigSepM_impl $$ Hs
      imodintro
      iintro %d %p %_ ⟨Hsl, Hfr⟩
      iframe Hfr
      iapply propSlot_grow γ d p (G.take m) e none (by simp) $$ Ho Hsl
    | some d =>
      ihave #Hdep := entDataIs_deposited γ e d $$ Ho
      unfold deposited
      icases Hdep with ⟨%p, #Hdq⟩
      icases ghost_map_lookup $$ Hra Hdq with %HRd
      icases (BigSepM.bigSepM_delete (Φ := fun d (p : PropRec) =>
        iprop(propSlot (GF := GF) γ d p (G.take m) ∗ propFresh γ d)) HRd).1 $$ Hs
        with ⟨⟨Hsl, Hfr⟩, Hs⟩
      iunfold propSlot at Hsl
      icases Hsl with ⟨%Q, #Hsp, #Hres, Hau⟩
      -- the update: fired (persistent, or (D21 M6) at most once: a second occurrence of a
      -- proposal deposited once would be at its one index, `propIdx_agree`)
      ihave Hfired : |={⊤ \ ↑raftN}=> ghostVar γ.reRLog (1 : Qp).half (G.take m ++ [e]) ∗ □ Q (G.take m) ∗
          (if p.2.2 then iprop(emp) else propAu γ d Q) $$ [Hau Hv]
      · cases hb : p.2.2
        · simp only [hb, Bool.false_eq_true, ↓reduceIte]
          icases Hau with #Hau
          imod propAu_fire γ d Q (G.take m) e Hidx $$ Hau Ho Hv with ⟨Hv, #HQ⟩
          imodintro
          iframe Hv HQ Hau
        · simp only [hb, ↓reduceIte]
          icases Hau with (Hau | #Hocc)
          · imod propAu1_fire γ d Q (G.take m) e Hidx $$ Hau Ho Hv with ⟨Hv, #HQ⟩
            imodintro
            iframe Hv HQ
          · iunfold propOcc at Hocc
            icases Hocc with ⟨%m0, %e0, %Hm0, #He0⟩
            ihave #Hon : propOnce γ d $$ []
            · unfold propOnce; iexists p; iframe Hdq; ipureintro; exact hb
            ihave #Hi0 := entDataIs_idx γ e0 d $$ Hon He0
            ihave #Hi := entDataIs_idx γ e d $$ Hon Ho
            ihave %Hii := propIdx_agree γ d _ _ $$ Hi0 Hi
            have Hm0l := (List.getElem?_eq_some_iff.mp Hm0).1
            rw [List.length_take] at Hm0l
            have HG0 : G[m0]? = some e0 := by
              rw [← Hm0, List.getElem?_take_of_lt (by omega)]
            have He0i := Hwf _ _ HG0
            rw [base0_index] at He0i
            push_cast at He0i
            rw [Hii] at He0i
            exfalso; omega
      imod Hfired with ⟨Hv, #HQ, Hau⟩
      imodintro
      iframe Hv Hra
      iapply (BigSepM.bigSepM_delete (Φ := fun d (p : PropRec) =>
        iprop(propSlot (GF := GF) γ d p (G.take m ++ [e]) ∗ propFresh γ d)) HRd).2
      isplitl [Hfr Hau]
      · iframe Hfr
        iapply propSlot_fire γ d p (G.take m) e Q $$ Hsp Ho Hau HQ Hres
      iapply BigSepM.bigSepM_impl $$ Hs
      imodintro
      iintro %d' %p' %Hk ⟨Hsl, Hfr⟩
      have Hne : d' ≠ d := (Iris.Std.LawfulPartialMap.get?_delete_some_iff.mp Hk).1.symm
      iframe Hfr
      iapply propSlot_grow γ d' p' (G.take m) e (some d)
        (by intro h; cases h; exact Hne rfl) $$ Ho Hsl
  imod Hfire with ⟨Hv, Hra, Hs⟩
  -- then every read, at the new log
  imod readsReg_fire γ (G.take m) e RR $$ Hreads Hv with ⟨Hv, Hreads⟩
  imodintro
  iframe HP Hds' Hv
  iexists R, RR
  iframe Hreads Hnoop Hra Hs

theorem fire_upto (γ : RaftNames) (G : List EntryM) (d m : Nat) :
    PlogWf base0 G → m + d ≤ G.length →
    ⊢ logRecs (GF := GF) γ base0 G -∗ commitSt γ (G.take m) ={⊤ \ ↑raftN}=∗
      commitSt γ (G.take (m + d)) := by
  induction d generalizing m with
  | zero =>
    intro _ _
    iintro #Hr Hs
    imodintro
    iexact Hs
  | succ d IH =>
    intro Hwf Hle
    iintro #Hr Hs
    obtain ⟨e, He⟩ : ∃ e, G[m]? = some e := ⟨G[m]'(by omega), List.getElem?_eq_getElem _⟩
    imod fire_one γ G m e Hwf He $$ Hr Hs with Hs
    rw [show m + (d + 1) = (m + 1) + d by omega]
    iapply IH (m + 1) Hwf (by omega) $$ Hr Hs

/-- `fire_upto` with both halves of the commit invariant open, from a ghost step. -/
theorem fire_upto_open (γ : RaftNames) (G : List EntryM) (d m : Nat) :
    PlogWf base0 G → m + d ≤ G.length →
    ⊢ logRecs (GF := GF) γ base0 G -∗ commitSt γ (G.take m) ={(⊤ \ ↑raftRegN) \ ↑raftLogN}=∗
      commitSt γ (G.take (m + d)) := by
  intro Hwf Hle
  iintro #Hr Hs
  iapply (fupd_mask_mono (P := commitSt (GF := GF) γ (G.take (m + d))) raftN_open_sub)
  iapply fire_upto γ G d m Hwf Hle $$ Hr Hs

/-- The two quarters of `reRLog` the commit invariant's halves hold agree, and make its
half. -/
theorem rlq_join (γ : RaftNames) (l1 l2 : List EntryM) :
    ⊢ ghostVar (GF := GF) γ.reRLog rlq l1 -∗ ghostVar γ.reRLog rlq l2 -∗
      ⌜l1 = l2⌝ ∗ ghostVar γ.reRLog (1 : Qp).half l1 := by
  iintro H1 H2
  ihave %Heq := ghostVar_agree γ.reRLog l1 rlq l2 rlq $$ H1 H2
  subst Heq
  isplitr; · ipureintro; rfl
  rw [← rlq_add]
  iframe H1 H2

theorem rlq_split (γ : RaftNames) (l : List EntryM) :
    ⊢ ghostVar (GF := GF) γ.reRLog (1 : Qp).half l -∗
      ghostVar γ.reRLog rlq l ∗ ghostVar γ.reRLog rlq l := by
  iintro H
  rw [← rlq_add]
  iapply ghostVar_split $$ H

/-- Committing: a new commit fact `cq γ t n G` extends the global log to `G`'s first `n`
entries, or finds it already past them. Inside the invariant, the global log is the
first `n0` entries of the log `G0` of an earlier commit fact; the two commit facts agree
below both (`cq_agree`, from the vote table), so -- the logs having records -- the two
prefixes are prefixes of one another (`full_take_eq`). The extension is entry by entry,
firing the deposited updates (`fire_upto`) -- with both halves of the invariant open: the
registry half by the ghost step (its contents `regsOwn`, held across the step since it took
`£ 1` to open them), the log half here; the updates' outer mask `⊤ ∖ ↑raftN` excludes
both. -/
theorem commit_extend (γ : RaftNames) (t n : w64) (G : List EntryM) (ldr : w64) :
    ⊢ raftCommitInv (GF := GF) γ -∗ regsOwn γ -∗ cq γ t n G -∗ isLeader γ ldr t -∗
      cmtLb γ ldr t n ={⊤ \ ↑raftRegN}=∗
      regsOwn γ ∗ isCommitted γ (G.take (uint.Z n).toNat) := by
  iintro #Hinv Hregs #Hcq #Hldr #Hclb
  ihave #Hli := raftCommitInv_log γ $$ Hinv
  unfold raftLogInv raftLogInvBody
  iinv Hli with ⟨%P, >HP, >#Hj, >Htbl, >Hwt, >Hrest⟩ Hclose
  unfold logRest regsOwn
  icases Hrest with ⟨#Hds, Hq1⟩
  icases Hregs with ⟨%l', Hq2, Hregs⟩
  icases rlq_join γ P l' $$ Hq1 Hq2 with ⟨%Heq, Hv⟩
  subst Heq
  icases cq_full γ t n G $$ Hcq with ⟨%HwG, #HrG⟩
  icases cq_base γ _ _ _ $$ Hcq with ⟨%HGn, -⟩
  have HnG := (plogTermAt_some_range _ _ _ _ HGn).2
  unfold plogLastIndexZ at HnG
  rw [base0_index] at HnG
  -- the log after: extended to `G`'s first `n` entries, or already past them
  ihave Hext : |={(⊤ \ ↑raftRegN) \ ↑raftLogN}=> ∃ P', commitSt γ P' ∗ committedJust γ P' ∗
      votesTbl γ ∗ isCommitted γ (G.take (uint.Z n).toNat) $$ [HP Hv Hregs Htbl]
  · unfold committedJust
    icases Hj with (%HP0 | ⟨%t0, %n0, %G0, %ldr0, #Hcq0, %HP0, #Hldr0, #Hclb0⟩)
    · -- (2026-10-16, stage R8b) the global log is the bootstrap log, which `G` starts with:
      -- extend from its end, or it is already past the new prefix
      obtain ⟨HP0, HwB⟩ := HP0
      subst HP0
      icases cq_boot γ t n G $$ Hcq with %HbG
      have HbGl := HbG.1.length_le
      by_cases Hle : (γ.reBoot.length : Int) ≤ uint.Z n
      · have Htk : G.take γ.reBoot.length = γ.reBoot := by
          rw [take_of_prefix HbG.1 (Nat.le_refl _)]; exact List.take_length
        ihave Hst : commitSt γ (G.take γ.reBoot.length) $$ [HP Hv Hregs]
        · unfold commitSt; rw [Htk]; iframe HP Hds Hv Hregs
        imod fire_upto_open γ G ((uint.Z n).toNat - γ.reBoot.length) γ.reBoot.length HwG
          (by omega) $$ HrG Hst with Hst
        rw [show γ.reBoot.length + ((uint.Z n).toNat - γ.reBoot.length) = (uint.Z n).toNat
          by omega]
        ihave #Hc : isCommitted γ (G.take (uint.Z n).toNat) $$ [Hst]
        · unfold commitSt
          icases Hst with ⟨HP, -⟩
          iapply ownCommitted_lb γ _ $$ HP
        imodintro
        iexists _
        iframe Hst Hc Htbl
        iright
        iexists t, n, G, ldr
        iframe Hcq Hldr Hclb
        ipureintro; rfl
      · ihave #Hc0 := ownCommitted_lb γ _ $$ HP
        imodintro
        iexists γ.reBoot
        isplitl [HP Hv Hregs]
        · unfold commitSt; iframe HP Hds Hv Hregs
        iframe Htbl
        isplitr
        · ileft; ipureintro; exact ⟨rfl, HwB⟩
        iapply isCommitted_mono γ _ _
          (by rw [take_of_prefix HbG.1 (by omega)]; exact List.take_prefix _ _) $$ Hc0
    · subst HP0
      icases cq_full γ t0 n0 G0 $$ Hcq0 with ⟨%HwG0, #HrG0⟩
      icases cq_base γ _ _ _ $$ Hcq0 with ⟨%HG0n, -⟩
      by_cases Hle : uint.Z n0 ≤ uint.Z n
      · -- the new prefix is longer: extend, firing the registries
        icases cq_agree γ t0 n0 t n n0 G0 G (Int.le_refl _) Hle $$ Htbl Hcq0 Hcq with %Hag
        icases full_take_eq γ G0 G n0 HwG0 HwG (by rw [HG0n]; rfl) (Hag n0 (Int.le_refl _))
          $$ HrG0 HrG with %Htk
        ihave Hst : commitSt γ (G.take (uint.Z n0).toNat) $$ [HP Hv Hregs]
        · unfold commitSt; rw [← Htk]; iframe HP Hds Hv Hregs
        imod fire_upto_open γ G ((uint.Z n).toNat - (uint.Z n0).toNat) (uint.Z n0).toNat HwG
          (by omega) $$ HrG Hst with Hst
        rw [show (uint.Z n0).toNat + ((uint.Z n).toNat - (uint.Z n0).toNat) = (uint.Z n).toNat
          by omega]
        ihave #Hc : isCommitted γ (G.take (uint.Z n).toNat) $$ [Hst]
        · unfold commitSt
          icases Hst with ⟨HP, -⟩
          iapply ownCommitted_lb γ _ $$ HP
        imodintro
        iexists _
        iframe Hst Hc Htbl
        iright
        iexists t, n, G, ldr
        iframe Hcq Hldr Hclb
        ipureintro; rfl
      · -- the global log is already past it
        icases cq_agree γ t0 n0 t n n G0 G (by omega) (Int.le_refl _) $$ Htbl Hcq0 Hcq with %Hag
        icases full_take_eq γ G0 G n HwG0 HwG
          (full_term_at_some G0 n n0 (by rw [HG0n]; rfl) (by omega)) (Hag n (Int.le_refl _))
          $$ HrG0 HrG with %Htk
        ihave #Hc0 := ownCommitted_lb γ _ $$ HP
        imodintro
        iexists (G0.take (uint.Z n0).toNat)
        isplitl [HP Hv Hregs]
        · unfold commitSt; iframe HP Hds Hv Hregs
        iframe Htbl
        isplitr
        · iright
          iexists t0, n0, G0, ldr0
          iframe Hcq0 Hldr0 Hclb0
          ipureintro; rfl
        iapply isCommitted_mono γ _ _ (by rw [← Htk]; exact take_prefix_le _ _ _ (by omega)) $$ Hc0
  imod Hext with ⟨%P', Hst, #Hj', Htbl, #Hc⟩
  unfold commitSt
  icases Hst with ⟨HP, #Hds', Hv, Hregs⟩
  icases rlq_split γ P' $$ Hv with ⟨Hq1, Hq2⟩
  imod Hclose $$ [HP Htbl Hwt Hq1] with -
  · inext
    iexists P'
    iframe HP Hj' Htbl Hwt Hds' Hq1
  imodintro
  iframe Hc
  iexists P'
  iframe Hq2 Hregs
/-- A vote, recorded in the node's half of its vote map and in the table, at any mask where the
log half of the commit invariant can be opened (2026-10-20: the witness's storage records its
votes inside its own invariant). -/
theorem vote_insertE (γ : RaftNames) (E : CoPset) (HE : (↑raftLogN : CoPset) ⊆ E) (id : w64)
    (γv : GName) (voted : GMap w64 w64) (T c : w64) :
    γ.reVotes !! id = some γv → voted !! T = none →
    ⊢ raftCommitInv (GF := GF) γ -∗ voteJust γ id T c -∗ ghostMapAuth γv (1 : Qp).half voted
      ={E}=∗
      ghostMapAuth γv (1 : Qp).half (<[T := c]> voted) ∗ T ↪[γv]□ c := by
  intro Hγv Hfree
  iintro #Hinv #Hj Ha
  ihave #Hli := raftCommitInv_log γ $$ Hinv
  unfold raftLogInv raftLogInvBody
  iinv Hli with ⟨%P, HP, Hjust, >Htbl, Hrest⟩ Hclose
  imod votesTbl_insert γ id γv voted T c Hγv Hfree $$ Hj Htbl Ha with ⟨Htbl, Ha, #Hf⟩
  imod Hclose $$ [HP Hjust Htbl Hrest] with -
  · inext
    iexists P
    iframe
  imodintro
  isplitl [Ha]
  · iexact Ha
  · iexact Hf

/-- `vote_insertE` at the mask a node's step runs at. -/
theorem vote_insert (γ : RaftNames) (id : w64) (γv : GName) (voted : GMap w64 w64)
    (T c : w64) :
    γ.reVotes !! id = some γv → voted !! T = none →
    ⊢ raftCommitInv (GF := GF) γ -∗ voteJust γ id T c -∗ ghostMapAuth γv (1 : Qp).half voted
      ={⊤ \ ↑raftRegN}=∗
      ghostMapAuth γv (1 : Qp).half (<[T := c]> voted) ∗ T ↪[γv]□ c :=
  vote_insertE γ (⊤ \ ↑raftRegN) raftLogN_sub id γv voted T c


/-! ### The winners table (2026-10-14, reconfiguration stage B4)

A candidate that wins `T` adds its entry to the winners table (`winTbl`, in `raftCommitInv`)
only after showing that every entry of `T` already there is its own: election safety is proved
at win time (the paper's `win_fresh`, section 5), and `isLeader_unique` is the table's
agreement. The table and the new winner's quorums meet in a voter (`win_fresh`), who voted
once in `T` (`isVote_agree`), so the entry's winner is the new one, whose quorum is frozen in
its `reWins` map. -/

/-- The new winner's quorum meets the quorum of any entry of its term (the static instance:
the two recorded configurations overlap, `CfgAt.overlap`). B5: by cases on the two
configuration indices -- adjacent, `fold_adjacent`; far, a contradiction through `lc_adj` at a
witness of the campaign record and I1 at a campaign, which for an older new winner needs the
existing winner's `lc_core` (the paper's repair 2). -/
theorem win_fresh (γ : RaftNames) (id T : w64) (c : CfgM) (V : GSet w64) :
    ⊢ votesTbl (GF := GF) γ -∗ isWinCore γ id T c V -∗
      ∀ (id' : w64) (c' : CfgM) (q' : GSet w64),
        isWinCore γ id' T c' q' -∗ T ↪[γ.reTbl]□ (((id', c'), q') : WinRec) -∗
        ⌜∃ v, v ∈ V ∧ v ∈ q'⌝ := by
  iintro HS #H %id' %c' %q' #H' #Hf'
  ihave #Hwin' : isWin γ id' T q' $$ []
  · unfold isWin; iexists c'; iframe H' Hf'
  ihave #Hl' : isLeader γ id' T $$ []
  · unfold isLeader; iexists q'; iexact Hwin'
  iunfold isWinCore at H H'
  icases H with ⟨%γw, %F0, %k, %Hw, #HcK, -, #Hvs, -⟩
  icases H' with ⟨%γw', %F0', %k', %Hw', #HcK', -, #Hvs', -⟩
  cases HD : γ.dyn with
  | none =>
    ipureintro
    exact CfgAt.overlap (RaftNames.dyn_eq_none.1 HD) Hw.2.2 Hw'.2.2 V q' Hw.2.1 Hw'.2.1
  | some D =>
  have Hdyn : γ.reDyn ≠ none := fun h => by rw [RaftNames.dyn_none h] at HD; cases HD
  -- the induction hypothesis at `T`: `lc_core` below it
  have IH : LcIH (GF := GF) γ T := fun T' t' n' F' c' F0' G' h1 h2 h3 h4 =>
    lc_core γ ((uint.Z T').toNat + 1) T' t' n' F' c' F0' G' (by omega) h2 h3 h4
  -- both campaigns' dynamic facts, from a vote of each quorum
  ihave #Hc : isCamp γ id T F0 $$ []
  · iapply isCampK_camp $$ HcK
  ihave #Hc' : isCamp γ id' T F0' $$ []
  · iapply isCampK_camp $$ HcK'
  icases winner_campDyn γ id T V F0 k Hdyn (CfgAt.member Hw.2.2 Hw.2.1) $$ HS Hvs HcK
    with ⟨%tmc, %Hcp, #HrF0, #HcmF0⟩
  icases winner_campDyn γ id' T q' F0' k' Hdyn (CfgAt.member Hw'.2.2 Hw'.2.1) $$ HS Hvs' HcK'
    with ⟨%tmc', %Hcp', #HrF0', #HcmF0'⟩
  icases isCamp_ok γ id T F0 $$ Hc with %Hcok
  icases isCamp_ok γ id' T F0' $$ Hc' with %Hcok'
  ihave #HcF0 := isCampK_committed γ id T F0 k $$ HcK
  ihave #HcF0' := isCampK_committed γ id' T F0' k' $$ HcK'
  icases isCommitted_agree γ _ _ $$ HcF0 HcF0' with %Hpre
  by_cases Hadj : confCount (F0.take (uint.Z k).toNat) ≤ confCount (F0'.take (uint.Z k').toNat) + 1 ∧
      confCount (F0'.take (uint.Z k').toNat) ≤ confCount (F0.take (uint.Z k).toNat) + 1
  · ipureintro
    exact CfgAt.overlap_adj Hpre Hadj.2 Hadj.1 Hw.2.2 Hw'.2.2 V q' Hw.2.1 Hw'.2.1
  rcases (by omega : confCount (F0'.take (uint.Z k').toNat) + 2 ≤ confCount (F0.take (uint.Z k).toNat) ∨
      confCount (F0.take (uint.Z k).toNat) + 2 ≤ confCount (F0'.take (uint.Z k').toNat)) with Hfar | Hfar
  · -- the table's winner is older: the new winner's campaign witness, adjacent to it
    obtain ⟨k2, hk2, hp2, hc2⟩ :=
      exists_confPos F0 (uint.Z k).toNat (confCount (F0'.take (uint.Z k').toNat) + 1) (by omega)
    ihave #Hws := commitIn_w γ F0 k tmc Hdyn $$ HcmF0
    iunfold witsB at Hws
    ihave Hw2 := Hws $$ %k2 %(And.intro hp2 hk2)
    icases Hw2 with ⟨%tw, %nw, %Gw, %aw, %cw, %qw, %Hwo, #Hcqw⟩
    icases cqAt_parts γ tw nw Gw aw cw qw $$ Hcqw with ⟨%Hpw, -, #HcGw, #Hackw, -⟩
    icases isCommitted_agree γ _ _ $$ HcGw HcF0' with %Hpre2
    obtain ⟨Htw, Hnw, Haw, Hag, Hcw⟩ := Hwo
    have Hcw' : confCount (Gw.take (uint.Z aw).toNat) = confCount (F0'.take (uint.Z k').toNat) + 1 := by
      rw [Hcw, hc2]
    have Hmeet := meet_nowit (RaftNames.wit_dyn Hdyn) (CfgAt.overlap_adj Hpre2 (by omega) (by omega)
      Hpw.2.2.1 Hw'.2.2 qw q' Hpw.2.2.2 Hw'.2.1)
    ihave #Hcqw' := cqAt_cq γ _ _ _ _ _ _ $$ Hcqw
    icases lc_adj γ T tw nw Gw id' F0' F0' qw q' IH (by omega) Hcok'.1 (camp_last T F0' Hcok') Hmeet
      $$ HS Hcqw' Hackw Hwin' Hc' HrF0' with %HF0nw
    icases cq_full γ tw nw Gw $$ Hcqw' with ⟨%HwGw, #HrGw⟩
    icases full_take_eq γ Gw F0' nw HwGw Hcok'.1 (by rw [Hpw.1]; rfl) (by rw [Hpw.1, HF0nw])
      $$ HrGw HrF0' with %Htk
    ipureintro
    exfalso
    refine far_older Hcp'.2.1 ?_ hp2 hc2
    rw [take_agree_le Htk.symm (by omega), Hag]
  · -- the new winner is older (the paper's repair 2): the table's winner's campaign witness,
    -- adjacent to the new winner, through `lc_adj_gen` -- a vote for the new winner cast
    -- knowing the leader of `T` knew the table's winner, whose logs agree with the witness by
    -- its `lc_core`
    obtain ⟨k2, hk2, hp2, hc2⟩ :=
      exists_confPos F0' (uint.Z k').toNat (confCount (F0.take (uint.Z k).toNat) + 1) (by omega)
    ihave #Hws := commitIn_w γ F0' k' tmc' Hdyn $$ HcmF0'
    iunfold witsB at Hws
    ihave Hw2 := Hws $$ %k2 %(And.intro hp2 hk2)
    icases Hw2 with ⟨%tw, %nw, %Gw, %aw, %cw, %qw, %Hwo, #Hcqw⟩
    icases cqAt_parts γ tw nw Gw aw cw qw $$ Hcqw with ⟨%Hpw, -, #HcGw, #Hackw, -⟩
    icases isCommitted_agree γ _ _ $$ HcGw HcF0 with %Hpre2
    obtain ⟨Htw, Hnw, Haw, Hag, Hcw⟩ := Hwo
    have Hcw' : confCount (Gw.take (uint.Z aw).toNat) = confCount (F0.take (uint.Z k).toNat) + 1 := by
      rw [Hcw, hc2]
    have Hmeet := meet_nowit (RaftNames.wit_dyn Hdyn) (CfgAt.overlap_adj Hpre2 (by omega) (by omega)
      Hpw.2.2.1 Hw.2.2 qw V Hpw.2.2.2 Hw.2.1)
    ihave #Hcqw' := cqAt_cq γ _ _ _ _ _ _ $$ Hcqw
    icases cq_full γ tw nw Gw $$ Hcqw' with ⟨%HwGw, #HrGw⟩
    icases lc_adj_gen γ T tw nw Gw id F0 F0 qw V IH (by omega) Hcok.1 (camp_last T F0 Hcok) Hmeet
      $$ HS Hcqw' Hackw Hvs [] Hc HrF0 with %HF0nw
    · imodintro
      iintro %ldr %qd #Hwd %-
      icases isWin_tbl_agree γ ldr id' T qd q' $$ Hwd Hwin' with %Heq
      obtain ⟨rfl, rfl⟩ := Heq
      imodintro
      iintro %X' %j' HS2 #HX' %Hj'
      icases leadFull_camp γ T X' $$ HX' with ⟨%ldr'', %F0'', #Hl'', #Hc'', %Hpre''⟩
      icases isLeader_unique γ ldr'' ldr T $$ Hl'' Hl' with %Hle
      subst Hle
      icases isCamp_agree γ ldr'' T F0'' F0' $$ Hc'' Hc' with %HF0e
      subst HF0e
      icases leadFull_wf γ T X' $$ HX' with ⟨%HwX', #HrX'⟩
      icases lc_core γ ((uint.Z T).toNat + 1) T tw nw Gw ldr'' F0'' X' (by omega) (by omega) HwX'.1
        (prefix_camp_last T F0'' X' Hcok' Hpre'') $$ HS2 Hcqw' Hl' Hc' HrX' with %HXnw
      icases full_match γ X' Gw nw HwX'.1 HwGw (by rw [HXnw]; rfl) (by rw [HXnw, Hpw.1])
        $$ HrX' HrGw with %Hm
      ipureintro; exact Hm j' Hj'.1
    icases full_take_eq γ Gw F0 nw HwGw Hcok.1 (by rw [Hpw.1]; rfl) (by rw [Hpw.1, HF0nw])
      $$ HrGw HrF0 with %Htk
    ipureintro
    exfalso
    refine far_older Hcp.2.1 ?_ hp2 hc2
    rw [take_agree_le Htk.symm (by omega), Hag]

/-- Adding a winner to the table, given that its quorum meets that of any entry of its term
(`win_fresh`): an existing entry of the term is the same winner with the same quorum. -/
theorem winTbl_insert (γ : RaftNames) (id T : w64) (c : CfgM) (V : GSet w64) :
    ⊢ winTbl (GF := GF) γ -∗ votesTbl γ -∗ isWinCore γ id T c V ==∗
      winTbl γ ∗ votesTbl γ ∗ isWin γ id T V := by
  iintro Ht HS #Hw
  unfold winTbl
  icases Ht with ⟨%W, Ha, #Hrecs⟩
  cases HT : W !! T with
  | none =>
    imod ghost_map_insert_persist T (((id, c), V) : WinRec) HT $$ Ha with ⟨Ha, #Hf⟩
    imodintro
    iframe HS
    isplitl [Ha]
    · iexists (<[T := ((id, c), V)]> W)
      iframe Ha
      iapply (BigSepM.bigSepM_insert (Φ := fun T (r : WinRec) =>
        iprop(isWinCore (GF := GF) γ r.1.1 T r.1.2 r.2 ∗ T ↪[γ.reTbl]□ r)) HT).2
      iframe Hw Hrecs Hf
    · unfold isWin
      iexists c
      iframe Hw Hf
  | some r =>
    obtain ⟨⟨id', c'⟩, q'⟩ := r
    ihave ⟨#Hr, #Hf⟩ := BigSepM.bigSepM_lookup (Φ := fun T (r : WinRec) =>
      iprop(isWinCore (GF := GF) γ r.1.1 T r.1.2 r.2 ∗ T ↪[γ.reTbl]□ r)) HT $$ Hrecs
    icases win_fresh γ id T c V $$ HS Hw %id' %c' %q' Hr Hf with %Hv
    obtain ⟨v, HvV, Hvq⟩ := Hv
    -- the voter voted once in `T`: the entry's winner is `id`
    ihave #Hvotes : iprop([∗map] v ↦ _u ∈ toMap V, isVote (GF := GF) γ v T id) $$ []
    · iunfold isWinCore at Hw
      icases Hw with ⟨%γw, %F0, %k, -, -, -, #Hv, -⟩
      iexact Hv
    ihave #Hvotes' : iprop([∗map] v ↦ _u ∈ toMap q', isVote (GF := GF) γ v T id') $$ []
    · iunfold isWinCore at Hr
      icases Hr with ⟨%γw, %F0, %k, -, -, -, #Hv, -⟩
      iexact Hv
    ihave #Hvs := BigSepM.bigSepM_lookup (Φ := fun v _ => isVote (GF := GF) γ v T id)
      ((GMap.elem_of_gset _ _).mp HvV) $$ Hvotes
    ihave #Hvs' := BigSepM.bigSepM_lookup (Φ := fun v _ => isVote (GF := GF) γ v T id')
      ((GMap.elem_of_gset _ _).mp Hvq) $$ Hvotes'
    icases isVote_agree γ v T id id' $$ Hvs Hvs' with %Hid
    subst Hid
    -- and its quorum is the one frozen in `id`'s `reWins`
    ihave %Hq : ⌜V = q'⌝ $$ []
    · iunfold isWinCore at Hw Hr
      icases Hw with ⟨%γw, %F0, %k, %Hw1, -, #Hf1, -⟩
      icases Hr with ⟨%γw', %F0', %k', %Hw2, -, #Hf2, -⟩
      rw [Hw1.1] at Hw2
      obtain ⟨Hw2, -⟩ := Hw2
      cases Hw2
      iapply ghostMapElem_agree $$ Hf1 Hf2
    subst Hq
    imodintro
    iframe HS
    isplitl [Ha]
    · iexists W
      iframe Ha Hrecs
    · unfold isWin
      iexists c'
      iframe Hr Hf

/-- `Step.win` on the winners table: inside the commit invariant. -/
theorem win_register (γ : RaftNames) (id T : w64) (c : CfgM) (V : GSet w64) :
    ⊢ raftCommitInv (GF := GF) γ -∗ isWinCore γ id T c V ={⊤ \ ↑raftRegN}=∗ isWin γ id T V := by
  iintro #Hinv #Hw
  ihave #Hli := raftCommitInv_log γ $$ Hinv
  unfold raftLogInv raftLogInvBody
  iinv Hli with ⟨%P, HP, Hjust, >Htbl, >Hwt, Hpo⟩ Hclose
  imod winTbl_insert γ id T c V $$ Hwt Htbl Hw with ⟨Hwt, Htbl, #Hwin⟩
  imod Hclose $$ [HP Hjust Htbl Hpo Hwt] with -
  · inext
    iexists P
    iframe
  imodintro
  iexact Hwin

end ghost

end EtcdGrove
end Perennial
