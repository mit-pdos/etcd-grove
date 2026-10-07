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
import EtcdGrove.Raft.Protocol.StepGhost

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI GMap go_etcd_io.raft.v3

section ghost
variable [FfiSyntax]
variable {GF : BundledGFunctors} [AllG GF] [InvGS GF]

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

/-- A campaign log ends at its last entry. -/
theorem camp_last (T : w64) (F0 : List raftpb.Entry) :
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
    uint.Z t < uint.Z T → 0 < uint.Z i →
    ⊢ votesTbl (GF := GF) γ -∗ isVote γ v T c -∗ isAcked γ v t i -∗
      ∃ d Fv Fc, isCamp γ c T Fc ∗ logRecs γ base0 Fv ∗
        ⌜PlogWf base0 Fv ∧ plogUpToDate base0 Fv (plogLast base0 Fc) = true⌝ ∗
        hist γ Fv t i (vbnd T d) ∗
        (if d then iprop(∃ ldr q, isWin γ ldr T q ∗ ⌜v ∉ q⌝) else iprop(True)) := by
  intro Ht Hi
  iintro Htbl #Hvote Hack
  unfold isAcked
  icases Hack with (%H0 | ⟨-, #Hev⟩)
  · exact False.elim (by omega)
  ihave Hj := votesTbl_just γ v T c $$ Htbl Hvote
  unfold voteJust
  icases Hj with ⟨%k, %d, %Fv, %Fc, -, #Hcamp, #HrFv, %Hpure, #Hd, #Hvev⟩
  iexists d, Fv, Fc
  iframe Hcamp HrFv Hd
  isplitr
  · ipureintro; exact Hpure
  iapply ev_pair γ v t i T d Fv Ht $$ Hev Hvev

/-- The induction hypothesis of `lc_core`, below the term `T`. -/
private def LcIH (γ : RaftNames) (T : w64) : Prop :=
  ∀ (T' t' n' : w64) (F' : List raftpb.Entry) (c' : w64) (F0' G' : List raftpb.Entry),
    uint.Z T' < uint.Z T → uint.Z t' < uint.Z T' →
    PlogWf base0 G' →
    plogTermAt base0 G' (W64 (plogLastIndexZ base0 F0'))
      = some (plogLast base0 F0').term' →
    ⊢ votesTbl (GF := GF) γ -∗ cq γ t' n' F' -∗ isLeader γ c' T' -∗ isCamp γ c' T' F0' -∗
      logRecs γ base0 G' -∗ ⌜plogTermAt base0 G' n' = some t'⌝

/-- A full log extends the campaign log of its leader, so it reaches that log's last
entry. -/
private theorem prefix_camp_last (T : w64) (F0 X : List raftpb.Entry) :
    CampOk T F0 → F0 <+: X →
    plogTermAt base0 X (W64 (plogLastIndexZ base0 F0)) = some (plogLast base0 F0).term' := by
  intro Hcok Hpre
  have Hcl := camp_last T F0 Hcok
  rw [plogTermAt_prefix _ F0 X _ Hpre (by rw [Hcl]; rfl), Hcl]

/-- In `lc_core` (Rocq: the `iAssert` `"Hagree"`): logs a history may mention agree with
`F` at and below `n`, by the induction hypothesis. -/
private theorem lc_agree (γ : RaftNames) (T t n : w64) (F : List raftpb.Entry)
    (IH : LcIH (GF := GF) γ T) (j : w64) (X : List raftpb.Entry) :
    uint.Z t < uint.Z T → uint.Z j ≤ uint.Z n → (plogTermAt base0 X j).isSome →
    ⊢ votesTbl (GF := GF) γ -∗ cq γ t n F -∗ okL γ t (uint.Z T) j X -∗
      ⌜plogTermAt base0 X j = plogTermAt base0 F j⌝ := by
  intro HtT Hj HsX
  iintro HS #Hcq HX
  icases cq_full γ t n F $$ Hcq with ⟨%HwF, #HrF⟩
  ihave #Hcq' := Hcq
  ieval (unfold cq) at Hcq'
  icases Hcq' with ⟨%HFn, #HFl, -⟩
  unfold okL
  icases HX with (⟨%t'', %Ht12, #HX⟩ | ⟨%t'', %n'', %Htj, #Hq''⟩)
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
    ihave #Hq3 := Hq''
    ieval (unfold cq) at Hq3
    icases Hq3 with ⟨%HXn'', -⟩
    icases leadFull_camp γ t F $$ HFl with ⟨%ldr, %F0t, #Hlt, #Hct, %Hpre⟩
    icases isCamp_ok γ ldr t F0t $$ Hct with %Hcok
    icases IH t t'' n'' X ldr F0t F HtT Ht'' HwF (prefix_camp_last t F0t F Hcok Hpre)
      $$ HS Hq'' Hlt Hct HrF with %HFn''
    icases full_match γ X F n'' HwX HwF (by rw [HXn'']; rfl) (by rw [HXn'', HFn''])
      $$ HrX HrF with %Hm
    ipureintro; exact Hm j Hjn

/-- The core of Leader Completeness, by strong induction on the term `T` of the leader
(`k` bounds it). If a quorum acknowledged the leader of `t < T` up to `n`, where its log
`F` has an entry of term `t`, then every full log `G` with records that reaches the last
entry of the campaign log of `T`'s leader has term `t` at `n`.

The election quorum of `T` and the acknowledgement quorum of `t` meet in a voter `v`:
its log `Fv` when it voted had `t` at `n` (its history of the acknowledgement, every
log it mentions agreeing with `F` below `n` by the induction hypothesis), and the
campaign log of `T` was at least as up to date. Same last term: `G` has that term down
to `Fv`'s last index (`recs_chain`), so it matches `Fv` there and below. A later last
term `tc`: `G` has `tc`'s campaign log's last entry (`recs_chain`), and the induction
hypothesis at `tc` applies to `G` itself. -/
theorem lc_core (γ : RaftNames) (k : Nat) :
    ∀ (T t n : w64) (F : List raftpb.Entry) (c : w64) (F0 G : List raftpb.Entry),
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
  icases cq_full γ t n F $$ Hcq with ⟨%HwF, #HrF⟩
  ihave #Hcq' := Hcq
  ieval (unfold cq) at Hcq'
  icases Hcq' with ⟨%HFn, #HFl, %q, %Hq, #Hacks⟩
  -- index 0
  by_cases Hn0 : uint.Z n = 0
  · have key : ∀ L : List raftpb.Entry, plogTermAt base0 L n = some base0.term' := by
      intro L; unfold plogTermAt; rw [base0_index]; simp [Hn0]
    rw [key] at HFn
    ipureintro; rw [key]; exact HFn
  -- the voter in both quorums
  ihave #Hl' := Hl
  ieval (unfold isLeader isWin) at Hl'
  icases Hl' with ⟨%V, %γwc, %HγV, #Hwfc, #Hvotes⟩
  obtain ⟨Hγwc, HV⟩ := HγV
  obtain ⟨v, Hvq, HvV, -⟩ := quorums_intersect_cfg _ _ _ Hq HV
  ihave Hackv0 := BigSepM.bigSepM_lookup
    (Φ := fun v _ => iprop(∃ i', ⌜uint.Z n ≤ uint.Z i'⌝ ∗ isAcked (GF := GF) γ v t i'))
    ((GMap.elem_of_gset _ _).mp Hvq) $$ Hacks
  icases Hackv0 with ⟨%iv, %Hiv, #Hackv⟩
  ihave #Hvotev := BigSepM.bigSepM_lookup (Φ := fun v _ => isVote (GF := GF) γ v T c)
    ((GMap.elem_of_gset _ _).mp HvV) $$ Hvotes
  icases tbl_voter γ v T c t iv HtT (by have := uint_Z_nonneg n; omega) $$ HS Hvotev Hackv
    with ⟨%d, %Fv, %Fc, #Hcv, #HrFv, %HFv, #Hh0, #Hd⟩
  obtain ⟨HwFv, Hutd⟩ := HFv
  -- `v`'s vote counted in `c`'s election, so it was cast before `v` knew `c`: the history
  -- is bounded by `T`
  ihave #Hh : hist γ Fv t iv (uint.Z T) $$ []
  · cases d with
    | false =>
      iapply hist_mono γ Fv t iv (vbnd T false) (uint.Z T) (by simp [vbnd]) $$ Hh0
    | true =>
      simp only [↓reduceIte]
      icases Hd with ⟨%ldr, %qd, #Hwd, %Hvq'⟩
      ihave #HwV : isWin γ c T V $$ []
      · unfold isWin
        iexists γwc
        isplitr
        · ipureintro; exact ⟨Hγwc, HV⟩
        isplitr
        · iexact Hwfc
        · iexact Hvotes
      ihave #Hld : isLeader γ ldr T $$ []
      · unfold isLeader; iexists qd; iexact Hwd
      icases isLeader_unique γ ldr c T $$ Hld Hl with %Heq
      subst Heq
      icases isWin_agree γ ldr T qd V $$ Hwd HwV with %Heq
      subst Heq
      exact absurd HvV Hvq'
  icases isCamp_agree γ c T F0 Fc $$ Hc Hcv with %HF0
  subst HF0
  icases isCamp_ok γ c T F0 $$ Hc with %Hcok
  -- `Fv` had `t` at `n`
  have Hnpos : 0 < uint.Z n := by have := uint_Z_nonneg n; omega
  ihave %HFvn : ⌜plogTermAt base0 Fv n = some t⌝ $$ [HS]
  · ieval (unfold hist) at Hh
    ihave Hhn := Hh $$ %n %(And.intro Hnpos Hiv)
    icases Hhn with (⟨%X, #HX, %HsX⟩ | ⟨%j', %X1, %X2, %Hj', #H1, #H2, %Hd'⟩)
    · obtain ⟨HsX, HXn⟩ := HsX
      icases lc_agree γ T t n F IH n X HtT (Int.le_refl _) HsX $$ HS Hcq HX with %HX'
      ipureintro; rw [← HXn, HX', HFn]
    · obtain ⟨Hs1, Hs2, Hne⟩ := Hd'
      icases lc_agree γ T t n F IH j' X1 HtT (by omega) Hs1 $$ HS Hcq H1 with %HX1
      icases lc_agree γ T t n F IH j' X2 HtT (by omega) Hs2 $$ HS Hcq H2 with %HX2
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
    icases Hxr with ⟨%ldr, %γt, %b, %l0, %F0c, #Hlc, -, #Hcc, -, -⟩
    rw [Hxt]
    icases recs_chain γ G ldr _ F0c HwG $$ Hlc Hcc HrG with %Hch
    obtain ⟨-, HGlc, -⟩ := Hch _ Hic0 HGl
    iapply IH _ t n F ldr F0c G HtcT (by omega) HwG HGlc $$ HS Hcq Hlc Hcc HrG
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
    icases Hyr with ⟨%ldr, %γt, %b, %l0, %F0c, #Hlc, -, #Hcc, -, %Hptok⟩
    have HyL := Hptok.1
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

/-- Two commit facts agree below the earlier one's index: same term, the leader's logs
agree; an earlier term, `lc_core` puts the earlier committed log's entry in the later
leader's log. -/
theorem cq_lt_agree (γ : RaftNames) (t1 n1 t2 n2 : w64) (G1 G2 : List raftpb.Entry) :
    uint.Z t1 < uint.Z t2 →
    ⊢ votesTbl (GF := GF) γ -∗ cq γ t1 n1 G1 -∗ cq γ t2 n2 G2 -∗
      ⌜∀ j : w64, uint.Z j ≤ uint.Z n1 → plogTermAt base0 G1 j = plogTermAt base0 G2 j⌝ := by
  intro Hlt
  iintro HS #Hq1 #Hq2
  icases cq_full γ t1 n1 G1 $$ Hq1 with ⟨%Hw1, #Hr1⟩
  icases cq_full γ t2 n2 G2 $$ Hq2 with ⟨%Hw2, #Hr2⟩
  ihave #Hq1' := Hq1
  ihave #Hq2' := Hq2
  ieval (unfold cq) at Hq1' Hq2'
  icases Hq1' with ⟨%H1n, -⟩
  icases Hq2' with ⟨-, #Hfl2, -⟩
  icases leadFull_camp γ t2 G2 $$ Hfl2 with ⟨%ldr, %F0, #Hl, #Hc, %Hpre⟩
  icases isCamp_ok γ ldr t2 F0 $$ Hc with %Hcok
  have Hcl := camp_last t2 F0 Hcok
  have HGl : plogTermAt base0 G2 (W64 (plogLastIndexZ base0 F0))
      = some (plogLast base0 F0).term' := by
    rw [plogTermAt_prefix _ F0 G2 _ Hpre (by rw [Hcl]; rfl), Hcl]
  icases lc_core γ ((uint.Z t2).toNat + 1) t2 t1 n1 G1 ldr F0 G2
      (by have := uint_Z_nonneg t2; omega) Hlt Hw2 HGl $$ HS Hq1 Hl Hc Hr2 with %H2n
  iapply full_match γ G1 G2 n1 Hw1 Hw2 (by rw [H1n]; rfl) (by rw [H1n, H2n]) $$ Hr1 Hr2

theorem cq_agree (γ : RaftNames) (t1 n1 t2 n2 i : w64) (G1 G2 : List raftpb.Entry) :
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
    ieval (unfold cq) at Hq1 Hq2
    icases Hq1 with ⟨%H1n, #Hf1, -⟩
    icases Hq2 with ⟨%H2n, #Hf2, -⟩
    have Hs1 := full_term_at_some G1 i n1 (by rw [H1n]; rfl) Hi1
    have Hs2 := full_term_at_some G2 i n2 (by rw [H2n]; rfl) Hi2
    icases leadFull_agree γ t1 G1 G2 i Hs1 Hs2 $$ Hf1 Hf2 with %Hag
    iapply full_match γ G1 G2 i Hw1 Hw2 Hs1 Hag $$ Hr1 Hr2
  · icases cq_lt_agree γ t2 n2 t1 n1 G2 G1 Hgt $$ HS Hq2 Hq1 with %H
    ipureintro; intro j Hj; exact (H j (by omega)).symm

/-! Firing the registry as the global log grows by one entry `e`, the entry at position
`m` of a full log `G` with records. A slot not at `e`'s `(term, index)` is unaffected:
the global log changes only at `e`'s index, where its term is another (`slot_keep`). The
slot at `e`'s `(term, index)`, if any, is the proposal of `e` (both are the leader's
entry there, `isEntry_agree`): pending, its update runs with the authority of the
extended log and its result is stored (`fire_one`). -/

omit [FfiSyntax] in
theorem take_S_lookup_ne {A : Type _} (G : List A) (m p : Nat) (e : A) :
    G[m]? = some e → p ≠ m → (G.take (m + 1))[p]? = (G.take m)[p]? := by
  intro He Hp
  have := (List.getElem?_eq_some_iff.mp He).1
  rw [List.getElem?_take, List.getElem?_take]
  split <;> split <;> first | rfl | omega

theorem slot_keep (γ : RaftNames) (k : w64 × w64) (v : PropRec) (G : List raftpb.Entry)
    (m : Nat) (e : raftpb.Entry) :
    G[m]? = some e → uint.Z e.Index' = (m : Int) + 1 →
    0 < uint.Z k.2 →
    k ≠ (e.Term', e.Index') →
    ⊢ ▷ propSlot (GF := GF) γ k v (G.take m) -∗ ▷ propSlot γ k v (G.take (m + 1)) := by
  intro He Hei Hk Hne
  iintro Hs
  inext
  unfold propSlot
  icases Hs with ⟨%Φ, #Hsp, Hst⟩
  iexists Φ
  isplitr
  · iexact Hsp
  have Hlt := (List.getElem?_eq_some_iff.mp He).1
  by_cases Hp : pos k.2 = m
  · have Hk2 : k.2 = e.Index' := by
      apply uint_Z_inj.mp; unfold pos at Hp; omega
    have Hk1 : k.1 ≠ e.Term' := by
      intro Heq; apply Hne; obtain ⟨k1, k2⟩ := k; simp only at Hk2 Heq; subst Hk2 Heq; rfl
    have HSm : (G.take (m + 1))[pos k.2]? = some e := by
      rw [Hp, List.getElem?_take, ite_eq_left (by omega)]; exact He
    have Hm : (G.take m)[pos k.2]? = none := by
      rw [Hp, List.getElem?_take, ite_eq_right (by omega)]
    icases Hst with (⟨%Hnc, Hau⟩ | ⟨%Hc, HQ⟩ | Htok)
    · ileft
      isplitr
      · ipureintro
        intro e' He'
        rw [HSm] at He'
        cases He'
        exact fun h => Hk1 h.symm
      · iexact Hau
    · obtain ⟨e', He', _⟩ := Hc
      rw [Hm] at He'
      cases He'
    · iright; iright; iexact Htok
  · rw [take_S_lookup_ne G m (pos k.2) e He Hp]
    iexact Hst

theorem fire_one (γ : RaftNames) (E : CoPset) (G : List raftpb.Entry) (m : Nat)
    (e : raftpb.Entry) (R : GMap (w64 × w64) PropRec) :
    PlogWf base0 G → G[m]? = some e →
    ⊢ logRecs (GF := GF) γ base0 G -∗ ownCommitted γ (G.take m) -∗ propsIdx γ R -∗
      ([∗map] k ↦ v ∈ R, ▷ propSlot γ k v (G.take m)) ={E}=∗
      ownCommitted γ (G.take (m + 1)) ∗ ([∗map] k ↦ v ∈ R, ▷ propSlot γ k v (G.take (m + 1))) := by
  intro Hwf He
  iintro #Hr HP #Hidx Hslots
  have Hei := Hwf _ _ He
  rw [base0_index] at Hei
  push_cast at Hei
  have Hrng := uint_Z_lt e.Index'
  have Hlt := (List.getElem?_eq_some_iff.mp He).1
  icases logRecs_lookup γ G m e He (by omega) $$ Hr with ⟨%pt, -, #Her⟩
  have Htk : G.take (m + 1) = G.take m ++ [e] := by rw [List.take_add_one, He]; rfl
  imod ownCommitted_extend γ (G.take m) (G.take (m + 1))
    (by rw [Htk]; exact List.prefix_append _ _) $$ HP with ⟨HP, -⟩
  unfold propsIdx
  ihave Hkeep : iprop(∀ (R' : GMap (w64 × w64) PropRec),
      ∀ (_ : R' !! (e.Term', e.Index') = none),
      ([∗map] k ↦ v ∈ R', isEntry γ (stampAt v.2 k.1 k.2) ∗ ⌜0 < uint.Z k.2⌝) -∗
      ([∗map] k ↦ v ∈ R', ▷ propSlot γ k v (G.take m)) -∗
      [∗map] k ↦ v ∈ R', ▷ propSlot γ k v (G.take (m + 1))) $$ []
  · iintro %R' %HR' #Hidx' Hs
    iapply BigSepM.bigSepM_impl $$ Hs
    imodintro
    iintro %k %v %Hkv Hs
    ihave ⟨-, %Hpos⟩ := BigSepM.bigSepM_lookup Hkv $$ Hidx'
    iapply slot_keep γ k v G m e He (by omega) Hpos
      (by intro Hk; subst Hk; nomatch HR'.symm.trans Hkv) $$ Hs
  cases Hv : R !! (e.Term', e.Index') with
  | none =>
    imodintro
    isplitl [HP]
    · iexact HP
    iapply Hkeep $$ %R %Hv Hidx Hslots
  | some v =>
    icases (BigSepM.bigSepM_delete Hv).1 $$ Hslots with ⟨Hs, Hslots⟩
    ihave Hidx2 := (BigSepM.bigSepM_delete Hv).1 $$ Hidx
    icases Hidx2 with ⟨⟨#Hie, %Hpos0⟩, #Hidx0⟩
    ihave #Hee : isEntry γ e $$ []
    · unfold isEntry; iexists pt; iexact Her
    icases isEntry_agree γ e (stampAt v.2 e.Term' e.Index') rfl rfl $$ Hee Hie with %Heq
    have Hpm : pos e.Index' = m := by unfold pos; omega
    ihave Hnew : iprop(▷ (ownCommitted γ (G.take (m + 1)) ∗
        propSlot γ (e.Term', e.Index') v (G.take (m + 1)))) $$ [HP Hs]
    · inext
      unfold propSlot
      icases Hs with ⟨%Φ, #Hsp, Hst⟩
      icases Hst with (⟨%Hnc, Hau⟩ | ⟨%Hc, HQ⟩ | Htok)
      · have Heq' : G.take (m + 1) = G.take m ++ [stampAt v.2 e.Term' e.Index'] := by
          rw [Htk, ← Heq]
        rw [Heq']
        unfold propAu
        ihave Hres := Hau $$ %e.Term' %e.Index' %(G.take m) [] [HP]
        · ipureintro; rw [List.length_take]; omega
        · iexact HP
        icases Hres with ⟨HP, HQ⟩
        rw [← Heq']
        isplitl [HP]
        · iexact HP
        iexists Φ
        isplitr
        · iexact Hsp
        iright; ileft
        isplitr
        · ipureintro
          refine ⟨e, ?_, rfl⟩
          simp only
          rw [Hpm, List.getElem?_take, ite_eq_left (by omega)]; exact He
        · iexact HQ
      · obtain ⟨e', He', _⟩ := Hc
        simp only at He'
        rw [Hpm, List.getElem?_take, ite_eq_right (by omega)] at He'
        cases He'
      · isplitl [HP]
        · iexact HP
        iexists Φ
        isplitr
        · iexact Hsp
        iright; iright; iexact Htok
    icases Hnew with ⟨>HP, Hnew⟩
    imodintro
    isplitl [HP]
    · iexact HP
    iapply (BigSepM.bigSepM_delete Hv).2
    isplitl [Hnew]
    · iexact Hnew
    iapply Hkeep $$ %_ %(GMap.lookup_delete_eq _ _) Hidx0 Hslots

theorem fire_upto (γ : RaftNames) (E : CoPset) (G : List raftpb.Entry)
    (R : GMap (w64 × w64) PropRec) (d m : Nat) :
    PlogWf base0 G → m + d ≤ G.length →
    ⊢ logRecs (GF := GF) γ base0 G -∗ ownCommitted γ (G.take m) -∗ propsIdx γ R -∗
      ([∗map] k ↦ v ∈ R, ▷ propSlot γ k v (G.take m)) ={E}=∗
      ownCommitted γ (G.take (m + d)) ∗ ([∗map] k ↦ v ∈ R, ▷ propSlot γ k v (G.take (m + d))) := by
  induction d generalizing m with
  | zero =>
    intro _ _
    iintro #Hr HP #Hidx Hs
    imodintro
    isplitl [HP]
    · iexact HP
    · iexact Hs
  | succ d IH =>
    intro Hwf Hle
    iintro #Hr HP #Hidx Hs
    obtain ⟨e, He⟩ : ∃ e, G[m]? = some e := ⟨G[m]'(by omega), List.getElem?_eq_getElem _⟩
    imod fire_one γ E G m e R Hwf He $$ Hr HP Hidx Hs with ⟨HP, Hs⟩
    rw [show m + (d + 1) = (m + 1) + d by omega]
    iapply IH (m + 1) Hwf (by omega) $$ Hr HP Hidx Hs

/-- Committing: a new commit fact `cq γ t n G` extends the global log to `G`'s first `n`
entries, or finds it already past them. Inside the invariant, the global log is the
first `n0` entries of the log `G0` of an earlier commit fact; the two commit facts agree
below both (`cq_agree`, from the vote table), so -- the logs having records -- the two
prefixes are prefixes of one another (`full_take_eq`). The extension is entry by entry,
firing the registered proposals (`fire_upto`). -/
theorem commit_extend (γ : RaftNames) (E : CoPset) (t n : w64) (G : List raftpb.Entry) :
    ↑raftN ⊆ E →
    ⊢ raftCommitInv (GF := GF) γ -∗ cq γ t n G ={E}=∗ isCommitted γ (G.take (uint.Z n).toNat) := by
  intro HE
  iintro #Hinv #Hcq
  unfold raftCommitInv
  iinv Hinv with ⟨%P, %R, >HP, >Hj, >Htbl, >Hra, >#Hidx, Hslots⟩ Hclose
  ihave Hslots := (BigSepM.bigSepM_later).1 $$ Hslots
  icases cq_full γ t n G $$ Hcq with ⟨%HwG, #HrG⟩
  ihave #Hcq' := Hcq
  ieval (unfold cq) at Hcq'
  icases Hcq' with ⟨%HGn, -⟩
  have HnG := (plogTermAt_some_range _ _ _ _ HGn).2
  unfold plogLastIndexZ at HnG
  rw [base0_index] at HnG
  unfold committedJust
  icases Hj with (%HP0 | ⟨%t0, %n0, %G0, #Hcq0, %HP0⟩)
  · subst HP0
    ihave HP' : ownCommitted γ (G.take 0) $$ [HP]
    · rw [List.take_zero]; iexact HP
    ihave Hslots' : iprop([∗map] k ↦ v ∈ R, ▷ propSlot γ k v (G.take 0)) $$ [Hslots]
    · rw [List.take_zero]; iexact Hslots
    imod fire_upto γ _ G R (uint.Z n).toNat 0 HwG (by omega) $$ HrG HP' Hidx Hslots'
      with ⟨HP, Hslots⟩
    rw [Nat.zero_add]
    ihave #Hc := ownCommitted_lb γ _ $$ HP
    ihave Hslots := (BigSepM.bigSepM_later).2 $$ Hslots
    imod Hclose $$ [HP Htbl Hra Hslots] with -
    · inext
      iexists _, R
      isplitl [HP]
      · iexact HP
      isplitr [Htbl Hra Hslots]
      · iright
        iexists t, n, G
        isplitr
        · iexact Hcq
        · ipureintro; rfl
      iframe
      iexact Hidx
    imodintro
    iexact Hc
  · subst HP0
    icases cq_full γ t0 n0 G0 $$ Hcq0 with ⟨%HwG0, #HrG0⟩
    ihave #Hcq0' := Hcq0
    ieval (unfold cq) at Hcq0'
    icases Hcq0' with ⟨%HG0n, -⟩
    by_cases Hle : uint.Z n0 ≤ uint.Z n
    · -- the new prefix is longer: extend, firing the registry
      icases cq_agree γ t0 n0 t n n0 G0 G (Int.le_refl _) Hle $$ Htbl Hcq0 Hcq with %Hag
      icases full_take_eq γ G0 G n0 HwG0 HwG (by rw [HG0n]; rfl) (Hag n0 (Int.le_refl _))
        $$ HrG0 HrG with %Htk
      rw [Htk]
      imod fire_upto γ _ G R ((uint.Z n).toNat - (uint.Z n0).toNat) (uint.Z n0).toNat HwG
        (by omega) $$ HrG HP Hidx Hslots with ⟨HP, Hslots⟩
      rw [show (uint.Z n0).toNat + ((uint.Z n).toNat - (uint.Z n0).toNat) = (uint.Z n).toNat
        by omega]
      ihave #Hc := ownCommitted_lb γ _ $$ HP
      ihave Hslots := (BigSepM.bigSepM_later).2 $$ Hslots
      imod Hclose $$ [HP Htbl Hra Hslots] with -
      · inext
        iexists _, R
        isplitl [HP]
        · iexact HP
        isplitr [Htbl Hra Hslots]
        · iright
          iexists t, n, G
          isplitr
          · iexact Hcq
          · ipureintro; rfl
        iframe
        iexact Hidx
      imodintro
      iexact Hc
    · -- the global log is already past it
      icases cq_agree γ t0 n0 t n n G0 G (by omega) (Int.le_refl _) $$ Htbl Hcq0 Hcq with %Hag
      icases full_take_eq γ G0 G n HwG0 HwG
        (full_term_at_some G0 n n0 (by rw [HG0n]; rfl) (by omega)) (Hag n (Int.le_refl _))
        $$ HrG0 HrG with %Htk
      ihave #Hc0 := ownCommitted_lb γ _ $$ HP
      ihave Hslots := (BigSepM.bigSepM_later).2 $$ Hslots
      imod Hclose $$ [HP Htbl Hra Hslots] with -
      · inext
        iexists _, R
        isplitl [HP]
        · iexact HP
        isplitr [Htbl Hra Hslots]
        · iright
          iexists t0, n0, G0
          isplitr
          · iexact Hcq0
          · ipureintro; rfl
        iframe
        iexact Hidx
      imodintro
      iapply isCommitted_mono γ _ _ (by rw [← Htk]; exact take_prefix_le _ _ _ (by omega)) $$ Hc0

/-- A vote, recorded in the node's half of its vote map and in the table. -/
theorem vote_insert (γ : RaftNames) (id : w64) (γv : GName) (voted : GMap w64 w64)
    (T c : w64) :
    γ.reVotes !! id = some γv → voted !! T = none →
    ⊢ raftCommitInv (GF := GF) γ -∗ voteJust γ id T c -∗ ghostMapAuth γv (1 : Qp).half voted ={⊤}=∗
      ghostMapAuth γv (1 : Qp).half (<[T := c]> voted) ∗ T ↪[γv]□ c := by
  intro Hγv Hfree
  iintro #Hinv #Hj Ha
  unfold raftCommitInv
  iinv Hinv with ⟨%P, %R, HP, Hjust, >Htbl, Hrest⟩ Hclose
  imod votesTbl_insert γ id γv voted T c Hγv Hfree $$ Hj Htbl Ha with ⟨Htbl, Ha, #Hf⟩
  imod Hclose $$ [HP Hjust Htbl Hrest] with -
  · inext
    iexists P, R
    iframe
  imodintro
  isplitl [Ha]
  · iexact Ha
  · iexact Hf

end ghost

end EtcdGrove
end Perennial
