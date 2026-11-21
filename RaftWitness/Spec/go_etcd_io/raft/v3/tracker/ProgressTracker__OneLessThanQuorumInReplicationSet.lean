/-
`(*ProgressTracker).OneLessThanQuorumInReplicationSet` (raft#168, `tracker/tracker.go`;
2026-10-19, witness support).
-/
module

public import RaftWitness.Proof.go_etcd_io.raft.v3.InvTrackerC
public import RaftWitness.Spec.go_etcd_io.raft.v3.quorum.MajorityConfig__OneLessThanQuorum

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI GMap go_etcd_io.raft.v3

/-- At least `k` voters of `V` have `f` at least `N`. -/
def CountGe (V : GSet w64) (f : w64 → w64) (k : Nat) (N : w64) : Prop :=
  k ≤ GMap.size (GMap.filter (fun v _ => decide (uint.Z N ≤ uint.Z (f v))) V)

/-- Fewer voters reach a larger index. -/
theorem CountGe.mono {V : GSet w64} {f : w64 → w64} {k : Nat} {N N' : w64}
    (H : CountGe V f k N) (Hle : uint.Z N' ≤ uint.Z N) : CountGe V f k N' := by
  unfold CountGe at *
  refine Nat.le_trans H (GMap.subseteq_size ?_)
  intro x u
  simp only [GMap.lookup_filter]
  cases hv : V !! x with
  | none => simp
  | some u' =>
    intro hx
    by_cases h : uint.Z N ≤ uint.Z (f x)
    · have h' : uint.Z N' ≤ uint.Z (f x) := by omega
      simp [Option.filter, h] at hx
      simp [Option.filter, h', hx]
    · simp [Option.filter, h] at hx

/-- What `MajorityConfig.OneLessThanQuorum` returns (its spec's three cases) is reached by
`|V| / 2` voters. -/
theorem CountGe.of_oltq {s : GSet w64} {f : w64 → w64} {N : w64}
    (H2 : GMap.size s = 1 → N = W64 0)
    (H3 : s ≠ ∅ → GMap.size s ≠ 1 → IsCountIndex s f (GMap.size s / 2) N) :
    CountGe s f (GMap.size s / 2) N := by
  by_cases h0 : s = ∅
  · subst h0; unfold CountGe; rw [GMap.map_size_empty]; exact Nat.zero_le _
  by_cases h1 : GMap.size s = 1
  · unfold CountGe; rw [h1]; exact Nat.zero_le _
  exact (H3 h0 h1).2.1

/-- The regular acknowledgements needed before offering an index to this half's witness.
An empty half places no constraint on a joint index. -/
def witnessRegularCount (s : GSet w64) (selected : Bool) : Nat := by
  classical
  exact if selected then GMap.size s / 2 else if s = ∅ then 0 else GMap.size s / 2 + 1

theorem CountGe.of_committed {s : GSet w64} {f : w64 → w64} {N : w64}
    (H : s ≠ ∅ → IsQuorumIndex s f N) : CountGe s f (witnessRegularCount s false) N := by
  by_cases he : s = ∅
  · simp [CountGe, witnessRegularCount, he]
  simp only [witnessRegularCount, Bool.false_eq_true, ite_false, he]
  have hq := (IsQuorum_alt _ _).1 (H he).2.1
  refine Nat.le_trans hq (GMap.subseteq_size ?_)
  rw [GMap.elem_of_subseteq]
  intro v hv
  exact ((GMap.elem_of_intersection _ _ _).1 hv).1

/-- A half's acknowledgements as the leader counts them for its witness: the `Match` of the
replication set's non-witness voters, `0` for the others. -/
def rsAcked (pvs : GMap w64 Progress) (r : RSM) (v : w64) : w64 :=
  (scopedAcked r.nwv (pvsAcked pvs) v).getD (W64 0)

/-- A shared witness has the same nonzero ID in both halves. -/
def sharedWitness (em : EpochM) : Bool :=
  decide (em.rs0.wit ≠ W64 0 ∧ em.rs0.wit = em.rs1.wit)

/-- The result contains each witness selected by at least one half. In each
half contributing to that witness's index, regular voters acknowledge the index at
the threshold for that half. A shared witness contributes to both halves. -/
def OltqOk (V0 V1 : GSet w64) (em : EpochM) (pvs : GMap w64 Progress) (res : GMap w64 w64) :
    Prop :=
  (∀ w, (res !! w).isSome = true ↔
    ((em.rs0.rep = true ∧ em.rs0.wit = w) ∨ (em.rs1.rep = true ∧ em.rs1.wit = w))) ∧
  ∀ w N, res !! w = some N →
    ((em.rs0.rep || sharedWitness em) = true → em.rs0.wit = w →
      CountGe V0 (rsAcked pvs em.rs0) (witnessRegularCount V0 em.rs0.rep) N) ∧
    ((em.rs1.rep || sharedWitness em) = true → em.rs1.wit = w →
      CountGe V1 (rsAcked pvs em.rs1) (witnessRegularCount V1 em.rs1.rep) N)

/-- There is no witness to send to exactly when neither half selected one. -/
def OltqNone (em : EpochM) : Prop := em.rs0.rep = false ∧ em.rs1.rep = false

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- The fields `OneLessThanQuorumInReplicationSet` reads past the epoch when a half replicates
to its witness: the voter halves (`&p.Voters[i]`, handed to `MajorityConfig.OneLessThanQuorum`,
which needs them whole -- so the tracker too; at most `2^62` voters each, its bound) and the
progress map (the indexer's). -/
def oltqRes (dq : DFrac) (tv : tracker.ProgressTracker) (V0 V1 : GSet w64)
    (pvs : GMap w64 Progress) : IProp GF :=
  iprop(⌜dq = DFrac.own 1⌝ ∗
    ∃ vin vout, ⌜tv.Config'.Voters'.arr = [vin, vout] ∧
      (GMap.size V0 : Int) ≤ 2 ^ 62 ∧ (GMap.size V1 : Int) ≤ 2 ^ 62⌝ ∗
    ownIdsetQ vin (DFrac.own 1) V0 ∗ ownIdsetQ vout (DFrac.own 1) V1 ∗
    ownProgressMap tv.Progress' pvs)

/-- `p.OneLessThanQuorumInReplicationSet()`: `nil` when no half replicates to its witness (the
early return, which reads nothing but the epoch). Otherwise the map satisfies
`OltqOk`, with the tracker fields in `oltqRes` returned to the caller. -/
abbrev tracker.ProgressTracker.OneLessThanQuorumInReplicationSet.spec : Prop :=
  ∀ (trk : Loc) (dq : DFrac) (tv : tracker.ProgressTracker) (em : EpochM) (V0 V1 : GSet w64)
    (pvs : GMap w64 Progress),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗ trk ↦{dq} tv ∗
      ownEpoch tv.Epoch' em ∗
      (⌜em.rs0.rep = false ∧ em.rs1.rep = false⌝ ∨ oltqRes dq tv V0 V1 pvs) }}
    (App (Val (trk @!! go.GoType.PointerType tracker.ProgressTracker.ty
      @!! go!"OneLessThanQuorumInReplicationSet")) (Val #()))
  {{ (mref : Loc), RET #mref; trk ↦{dq} tv ∗
      (⌜em.rs0.rep = false ∧ em.rs1.rep = false⌝ ∨ oltqRes dq tv V0 V1 pvs) ∗
      (⌜OltqNone em ∧ mref = map.nil⌝ ∨
       ⌜¬ OltqNone em⌝ ∗ ∃ res : GMap w64 w64, mref ↦$ res ∗ ⌜OltqOk V0 V1 em pvs res⌝) }}

/-- With a witness-free epoch, `nil` (the statement this spec had until the epoch model). -/
theorem tracker.ProgressTracker.OneLessThanQuorumInReplicationSet.spec_nw
    (H : tracker.ProgressTracker.OneLessThanQuorumInReplicationSet.spec (GF := GF) (hG := hG))
    (trk : Loc) (dq : DFrac) (tv : tracker.ProgressTracker) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗ trk ↦{dq} tv ∗
        ownEpochNW tv.Epoch' }}
      (App (Val (trk @!! go.GoType.PointerType tracker.ProgressTracker.ty
        @!! go!"OneLessThanQuorumInReplicationSet")) (Val #()))
    {{ RET #map.nil; trk ↦{dq} tv }} := by
  iintro %Φ ⟨#Hpkg, Htrk, #He⟩ HΦ
  iunfold ownEpochNW at He
  iapply H trk dq tv (EpochM.bare (W64 0)) ∅ ∅ ∅ $$ [Htrk]
  · iframe Hpkg Htrk He
    ileft; ipureintro; exact ⟨rfl, rfl⟩
  inext
  iintro %mref ⟨Htrk, -, (%Hm | ⟨%Hrep, -⟩)⟩
  · rw [Hm.2]; iapply HΦ $$ Htrk
  · exfalso
    exact Hrep (by simp [OltqNone, EpochM.bare, RSM.bare, RSM.rep])

/-- At a tracker of the configuration `c` (2026-10-20, witness support): `nil` (`OltqNone`), or a
map satisfying `OltqOk` for the configuration's halves and the tracker's epoch and peers; the
tracker given back. -/
theorem tracker.ProgressTracker.OneLessThanQuorumInReplicationSet.spec_c
    (H : tracker.ProgressTracker.OneLessThanQuorumInReplicationSet.spec (GF := GF) (hG := hG))
    (c : CfgM) (trk : Loc) (tv : tracker.ProgressTracker) (t : Trk) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.tracker ∗ trk ↦ tv ∗
        ownTrackerC c tv t }}
      (App (Val (trk @!! go.GoType.PointerType tracker.ProgressTracker.ty
        @!! go!"OneLessThanQuorumInReplicationSet")) (Val #()))
    {{ (mref : Loc), RET #mref; trk ↦ tv ∗ ownTrackerC c tv t ∗
        (⌜OltqNone t.ep ∧ mref = map.nil⌝ ∨
         ⌜¬ OltqNone t.ep⌝ ∗ ∃ res : GMap w64 w64, mref ↦$ res ∗
           ⌜OltqOk c.incoming c.outgoing t.ep t.peers res⌝) }} := by
  iintro %Φ ⟨#Hpkg, Htrk, Hown⟩ HΦ
  iunfold ownTrackerC at Hown
  iNamed Hown
  iunfold ownEpochOk at Hepoch
  icases Hepoch with ⟨#He, %Hok⟩
  by_cases hnone : t.ep.rs0.rep = false ∧ t.ep.rs1.rep = false
  · -- neither half replicates: the early return, which reads nothing else
    iapply H trk (DFrac.own 1) tv t.ep c.incoming c.outgoing t.peers $$ [Htrk]
    · iframe Hpkg Htrk He
      ileft; ipureintro; exact hnone
    inext
    iintro %mref ⟨Htrk, -, Hr⟩
    iapply HΦ
    iframe Htrk Hr
    iapply ownTrackerC_intro c tv t.votes t.prs t.peers Hinv Hdom Hflags Hsize HmaxInfl Hnw
      $$ Hvotes Hprs Hprogs Hcfg [He]
    unfold ownEpochOk; iframe He; ipureintro; exact Hok
  icases ownCfgCC_elim _ _ _ $$ Hcfg with ⟨%vin, %vout, %Harr, Hin, Hout, Hl, Hln, %Hal, %Hwit⟩
  ihave %Hvnn := ownMap_not_nil _ _ _ $$ Hin
  ihave %Hpo : ⌜(vout = map.nil ∧ c.outgoing = ∅) ∨ c.outgoing ≠ ∅⌝ $$ [Hout]
  · unfold ownIdsetC
    icases Hout with (%H | ⟨-, %H⟩)
    · ipureintro; exact Or.inl H
    · ipureintro; exact Or.inr H
  have Hsz : ∀ S : GSet w64, S ⊆ c.ids → (GMap.size S : Int) ≤ 2 ^ 62 := fun S hS => by
    have h := size_le_of_sub_dom S t.prs (by rw [Hdom]; exact hS)
    omega
  have Hsub_i : c.incoming ⊆ c.ids := (GMap.elem_of_subseteq _ _).2 fun k hk =>
    (GMap.elem_of_subseteq _ _).1 (voters_sub_ids c) k
      ((GMap.elem_of_subseteq _ _).1 (incoming_sub_voters c) k hk)
  have Hsub_o : c.outgoing ⊆ c.ids := (GMap.elem_of_subseteq _ _).2 fun k hk =>
    (GMap.elem_of_subseteq _ _).1 (voters_sub_ids c) k
      ((GMap.elem_of_subseteq _ _).1 (outgoing_sub_voters c) k hk)
  iapply H trk (DFrac.own 1) tv t.ep c.incoming c.outgoing t.peers $$ [Htrk Hin Hout Hprogs]
  · iframe Hpkg Htrk He
    iright
    unfold oltqRes
    isplitr; · ipureintro; rfl
    iexists vin, vout
    isplitr; · ipureintro; exact ⟨Harr, Hsz _ Hsub_i, Hsz _ Hsub_o⟩
    isplitl [Hin]
    · unfold ownIdsetQ; iright; iexact Hin
    isplitl [Hout]
    · iapply ownIdsetC_Q $$ Hout
    unfold ownProgressMap
    iexists t.prs
    iframe Hprs Hprogs
  inext
  iintro %mref ⟨Htrk, Hres, Hr⟩
  icases Hres with (%Hf | Hres)
  · exact absurd Hf hnone
  unfold oltqRes
  icases Hres with ⟨-, %vin', %vout', %Hvv, Hin, Hout, HP⟩
  have Hv : vin' = vin ∧ vout' = vout := by
    have h := Hvv.1; rw [Harr] at h; simp only [List.cons.injEq] at h; exact ⟨h.1.symm, h.2.1.symm⟩
  obtain ⟨rfl, rfl⟩ := Hv
  iunfold ownProgressMap at HP
  icases HP with ⟨%prs', #Hprs', Hprogs⟩
  ihave %Hprs_eq := progress_map_agree _ _ _ _ _ $$ Hprs Hprs'
  subst Hprs_eq
  unfold ownIdsetQ
  icases Hin with (%Hnil | Hin)
  · exact absurd Hnil.1 Hvnn
  ihave Hout : ownIdsetC vout' (DFrac.own 1) c.outgoing $$ [Hout]
  · unfold ownIdsetC
    icases Hout with (%Hn | Ho)
    · ileft; ipureintro; exact Hn
    · ihave %Honn := ownMap_not_nil _ _ _ $$ Ho
      iright; iframe Ho
      ipureintro
      rcases Hpo with Hp | Hp
      · exact absurd Hp.1 Honn
      · exact Hp
  iapply HΦ
  iframe Htrk Hr
  iapply ownTrackerC_intro c tv t.votes t.prs t.peers Hinv Hdom Hflags Hsize HmaxInfl Hnw
    $$ Hvotes Hprs Hprogs [Hin Hout Hl Hln] [He]
  · iapply ownCfgCC_intro _ _ c vin' vout' Harr Hal Hwit $$ Hin Hout Hl Hln
  · unfold ownEpochOk; iframe He; ipureintro; exact Hok

end spec

end EtcdGrove
end Perennial
