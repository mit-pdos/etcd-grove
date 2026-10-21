/-
Proof of `Spec/go_etcd_io/raft/v3/tracker/ProgressTracker__ChangeReplicationSet.lean`.
-/
module

public import RaftWitness.Spec.go_etcd_io.raft.v3.tracker.ProgressTracker__ChangeReplicationSet
public import RaftWitness.Spec.go_etcd_io.raft.v3.tracker.Epoch__HasWitness

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- A half of the new epoch: well formed, with the old one's witness; the old half (read-only)
or a rebuilt one (its voter map still owned). -/
def ownRSn (V : GSet w64) (w : w64) (m : RSM) (q : tracker.ReplicationSet) : IProp GF :=
  iprop(∃ m', ⌜RSWF V w m' ∧ m'.wit = m.wit⌝ ∗ (ownRS q m' ∨ ownRSb q m'))

theorem ownRSn_persist (V : GSet w64) (w : w64) (m : RSM) (q : tracker.ReplicationSet) :
    ownRSn (GF := GF) V w m q ⊢ |==> ∃ m', ⌜RSWF V w m' ∧ m'.wit = m.wit⌝ ∗ ownRS q m' := by
  unfold ownRSn
  iintro ⟨%m', %Hm, (#Hq | Hq)⟩
  · imodintro; iexists m'; iframe Hq; ipureintro; exact Hm
  · imod ownRSb_persist _ _ $$ Hq with #Hq
    imodintro; iexists m'; iframe Hq; ipureintro; exact Hm

/-- A peer's `Progress` struct, out of the progress map's and back. -/
theorem progs_acc_at (prs : GMap w64 Loc) (pvs : GMap w64 Progress) (id : w64) (pr : Loc)
    (Hpr : prs !! id = some pr) :
    ([∗map] _k ↦ pr;p ∈ prs;pvs, ownProgress (GF := GF) pr p) ⊢
      ∃ pv : tracker.Progress, pr ↦ pv ∗
        (pr ↦ pv -∗ [∗map] _k ↦ pr;p ∈ prs;pvs, ownProgress (GF := GF) pr p) := by
  iintro Hprogs
  ihave %Hiff := BigSepM2.bigSepM2_lookup_iff $$ Hprogs
  obtain ⟨p, Hp⟩ := Option.isSome_iff_exists.1
    ((Hiff id).1 (by show (prs !! id).isSome = true; rw [Hpr]; rfl))
  icases BigSepM2.bigSepM2_lookup_acc (Φ := fun _ pr p => ownProgress (GF := GF) pr p)
    (m1 := prs) (m2 := pvs) Hpr Hp $$ Hprogs with ⟨Hp, Hback⟩
  iNamed Hp
  iexists pv
  iframe Hpv
  iintro Hpv
  iapply Hback
  unfold ownProgress
  iexists pv
  iframe Hpv Hinfl
  ipureintro; exact Habs

/-- ... at a peer of `pvs`. -/
theorem progs_acc (prs : GMap w64 Loc) (pvs : GMap w64 Progress) (id : w64)
    (Hid : (pvs !! id).isSome) :
    ([∗map] _k ↦ pr;p ∈ prs;pvs, ownProgress (GF := GF) pr p) ⊢
      ∃ (pr : Loc) (pv : tracker.Progress), ⌜prs !! id = some pr⌝ ∗ pr ↦ pv ∗
        (pr ↦ pv -∗ [∗map] _k ↦ pr;p ∈ prs;pvs, ownProgress (GF := GF) pr p) := by
  iintro Hprogs
  ihave %Hiff := BigSepM2.bigSepM2_lookup_iff $$ Hprogs
  obtain ⟨pr, Hpr⟩ := Option.isSome_iff_exists.1 ((Hiff id).2 Hid)
  icases progs_acc_at prs pvs id pr Hpr $$ Hprogs with ⟨%pv, Hpv, Hback⟩
  iexists pr, pv
  iframe Hpv Hback
  ipureintro; exact Hpr

/-- `_, ok := m[k]` in a read-only id set (nil, empty). -/
theorem wp_scope_lookup2 (m : Loc) (S : GSet w64) (k : w64) :
    {{ ownScope (GF := GF) m S }}
      (App (App (Val (map.lookup2 go.uint64 (go.StructType []))) (Val #m)) (Val #k))
    {{ RET (PairV #() #(decide (k ∈ S))); True }} := by
  iintro %Φ #Hs HΦ
  unfold ownScope
  icases Hs with (⟨%Hn, %HS⟩ | ⟨%ids, %Hd, #Hm⟩)
  · subst Hn HS
    wp_auto
    rw [decide_eq_false (not_elem_of_empty k)]
    iapply HΦ; itrivial
  · wp_apply wp_map_lookup2 $$ Hm as -
    have h : k ∈ S ↔ (ids !! k).isSome = true := by
      rw [← Hd, GMap.elem_of_dom']; rfl
    rw [show decide (k ∈ S) = decide ((ids !! k).isSome = true) from decide_eq_decide.2 h]
    iapply HΦ; itrivial

/-- With no witness, the early return; else a copy of the epoch at the next subterm, each of whose
halves with an excluded voter ready to come back is rebuilt around a new excluded voter (an
inactive member of its replication set, or the witness: `rsChanged`), installed if one was. -/
theorem tracker.ProgressTracker.ChangeReplicationSet.wp_proof
    (wp_HasWitness : tracker.Epoch.HasWitness.spec (GF := GF) (hG := hG)) :
    tracker.ProgressTracker.ChangeReplicationSet.spec (GF := GF) (hG := hG) := by
  intro trk dq tv em V0 V1 w0 w1 pvs
  wp_start as ⟨Htrk, #He, Hres⟩
  ihave #He' := He
  iunfold ownEpoch at He'
  icases He' with ⟨%ev, %r0, %r1, #Hev, -⟩
  ihave %Hnn := typedPointsto_not_null $$ Hev
  wp_auto
  icases (Access.access
      (A := trk.[tracker.ProgressTracker, go!"Epoch"] ↦{dq} tv.Epoch')
      (A' := trk.[tracker.ProgressTracker, go!"Epoch"] ↦{dq} tv.Epoch')
      (P := trk ↦{dq} tv)) $$ Htrk with ⟨Hef, Htrkback⟩
  wp_auto
  ihave Htrk := Htrkback $$ Hef
  rw [decide_eq_false (by simpa using Hnn)]
  wp_auto
  wp_apply wp_HasWitness tv.Epoch' em $$ [$He]
  cases Hhw : em.hasWit
  · -- no witness: `return false`
    wp_auto
    iapply HΦ
    iframe Htrk Hres
    ileft; ipureintro; exact ⟨rfl, rfl⟩
  icases Hres with (%Hf | Hres)
  · cases Hf
  iunfold chgRes at Hres
  icases Hres with ⟨%Hc, Hpm⟩
  obtain ⟨Hdq, Hwf, H0, H1, Hdom⟩ := Hc
  subst Hdq
  -- the epoch's fields, read-only
  icases ownEpoch_we _ _ $$ He with ⟨#Hw0f, -, #Hw1f, -⟩
  iunfold ownEpoch at He
  icases He with ⟨%ev', %r0, %r1, #Hev', %Hsa, #Hrs0, #Hrs1⟩
  obtain ⟨Hsub, Harr⟩ := Hsa
  icases (Access.access (A := iprop(tv.Epoch'.[tracker.Epoch, go!"Subterm"] ↦□ ev'.Subterm'))
    (A' := iprop(tv.Epoch'.[tracker.Epoch, go!"Subterm"] ↦□ ev'.Subterm'))
    (P := iprop(tv.Epoch' ↦□ ev'))) $$ Hev' with ⟨#Hs, -⟩
  icases (Access.access
    (A := iprop(tv.Epoch'.[tracker.Epoch, go!"ReplicationSet"] ↦□ ev'.ReplicationSet'))
    (A' := iprop(tv.Epoch'.[tracker.Epoch, go!"ReplicationSet"] ↦□ ev'.ReplicationSet'))
    (P := iprop(tv.Epoch' ↦□ ev'))) $$ Hev' with ⟨#Hrsf, -⟩
  icases array_acc_same _ (sint.Z (W64 0)) _ _ _ r0 (by decide) (by rw [Harr]; rfl) $$ Hrsf
    with ⟨#Hr0, -⟩
  icases array_acc_same _ (sint.Z (W64 1)) _ _ _ r1 (by decide) (by rw [Harr]; rfl) $$ Hrsf
    with ⟨#Hr1, -⟩
  wp_auto
  -- both halves are well formed (the epoch has a witness: not the bare one)
  have Hwf' : RSWF V0 w0 em.rs0 ∧ RSWF V1 w1 em.rs1 := by
    rcases Hwf with ⟨-, -, h0, h1⟩ | ⟨-, h0, h1⟩
    · exfalso; simp [EpochM.hasWit, h0, h1, RSM.bare] at Hhw
    · exact ⟨h0, h1⟩
  obtain ⟨Hwf0, Hwf1⟩ := Hwf'
  have Hnb : ¬ (w0 = W64 0 ∧ w1 = W64 0) := by
    rcases Hwf with ⟨-, -, h0, h1⟩ | ⟨h, -, -⟩
    · exfalso; simp [EpochM.hasWit, h0, h1, RSM.bare] at Hhw
    · exact h
  rename_i ii_ptr
  irename : (ii_ptr ↦ zero_val w64 : IProp GF) => ii
  icases epoch_split _ _ $$ «$r0» with ⟨%Hrn, Hsubf, Hrs⟩
  -- `for i, set := range epoch.ReplicationSet`: the halves before `j` done
  ihave HI : (∃ (j iv : w64) (sv : tracker.ReplicationSet) (cb : Bool)
      (arr : GoArray tracker.ReplicationSet 2),
      "i" ∷ i_ptr ↦ j ∗ "ii" ∷ ii_ptr ↦ iv ∗ "set" ∷ set_ptr ↦ sv ∗ "changed" ∷ changed_ptr ↦ cb ∗
      "Hrs" ∷ «$r0_ptr».[tracker.Epoch, go!"ReplicationSet"] ↦ arr ∗
      "Htrk" ∷ trk ↦ tv ∗ "p" ∷ p_ptr ↦ trk ∗
      "result" ∷ result_ptr ↦ «$r0_ptr» ∗ "Hpm" ∷ ownProgressMap tv.Progress' pvs ∗
      "Hj" ∷ (⌜j = W64 0 ∧ arr.arr = [r0, r1]⌝ ∨
        (⌜j = W64 1⌝ ∗ ∃ q0, ⌜arr.arr = [q0, r1]⌝ ∗ ownRSn V0 w0 em.rs0 q0) ∨
        (⌜j = W64 2⌝ ∗ ∃ q0 q1, ⌜arr.arr = [q0, q1]⌝ ∗ ownRSn V0 w0 em.rs0 q0 ∗
          ownRSn V1 w1 em.rs1 q1)) : IProp GF)
    $$ [i ii set changed Hrs Htrk p result Hpm]
  · iexists W64 0, _, _, false, _
    iframe i ii set changed Hrs Htrk p result Hpm
    ileft; ipureintro; exact ⟨rfl, rfl⟩
  wp_for HI
  icases Hj with (⟨%Hj, %Ha⟩ | ⟨%Hj, %q0, %Ha, Hq0⟩ | ⟨%Hj, %q0, %q1, %Ha, Hq0, Hq1⟩)
  · subst Hj
    wp_if_destruct <;> try (exfalso; word)
    wp_func_lits
    rw [Harr]
    simp only [List.getElem?_cons_zero]
    wp_auto
    iunfold ownRS at Hrs0
    icases Hrs0 with ⟨%Hwe0, #Hsc0⟩
    obtain ⟨Hw0e, Hx0e⟩ := Hwe0
    rw [Hx0e]
    wp_if_destruct
    · -- no excluded voter: `continue`, the half as it was
      wp_for_post
      simp only [named]
      iframe HΦ Hsubf
      iexists W64 0 + W64 1, W64 0, r0, cb, arr
      iframe i ii set changed Hrs Htrk p result Hpm
      iright; ileft
      isplitr
      · ipureintro; rfl
      iexists r0
      isplitr
      · ipureintro; exact Ha
      unfold ownRSn
      iexists em.rs0
      isplitr
      · ipureintro; exact ⟨Hwf0, rfl⟩
      ileft; unfold ownRS; isplitr
      · ipureintro; exact ⟨Hw0e, Hx0e⟩
      iexact Hsc0
    have Hx0 := Hif
    have Hmem0 := Hwf0.mem Hx0
    iNamed Hpm
    icases progs_acc prs pvs em.rs0.excl (Hdom _ (Or.inl Hmem0.2)) $$ Hprogs
      with ⟨%pr, %pv, %Hpr, Hpv, Hprback⟩
    have Hpr' : prs !! r0.Excluded' = some pr := by rw [Hx0e]; exact Hpr
    wp_apply wp_map_lookup1 $$ Hprs as -
    rw [Hpr']
    simp only [Option.getD_some]
    -- `isExcludedReady`: some bool
    wp_bind (If (App (Val (GoInstruction (GoLoad go.bool))) _) _ _)
    iapply (wp_wand (Φ := fun v => iprop(⌜∃ b : Bool, v = #b⌝ ∗ pr ↦ pv ∗ set_ptr ↦ r0 ∗
        trk ↦ tv ∗ p_ptr ↦ trk))) $$ [Hpv set Htrk p]
    · wp_auto
      cases pv.RecentActive'
      · wp_auto
        iframe Hpv set Htrk p
        ipureintro; exact ⟨false, rfl⟩
      · wp_auto
        wp_if_destruct
        · iframe Hpv set Htrk p
          ipureintro; exact ⟨true, rfl⟩
        · wp_apply wp_map_lookup1 $$ Hprs as -
          rw [Hpr']
          simp only [Option.getD_some]
          wp_auto
          iframe Hpv set Htrk p
          ipureintro; exact ⟨_, rfl⟩
    iintro %v ⟨%Hv, Hpv, set, Htrk, p⟩
    obtain ⟨rdy, rfl⟩ := Hv
    ihave Hprogs := Hprback $$ Hpv
    ihave Hpm : ownProgressMap tv.Progress' pvs $$ [Hprogs]
    · unfold ownProgressMap; iexists prs; iframe Hprs Hprogs
    cases rdy
    · -- not ready: `continue`
      wp_auto
      wp_for_post
      simp only [named]
      iframe HΦ Hsubf
      iexists W64 0 + W64 1, W64 0, r0, cb, arr
      iframe i ii set changed Hrs Htrk p result Hpm
      iright; ileft
      isplitr
      · ipureintro; rfl
      iexists r0
      isplitr
      · ipureintro; exact Ha
      unfold ownRSn
      iexists em.rs0
      isplitr
      · ipureintro; exact ⟨Hwf0, rfl⟩
      ileft; unfold ownRS; isplitr
      · ipureintro; exact ⟨Hw0e, Hx0e⟩
      iexact Hsc0
    wp_auto
    -- `for id, pr := range p.Progress`: an inactive member of the replication set, or none
    iNamed Hpm
    wp_bind (App (App (Val (map.forRange go.uint64 tracker.Progress.ty.PointerType)) _) _)
    iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ ∃ (x : w64) (pp : Loc) (iid : w64),
        id_ptr ↦ x ∗ pr_ptr ↦ pp ∗ inactiveID_ptr ↦ iid ∗ set_ptr ↦ r0 ∗
        ([∗map] _k ↦ pr;p ∈ prs;pvs, ownProgress (GF := GF) pr p) ∗
        ⌜iid = W64 0 ∨ iid = em.rs0.wit ∨ iid ∈ em.rs0.nwv⌝)))
      $$ [id pr inactiveID set Hprogs]
    · wp_func_lits
      iapply wp_map_for_range (fun (keys : List w64) (i : Int) => iprop(
          ∃ (x : w64) (pp : Loc) (iid : w64),
          "id" ∷ id_ptr ↦ x ∗ "pr" ∷ pr_ptr ↦ pp ∗ "inactiveID" ∷ inactiveID_ptr ↦ iid ∗
          "set" ∷ set_ptr ↦ r0 ∗
          "Hprogs" ∷ ([∗map] _k ↦ pr;p ∈ prs;pvs, ownProgress (GF := GF) pr p) ∗
          "%Hiid" ∷ ⌜iid = W64 0 ∨ iid = em.rs0.wit ∨ iid ∈ em.rs0.nwv⌝)) $$ Hprs
      iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
      isplitl [id pr inactiveID set Hprogs]
      · iexists _, _, W64 0
        simp only [named]
        iframe id pr inactiveID set Hprogs
        ipureintro; simp
      isplitr
      · imodintro
        iintro %i %key %vv ⟨%Hkey, %Hvv⟩ HP
        iNamed HP
        wp_auto
        icases progs_acc_at prs pvs key vv Hvv $$ Hprogs with ⟨%pv', Hpv, Hprback⟩
        wp_auto
        ihave Hprogs := Hprback $$ Hpv
        cases pv'.RecentActive'
        · -- inactive: in the replication set (or its witness)?
          wp_auto
          wp_apply wp_scope_lookup2 r0.NonWitnessVoters' em.rs0.nwv key $$ Hsc0
          by_cases hk : key ∈ em.rs0.nwv
          · rw [decide_eq_true hk]
            wp_auto
            unfold forMapPostcondition
            iright; iright; ileft
            isplitr
            · ipureintro; rfl
            simp only []
            iintro -
            isplitr
            · ipureintro; trivial
            iexists _, _, key
            iframe id pr inactiveID set Hprogs
            ipureintro; exact Or.inr (Or.inr hk)
          · rw [decide_eq_false hk]
            wp_auto
            rw [Hw0e]
            wp_if_destruct
            · unfold forMapPostcondition
              iright; iright; ileft
              isplitr
              · ipureintro; rfl
              simp only []
              iintro -
              isplitr
              · ipureintro; trivial
              iexists _, _, em.rs0.wit
              iframe id pr inactiveID set Hprogs
              ipureintro; exact Or.inr (Or.inl rfl)
            · unfold forMapPostcondition
              iright; ileft
              isplitr
              · ipureintro; rfl
              iexists _, _, iid
              simp only [named]
              iframe id pr inactiveID set Hprogs
              ipureintro; exact Hiid
        · wp_auto
          unfold forMapPostcondition
          iright; ileft
          isplitr
          · ipureintro; rfl
          iexists _, _, iid
          simp only [named]
          iframe id pr inactiveID set Hprogs
          ipureintro; exact Hiid
      iintro HP -
      iNamed HP
      isplitr
      · ipureintro; rfl
      iexists _, _, iid
      iframe id pr inactiveID set Hprogs
      ipureintro; exact Hiid
    iintro %v ⟨%Hv, %x, %pp, %iid, id, pr, inactiveID, set, Hprogs, %Hiid⟩
    subst Hv
    ihave Hpm : ownProgressMap tv.Progress' pvs $$ [Hprogs]
    · unfold ownProgressMap; iexists prs; iframe Hprs Hprogs
    wp_auto
    -- `if inactiveID == 0 && set.Excluded == set.Witness { continue }`
    wp_bind (If (Val #(decide (iid = W64 0))) _ _)
    iapply (wp_wand (Φ := fun v => iprop(⌜v = #(decide (iid = W64 0 ∧
        em.rs0.excl = em.rs0.wit))⌝ ∗ set_ptr ↦ r0))) $$ [set]
    · by_cases h : iid = W64 0
      · rw [decide_eq_true h]
        wp_auto
        rw [Hx0e, Hw0e]
        iframe set
        ipureintro
        by_cases h' : em.rs0.excl = em.rs0.wit
        · rw [decide_eq_true h', decide_eq_true ⟨h, h'⟩]
        · rw [decide_eq_false h', decide_eq_false (fun hh => h' hh.2)]
      · rw [decide_eq_false h]
        wp_auto
        iframe set
        ipureintro
        rw [decide_eq_false (fun hh => h hh.1)]
    iintro %v ⟨%Hv, set⟩
    subst Hv
    wp_if_destruct
    · -- nothing to swap: `continue`
      wp_for_post
      simp only [named]
      iframe HΦ Hsubf
      iexists W64 0 + W64 1, W64 0, r0, cb, arr
      iframe i ii set changed Hrs Htrk p result Hpm
      iright; ileft
      isplitr
      · ipureintro; rfl
      iexists r0
      isplitr
      · ipureintro; exact Ha
      unfold ownRSn
      iexists em.rs0
      isplitr
      · ipureintro; exact ⟨Hwf0, rfl⟩
      ileft; unfold ownRS; isplitr
      · ipureintro; exact ⟨Hw0e, Hx0e⟩
      iexact Hsc0
    have Hnc := Hif
    -- `changed = true`; the half rebuilt around `x`
    icases array_acc (GF := GF) _ (sint.Z (W64 0)) _ _ arr r0 (by decide) (by rw [Ha]; rfl)
      $$ Hrs with ⟨Hel, Hrsback⟩
    wp_bind (If (Val #(decide (uint.Z (W64 0) < uint.Z iid))) _ _)
    iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ ∃ mref : Loc,
        arrayIndexRef tracker.ReplicationSet (sint.Z (W64 0))
          «$r0_ptr».[tracker.Epoch, go!"ReplicationSet"] ↦
          tracker.ReplicationSet.mk em.rs0.wit (if iid = W64 0 then em.rs0.wit else iid) mref ∗
        mref ↦$ (∅ : GMap w64 Unit) ∗ trk ↦ tv ∗ p_ptr ↦ trk ∗ inactiveID_ptr ↦ iid ∗
        result_ptr ↦ «$r0_ptr» ∗ ii_ptr ↦ W64 0)))
      $$ [Hel Htrk p inactiveID result ii]
    · by_cases h : iid = W64 0
      · subst h
        rw [show decide (uint.Z (W64 0) < uint.Z (W64 0)) = false by decide]
        wp_auto
        wp_apply wp_map_make1 (K := w64) (V := Unit) as %mref Hmref
        iframe Htrk p inactiveID result ii
        isplitr
        · ipureintro; rfl
        iexists mref
        iframe Hmref
        simp only [↓reduceIte]
        iexact Hel
      · rw [show decide (uint.Z (W64 0) < uint.Z iid) = true by
          apply decide_eq_true; have : uint.Z iid ≠ 0 := fun e => h (by word); word]
        wp_auto
        wp_apply wp_map_make1 (K := w64) (V := Unit) as %mref Hmref
        iframe Htrk p inactiveID result ii
        isplitr
        · ipureintro; rfl
        iexists mref
        iframe Hmref
        rw [if_neg h]
        iexact Hel
    iintro %v ⟨%Hv, %mref, Hel, Hmref, Htrk, p, inactiveID, result, ii⟩
    subst Hv
    wp_auto
    generalize Hxd : (if iid = W64 0 then em.rs0.wit else iid) = x
    -- `for id := range set.NonWitnessVoters`: all but `x`
    wp_bind (App (App (Val (map.forRange go.uint64 (go.StructType []))) _) _)
    iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗
        ∃ (ids mv : GMap w64 Unit) (xi : w64),
        ⌜domSet mv = ids \ {[x]} ∧ domSet ids = em.rs0.nwv⌝ ∗ id_ptr ↦ xi ∗
        arrayIndexRef tracker.ReplicationSet (sint.Z (W64 0))
          «$r0_ptr».[tracker.Epoch, go!"ReplicationSet"] ↦ tracker.ReplicationSet.mk em.rs0.wit x mref ∗
        mref ↦$ mv ∗ result_ptr ↦ «$r0_ptr» ∗ ii_ptr ↦ W64 0)))
      $$ [id Hel Hmref result ii]
    · ihave #Hsc0' := Hsc0
      iunfold ownScope at Hsc0'
      icases Hsc0' with (⟨%Hn, %HS⟩ | ⟨%ids, %Hd, #Hids⟩)
      · rw [Hn]
        wp_func_lits
        wp_auto
        isplitr
        · ipureintro; rfl
        iexists ∅, ∅, _
        iframe id Hel Hmref result ii
        ipureintro
        refine ⟨?_, by rw [HS, GMap.dom_empty]⟩
        rw [GMap.dom_empty]
        apply set_eq; intro k
        rw [elem_of_difference]
        constructor
        · intro h; exact absurd h (not_elem_of_empty k)
        · intro h; exact absurd h.1 (not_elem_of_empty k)
      wp_func_lits
      iapply wp_map_for_range (fun (keys : List w64) (i : Int) => iprop(∃ (xi : w64)
          (mv : GMap w64 Unit),
          "%Hi" ∷ ⌜0 ≤ i⌝ ∗
          "%Hmv" ∷ ⌜∀ k, k ∈ domSet mv ↔ k ∈ keys.take i.toNat ∧ k ≠ x⌝ ∗
          "id" ∷ id_ptr ↦ xi ∗
          "Hel" ∷ arrayIndexRef tracker.ReplicationSet (sint.Z (W64 0))
          «$r0_ptr».[tracker.Epoch, go!"ReplicationSet"] ↦ tracker.ReplicationSet.mk em.rs0.wit x mref ∗
          "Hmref" ∷ mref ↦$ mv ∗ "result" ∷ result_ptr ↦ «$r0_ptr» ∗
          "ii" ∷ ii_ptr ↦ W64 0)) $$ Hids
      iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
      isplitl [id Hel Hmref result ii]
      · iexists _, ∅
        simp only [named]
        iframe id Hel Hmref result ii
        ipureintro
        refine ⟨Int.le_refl _, fun k => ?_⟩
        rw [GMap.dom_empty]
        simp only [Int.toNat_zero, List.take_zero, List.not_mem_nil, _root_.false_and]
        exact iff_false_intro (not_elem_of_empty k)
      isplitr
      · imodintro
        iintro %i %key %vv ⟨%Hkey, %Hvv⟩ HP
        iNamed HP
        have Hst := reset_step keys i key x mv Hi Hkey Hmv
        wp_auto
        wp_if_destruct
        · -- `id == x`: skipped
          have Heq : key = x := by simpa using Hif
          unfold forMapPostcondition
          iright; ileft
          isplitr
          · ipureintro; rfl
          iexists key, mv
          simp only [named]
          iframe id Hel Hmref result ii
          ipureintro
          exact ⟨by omega, (Hst.1 Heq).1⟩
        · -- `NonWitnessVoters[id] = struct{}{}`
          have Hne : key ≠ x := by simpa using Hif
          wp_apply wp_mapInsert $$ Hmref as Hmref
          unfold forMapPostcondition
          iright; ileft
          isplitr
          · ipureintro; rfl
          iexists key, _
          simp only [named]
          iframe id Hel Hmref result ii
          ipureintro
          exact ⟨by omega, (Hst.2 Hne).1⟩
      iintro HP -
      iNamed HP
      rw [Int.toNat_natCast, ← Hklen, List.take_length] at Hmv
      obtain ⟨Hd', -⟩ := reset_done ids x keys mv Hkset Hmv
      isplitr
      · ipureintro; rfl
      iexists ids, mv, xi
      iframe id Hel Hmref result ii
      ipureintro; exact ⟨Hd', Hd⟩
    iintro %v ⟨%Hv, %ids, %mv, %xi, %Hdm, id, Hel, Hmref, result, ii⟩
    subst Hv
    wp_auto
    -- `if set.Excluded != x && set.Excluded != set.Witness { NonWitnessVoters[set.Excluded] = .. }`
    wp_bind (If (Val #(!decide (r0.Excluded' = x))) _ _)
    iapply (wp_wand (Φ := fun v => iprop(⌜v = #(decide (em.rs0.excl ≠ x ∧
        em.rs0.excl ≠ em.rs0.wit))⌝ ∗ set_ptr ↦ r0))) $$ [set]
    · rw [Hx0e]
      by_cases h : em.rs0.excl = x
      · rw [decide_eq_true h]
        wp_auto
        iframe set
        ipureintro
        rw [decide_eq_false (fun hh => hh.1 h)]
      · rw [decide_eq_false h]
        wp_auto
        rw [Hx0e, Hw0e]
        iframe set
        ipureintro
        by_cases h' : em.rs0.excl = em.rs0.wit
        · rw [decide_eq_true h', decide_eq_false (fun hh => hh.2 h')]; rfl
        · rw [decide_eq_false h', decide_eq_true ⟨h, h'⟩]; rfl
    iintro %v ⟨%Hv, set⟩
    subst Hv
    wp_bind (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) _) _ _)
    iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗
        mref ↦$ (if em.rs0.excl ≠ x ∧ em.rs0.excl ≠ em.rs0.wit then <[em.rs0.excl := ()]> mv
          else mv) ∗ set_ptr ↦ r0 ∗ arrayIndexRef tracker.ReplicationSet (sint.Z (W64 0))
          «$r0_ptr».[tracker.Epoch, go!"ReplicationSet"] ↦ tracker.ReplicationSet.mk em.rs0.wit x mref ∗
        result_ptr ↦ «$r0_ptr» ∗ ii_ptr ↦ W64 0))) $$ [Hmref set Hel result ii]
    · by_cases hc : em.rs0.excl ≠ x ∧ em.rs0.excl ≠ em.rs0.wit
      · rw [decide_eq_true hc]
        wp_auto
        rw [Hx0e]
        wp_apply wp_mapInsert $$ Hmref as Hmref
        rw [if_pos hc]
        iframe Hmref set Hel result ii
        ipureintro; rfl
      · rw [decide_eq_false hc]
        wp_auto
        rw [if_neg hc]
        iframe Hmref set Hel result ii
        ipureintro; rfl
    iintro %v ⟨%Hv, Hmref, set, Hel, result, ii⟩
    subst Hv
    have Hxc : x = em.rs0.wit ∨ x ∈ em.rs0.nwv := by
      subst Hxd
      rcases Hiid with h | h | h
      · rw [if_pos h]; exact Or.inl rfl
      · by_cases h0 : iid = W64 0
        · rw [if_pos h0]; exact Or.inl rfl
        · rw [if_neg h0]; exact Or.inl h
      · by_cases h0 : iid = W64 0
        · rw [if_pos h0]; exact Or.inl rfl
        · rw [if_neg h0]; exact Or.inr h
    wp_for_post
    simp only [named]
    iframe HΦ Hsubf
    iexists W64 0 + W64 1, W64 0, r0, true,
      array.mk 2 (arr.arr.set (sint.Z (W64 0)).toNat (tracker.ReplicationSet.mk em.rs0.wit x mref))
    ihave Hrs := Hrsback $$ %(tracker.ReplicationSet.mk em.rs0.wit x mref) Hel
    iframe i ii set changed Hrs Htrk p result Hpm
    iright; ileft
    isplitr
    · ipureintro; rfl
    iexists tracker.ReplicationSet.mk em.rs0.wit x mref
    isplitr
    · ipureintro; rw [Ha]; rfl
    unfold ownRSn
    iexists rsChanged em.rs0 x
    isplitr
    · ipureintro; exact ⟨rsChanged_wf x Hwf0 (Hwf0.wit_nz Hx0) Hxc, rfl⟩
    iright
    unfold ownRSb
    isplitr
    · ipureintro; exact ⟨rfl, rfl⟩
    iexists _
    iframe Hmref
    ipureintro; exact chg_dom em.rs0 x ids mv Hdm.1 Hdm.2
  · subst Hj
    wp_if_destruct <;> try (exfalso; word)
    wp_func_lits
    rw [Harr]
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero]
    wp_auto
    iunfold ownRS at Hrs1
    icases Hrs1 with ⟨%Hwe1, #Hsc1⟩
    obtain ⟨Hw1e, Hx1e⟩ := Hwe1
    rw [Hx1e]
    wp_if_destruct
    · -- no excluded voter: `continue`, the half as it was
      wp_for_post
      simp only [named]
      iframe HΦ Hsubf
      iexists W64 1 + W64 1, W64 1, r1, cb, arr
      iframe i ii set changed Hrs Htrk p result Hpm
      iright; iright
      isplitr
      · ipureintro; rfl
      iexists q0, r1
      isplitr
      · ipureintro; exact Ha
      isplitl [Hq0]
      · iexact Hq0
      unfold ownRSn
      iexists em.rs1
      isplitr
      · ipureintro; exact ⟨Hwf1, rfl⟩
      ileft; unfold ownRS; isplitr
      · ipureintro; exact ⟨Hw1e, Hx1e⟩
      iexact Hsc1
    have Hx1 := Hif
    have Hmem1 := Hwf1.mem Hx1
    iNamed Hpm
    icases progs_acc prs pvs em.rs1.excl (Hdom _ (Or.inr Hmem1.2)) $$ Hprogs
      with ⟨%pr, %pv, %Hpr, Hpv, Hprback⟩
    have Hpr' : prs !! r1.Excluded' = some pr := by rw [Hx1e]; exact Hpr
    wp_apply wp_map_lookup1 $$ Hprs as -
    rw [Hpr']
    simp only [Option.getD_some]
    -- `isExcludedReady`: some bool
    wp_bind (If (App (Val (GoInstruction (GoLoad go.bool))) _) _ _)
    iapply (wp_wand (Φ := fun v => iprop(⌜∃ b : Bool, v = #b⌝ ∗ pr ↦ pv ∗ set_ptr ↦ r1 ∗
        trk ↦ tv ∗ p_ptr ↦ trk))) $$ [Hpv set Htrk p]
    · wp_auto
      cases pv.RecentActive'
      · wp_auto
        iframe Hpv set Htrk p
        ipureintro; exact ⟨false, rfl⟩
      · wp_auto
        wp_if_destruct
        · iframe Hpv set Htrk p
          ipureintro; exact ⟨true, rfl⟩
        · wp_apply wp_map_lookup1 $$ Hprs as -
          rw [Hpr']
          simp only [Option.getD_some]
          wp_auto
          iframe Hpv set Htrk p
          ipureintro; exact ⟨_, rfl⟩
    iintro %v ⟨%Hv, Hpv, set, Htrk, p⟩
    obtain ⟨rdy, rfl⟩ := Hv
    ihave Hprogs := Hprback $$ Hpv
    ihave Hpm : ownProgressMap tv.Progress' pvs $$ [Hprogs]
    · unfold ownProgressMap; iexists prs; iframe Hprs Hprogs
    cases rdy
    · -- not ready: `continue`
      wp_auto
      wp_for_post
      simp only [named]
      iframe HΦ Hsubf
      iexists W64 1 + W64 1, W64 1, r1, cb, arr
      iframe i ii set changed Hrs Htrk p result Hpm
      iright; iright
      isplitr
      · ipureintro; rfl
      iexists q0, r1
      isplitr
      · ipureintro; exact Ha
      isplitl [Hq0]
      · iexact Hq0
      unfold ownRSn
      iexists em.rs1
      isplitr
      · ipureintro; exact ⟨Hwf1, rfl⟩
      ileft; unfold ownRS; isplitr
      · ipureintro; exact ⟨Hw1e, Hx1e⟩
      iexact Hsc1
    wp_auto
    -- `for id, pr := range p.Progress`: an inactive member of the replication set, or none
    iNamed Hpm
    wp_bind (App (App (Val (map.forRange go.uint64 tracker.Progress.ty.PointerType)) _) _)
    iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ ∃ (x : w64) (pp : Loc) (iid : w64),
        id_ptr ↦ x ∗ pr_ptr ↦ pp ∗ inactiveID_ptr ↦ iid ∗ set_ptr ↦ r1 ∗
        ([∗map] _k ↦ pr;p ∈ prs;pvs, ownProgress (GF := GF) pr p) ∗
        ⌜iid = W64 0 ∨ iid = em.rs1.wit ∨ iid ∈ em.rs1.nwv⌝)))
      $$ [id pr inactiveID set Hprogs]
    · wp_func_lits
      iapply wp_map_for_range (fun (keys : List w64) (i : Int) => iprop(
          ∃ (x : w64) (pp : Loc) (iid : w64),
          "id" ∷ id_ptr ↦ x ∗ "pr" ∷ pr_ptr ↦ pp ∗ "inactiveID" ∷ inactiveID_ptr ↦ iid ∗
          "set" ∷ set_ptr ↦ r1 ∗
          "Hprogs" ∷ ([∗map] _k ↦ pr;p ∈ prs;pvs, ownProgress (GF := GF) pr p) ∗
          "%Hiid" ∷ ⌜iid = W64 0 ∨ iid = em.rs1.wit ∨ iid ∈ em.rs1.nwv⌝)) $$ Hprs
      iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
      isplitl [id pr inactiveID set Hprogs]
      · iexists _, _, W64 0
        simp only [named]
        iframe id pr inactiveID set Hprogs
        ipureintro; simp
      isplitr
      · imodintro
        iintro %i %key %vv ⟨%Hkey, %Hvv⟩ HP
        iNamed HP
        wp_auto
        icases progs_acc_at prs pvs key vv Hvv $$ Hprogs with ⟨%pv', Hpv, Hprback⟩
        wp_auto
        ihave Hprogs := Hprback $$ Hpv
        cases pv'.RecentActive'
        · -- inactive: in the replication set (or its witness)?
          wp_auto
          wp_apply wp_scope_lookup2 r1.NonWitnessVoters' em.rs1.nwv key $$ Hsc1
          by_cases hk : key ∈ em.rs1.nwv
          · rw [decide_eq_true hk]
            wp_auto
            unfold forMapPostcondition
            iright; iright; ileft
            isplitr
            · ipureintro; rfl
            simp only []
            iintro -
            isplitr
            · ipureintro; trivial
            iexists _, _, key
            iframe id pr inactiveID set Hprogs
            ipureintro; exact Or.inr (Or.inr hk)
          · rw [decide_eq_false hk]
            wp_auto
            rw [Hw1e]
            wp_if_destruct
            · unfold forMapPostcondition
              iright; iright; ileft
              isplitr
              · ipureintro; rfl
              simp only []
              iintro -
              isplitr
              · ipureintro; trivial
              iexists _, _, em.rs1.wit
              iframe id pr inactiveID set Hprogs
              ipureintro; exact Or.inr (Or.inl rfl)
            · unfold forMapPostcondition
              iright; ileft
              isplitr
              · ipureintro; rfl
              iexists _, _, iid
              simp only [named]
              iframe id pr inactiveID set Hprogs
              ipureintro; exact Hiid
        · wp_auto
          unfold forMapPostcondition
          iright; ileft
          isplitr
          · ipureintro; rfl
          iexists _, _, iid
          simp only [named]
          iframe id pr inactiveID set Hprogs
          ipureintro; exact Hiid
      iintro HP -
      iNamed HP
      isplitr
      · ipureintro; rfl
      iexists _, _, iid
      iframe id pr inactiveID set Hprogs
      ipureintro; exact Hiid
    iintro %v ⟨%Hv, %x, %pp, %iid, id, pr, inactiveID, set, Hprogs, %Hiid⟩
    subst Hv
    ihave Hpm : ownProgressMap tv.Progress' pvs $$ [Hprogs]
    · unfold ownProgressMap; iexists prs; iframe Hprs Hprogs
    wp_auto
    -- `if inactiveID == 0 && set.Excluded == set.Witness { continue }`
    wp_bind (If (Val #(decide (iid = W64 0))) _ _)
    iapply (wp_wand (Φ := fun v => iprop(⌜v = #(decide (iid = W64 0 ∧
        em.rs1.excl = em.rs1.wit))⌝ ∗ set_ptr ↦ r1))) $$ [set]
    · by_cases h : iid = W64 0
      · rw [decide_eq_true h]
        wp_auto
        rw [Hx1e, Hw1e]
        iframe set
        ipureintro
        by_cases h' : em.rs1.excl = em.rs1.wit
        · rw [decide_eq_true h', decide_eq_true ⟨h, h'⟩]
        · rw [decide_eq_false h', decide_eq_false (fun hh => h' hh.2)]
      · rw [decide_eq_false h]
        wp_auto
        iframe set
        ipureintro
        rw [decide_eq_false (fun hh => h hh.1)]
    iintro %v ⟨%Hv, set⟩
    subst Hv
    wp_if_destruct
    · -- nothing to swap: `continue`
      wp_for_post
      simp only [named]
      iframe HΦ Hsubf
      iexists W64 1 + W64 1, W64 1, r1, cb, arr
      iframe i ii set changed Hrs Htrk p result Hpm
      iright; iright
      isplitr
      · ipureintro; rfl
      iexists q0, r1
      isplitr
      · ipureintro; exact Ha
      isplitl [Hq0]
      · iexact Hq0
      unfold ownRSn
      iexists em.rs1
      isplitr
      · ipureintro; exact ⟨Hwf1, rfl⟩
      ileft; unfold ownRS; isplitr
      · ipureintro; exact ⟨Hw1e, Hx1e⟩
      iexact Hsc1
    have Hnc := Hif
    -- `changed = true`; the half rebuilt around `x`
    icases array_acc (GF := GF) _ (sint.Z (W64 1)) _ _ arr r1 (by decide) (by rw [Ha]; rfl)
      $$ Hrs with ⟨Hel, Hrsback⟩
    wp_bind (If (Val #(decide (uint.Z (W64 0) < uint.Z iid))) _ _)
    iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ ∃ mref : Loc,
        arrayIndexRef tracker.ReplicationSet (sint.Z (W64 1))
          «$r0_ptr».[tracker.Epoch, go!"ReplicationSet"] ↦
          tracker.ReplicationSet.mk em.rs1.wit (if iid = W64 0 then em.rs1.wit else iid) mref ∗
        mref ↦$ (∅ : GMap w64 Unit) ∗ trk ↦ tv ∗ p_ptr ↦ trk ∗ inactiveID_ptr ↦ iid ∗
        result_ptr ↦ «$r0_ptr» ∗ ii_ptr ↦ W64 1)))
      $$ [Hel Htrk p inactiveID result ii]
    · by_cases h : iid = W64 0
      · subst h
        rw [show decide (uint.Z (W64 0) < uint.Z (W64 0)) = false by decide]
        wp_auto
        wp_apply wp_map_make1 (K := w64) (V := Unit) as %mref Hmref
        iframe Htrk p inactiveID result ii
        isplitr
        · ipureintro; rfl
        iexists mref
        iframe Hmref
        simp only [↓reduceIte]
        iexact Hel
      · rw [show decide (uint.Z (W64 0) < uint.Z iid) = true by
          apply decide_eq_true; have : uint.Z iid ≠ 0 := fun e => h (by word); word]
        wp_auto
        wp_apply wp_map_make1 (K := w64) (V := Unit) as %mref Hmref
        iframe Htrk p inactiveID result ii
        isplitr
        · ipureintro; rfl
        iexists mref
        iframe Hmref
        rw [if_neg h]
        iexact Hel
    iintro %v ⟨%Hv, %mref, Hel, Hmref, Htrk, p, inactiveID, result, ii⟩
    subst Hv
    wp_auto
    generalize Hxd : (if iid = W64 0 then em.rs1.wit else iid) = x
    -- `for id := range set.NonWitnessVoters`: all but `x`
    wp_bind (App (App (Val (map.forRange go.uint64 (go.StructType []))) _) _)
    iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗
        ∃ (ids mv : GMap w64 Unit) (xi : w64),
        ⌜domSet mv = ids \ {[x]} ∧ domSet ids = em.rs1.nwv⌝ ∗ id_ptr ↦ xi ∗
        arrayIndexRef tracker.ReplicationSet (sint.Z (W64 1))
          «$r0_ptr».[tracker.Epoch, go!"ReplicationSet"] ↦ tracker.ReplicationSet.mk em.rs1.wit x mref ∗
        mref ↦$ mv ∗ result_ptr ↦ «$r0_ptr» ∗ ii_ptr ↦ W64 1)))
      $$ [id Hel Hmref result ii]
    · ihave #Hsc1' := Hsc1
      iunfold ownScope at Hsc1'
      icases Hsc1' with (⟨%Hn, %HS⟩ | ⟨%ids, %Hd, #Hids⟩)
      · rw [Hn]
        wp_func_lits
        wp_auto
        isplitr
        · ipureintro; rfl
        iexists ∅, ∅, _
        iframe id Hel Hmref result ii
        ipureintro
        refine ⟨?_, by rw [HS, GMap.dom_empty]⟩
        rw [GMap.dom_empty]
        apply set_eq; intro k
        rw [elem_of_difference]
        constructor
        · intro h; exact absurd h (not_elem_of_empty k)
        · intro h; exact absurd h.1 (not_elem_of_empty k)
      wp_func_lits
      iapply wp_map_for_range (fun (keys : List w64) (i : Int) => iprop(∃ (xi : w64)
          (mv : GMap w64 Unit),
          "%Hi" ∷ ⌜0 ≤ i⌝ ∗
          "%Hmv" ∷ ⌜∀ k, k ∈ domSet mv ↔ k ∈ keys.take i.toNat ∧ k ≠ x⌝ ∗
          "id" ∷ id_ptr ↦ xi ∗
          "Hel" ∷ arrayIndexRef tracker.ReplicationSet (sint.Z (W64 1))
          «$r0_ptr».[tracker.Epoch, go!"ReplicationSet"] ↦ tracker.ReplicationSet.mk em.rs1.wit x mref ∗
          "Hmref" ∷ mref ↦$ mv ∗ "result" ∷ result_ptr ↦ «$r0_ptr» ∗
          "ii" ∷ ii_ptr ↦ W64 1)) $$ Hids
      iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
      isplitl [id Hel Hmref result ii]
      · iexists _, ∅
        simp only [named]
        iframe id Hel Hmref result ii
        ipureintro
        refine ⟨Int.le_refl _, fun k => ?_⟩
        rw [GMap.dom_empty]
        simp only [Int.toNat_zero, List.take_zero, List.not_mem_nil, _root_.false_and]
        exact iff_false_intro (not_elem_of_empty k)
      isplitr
      · imodintro
        iintro %i %key %vv ⟨%Hkey, %Hvv⟩ HP
        iNamed HP
        have Hst := reset_step keys i key x mv Hi Hkey Hmv
        wp_auto
        wp_if_destruct
        · -- `id == x`: skipped
          have Heq : key = x := by simpa using Hif
          unfold forMapPostcondition
          iright; ileft
          isplitr
          · ipureintro; rfl
          iexists key, mv
          simp only [named]
          iframe id Hel Hmref result ii
          ipureintro
          exact ⟨by omega, (Hst.1 Heq).1⟩
        · -- `NonWitnessVoters[id] = struct{}{}`
          have Hne : key ≠ x := by simpa using Hif
          wp_apply wp_mapInsert $$ Hmref as Hmref
          unfold forMapPostcondition
          iright; ileft
          isplitr
          · ipureintro; rfl
          iexists key, _
          simp only [named]
          iframe id Hel Hmref result ii
          ipureintro
          exact ⟨by omega, (Hst.2 Hne).1⟩
      iintro HP -
      iNamed HP
      rw [Int.toNat_natCast, ← Hklen, List.take_length] at Hmv
      obtain ⟨Hd', -⟩ := reset_done ids x keys mv Hkset Hmv
      isplitr
      · ipureintro; rfl
      iexists ids, mv, xi
      iframe id Hel Hmref result ii
      ipureintro; exact ⟨Hd', Hd⟩
    iintro %v ⟨%Hv, %ids, %mv, %xi, %Hdm, id, Hel, Hmref, result, ii⟩
    subst Hv
    wp_auto
    -- `if set.Excluded != x && set.Excluded != set.Witness { NonWitnessVoters[set.Excluded] = .. }`
    wp_bind (If (Val #(!decide (r1.Excluded' = x))) _ _)
    iapply (wp_wand (Φ := fun v => iprop(⌜v = #(decide (em.rs1.excl ≠ x ∧
        em.rs1.excl ≠ em.rs1.wit))⌝ ∗ set_ptr ↦ r1))) $$ [set]
    · rw [Hx1e]
      by_cases h : em.rs1.excl = x
      · rw [decide_eq_true h]
        wp_auto
        iframe set
        ipureintro
        rw [decide_eq_false (fun hh => hh.1 h)]
      · rw [decide_eq_false h]
        wp_auto
        rw [Hx1e, Hw1e]
        iframe set
        ipureintro
        by_cases h' : em.rs1.excl = em.rs1.wit
        · rw [decide_eq_true h', decide_eq_false (fun hh => hh.2 h')]; rfl
        · rw [decide_eq_false h', decide_eq_true ⟨h, h'⟩]; rfl
    iintro %v ⟨%Hv, set⟩
    subst Hv
    wp_bind (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) _) _ _)
    iapply (wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗
        mref ↦$ (if em.rs1.excl ≠ x ∧ em.rs1.excl ≠ em.rs1.wit then <[em.rs1.excl := ()]> mv
          else mv) ∗ set_ptr ↦ r1 ∗ arrayIndexRef tracker.ReplicationSet (sint.Z (W64 1))
          «$r0_ptr».[tracker.Epoch, go!"ReplicationSet"] ↦ tracker.ReplicationSet.mk em.rs1.wit x mref ∗
        result_ptr ↦ «$r0_ptr» ∗ ii_ptr ↦ W64 1))) $$ [Hmref set Hel result ii]
    · by_cases hc : em.rs1.excl ≠ x ∧ em.rs1.excl ≠ em.rs1.wit
      · rw [decide_eq_true hc]
        wp_auto
        rw [Hx1e]
        wp_apply wp_mapInsert $$ Hmref as Hmref
        rw [if_pos hc]
        iframe Hmref set Hel result ii
        ipureintro; rfl
      · rw [decide_eq_false hc]
        wp_auto
        rw [if_neg hc]
        iframe Hmref set Hel result ii
        ipureintro; rfl
    iintro %v ⟨%Hv, Hmref, set, Hel, result, ii⟩
    subst Hv
    have Hxc : x = em.rs1.wit ∨ x ∈ em.rs1.nwv := by
      subst Hxd
      rcases Hiid with h | h | h
      · rw [if_pos h]; exact Or.inl rfl
      · by_cases h0 : iid = W64 0
        · rw [if_pos h0]; exact Or.inl rfl
        · rw [if_neg h0]; exact Or.inl h
      · by_cases h0 : iid = W64 0
        · rw [if_pos h0]; exact Or.inl rfl
        · rw [if_neg h0]; exact Or.inr h
    wp_for_post
    simp only [named]
    iframe HΦ Hsubf
    iexists W64 1 + W64 1, W64 1, r1, true,
      array.mk 2 (arr.arr.set (sint.Z (W64 1)).toNat (tracker.ReplicationSet.mk em.rs1.wit x mref))
    ihave Hrs := Hrsback $$ %(tracker.ReplicationSet.mk em.rs1.wit x mref) Hel
    iframe i ii set changed Hrs Htrk p result Hpm
    iright; iright
    isplitr
    · ipureintro; rfl
    iexists q0, tracker.ReplicationSet.mk em.rs1.wit x mref
    isplitr
    · ipureintro; rw [Ha]; rfl
    isplitl [Hq0]
    · iexact Hq0
    unfold ownRSn
    iexists rsChanged em.rs1 x
    isplitr
    · ipureintro; exact ⟨rsChanged_wf x Hwf1 (Hwf1.wit_nz Hx1) Hxc, rfl⟩
    iright
    unfold ownRSb
    isplitr
    · ipureintro; exact ⟨rfl, rfl⟩
    iexists _
    iframe Hmref
    ipureintro; exact chg_dom em.rs1 x ids mv Hdm.1 Hdm.2
  · subst Hj
    rw [show decide (sint.Z (W64 2) < sint.Z (W64 2)) = false by decide]
    simp only [Bool.false_eq_true, ↓reduceIte]
    cases cb
    · -- nothing changed: `return false`
      wp_auto
      iapply HΦ
      iframe Htrk
      isplitl [Hpm]
      · iright
        unfold chgRes
        iframe Hpm
        ipureintro; exact ⟨rfl, Hwf, H0, H1, Hdom⟩
      ileft; ipureintro; exact ⟨rfl, rfl⟩
    · -- `p.Epoch = result`, frozen
      imod ownRSn_persist _ _ _ _ $$ Hq0 with ⟨%m0', %Hm0, #Hq0⟩
      imod ownRSn_persist _ _ _ _ $$ Hq1 with ⟨%m1', %Hm1, #Hq1⟩
      ihave He := epoch_combine _ _ _ Hrn $$ [Hsubf Hrs]
      · iframe Hsubf Hrs
      imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ He with #He
      wp_auto
      iapply HΦ
      iframe Htrk
      isplitl [Hpm]
      · iright
        unfold chgRes
        iframe Hpm
        ipureintro; exact ⟨rfl, Hwf, H0, H1, Hdom⟩
      iright
      isplitr
      · ipureintro; exact ⟨rfl, trivial⟩
      iexists ⟨ev'.Subterm' + W64 1, m0', m1'⟩
      isplitl
      · unfold ownEpoch
        iexists _, q0, q1
        iframe He Hq0 Hq1
        ipureintro; exact ⟨rfl, Ha⟩
      ipureintro
      refine ⟨by simp only; rw [Hsub], Or.inr ⟨Hnb, Hm0.1, Hm1.1⟩, Hm0.2, Hm1.2⟩

end proof

end EtcdGrove
end Perennial
