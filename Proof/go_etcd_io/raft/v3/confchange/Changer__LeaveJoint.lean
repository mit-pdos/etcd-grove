/-
Proof of `Spec/go_etcd_io/raft/v3/confchange/Changer__LeaveJoint.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.raft.v3.confchange.Changer__LeaveJoint
public import Spec.go_etcd_io.raft.v3.confchange.Changer__checkAndCopy
public import Spec.go_etcd_io.raft.v3.confchange.joint
public import Spec.go_etcd_io.raft.v3.confchange.Changer__err
public import Spec.go_etcd_io.raft.v3.confchange.nilAwareAdd
public import Spec.go_etcd_io.raft.v3.confchange.outgoing
public import Spec.go_etcd_io.raft.v3.confchange.incoming
public import Spec.go_etcd_io.raft.v3.confchange.outgoingPtr
public import Spec.go_etcd_io.raft.v3.confchange.checkAndReturn

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

/-- The outgoing-voter loop, one key kept. -/
theorem lj_step_keep {V : Type} (mI m : GMap w64 V) (keys : List w64) (i : Int) (key : w64)
    (inc L : GMap w64 Unit) (Hi : 0 ≤ i) (Hkey : keys[i.toNat]? = some key)
    (H : ∀ k, mI !! k = if k ∈ keys.take i.toNat ∧ k ∉ inc ∧ k ∉ L then none else m !! k)
    (Hkeep : key ∈ inc ∨ key ∈ L) :
    ∀ k, mI !! k = if k ∈ keys.take (i + 1).toNat ∧ k ∉ inc ∧ k ∉ L then none else m !! k := by
  intro k
  rw [H k, show (i + 1).toNat = i.toNat + 1 by omega, List.take_add_one, Hkey]
  simp only [Option.toList_some, List.mem_append, List.mem_singleton]
  by_cases hk : k = key
  · subst hk
    have : ¬ (k ∉ inc ∧ k ∉ L) := fun h => by rcases Hkeep with h' | h' <;> simp_all
    by_cases h1 : k ∈ keys.take i.toNat <;> simp_all
  · simp [hk]

/-- The outgoing-voter loop, one key untracked. -/
theorem lj_step_del {V : Type} (mI m : GMap w64 V) (keys : List w64) (i : Int) (key : w64)
    (inc L : GMap w64 Unit) (Hi : 0 ≤ i) (Hkey : keys[i.toNat]? = some key)
    (H : ∀ k, mI !! k = if k ∈ keys.take i.toNat ∧ k ∉ inc ∧ k ∉ L then none else m !! k)
    (Hdel : key ∉ inc ∧ key ∉ L) :
    ∀ k, (GMap.delete key mI) !! k =
      if k ∈ keys.take (i + 1).toNat ∧ k ∉ inc ∧ k ∉ L then none else m !! k := by
  intro k
  rw [show (i + 1).toNat = i.toNat + 1 by omega, List.take_add_one, Hkey]
  simp only [Option.toList_some, List.mem_append, List.mem_singleton]
  by_cases hk : k = key
  · subst hk; simp [Hdel]
  · rw [GMap.lookup_delete_ne _ (Ne.symm hk), H k]
    simp [hk]

/-- What the staged-learner loop leaves of the progress values, as the model. -/
theorem lj_flags (c : CfgM) (pvs pvs2 : GMap w64 tracker.Progress) (LI : GMap w64 Unit)
    (HLI : ∀ k, k ∈ LI ↔ k ∈ c.learners ∨ k ∈ c.learnersNext)
    (H2 : ∀ k, pvs2 !! k = if k ∈ c.outgoing ∧ k ∉ c.incoming ∧ k ∉ LI then none else
      (if k ∈ c.learnersNext then (pvs !! k).map (fun pv => { pv with IsLearner' := true })
       else pvs !! k)) :
    flagsOf pvs2 = (leaveJointState { cfg := c, prs := flagsOf pvs }).prs := by
  apply GMap.map_eq; intro k
  rw [flagsOf_lookup', H2 k]
  simp only [leaveJointState.proj_prs, GMap.lookup_filter, GMap.lookup_union, GMap.lookup_fmap,
    flagsOf_lookup']
  have HL' : k ∈ c.learners ∪ c.learnersNext ↔ k ∈ LI := by rw [GMap.elem_of_union, HLI]
  by_cases h1 : k ∈ c.outgoing <;> by_cases h2 : k ∈ c.incoming <;> by_cases h3 : k ∈ LI <;>
    by_cases h4 : k ∈ c.learnersNext <;> rcases h5 : pvs !! k with _ | pv <;>
    simp_all [Option.filter]

theorem confchange.Changer.LeaveJoint.wp_proof
    (wp_Changer_checkAndCopy : confchange.Changer.checkAndCopy.spec (GF := GF) (hG := hG))
    (wp_confchange_joint : confchange.joint.spec (GF := GF) (hG := hG))
    (wp_Changer_err : confchange.Changer.err.spec (GF := GF) (hG := hG))
    (wp_confchange_nilAwareAdd : confchange.nilAwareAdd.spec (GF := GF) (hG := hG))
    (wp_confchange_outgoing : confchange.outgoing.spec (GF := GF) (hG := hG))
    (wp_confchange_incoming : confchange.incoming.spec (GF := GF) (hG := hG))
    (wp_confchange_outgoingPtr : confchange.outgoingPtr.spec (GF := GF) (hG := hG))
    (wp_confchange_checkAndReturn : confchange.checkAndReturn.spec (GF := GF) (hG := hG)) :
    confchange.Changer.LeaveJoint.spec (GF := GF) (hG := hG) := by
  intro p chg c prs pvs dq dqc dqm dqp
  wp_start as ⟨Hp, Htc⟩
  wp_auto
  wp_method_call
  wp_call
  wp_auto
  -- `cfg, trk, err := c.checkAndCopy()`
  wp_apply wp_Changer_checkAndCopy c_ptr chg c prs pvs _ dqc dqm dqp $$ [$c $Htc]
    as %cfg' %trk %err ⟨c, Htc, Hres⟩
  icases Hres with (⟨%Hninv, %Herr⟩ | ⟨⟨%Hinv, %Herr⟩, Hc', ⟨%prs', Htrk, Hcopies⟩⟩)
  · cases err with
    | nil => exact absurd rfl Herr
    | ok e =>
      wp_auto
      wp_apply wp_Changer_err $$ [$c] as %cfg0 c
      iapply HΦ
      iframe
      simp only [leaveJointM, if_pos Hninv, ownResult]
      ipureintro; intro h; cases h
  subst Herr
  wp_auto
  have Hs0 : ¬ ¬ CfgInv (clearAutoLeave { cfg := c, prs := flagsOf pvs }) := fun h => h Hinv
  icases ownCfgCC_elim _ _ _ $$ Hc' with ⟨%vin, %vout, %Harr, Hin, Hout, Hl, Hln, %Hal⟩
  icases ownIdsetC_split _ _ _ $$ Hout with ⟨Hout, %Hcout⟩
  wp_apply wp_confchange_joint _ vin vout _ _ Harr $$ [$Hout] as Hout
  wp_if_destruct
  rotate_left
  · -- not joint: "can't leave a non-joint config"
    have Hj : c.outgoing = ∅ := by
      rcases Nat.eq_zero_or_pos (GMap.size c.outgoing) with h0 | h0
      · exact GMap.map_size_empty_inv _ h0
      · exact absurd h0 Hif
    wp_apply errors.wp_New as %e #He
    wp_apply wp_Changer_err $$ [$c] as %cfg0 c
    iapply HΦ
    iframe
    simp only [leaveJointM, if_neg Hs0, Hj, if_true, ownResult]
    ipureintro; intro h; cases h
  have Hjne : c.outgoing ≠ ∅ := by
    intro h; rw [h, GMap.map_size_empty] at Hif; exact absurd Hif (by decide)
  obtain ⟨HinvTr, HinvLN, -, -⟩ := Hinv
  simp only [clearAutoLeave.proj_prs, clearAutoLeave.proj_cfg] at HinvTr HinvLN
  ihave %Hdom0 := BigSepM2.bigSepM2_lookup_iff $$ Hcopies
  have Hdom : ∀ k, (prs' !! k).isSome ↔ (pvs !! k).isSome := Hdom0
  icases typedPointsto_not_null_dup _ _ _ $$ cfg with ⟨Hcfgp, %Hcnn⟩
  iStructNamed Hcfgp
  ihave Hnew : ([∗map] k ↦ pv ∈ pvs, ownNewPr chg pvs k pv) $$ []
  · iapply ownNewPr_copies
  ihave Hln := ownIdsetC_Q _ _ _ $$ Hln
  -- `for id := range cfg.LearnersNext { nilAwareAdd(&cfg.Learners, id); trk[id].IsLearner = true }`
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_idset_for_range (fun (keys : List w64) (i : Int) => iprop(∃ (y : w64) (ml : Loc)
      (pvsI : GMap w64 tracker.Progress) (LI : GMap w64 Unit),
      "%Hi" ∷ ⌜0 ≤ i⌝ ∗
      "id" ∷ id_ptr ↦ y ∗
      "Learners" ∷ cfg_ptr.[tracker.Config, go!"Learners"] ↦ ml ∗
      "Hl" ∷ ownIdsetC ml (DFrac.own 1) LI ∗
      "trk" ∷ trk_ptr ↦ trk ∗
      "Htrk" ∷ trk ↦$ prs' ∗
      "Hprs" ∷ ([∗map] _k ↦ pr;pv ∈ prs';pvsI, pr ↦ pv) ∗
      "Hnew" ∷ ([∗map] k ↦ pv ∈ pvsI, ownNewPr chg pvs k pv) ∗
      "%HLI" ∷ ⌜∀ k, k ∈ LI ↔ k ∈ c.learners ∨ k ∈ keys.take i.toNat⌝ ∗
      "%HpvsI" ∷ ⌜∀ k, pvsI !! k = if k ∈ keys.take i.toNat then
        (pvs !! k).map (fun pv => { pv with IsLearner' := true }) else pvs !! k⌝))
    $$ Hln
  iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
  isplitl [id Learners Hl trk Htrk Hcopies Hnew]
  · iexists zero_val w64, cfg'.Learners', pvs, c.learners
    iframe
    ipureintro
    refine ⟨Int.le_refl _, fun k => by simp, fun k => by simp⟩
  isplitr
  · imodintro
    iintro %i %key %vv ⟨%Hkey, %Hvv⟩ HP
    iNamed HP
    have HkLN : key ∈ c.learnersNext := by rw [GMap.mem_iff, Hvv]; rfl
    have Hnew' : key ∉ keys.take i.toNat := not_mem_take_of_nodup Hknodup Hkey
    obtain ⟨pv, Hpv⟩ : ∃ pv, pvs !! key = some pv := by
      have h := (HinvLN key HkLN).2
      rw [flagsOf_lookup'] at h
      cases h' : pvs !! key with
      | none => rw [h'] at h; cases h
      | some pv => exact ⟨pv, rfl⟩
    obtain ⟨pr, Hpr⟩ : ∃ pr, prs' !! key = some pr :=
      Option.isSome_iff_exists.1 ((Hdom key).2 (by rw [Hpv]; rfl))
    have HpvI : pvsI !! key = some pv := by rw [HpvsI, if_neg Hnew', Hpv]
    wp_auto
    ihave Hl := ownIdsetC_Q _ _ _ $$ Hl
    wp_apply wp_confchange_nilAwareAdd $$ [$Learners $Hl] as %ml' ⟨Learners, Hl⟩
    wp_apply wp_map_lookup1 $$ Htrk as Htrk
    rw [Hpr]
    simp only [Option.getD_some]
    icases ownPrs_borrow chg pvs prs' pvsI key pr pv Hpr HpvI $$ [$Hprs $Hnew] with ⟨Hpr, Hback⟩
    wp_auto
    icases Hback $$ %true Hpr with ⟨Hprs, Hnew⟩
    unfold forMapPostcondition
    iright; ileft
    isplitr
    · ipureintro; rfl
    ihave Hl := ownIdsetC_insert _ _ _ _ $$ Hl
    iexists key, ml', _, _
    iframe
    ipureintro
    have Htake : keys.take (i + 1).toNat = keys.take i.toNat ++ [key] := by
      rw [show (i + 1).toNat = i.toNat + 1 by omega, List.take_add_one, Hkey]; rfl
    refine ⟨by omega, fun k => ?_, fun k => ?_⟩
    · rw [Htake, GMap.mem_iff]
      by_cases hk : key = k
      · subst hk; simp
      · rw [GMap.lookup_insert_ne _ _ hk, ← GMap.mem_iff, HLI]
        simp only [List.mem_append, List.mem_singleton]
        constructor
        · rintro (h | h); exact .inl h; exact .inr (.inl h)
        · rintro (h | h | h); exact .inl h; exact .inr h; exact absurd h.symm hk
    · rw [Htake]
      by_cases hk : key = k
      · subst hk; simp [Hpv]
      · rw [GMap.lookup_insert_ne _ _ hk, HpvsI]
        simp [Ne.symm hk]
  iintro HP Hln
  iNamed HP
  rw [Int.toNat_natCast, ← Hklen, List.take_length] at HLI HpvsI
  have HLIeq : LI = c.learners ∪ c.learnersNext := by
    apply GMap.set_eq; intro k
    rw [HLI, GMap.elem_of_union, Hkset]; rfl
  subst HLIeq
  have HpvsI' : ∀ k, pvsI !! k = if k ∈ c.learnersNext then
      (pvs !! k).map (fun pv => { pv with IsLearner' := true }) else pvs !! k := by
    intro k; rw [HpvsI k]
    have h := Hkset k
    by_cases hk : k ∈ keys
    · rw [if_pos hk, if_pos (show k ∈ c.learnersNext from h.1 hk)]
    · rw [if_neg hk, if_neg (show k ∉ c.learnersNext from fun h' => hk (h.2 h'))]
  clear HLI HpvsI Hkset Hklen Hknodup
  icases ownIdsetC_split _ _ _ $$ Hl with ⟨Hl, %Hcl⟩
  -- `cfg.LearnersNext = nil`, then `for id := range outgoing(cfg.Voters) {...}`
  wp_auto
  wp_apply wp_confchange_outgoing _ vin vout Harr
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_idset_for_range (fun (keys : List w64) (i : Int) => iprop(∃ (y : w64)
      (prsI : GMap w64 Loc) (pvsI2 : GMap w64 tracker.Progress),
      "%Hi" ∷ ⌜0 ≤ i⌝ ∗
      "id" ∷ id_ptr ↦ y ∗
      "Voters" ∷ cfg_ptr.[tracker.Config, go!"Voters"] ↦ cfg'.Voters' ∗
      "Learners" ∷ cfg_ptr.[tracker.Config, go!"Learners"] ↦ ml ∗
      "Hl" ∷ ownIdsetQ ml (DFrac.own 1) (c.learners ∪ c.learnersNext) ∗
      "Hin" ∷ vin ↦$ c.incoming ∗
      "trk" ∷ trk_ptr ↦ trk ∗
      "Htrk" ∷ trk ↦$ prsI ∗
      "Hprs" ∷ ([∗map] _k ↦ pr;pv ∈ prsI;pvsI2, pr ↦ pv) ∗
      "Hnew" ∷ ([∗map] k ↦ pv ∈ pvsI2, ownNewPr chg pvs k pv) ∗
      "%Hp1" ∷ ⌜∀ k, prsI !! k = if k ∈ keys.take i.toNat ∧ k ∉ c.incoming ∧
        k ∉ c.learners ∪ c.learnersNext then none else prs' !! k⌝ ∗
      "%Hp2" ∷ ⌜∀ k, pvsI2 !! k = if k ∈ keys.take i.toNat ∧ k ∉ c.incoming ∧
        k ∉ c.learners ∪ c.learnersNext then none else pvsI !! k⌝))
    $$ Hout
  iintro %keys2 ⟨%Hkset2, %Hklen2, %Hknodup2⟩
  isplitl [id Voters Learners Hl Hin trk Htrk Hprs Hnew]
  · iexists _, prs', pvsI
    iframe
    ipureintro
    refine ⟨Int.le_refl _, fun k => by simp, fun k => by simp⟩
  isplitr
  · imodintro
    iintro %i %key %vv ⟨%Hkey, %Hvv⟩ HP
    iNamed HP
    wp_auto
    wp_apply wp_confchange_incoming _ vin vout Harr
    wp_apply wp_map_lookup2 $$ Hin as Hin
    wp_apply wp_idset_lookup2 $$ Hl as Hl
    cases h1 : (c.incoming !! key).isSome <;>
      cases h2 : ((c.learners !! key).or (c.learnersNext !! key)).isSome
    case false.false =>
      wp_auto
      wp_apply wp_mapDelete_named tracker.ProgressMap.ty go.uint64
        (go.GoType.PointerType tracker.Progress.ty) $$ Htrk as Htrk
      icases ownPrs_delete chg pvs prsI pvsI2 key $$ [$Hprs $Hnew] with ⟨Hprs, Hnew⟩
      unfold forMapPostcondition
      iright; ileft
      isplitr
      · ipureintro; rfl
      iexists key, _, _
      iframe
      ipureintro
      have Hdel : key ∉ c.incoming ∧ key ∉ c.learners ∪ c.learnersNext := by
        rw [GMap.mem_iff, GMap.mem_iff, GMap.lookup_union, h1, h2]; simp
      exact ⟨by omega, lj_step_del prsI prs' keys2 i key _ _ Hi Hkey Hp1 Hdel,
        lj_step_del pvsI2 pvsI keys2 i key _ _ Hi Hkey Hp2 Hdel⟩
    all_goals
      wp_auto
      unfold forMapPostcondition
      iright; ileft
      isplitr
      · ipureintro; rfl
      iexists key, _, _
      iframe
      ipureintro
      have Hkeep : key ∈ c.incoming ∨ key ∈ c.learners ∪ c.learnersNext := by
        first | exact .inl h1 | exact .inr (by rw [GMap.mem_iff, GMap.lookup_union]; exact h2)
      exact ⟨by omega, lj_step_keep prsI prs' keys2 i key _ _ Hi Hkey Hp1 Hkeep,
        lj_step_keep pvsI2 pvsI keys2 i key _ _ Hi Hkey Hp2 Hkeep⟩
  iintro HP Hout
  iNamed HP
  rw [Int.toNat_natCast, ← Hklen2, List.take_length] at Hp1 Hp2
  have Hp2' : ∀ k, pvsI2 !! k = if k ∈ c.outgoing ∧ k ∉ c.incoming ∧
      k ∉ c.learners ∪ c.learnersNext then none else
      (if k ∈ c.learnersNext then (pvs !! k).map (fun pv => { pv with IsLearner' := true })
       else pvs !! k) := by
    intro k; rw [Hp2 k, HpvsI' k]
    have h := Hkset2 k
    by_cases hk : k ∈ keys2
    · have hk' : k ∈ c.outgoing := h.1 hk
      simp only [hk, hk', _root_.true_and]
    · have hk' : k ∉ c.outgoing := fun h' => hk (h.2 h')
      simp only [hk, hk', _root_.false_and, if_false]
  have Hflags2 := lj_flags c pvs pvsI2 (c.learners ∪ c.learnersNext)
    (fun k => GMap.elem_of_union _ _ _) Hp2'
  -- `*outgoingPtr(&cfg.Voters) = nil`, `cfg.AutoLeave = false`
  wp_auto
  wp_apply wp_confchange_outgoingPtr
  icases array_acc _ (sint.Z (W64 1)) _ _ _ vout (by decide) (by rw [Harr]; rfl)
    $$ Voters with ⟨Hv1, Hvback⟩
  rw [show sint.Z (W64 1) = (1 : Int) by decide]
  wp_auto
  ihave Voters := Hvback $$ Hv1
  rw [show (1 : Int).toNat = 1 from rfl]
  have Harr2 : (cfg'.Voters'.arr.set 1 map.nil) = [vin, map.nil] := by rw [Harr]; rfl
  ihave Hcfgp : (cfg_ptr ↦ (tracker.Config.mk (array.mk 2 (cfg'.Voters'.arr.set 1 map.nil)) false ml map.nil)) $$
      [Voters AutoLeave Learners LearnersNext]
  · iapply typedPointsto_combine _ _ _ Hcnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  ihave Hc2 : ownCfgCC (tracker.Config.mk (array.mk 2 (cfg'.Voters'.arr.set 1 map.nil)) false ml map.nil)
      (DFrac.own 1) (leaveJointState { cfg := c, prs := flagsOf pvs }).cfg $$ [Hin Hl]
  · iapply ownCfgCC_intro (tracker.Config.mk (array.mk 2 (cfg'.Voters'.arr.set 1 map.nil)) false ml map.nil)
      (DFrac.own 1) (leaveJointState { cfg := c, prs := flagsOf pvs }).cfg vin map.nil Harr2
      (by simp [leaveJointState]) $$ [Hin] [] [Hl] []
    all_goals simp only [leaveJointState.proj_cfg]
    · iexact Hin
    · unfold ownIdsetC; ileft; ipureintro; exact ⟨rfl, rfl⟩
    · iapply ownIdsetC_join _ _ _ Hcl $$ Hl
    · unfold ownIdsetC; ileft; ipureintro; exact ⟨rfl, rfl⟩
  -- `checkAndReturn(cfg, trk)`
  wp_auto
  wp_apply wp_confchange_checkAndReturn _ _ _ _ _ _ _ _ $$ [$Hc2 $Htrk $Hprs]
    as %cfg2 %trk2 %err3 ⟨Hc2, Htrk, Hprs, %Hres3⟩
  iapply HΦ
  iframe
  simp only [leaveJointM, if_neg Hs0, if_neg Hjne, checkedM]
  rw [Hflags2] at Hres3
  rcases Hres3 with ⟨Hinv3, Herr3, rfl, rfl⟩ | ⟨Hinv3, Herr3⟩
  · simp only [if_pos Hinv3, ownResult]
    iframe
    isplitr
    · ipureintro; exact Herr3
    unfold ownPrsW
    iexists prsI, pvsI2
    simp only [named]
    iframe
    ipureintro; exact Hflags2
  · simp only [if_neg Hinv3, ownResult]
    ipureintro; exact Herr3

end proof

end EtcdGrove
end Perennial
