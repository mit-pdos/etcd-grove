/-
Proof of `Spec/go_etcd_io/raft/v3/confchange/Changer__EnterJoint.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.raft.v3.confchange.Changer__EnterJoint
public import Spec.go_etcd_io.raft.v3.confchange.Changer__checkAndCopy
public import Spec.go_etcd_io.raft.v3.confchange.joint
public import Spec.go_etcd_io.raft.v3.confchange.Changer__err
public import Spec.go_etcd_io.raft.v3.confchange.incoming
public import Spec.go_etcd_io.raft.v3.confchange.outgoingPtr
public import Spec.go_etcd_io.raft.v3.confchange.outgoing
public import Spec.go_etcd_io.raft.v3.confchange.Changer__apply
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

theorem confchange.Changer.EnterJoint.wp_proof
    (wp_Changer_checkAndCopy : confchange.Changer.checkAndCopy.spec (GF := GF) (hG := hG))
    (wp_confchange_joint : confchange.joint.spec (GF := GF) (hG := hG))
    (wp_Changer_err : confchange.Changer.err.spec (GF := GF) (hG := hG))
    (wp_confchange_incoming : confchange.incoming.spec (GF := GF) (hG := hG))
    (wp_confchange_outgoingPtr : confchange.outgoingPtr.spec (GF := GF) (hG := hG))
    (wp_confchange_outgoing : confchange.outgoing.spec (GF := GF) (hG := hG))
    (wp_Changer_apply : confchange.Changer.apply.spec (GF := GF) (hG := hG))
    (wp_confchange_checkAndReturn : confchange.checkAndReturn.spec (GF := GF) (hG := hG)) :
    confchange.Changer.EnterJoint.spec (GF := GF) (hG := hG) := by
  intro p chg c prs pvs autoLeave ccs l dq dqs dqc dqm dqp Hmi
  wp_start as ⟨Hp, Hccs, Htc⟩
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
      simp only [enterJointM, if_pos Hninv, ownResult]
      ipureintro; intro h; cases h
  subst Herr
  wp_auto
  have Hs0 : ¬ ¬ CfgInv (clearAutoLeave { cfg := c, prs := flagsOf pvs }) := fun h => h Hinv
  icases ownCfgCC_elim _ _ _ $$ Hc' with ⟨%vin, %vout, %Harr, Hin, Hout, Hl, Hln, %Hal⟩
  icases ownIdsetC_split _ _ _ $$ Hout with ⟨Hout, %Hcout⟩
  wp_apply wp_confchange_joint _ vin vout _ _ Harr $$ [$Hout] as Hout
  wp_if_destruct
  · -- "config is already joint"
    have Hj : c.outgoing ≠ ∅ := by
      intro h; rw [h, GMap.map_size_empty] at Hif; exact absurd Hif (by decide)
    wp_apply errors.wp_New as %e #He
    wp_apply wp_Changer_err $$ [$c] as %cfg0 c
    iapply HΦ
    iframe
    simp only [enterJointM, if_neg Hs0, if_pos Hj, ownResult]
    ipureintro; intro h; cases h
  have Hout0 : c.outgoing = ∅ := by
    rcases Nat.eq_zero_or_pos (GMap.size c.outgoing) with h0 | h0
    · exact GMap.map_size_empty_inv _ h0
    · exact absurd h0 Hif
  have Hj : ¬ c.outgoing ≠ ∅ := fun h => h Hout0
  have Hvout : vout = map.nil := by
    rcases Hcout with h | h
    · exact h
    · exact absurd Hout0 h
  -- `len(incoming(cfg.Voters)) == 0`?
  wp_apply wp_confchange_incoming _ vin vout Harr
  wp_apply wp_map_len_lt $$ Hin as ⟨Hin, %Hlt⟩
  wp_if_destruct
  · -- "can't make a zero-voter config joint"
    have Hi0 : c.incoming = ∅ := by
      apply GMap.map_size_empty_inv
      have := congrArg sint.Z Hif
      word
    wp_apply errors.wp_New as %e #He
    wp_apply wp_Changer_err $$ [$c] as %cfg0 c
    iapply HΦ
    iframe
    simp only [enterJointM, if_neg Hs0, if_neg Hj, Hi0, if_true, ownResult]
    ipureintro; intro h; cases h
  have Hi0 : c.incoming ≠ ∅ := by
    intro h; rw [h, GMap.map_size_empty] at Hif; exact Hif rfl
  -- `*outgoingPtr(&cfg.Voters) = quorum.MajorityConfig{}`
  wp_apply wp_map_make1 (K := w64) (V := Unit) as %mout Hmout
  icases typedPointsto_not_null_dup _ _ _ $$ cfg with ⟨Hcfgp, %Hcnn⟩
  iStructNamed Hcfgp
  wp_apply wp_confchange_outgoingPtr
  icases array_acc _ (sint.Z (W64 1)) _ _ _ vout (by decide) (by rw [Harr]; rfl)
    $$ Voters with ⟨Hv1, Hvback⟩
  rw [show sint.Z (W64 1) = (1 : Int) by decide]
  wp_auto
  ihave Voters := Hvback $$ Hv1
  rw [show (1 : Int).toNat = 1 from rfl]
  have Harr2 : (cfg'.Voters'.arr.set 1 mout) = [vin, mout] := by
    rw [Harr]; rfl
  -- `for id := range incoming(cfg.Voters) { outgoing(cfg.Voters)[id] = struct{}{} }`
  wp_auto
  wp_apply wp_confchange_incoming _ vin mout Harr2
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range (fun (keys : List w64) (i : Int) => iprop(∃ (x : w64)
      (mv : GMap w64 Unit),
      "%Hi" ∷ ⌜0 ≤ i⌝ ∗
      "%Hmv" ∷ ⌜∀ k, k ∈ domSet mv ↔ k ∈ keys.take i.toNat⌝ ∗
      "id" ∷ id_ptr ↦ x ∗
      "Voters" ∷ cfg_ptr.[tracker.Config, go!"Voters"] ↦
        (array.mk 2 (cfg'.Voters'.arr.set 1 mout) : quorum.JointConfig) ∗
      "Hmout" ∷ mout ↦$ mv)) $$ Hin
  iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
  isplitl [id Voters Hmout]
  · iexists zero_val w64, ∅
    simp only [named]
    iframe id Voters Hmout
    ipureintro
    refine ⟨Int.le_refl _, fun k => ?_⟩
    simp only [Int.toNat_zero, List.take_zero, List.not_mem_nil, iff_false]
    rw [GMap.elem_of_dom]
    rintro ⟨v, hv⟩
    simp at hv
  isplitr
  · imodintro
    iintro %i %key %vv ⟨%Hkey, %Hvv⟩ HP
    iNamed HP
    wp_auto
    wp_apply wp_confchange_outgoing _ vin mout Harr2
    wp_apply wp_mapInsert $$ Hmout as Hmout
    unfold forMapPostcondition
    iright; ileft
    isplitr
    · ipureintro; rfl
    iexists key, _
    simp only [named]
    iframe id Voters Hmout
    ipureintro
    refine ⟨by omega, fun k => ?_⟩
    have Htake : keys.take (i + 1).toNat = keys.take i.toNat ++ [key] := by
      rw [show (i + 1).toNat = i.toNat + 1 by omega]
      rw [List.take_add_one, Hkey]; rfl
    rw [Htake, List.mem_append, List.mem_singleton, ← Hmv, GMap.elem_of_dom,
      GMap.elem_of_dom]
    by_cases hk : key = k
    · subst hk; simp
    · rw [GMap.lookup_insert_ne _ _ hk]
      constructor
      · intro h; exact .inl h
      · rintro (h | h)
        · exact h
        · exact absurd h.symm hk
  iintro HP Hin
  iNamed HP
  rw [Int.toNat_natCast, ← Hklen, List.take_length] at Hmv
  have Hmv' : mv = c.incoming := by
    apply GMap.map_eq; intro k
    have := Hmv k
    rw [Hkset, GMap.elem_of_dom] at this
    rcases h1 : mv !! k with _ | ⟨⟩ <;> rcases h2 : c.incoming !! k with _ | ⟨⟩ <;> simp_all
  subst Hmv'
  -- the configuration: the outgoing voters a copy of the incoming ones
  ihave Hcfgp : (cfg_ptr ↦ ({ cfg' with Voters' := array.mk 2 (cfg'.Voters'.arr.set 1 mout) } :
      tracker.Config)) $$ [Voters AutoLeave Learners LearnersNext]
  · iapply typedPointsto_combine _ _ _ Hcnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  ihave Hc0 : ownCfgCC ({ cfg' with Voters' := array.mk 2 (cfg'.Voters'.arr.set 1 mout) } :
      tracker.Config) (DFrac.own 1) (⟨c.incoming, c.incoming, c.learners, c.learnersNext, false⟩ : CfgM)
    $$ [Hin Hmout Hl Hln]
  · iapply ownCfgCC_intro ({ cfg' with Voters' := array.mk 2 (cfg'.Voters'.arr.set 1 mout) } :
      tracker.Config) (DFrac.own 1) (⟨c.incoming, c.incoming, c.learners, c.learnersNext, false⟩ : CfgM)
      vin mout Harr2 (by simpa using Hal) $$ Hin [Hmout] Hl Hln
    unfold ownIdsetC; iright; iframe Hmout; ipureintro; exact Hi0
  ihave Hnew := ownNewPr_copies (GF := GF) chg pvs
  ihave Hw := ownWork_intro chg pvs cfg_ptr trk
    (⟨(⟨c.incoming, c.incoming, c.learners, c.learnersNext, false⟩ : CfgM), flagsOf pvs⟩ : CCState)
    _ prs' pvs rfl $$ Hcfgp Hc0 Htrk Hcopies Hnew
  -- `c.apply(&cfg, trk, ccs...)`
  wp_auto
  wp_apply wp_Changer_apply c_ptr cfg_ptr trk chg pvs _ ccs l _ _ Hmi $$ [$c $Hccs $Hw]
    as %err2 ⟨c, Hccs, Hres⟩
  have Hej : enterJointM autoLeave l { cfg := c, prs := flagsOf pvs } =
      match (applyM l (⟨(⟨c.incoming, c.incoming, c.learners, c.learnersNext, false⟩ : CfgM), flagsOf pvs⟩ : CCState)) with
      | none => none
      | some s1 => checkedM { cfg := { s1.cfg with autoLeave := autoLeave }, prs := s1.prs } := by
    simp only [enterJointM, if_neg Hs0, if_neg Hj, if_neg Hi0] <;> rfl
  rw [Hej]
  rcases Happ : applyM l (⟨(⟨c.incoming, c.incoming, c.learners, c.learnersNext, false⟩ : CfgM), flagsOf pvs⟩ : CCState) with _ | s1
  · icases Hres with %Herr2
    cases err2 with
    | nil => exact absurd rfl Herr2
    | ok e =>
      wp_auto
      wp_apply wp_Changer_err $$ [$c] as %cfg0 c
      iapply HΦ
      iframe
      simp only [ownResult]
      ipureintro; intro h; cases h
  icases Hres with ⟨%Herr2, Hw⟩
  subst Herr2
  wp_auto
  icases ownWork_elim _ _ _ _ _ $$ Hw with
    ⟨%cfg1, %prs1, %pvs1, Hcfgp, Hc1, Htrk, Hprs1, %Hflags1, Hnew1⟩
  -- `cfg.AutoLeave = autoLeave`
  wp_auto
  icases ownCfgCC_elim _ _ _ $$ Hc1 with ⟨%vin1, %vout1, %Harr1, Hin1, Hout1, Hl1, Hln1, %Hal1⟩
  ihave Hc1 := ownCfgCC_intro ({ cfg1 with AutoLeave' := autoLeave } : tracker.Config) (DFrac.own 1)
    { s1.cfg with autoLeave := autoLeave } vin1 vout1 Harr1 rfl $$ Hin1 Hout1 Hl1 Hln1
  -- `checkAndReturn(cfg, trk)`
  wp_apply wp_confchange_checkAndReturn _ _ _ _ _ _ _ _ $$ [$Hc1 $Htrk $Hprs1]
    as %cfg2 %trk2 %err3 ⟨Hc1, Htrk, Hprs1, %Hres3⟩
  iapply HΦ
  iframe
  simp only [checkedM]
  rw [Hflags1] at Hres3
  rcases Hres3 with ⟨Hinv3, Herr3, rfl, rfl⟩ | ⟨Hinv3, Herr3⟩
  · simp only [if_pos Hinv3, ownResult]
    iframe
    isplitr
    · ipureintro; exact Herr3
    unfold ownPrsW
    iexists prs1, pvs1
    simp only [named]
    iframe
    ipureintro; exact Hflags1
  · simp only [if_neg Hinv3, ownResult]
    ipureintro; exact Herr3

end proof

end EtcdGrove
end Perennial
