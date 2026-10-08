/-
Proof of `Spec/confchange_checkInvariants.lean`. Lean-first (no Rocq counterpart).
-/
import EtcdGrove.Raft.Spec.confchange_checkInvariants
import EtcdGrove.Raft.Spec.JointConfig__IDs
import EtcdGrove.Raft.Spec.confchange_joint
import EtcdGrove.Raft.Spec.confchange_outgoing

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

theorem confchange.checkInvariants.wp_proof
    (wp_JointConfig_IDs : quorum.JointConfig.IDs.spec (GF := GF) (hG := hG))
    (wp_confchange_joint : confchange.joint.spec (GF := GF) (hG := hG))
    (wp_confchange_outgoing : confchange.outgoing.spec (GF := GF) (hG := hG)) :
    confchange.checkInvariants.spec (GF := GF) (hG := hG) := by
  intro cfg trk v vm prs dqv dqp Hcfg Hdom
  obtain ⟨⟨Harr, Hl, Hln⟩, Hal⟩ := Hcfg
  wp_start as ⟨Hv, Htrk⟩
  wp_alloc trk_ptr as trk; wp_pures; wp_alloc cfg_ptr as cfg; wp_pures
  -- `cfg.Voters.IDs()`: the field out of the local copy, and back
  icases (Access.access (A := iprop(cfg_ptr.[tracker.Config, go!"Voters"] ↦ cfg.Voters'))
    (A' := iprop(cfg_ptr.[tracker.Config, go!"Voters"] ↦ cfg.Voters'))
    (P := iprop(cfg_ptr ↦ cfg))) $$ cfg with ⟨Hf, Hback⟩
  wp_apply wp_JointConfig_IDs _ _ v vm _ _ Harr $$ [$Hf $Hv] as %mref %idm ⟨Hf, Hv, Hidm, %Hidm⟩
  wp_pures
  ihave cfg := Hback $$ Hf
  wp_load; wp_pures; wp_load; wp_pures
  rw [Hl, Hln, Hal]
  wp_apply wp_slice_literal (V := GoMap) [mref, map.nil, map.nil]
  wp_pures
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, Hslcap⟩
  simp only [go.arrayLiteralSize, List.foldl]
  rw [show (max (max ((0 : Int) + 1 + 1 + 1) 0) 0) = 3 by decide]
  wp_pures; wp_alloc ids_ptr as ids; wp_pures; wp_alloc i_ptr as i; wp_pures
  -- `for _, ids := range []map{cfg.Voters.IDs(), cfg.Learners, cfg.LearnersNext}`: the
  -- first map is the voters' ids, every one of which has a progress; the other two
  -- are `nil`
  ihave IH : iprop(∃ (n : w64) (x : Loc),
      "i" ∷ i_ptr ↦ n ∗
      "ids" ∷ ids_ptr ↦ x ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ 3⌝) $$ [i ids]
  · iexists W64 0, zero_val Loc
    iframe i ids
    ipureintro; constructor <;> word
  wp_for_core
  iNamed IH
  wp_pures; wp_load; wp_pures
  cleanup_bool_decide
  wp_if_destruct
  · wp_load; wp_pures
    have Hbnd' : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z (W64 3) := ⟨Hn.1, by word⟩
    simp only [Hbnd', and_self]
    have Hcase : sint.nat n = 0 ∨ sint.nat n = 1 ∨ sint.nat n = 2 := by word
    rcases Hcase with Hc | Hc | Hc
    · -- the voters' ids
      wp_apply wp_load_slice_index _ (sint.Z n) _ _ mref Hn.1 $$ [Hsl] with Hsl
      · iframe Hsl; ipureintro; show [mref, map.nil, map.nil][sint.nat n]? = _; rw [Hc]; rfl
      wp_load; wp_pures; wp_store; wp_pures; wp_load; wp_pures; wp_alloc id_ptr as id; wp_pures
      wp_func_lits
      wp_bind (App (App (Val (map.forRange _ _)) _) _)
      iapply wp_map_for_range (fun (keys : List w64) (i : Int) => iprop(∃ (x : w64),
          "id" ∷ id_ptr ↦ x ∗
          "trk" ∷ trk_ptr ↦ trk ∗
          "Htrk" ∷ trk ↦${dqp} prs)) $$ Hidm
      iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
      isplitl [id trk Htrk]
      · iexists zero_val w64
        iframe
      isplitr
      · imodintro
        iintro %i %key %vv ⟨%Hkey, %Hvv⟩ HP
        iNamed HP
        wp_pures; wp_store; wp_pures; wp_load; wp_load
        wp_apply wp_map_lookup2 $$ Htrk as Htrk
        wp_pures; wp_alloc ok_ptr as ok; wp_pures; wp_store; wp_pures; wp_load; wp_pures; iclear ok
        -- `key` is a voter, so it has a progress
        have Hok : (prs !! key).isSome = true := by
          have h : key ∈ domSet idm := GMap.elem_of_dom_2 _ _ _ Hvv
          rw [Hidm, ← Hdom, GMap.elem_of_dom'] at h
          exact h
        simp only [Hok]
        wp_pures
        unfold forMapPostcondition
        iright; ileft
        isplitr
        · ipureintro; rfl
        iexists key
        iframe
      iintro HP Hidm
      iNamed HP
      wp_for_post
      wp_load; wp_pures; wp_store; iclear id
      iframe
      iexists n + W64 1, mref
      iframe
      ipureintro; constructor <;> word
    · -- `Learners`, nil
      wp_apply wp_load_slice_index _ (sint.Z n) _ _ map.nil Hn.1 $$ [Hsl] with Hsl
      · iframe Hsl; ipureintro; show [mref, map.nil, map.nil][sint.nat n]? = _; rw [Hc]; rfl
      wp_load; wp_pures; wp_store; wp_pures; wp_load; wp_pures; wp_alloc id_ptr as id; wp_pures
      wp_func_lits
      wp_pures; iclear id
      wp_for_post
      wp_load; wp_pures; wp_store
      iframe
      iexists n + W64 1, map.nil
      iframe
      ipureintro; constructor <;> word
    · -- `LearnersNext`, nil
      wp_apply wp_load_slice_index _ (sint.Z n) _ _ map.nil Hn.1 $$ [Hsl] with Hsl
      · iframe Hsl; ipureintro; show [mref, map.nil, map.nil][sint.nat n]? = _; rw [Hc]; rfl
      wp_load; wp_pures; wp_store; wp_pures; wp_load; wp_pures; wp_alloc id_ptr as id; wp_pures
      wp_func_lits
      wp_pures; iclear id
      wp_for_post
      wp_load; wp_pures; wp_store
      iframe
      iexists n + W64 1, map.nil
      iframe
      ipureintro; constructor <;> word
  · wp_load; wp_pures; wp_alloc id_ptr as id; wp_pures; iclear i ids
    -- the learner ranges (nil), then the non-joint checks
    wp_func_lits
    -- TODO(no-wp-auto): wp_auto: no manual sequence found (['mismatch'])
    wp_auto
    wp_func_lits
    wp_pures; wp_load; wp_pures; iclear trk id
    wp_apply wp_confchange_joint
      { Voters' := cfg.Voters', AutoLeave' := false, Learners' := map.nil, LearnersNext' := map.nil }
      v Harr
    wp_pures; wp_load; wp_pures
    wp_apply wp_confchange_outgoing _ v map.nil Harr
    wp_pures; wp_load; wp_pures; wp_load; wp_pures; iclear cfg
    iapply HΦ
    iframe
