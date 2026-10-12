/-
Proof of `Spec/confchange_checkInvariants.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.raft.v3.confchange.checkInvariants
public import Spec.go_etcd_io.raft.v3.quorum.JointConfig__IDs
public import Spec.go_etcd_io.raft.v3.confchange.joint
public import Spec.go_etcd_io.raft.v3.confchange.outgoing

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
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
  wp_auto
  -- `cfg.Voters.IDs()`: the field was read out of the local copy when the method value
  -- was formed
  wp_apply wp_JointConfig_IDs _ v vm _ Harr $$ [$Hv] as %mref %idm ⟨Hv, Hidm, %Hidm⟩
  rw [Hl, Hln]
  wp_apply wp_slice_literal (V := GoMap) [mref, map.nil, map.nil]
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, Hslcap⟩
  simp only [go.arrayLiteralSize, List.foldl]
  rw [show (max (max ((0 : Int) + 1 + 1 + 1) 0) 0) = 3 by decide]
  wp_auto
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
  wp_for IH
  wp_if_destruct
  · have Hbnd' : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z (W64 3) := ⟨Hn.1, by word⟩
    simp only [Hbnd', and_self]
    have Hcase : sint.nat n = 0 ∨ sint.nat n = 1 ∨ sint.nat n = 2 := by word
    rcases Hcase with Hc | Hc | Hc
    · -- the voters' ids
      wp_apply wp_load_slice_index _ (sint.Z n) _ _ mref Hn.1 $$ [Hsl] with Hsl
      · iframe Hsl; ipureintro; show [mref, map.nil, map.nil][sint.nat n]? = _; rw [Hc]; rfl
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
        wp_auto
        wp_apply wp_map_lookup2 $$ Htrk as Htrk
        -- `key` is a voter, so it has a progress
        have Hok : (prs !! key).isSome = true := by
          have h : key ∈ domSet idm := GMap.elem_of_dom_2 _ _ _ Hvv
          rw [Hidm, ← Hdom, GMap.elem_of_dom'] at h
          exact h
        simp only [Hok]
        wp_auto
        unfold forMapPostcondition
        iright; ileft
        isplitr
        · ipureintro; rfl
        iexists key
        iframe
      iintro HP Hidm
      iNamed HP
      wp_for_post
      iframe
      iexists n + W64 1, mref
      iframe
      ipureintro; constructor <;> word
    · -- `Learners`, nil
      wp_apply wp_load_slice_index _ (sint.Z n) _ _ map.nil Hn.1 $$ [Hsl] with Hsl
      · iframe Hsl; ipureintro; show [mref, map.nil, map.nil][sint.nat n]? = _; rw [Hc]; rfl
      wp_func_lits
      wp_auto
      wp_for_post
      iframe
      iexists n + W64 1, map.nil
      iframe
      ipureintro; constructor <;> word
    · -- `LearnersNext`, nil
      wp_apply wp_load_slice_index _ (sint.Z n) _ _ map.nil Hn.1 $$ [Hsl] with Hsl
      · iframe Hsl; ipureintro; show [mref, map.nil, map.nil][sint.nat n]? = _; rw [Hc]; rfl
      wp_func_lits
      wp_auto
      wp_for_post
      iframe
      iexists n + W64 1, map.nil
      iframe
      ipureintro; constructor <;> word
  · -- the learner ranges (nil), then the non-joint checks
    wp_func_lits
    rw [Hln]
    wp_auto
    wp_func_lits
    rw [Hl]
    wp_auto
    wp_apply wp_confchange_joint cfg v Harr
    wp_apply wp_confchange_outgoing _ v map.nil Harr
    rw [Hln]
    wp_auto
    rw [Hal]
    wp_auto
    iapply HΦ
    iframe
