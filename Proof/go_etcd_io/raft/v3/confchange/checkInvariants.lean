/-
Proof of `Spec/go_etcd_io/raft/v3/confchange/checkInvariants.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.raft.v3.confchange.checkInvariants
public import Spec.go_etcd_io.raft.v3.quorum.JointConfig__IDs
public import Spec.go_etcd_io.raft.v3.confchange.joint
public import Spec.go_etcd_io.raft.v3.confchange.outgoing
public import Spec.go_etcd_io.raft.v3.confchange.incoming

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

/-- The three id sets `checkInvariants` first ranges over, by index. -/
def ciSets (c : CfgM) : List (GMap w64 Unit) := [c.incoming ∪ c.outgoing, c.learners, c.learnersNext]

/-- After `n` sets of the first loop, every id of them is tracked. -/
def ciTracked (c : CfgM) (prs : GMap w64 Loc) (n : Nat) : Prop :=
  ∀ j S k, j < n → (ciSets c)[j]? = some S → (S !! k).isSome → (prs !! k).isSome

theorem ciTracked_step (c : CfgM) (prs : GMap w64 Loc) (n : Nat) (S : GMap w64 Unit)
    (Hn : ciTracked c prs n) (HS : (ciSets c)[n]? = some S)
    (Hall : ∀ k, (S !! k).isSome → (prs !! k).isSome) : ciTracked c prs (n + 1) := by
  intro j S' k hj hS' hk
  rcases Nat.lt_or_ge j n with h | h
  · exact Hn j S' k h hS' hk
  · have : j = n := by omega
    subst this
    rw [HS] at hS'
    cases hS'
    exact Hall k hk

/-- An id of one of the four sets. -/
def ciMember (c : CfgM) (k : w64) : Prop :=
  k ∈ c.incoming ∨ k ∈ c.outgoing ∨ k ∈ c.learners ∨ k ∈ c.learnersNext

theorem ciSets_member (c : CfgM) (n : Nat) (S : GMap w64 Unit) (k : w64)
    (HS : (ciSets c)[n]? = some S) (Hk : (S !! k).isSome) : ciMember c k := by
  unfold ciMember
  simp only [GMap.mem_iff]
  rcases n with _ | _ | _ | n <;> simp [ciSets] at HS <;> subst HS
  · simp only [GMap.lookup_union] at Hk
    rcases h : c.incoming !! k with _ | v
    · rw [h] at Hk; simp only [Option.none_or] at Hk; exact .inr (.inl Hk)
    · exact .inl (by simp)
  · exact .inr (.inr (.inl Hk))
  · exact .inr (.inr (.inr Hk))

theorem ciTracked_all (c : CfgM) (prs : GMap w64 Loc) (H : ciTracked c prs 3) (k : w64)
    (Hk : ciMember c k) : (prs !! k).isSome := by
  unfold ciMember at Hk
  simp only [GMap.mem_iff] at Hk
  rcases Hk with h | h | h | h
  · refine H 0 _ k (by decide) rfl ?_
    simp [GMap.lookup_union, h]
  · refine H 0 _ k (by decide) rfl ?_
    simp only [GMap.lookup_union]
    rcases h1 : c.incoming !! k with _ | v
    · simp only [Option.none_or]; exact h
    · simp
  · exact H 1 _ k (by decide) rfl h
  · exact H 2 _ k (by decide) rfl h

theorem ci_err {P : Prop} (e : GoInterfaceOk) (H : ¬ P) :
    (GoInterface.ok e = interface.nil ↔ P) := by
  constructor
  · intro h; cases h
  · intro h; exact absurd h H

/-- Close the configuration's representation from its pieces. -/
theorem ci_close (cfg : tracker.Config) (c : CfgM) (vin vout : Loc) (dqc : DFrac)
    (Harr : cfg.Voters'.arr = [vin, vout]) (Hal : cfg.AutoLeave' = c.autoLeave)
    (Hinnn : vin ≠ map.nil) (Hcout : vout = map.nil ∨ c.outgoing ≠ ∅)
    (Hcln : cfg.LearnersNext' = map.nil ∨ c.learnersNext ≠ ∅)
    (Hcl : cfg.Learners' = map.nil ∨ c.learners ≠ ∅) :
    ⊢ ownIdsetQ (GF := GF) vin dqc c.incoming -∗ ownIdsetQ vout dqc c.outgoing -∗
      ownIdsetQ cfg.Learners' dqc c.learners -∗ ownIdsetQ cfg.LearnersNext' dqc c.learnersNext -∗
      ownCfgCC cfg dqc c := by
  iintro Hin Hout Hl Hln
  ihave Hin := ownIdsetQ_not_nil _ _ _ Hinnn $$ Hin
  ihave Hout := ownIdsetC_join _ _ _ Hcout $$ Hout
  ihave Hln := ownIdsetC_join _ _ _ Hcln $$ Hln
  ihave Hl := ownIdsetC_join _ _ _ Hcl $$ Hl
  iapply ownCfgCC_intro cfg dqc c vin vout Harr Hal $$ Hin Hout Hl Hln

theorem confchange.checkInvariants.wp_proof
    (wp_JointConfig_IDs : quorum.JointConfig.IDs.spec (GF := GF) (hG := hG))
    (wp_confchange_joint : confchange.joint.spec (GF := GF) (hG := hG))
    (wp_confchange_outgoing : confchange.outgoing.spec (GF := GF) (hG := hG))
    (wp_confchange_incoming : confchange.incoming.spec (GF := GF) (hG := hG)) :
    confchange.checkInvariants.spec (GF := GF) (hG := hG) := by
  intro cfg trk c prs pvs dqc dqm dqp
  wp_start as ⟨Hc, Htrk, Hprs⟩
  icases ownCfgCC_elim _ _ _ $$ Hc with ⟨%vin, %vout, %Harr, Hin, Hout, Hl, Hln, %Hal⟩
  ihave %Hdom0 := BigSepM2.bigSepM2_lookup_iff $$ Hprs
  have Hdom : ∀ k, (prs !! k).isSome ↔ (pvs !! k).isSome := Hdom0
  wp_auto
  -- `cfg.Voters.IDs()`: the field out of the local copy, and back
  icases (Access.access (A := iprop(cfg_ptr.[tracker.Config, go!"Voters"] ↦ cfg.Voters'))
    (A' := iprop(cfg_ptr.[tracker.Config, go!"Voters"] ↦ cfg.Voters'))
    (P := iprop(cfg_ptr ↦ cfg))) $$ cfg with ⟨Hf, Hback⟩
  ihave %Hinnn := ownMap_not_nil _ _ _ $$ Hin
  icases ownIdsetC_split _ _ _ $$ Hout with ⟨Hout, %Hcout⟩
  ihave Hin := ownIdsetQ_map _ _ _ $$ Hin
  wp_apply wp_JointConfig_IDs _ _ vin vout c.incoming c.outgoing _ dqc dqc Harr
    $$ [$Hf $Hin $Hout] as %mref ⟨Hf, Hin, Hout, Hmref⟩
  ihave cfg := Hback $$ Hf
  wp_auto
  wp_apply wp_slice_literal (V := GoMap) [mref, cfg.Learners', cfg.LearnersNext']
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, Hslcap⟩
  simp only [go.arrayLiteralSize, List.foldl]
  rw [show (max (max ((0 : Int) + 1 + 1 + 1) 0) 0) = 3 by decide]
  wp_auto
  icases ownIdsetC_split _ _ _ $$ Hln with ⟨Hln, %Hcln⟩
  icases ownIdsetC_split _ _ _ $$ Hl with ⟨Hl, %Hcl⟩
  ihave Hmref := ownIdsetQ_map _ _ _ $$ Hmref
  -- `for _, ids := range []map{cfg.Voters.IDs(), cfg.Learners, cfg.LearnersNext}`: every
  -- id of each is tracked
  ihave IH : iprop(∃ (n : w64) (x : Loc),
      "i" ∷ i_ptr ↦ n ∗
      "ids" ∷ ids_ptr ↦ x ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ 3 ∧ ciTracked c prs (sint.nat n)⌝) $$ [i ids]
  · iexists W64 0, zero_val Loc
    iframe i ids
    ipureintro
    refine ⟨by decide, by decide, fun j S k hj => absurd hj (by simp)⟩
  wp_for IH
  wp_if_destruct
  · have Hbnd' : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z (W64 3) := ⟨Hn.1, by word⟩
    simp only [Hbnd', and_self]
    have Hcase : sint.nat n = 0 ∨ sint.nat n = 1 ∨ sint.nat n = 2 := by word
    -- the `n`th id set, borrowed: `nil` or a map
    ihave Hbor : iprop(∃ (x : Loc) (S : GMap w64 Unit) (dqx : DFrac),
        ⌜[mref, cfg.Learners', cfg.LearnersNext'][sint.nat n]? = some x⌝ ∗
        ⌜(ciSets c)[sint.nat n]? = some S⌝ ∗
        ownIdsetQ x dqx S ∗
        (ownIdsetQ x dqx S -∗
          ownIdsetQ mref (DFrac.own 1) (c.incoming ∪ c.outgoing) ∗
          ownIdsetQ cfg.Learners' dqc c.learners ∗
          ownIdsetQ cfg.LearnersNext' dqc c.learnersNext)) $$ [Hmref Hl Hln]
    · rcases Hcase with Hc | Hc | Hc
      · iexists mref, _, _
        iframe Hmref
        isplitr
        · ipureintro; rw [Hc]; rfl
        isplitr
        · ipureintro; rw [Hc]; rfl
        iintro Hmref
        iframe
      · iexists cfg.Learners', _, _
        iframe Hl
        isplitr
        · ipureintro; rw [Hc]; rfl
        isplitr
        · ipureintro; rw [Hc]; rfl
        iintro Hl
        iframe
      · iexists cfg.LearnersNext', _, _
        iframe Hln
        isplitr
        · ipureintro; rw [Hc]; rfl
        isplitr
        · ipureintro; rw [Hc]; rfl
        iintro Hln
        iframe
    icases Hbor with ⟨%x, %S, %dqx, %Hx, %HS, Hx, Hxback⟩
    wp_apply wp_load_slice_index _ (sint.Z n) _ _ x Hn.1 $$ [Hsl] with Hsl
    · iframe Hsl; ipureintro; exact Hx
    -- `for id := range ids { if _, ok := trk[id]; !ok { return error } }`
    wp_func_lits
    wp_bind (App (App (Val (map.forRange _ _)) _) _)
    iapply wp_idset_for_range (fun (keys : List w64) (i : Int) => iprop(∃ (y : w64),
        "%Hi" ∷ ⌜0 ≤ i⌝ ∗
        "%Hseen" ∷ ⌜∀ k, k ∈ keys.take i.toNat → (prs !! k).isSome⌝ ∗
        "id" ∷ id_ptr ↦ y ∗
        "trk" ∷ trk_ptr ↦ trk ∗
        "Htrk" ∷ trk ↦${dqm} prs ∗
        "Hprs" ∷ ([∗map] _k ↦ pr;pv ∈ prs;pvs, pr ↦{dqp} pv) ∗
        "Hin" ∷ ownIdsetQ vin dqc c.incoming ∗
        "Hout" ∷ ownIdsetQ vout dqc c.outgoing ∗
        "Hxback" ∷ (ownIdsetQ x dqx S -∗
          ownIdsetQ mref (DFrac.own 1) (c.incoming ∪ c.outgoing) ∗
          ownIdsetQ cfg.Learners' dqc c.learners ∗
          ownIdsetQ cfg.LearnersNext' dqc c.learnersNext) ∗
        "HΦ" ∷ (∀ (err : GoInterface), ownCfgCC cfg dqc c ∗ trk ↦${dqm} prs ∗
          ([∗map] _k ↦ pr;pv ∈ prs;pvs, pr ↦{dqp} pv) ∗
          ⌜err = interface.nil ↔ CfgInv { cfg := c, prs := flagsOf pvs }⌝ -∗ Φ #err)))
      $$ Hx
    iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
    isplitl [id trk Htrk Hprs Hin Hout Hxback HΦ]
    · iexists zero_val w64
      iframe
      ipureintro
      refine ⟨Int.le_refl _, fun k hk => by simp at hk⟩
    isplitr
    · imodintro
      iintro %i %key %vv ⟨%Hkey, %Hvv⟩ HP
      iNamed HP
      wp_auto
      wp_apply wp_map_lookup2 $$ Htrk as Htrk
      wp_if_destruct
      · unfold forMapPostcondition
        iright; ileft
        isplitr
        · ipureintro; rfl
        iexists key
        iframe
        ipureintro
        refine ⟨by omega, fun k hk => ?_⟩
        rw [show (i + 1).toNat = i.toNat + 1 by omega, List.take_add_one, Hkey] at hk
        simp only [Option.toList_some, List.mem_append, List.mem_singleton] at hk
        rcases hk with hk | hk
        · exact Hseen k hk
        · subst hk; simpa using Hif
      · -- `key` is untracked: the error "no progress for %d"
        wp_apply wp_slice_literal
        isplitr
        · ipureintro; rfl
        iintro %sl' ⟨Hsl', -⟩
        wp_apply fmt.wp_Errorf $$ [$Hsl'] as %e #He
        unfold forMapPostcondition
        iright; iright; iright
        iexists _
        isplitr
        · ipureintro; rfl
        iintro Hx
        icases Hxback $$ Hx with ⟨Hmref, Hl, Hln⟩
        wp_for_post
        iapply HΦ
        iframe Htrk Hprs
        isplitl [Hin Hout Hl Hln]
        · iapply ci_close cfg c vin vout dqc Harr Hal Hinnn Hcout Hcln Hcl $$ Hin Hout Hl Hln
        ipureintro
        refine ci_err e (fun Hinv => ?_)
        have Hk := Hinv.1 key (ciSets_member c _ S key HS (by rw [Hvv]; rfl))
        rw [flagsOf_mem, ← Hdom] at Hk
        exact Hif (by simpa using Hk)
    iintro HP Hx
    iNamed HP
    rw [Int.toNat_natCast, ← Hklen, List.take_length] at Hseen
    icases Hxback $$ Hx with ⟨Hmref, Hl, Hln⟩
    wp_for_post
    iframe
    iexists n + W64 1, x
    iframe
    ipureintro
    refine ⟨by word, by word, ?_⟩
    rw [show sint.nat (n + W64 1) = sint.nat n + 1 by word]
    exact ciTracked_step c prs _ S Hn.2.2 HS (fun k hk => Hseen k ((Hkset k).2 hk))
  -- every voter, learner and staged learner is tracked
  have Htracked : ciTracked c prs 3 := by
    have : sint.nat n = 3 := by word
    rw [← this]; exact Hn.2.2
  have Htr : ∀ k, ciMember c k → ∃ pr pv, prs !! k = some pr ∧ pvs !! k = some pv := by
    intro k hk
    have h1 := ciTracked_all c prs Htracked k hk
    have h2 := (Hdom k).1 h1
    obtain ⟨pr, hpr⟩ := Option.isSome_iff_exists.1 h1
    obtain ⟨pv, hpv⟩ := Option.isSome_iff_exists.1 h2
    exact ⟨pr, pv, hpr, hpv⟩
  -- `for id := range cfg.LearnersNext`: an outgoing voter, not marked a learner
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_idset_for_range (fun (keys : List w64) (i : Int) => iprop(∃ (y : w64),
      "%Hi" ∷ ⌜0 ≤ i⌝ ∗
      "%Hseen" ∷ ⌜∀ k, k ∈ keys.take i.toNat →
        k ∈ c.outgoing ∧ flagsOf pvs !! k = some false⌝ ∗
      "id" ∷ id_ptr ↦ y ∗
      "trk" ∷ trk_ptr ↦ trk ∗
      "cfg" ∷ cfg_ptr ↦ cfg ∗
      "Htrk" ∷ trk ↦${dqm} prs ∗
      "Hprs" ∷ ([∗map] _k ↦ pr;pv ∈ prs;pvs, pr ↦{dqp} pv) ∗
      "Hin" ∷ ownIdsetQ vin dqc c.incoming ∗
      "Hout" ∷ ownIdsetQ vout dqc c.outgoing ∗
      "Hl" ∷ ownIdsetQ cfg.Learners' dqc c.learners ∗
      "HΦ" ∷ (∀ (err : GoInterface), ownCfgCC cfg dqc c ∗ trk ↦${dqm} prs ∗
        ([∗map] _k ↦ pr;pv ∈ prs;pvs, pr ↦{dqp} pv) ∗
        ⌜err = interface.nil ↔ CfgInv { cfg := c, prs := flagsOf pvs }⌝ -∗ Φ #err)))
    $$ Hln
  iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
  isplitl [id trk cfg Htrk Hprs Hin Hout Hl HΦ]
  · iexists zero_val w64
    iframe
    ipureintro
    refine ⟨Int.le_refl _, fun k hk => by simp at hk⟩
  isplitr
  · imodintro
    iintro %i %key %vv ⟨%Hkey, %Hvv⟩ HP
    iNamed HP
    have HkLN : key ∈ c.learnersNext := by rw [GMap.mem_iff, Hvv]; rfl
    wp_auto
    wp_apply wp_confchange_outgoing _ vin vout Harr
    wp_apply wp_idset_lookup2 $$ Hout as Hout
    wp_if_destruct
    · obtain ⟨pr, pv, hpr, hpv⟩ := Htr key (.inr (.inr (.inr HkLN)))
      wp_apply wp_map_lookup1 $$ Htrk as Htrk
      rw [hpr]
      simp only [Option.getD_some]
      icases (BigSepM2.bigSepM2_lookup_acc hpr hpv) $$ Hprs with ⟨Hpr, Hprback⟩
      icases typedPointsto_not_null_dup _ _ _ $$ Hpr with ⟨Hpr, %Hprnn⟩
      iStructNamed Hpr
      wp_auto
      ihave Hpr : (pr ↦{dqp} pv) $$ [Match Next sentCommit State PendingSnapshot RecentActive
          MsgAppFlowPaused Inflights IsLearner]
      · iapply typedPointsto_combine _ _ _ Hprnn
        simp only [TypedPointsto.typedPointstoDef]
        iframe
      ihave Hprs := Hprback $$ Hpr
      cases hl : pv.IsLearner'
      case true =>
        -- "%d is in LearnersNext, but is already marked as learner"
        wp_auto
        wp_apply wp_slice_literal
        isplitr
        · ipureintro; rfl
        iintro %sl' ⟨Hsl', -⟩
        wp_apply fmt.wp_Errorf $$ [$Hsl'] as %e #He
        unfold forMapPostcondition
        iright; iright; iright
        iexists _
        isplitr
        · ipureintro; rfl
        iintro Hln
        wp_auto
        iapply HΦ
        iframe Htrk Hprs
        isplitl [Hin Hout Hl Hln]
        · iapply ci_close cfg c vin vout dqc Harr Hal Hinnn Hcout Hcln Hcl $$ Hin Hout Hl Hln
        ipureintro
        refine ci_err e (fun Hinv => ?_)
        have h := (Hinv.2.1 key HkLN).2
        rw [flagsOf_lookup pvs key pv hpv] at h
        simp_all
      case false =>
        wp_auto
        unfold forMapPostcondition
        iright; ileft
        isplitr
        · ipureintro; rfl
        iexists key
        iframe
        ipureintro
        refine ⟨by omega, fun k hk => ?_⟩
        rw [show (i + 1).toNat = i.toNat + 1 by omega, List.take_add_one, Hkey] at hk
        simp only [Option.toList_some, List.mem_append, List.mem_singleton] at hk
        rcases hk with hk | hk
        · exact Hseen k hk
        · subst hk
          refine ⟨by simpa [GMap.mem_iff] using Hif, ?_⟩
          rw [flagsOf_lookup pvs k pv hpv]
          simp_all
    · -- "%d is in LearnersNext, but not Voters[1]"
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %sl' ⟨Hsl', -⟩
      wp_apply fmt.wp_Errorf $$ [$Hsl'] as %e #He
      unfold forMapPostcondition
      iright; iright; iright
      iexists _
      isplitr
      · ipureintro; rfl
      iintro Hln
      wp_auto
      iapply HΦ
      iframe Htrk Hprs
      isplitl [Hin Hout Hl Hln]
      · iapply ci_close cfg c vin vout dqc Harr Hal Hinnn Hcout Hcln Hcl $$ Hin Hout Hl Hln
      ipureintro
      refine ci_err e (fun Hinv => ?_)
      have h := (Hinv.2.1 key HkLN).1
      rw [GMap.mem_iff] at h
      simp_all
  iintro HP Hln
  iNamed HP
  rw [Int.toNat_natCast, ← Hklen, List.take_length] at Hseen
  have HLN : ∀ k, k ∈ c.learnersNext → k ∈ c.outgoing ∧ flagsOf pvs !! k = some false :=
    fun k hk => Hseen k ((Hkset k).2 hk)
  clear Hseen Hkset Hklen Hknodup
  -- `for id := range cfg.Learners`: neither voter, and marked a learner
  wp_auto
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_idset_for_range (fun (keys : List w64) (i : Int) => iprop(∃ (y : w64),
      "%Hi" ∷ ⌜0 ≤ i⌝ ∗
      "%Hseen" ∷ ⌜∀ k, k ∈ keys.take i.toNat →
        k ∉ c.outgoing ∧ k ∉ c.incoming ∧ flagsOf pvs !! k = some true⌝ ∗
      "id" ∷ id_ptr ↦ y ∗
      "trk" ∷ trk_ptr ↦ trk ∗
      "cfg" ∷ cfg_ptr ↦ cfg ∗
      "Htrk" ∷ trk ↦${dqm} prs ∗
      "Hprs" ∷ ([∗map] _k ↦ pr;pv ∈ prs;pvs, pr ↦{dqp} pv) ∗
      "Hin" ∷ ownIdsetQ vin dqc c.incoming ∗
      "Hout" ∷ ownIdsetQ vout dqc c.outgoing ∗
      "Hln" ∷ ownIdsetQ cfg.LearnersNext' dqc c.learnersNext ∗
      "HΦ" ∷ (∀ (err : GoInterface), ownCfgCC cfg dqc c ∗ trk ↦${dqm} prs ∗
        ([∗map] _k ↦ pr;pv ∈ prs;pvs, pr ↦{dqp} pv) ∗
        ⌜err = interface.nil ↔ CfgInv { cfg := c, prs := flagsOf pvs }⌝ -∗ Φ #err)))
    $$ Hl
  iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
  isplitl [id trk cfg Htrk Hprs Hin Hout Hln HΦ]
  · iexists zero_val w64
    iframe
    ipureintro
    refine ⟨Int.le_refl _, fun k hk => by simp at hk⟩
  isplitr
  · imodintro
    iintro %i %key %vv ⟨%Hkey, %Hvv⟩ HP
    iNamed HP
    have HkL : key ∈ c.learners := by rw [GMap.mem_iff, Hvv]; rfl
    wp_auto
    wp_apply wp_confchange_outgoing _ vin vout Harr
    wp_apply wp_idset_lookup2 $$ Hout as Hout
    wp_if_destruct
    · -- "%d is in Learners and Voters[1]"
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %sl' ⟨Hsl', -⟩
      wp_apply fmt.wp_Errorf $$ [$Hsl'] as %e #He
      unfold forMapPostcondition
      iright; iright; iright
      iexists _
      isplitr
      · ipureintro; rfl
      iintro Hl
      wp_auto
      iapply HΦ
      iframe Htrk Hprs
      isplitl [Hin Hout Hl Hln]
      · iapply ci_close cfg c vin vout dqc Harr Hal Hinnn Hcout Hcln Hcl $$ Hin Hout Hl Hln
      ipureintro
      refine ci_err e (fun Hinv => ?_)
      have h := (Hinv.2.2.1 key HkL).1
      rw [GMap.mem_iff] at h
      simp_all
    wp_apply wp_confchange_incoming _ vin vout Harr
    wp_apply wp_idset_lookup2 $$ Hin as Hin
    wp_if_destruct
    · -- "%d is in Learners and Voters[0]"
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %sl' ⟨Hsl', -⟩
      wp_apply fmt.wp_Errorf $$ [$Hsl'] as %e #He
      unfold forMapPostcondition
      iright; iright; iright
      iexists _
      isplitr
      · ipureintro; rfl
      iintro Hl
      wp_auto
      iapply HΦ
      iframe Htrk Hprs
      isplitl [Hin Hout Hl Hln]
      · iapply ci_close cfg c vin vout dqc Harr Hal Hinnn Hcout Hcln Hcl $$ Hin Hout Hl Hln
      ipureintro
      refine ci_err e (fun Hinv => ?_)
      have h := (Hinv.2.2.1 key HkL).2.1
      rw [GMap.mem_iff] at h
      simp_all
    obtain ⟨pr, pv, hpr, hpv⟩ := Htr key (.inr (.inr (.inl HkL)))
    wp_apply wp_map_lookup1 $$ Htrk as Htrk
    rw [hpr]
    simp only [Option.getD_some]
    icases (BigSepM2.bigSepM2_lookup_acc hpr hpv) $$ Hprs with ⟨Hpr, Hprback⟩
    icases typedPointsto_not_null_dup _ _ _ $$ Hpr with ⟨Hpr, %Hprnn⟩
    iStructNamed Hpr
    wp_auto
    ihave Hpr : (pr ↦{dqp} pv) $$ [Match Next sentCommit State PendingSnapshot RecentActive
        MsgAppFlowPaused Inflights IsLearner]
    · iapply typedPointsto_combine _ _ _ Hprnn
      simp only [TypedPointsto.typedPointstoDef]
      iframe
    ihave Hprs := Hprback $$ Hpr
    cases hl : pv.IsLearner'
    case true =>
      wp_auto
      unfold forMapPostcondition
      iright; ileft
      isplitr
      · ipureintro; rfl
      iexists key
      iframe
      ipureintro
      refine ⟨by omega, fun k hk => ?_⟩
      rw [show (i + 1).toNat = i.toNat + 1 by omega, List.take_add_one, Hkey] at hk
      simp only [Option.toList_some, List.mem_append, List.mem_singleton] at hk
      rcases hk with hk | hk
      · exact Hseen k hk
      · subst hk
        refine ⟨by simp_all [GMap.mem_iff], by simp_all [GMap.mem_iff], ?_⟩
        rw [flagsOf_lookup pvs k pv hpv]
        simp_all
    case false =>
      -- "%d is in Learners, but is not marked as learner"
      wp_auto
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %sl' ⟨Hsl', -⟩
      wp_apply fmt.wp_Errorf $$ [$Hsl'] as %e #He
      unfold forMapPostcondition
      iright; iright; iright
      iexists _
      isplitr
      · ipureintro; rfl
      iintro Hl
      wp_auto
      iapply HΦ
      iframe Htrk Hprs
      isplitl [Hin Hout Hl Hln]
      · iapply ci_close cfg c vin vout dqc Harr Hal Hinnn Hcout Hcln Hcl $$ Hin Hout Hl Hln
      ipureintro
      refine ci_err e (fun Hinv => ?_)
      have h := (Hinv.2.2.1 key HkL).2.2
      rw [flagsOf_lookup pvs key pv hpv] at h
      simp_all
  iintro HP Hl
  iNamed HP
  rw [Int.toNat_natCast, ← Hklen, List.take_length] at Hseen
  have HL : ∀ k, k ∈ c.learners →
      k ∉ c.outgoing ∧ k ∉ c.incoming ∧ flagsOf pvs !! k = some true :=
    fun k hk => Hseen k ((Hkset k).2 hk)
  clear Hseen Hkset Hklen Hknodup
  have Hmem : ∀ k, ciMember c k → k ∈ flagsOf pvs := by
    intro k hk
    rw [flagsOf_mem, ← Hdom]
    exact ciTracked_all c prs Htracked k hk
  -- `if !joint(cfg) { ... }`
  wp_auto
  wp_apply wp_confchange_joint cfg vin vout c.outgoing dqc Harr $$ [$Hout] as Hout
  wp_if_destruct
  · -- joint: nothing more to check
    iapply HΦ
    iframe Htrk Hprs
    isplitl [Hin Hout Hl Hln]
    · iapply ci_close cfg c vin vout dqc Harr Hal Hinnn Hcout Hcln Hcl $$ Hin Hout Hl Hln
    ipureintro
    refine ⟨fun _ => ⟨fun k hk => Hmem k hk, HLN, HL, fun h => ?_⟩, fun _ => rfl⟩
    rw [h, GMap.map_size_empty] at Hif
    exact absurd Hif (by decide)
  · -- not joint: the outgoing config is empty, so `nil`
    have Hout0 : c.outgoing = ∅ := GMap.map_size_empty_inv _ (by omega)
    have Hvout : vout = map.nil := by
      rcases Hcout with h | h
      · exact h
      · exact absurd Hout0 h
    wp_apply wp_confchange_outgoing _ vin vout Harr
    subst Hvout
    icases ownIdsetQ_nil_empty _ _ _ $$ Hln with ⟨Hln, %HlnE⟩
    wp_auto
    wp_if_destruct
    · -- `LearnersNext` is `nil`: empty
      have Hln0 : c.learnersNext = ∅ := HlnE (by simpa using Hif)
      rw [Hal]
      cases hal : c.autoLeave
      · wp_auto
        iapply HΦ
        iframe Htrk Hprs
        isplitl [Hin Hout Hl Hln]
        · iapply ci_close cfg c vin _ dqc Harr Hal Hinnn Hcout Hcln Hcl $$ Hin Hout Hl Hln
        ipureintro
        exact ⟨fun _ => ⟨fun k hk => Hmem k hk, HLN, HL, fun _ => ⟨Hln0, hal⟩⟩, fun _ => rfl⟩
      · -- "AutoLeave must be false when not joint"
        wp_auto
        ihave Hnil : (slice.nil ↦* ([] : List GoAny)) $$ []
        · iapply ownSlice_nil
        wp_apply fmt.wp_Errorf $$ [$Hnil] as %e #He
        iapply HΦ
        iframe Htrk Hprs
        isplitl [Hin Hout Hl Hln]
        · iapply ci_close cfg c vin _ dqc Harr Hal Hinnn Hcout Hcln Hcl $$ Hin Hout Hl Hln
        ipureintro
        refine ci_err e (fun Hinv => ?_)
        have := (Hinv.2.2.2 Hout0).2
        simp_all
    · -- "cfg.LearnersNext must be nil when not joint"
      ihave Hnil : (slice.nil ↦* ([] : List GoAny)) $$ []
      · iapply ownSlice_nil
      wp_apply fmt.wp_Errorf $$ [$Hnil] as %e #He
      iapply HΦ
      iframe Htrk Hprs
      isplitl [Hin Hout Hl Hln]
      · iapply ci_close cfg c vin _ dqc Harr Hal Hinnn Hcout Hcln Hcl $$ Hin Hout Hl Hln
      ipureintro
      refine ci_err e (fun Hinv => ?_)
      have := (Hinv.2.2.2 Hout0).1
      have Hlnnn : cfg.LearnersNext' ≠ map.nil := by simpa using Hif
      rcases Hcln with h | h
      · exact Hlnnn h
      · exact h this

end proof

end EtcdGrove
end Perennial
