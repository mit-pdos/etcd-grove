/-
Proof of `Spec/go_etcd_io/raft/v3/confchange/Changer__apply.lean`. Lean-first (no Rocq
counterpart). (2026-10-15, raft v3.7 retarget, stage R2: each change a `*pb.ConfChangeSingle`
read through `GetNodeId`/`GetType`.)
-/
module

public import Spec.go_etcd_io.raft.v3.confchange.Changer__apply
public import Spec.go_etcd_io.raft.v3.confchange.Changer__makeVoter
public import Spec.go_etcd_io.raft.v3.confchange.Changer__makeLearner
public import Spec.go_etcd_io.raft.v3.confchange.Changer__remove
public import Spec.go_etcd_io.raft.v3.confchange.incoming
public import Spec.fmt.Errorf
public import Spec.go_etcd_io.raft.v3.raftpb.ConfChangeType__String
public import Spec.go_etcd_io.raft.v3.raftpb.ConfChangeSingle__GetNodeId
public import Spec.go_etcd_io.raft.v3.raftpb.ConfChangeSingle__GetType

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

/-- `remove` on the whole working state: an untracked id's `Progress` is dropped. -/
theorem wp_remove_work
    (wp_Changer_remove : confchange.Changer.remove.spec (GF := GF) (hG := hG))
    (p cfgp trk : Loc) (chg : confchange.Changer) (base : GMap w64 tracker.Progress)
    (s : CCState) (id : w64) (dq : DFrac) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.confchange ∗ p ↦{dq} chg ∗
        ownWork chg base cfgp trk s }}
      (App (App (App (Val (p @!! go.GoType.PointerType confchange.Changer.ty @!! go!"remove"))
        (Val #cfgp)) (Val #trk)) (Val #id))
    {{ RET #(); p ↦{dq} chg ∗ ownWork chg base cfgp trk (removeM id s) }} := by
  iintro %Φ ⟨#Hpkg, Hp, Hw⟩ HΦ
  icases ownWork_elim _ _ _ _ _ $$ Hw with
    ⟨%cfg, %prs, %pvs, Hcfgp, Hc, Htrk, Hprs, %Hflags, Hnew⟩
  ihave %Hdom0 := BigSepM2.bigSepM2_lookup_iff $$ Hprs
  have Hdomeq : domSet prs = domSet s.prs := by
    apply GMap.set_eq; intro k
    rw [GMap.elem_of_dom', GMap.elem_of_dom', ← Hflags, flagsOf_mem]
    exact Hdom0 k
  ihave Hcw : ownCfgAt cfgp s.cfg $$ [Hcfgp Hc]
  · unfold ownCfgAt; iexists cfg; iframe
  iapply wp_Changer_remove p cfgp trk chg s prs id dq Hdomeq $$ [$Hpkg $Hp $Hcw $Htrk]
  inext
  iintro ⟨Hp, Hcw, Htrk⟩
  iapply HΦ
  iframe Hp
  unfold ownCfgAt
  icases Hcw with ⟨%cfg', Hcfgp, Hc⟩
  by_cases hc : id ∈ s.prs ∧ id ∉ s.cfg.outgoing
  · rw [ite_eq_left hc]
    icases ownPrs_delete chg base prs pvs id $$ [$Hprs $Hnew] with ⟨Hprs, Hnew⟩
    iapply ownWork_intro chg base cfgp trk (removeM id s) cfg' _ _ ?_ $$ Hcfgp Hc Htrk Hprs Hnew
    simp only [removeM, ite_eq_left hc.1, ite_eq_right hc.2, flagsOf_delete, Hflags]
  · rw [ite_eq_right hc]
    iapply ownWork_intro chg base cfgp trk (removeM id s) cfg' prs pvs ?_ $$ Hcfgp Hc Htrk Hprs Hnew
    unfold removeM
    by_cases h1 : id ∈ s.prs
    · have h2 : id ∈ s.cfg.outgoing := by
        exact Classical.byContradiction fun h2 => hc ⟨h1, h2⟩
      simp only [ite_eq_left h1, ite_eq_left h2, Hflags]
    · simp only [ite_eq_right h1, Hflags]

theorem confchange.Changer.apply.wp_proof
    (wp_Changer_makeVoter : confchange.Changer.makeVoter.spec (GF := GF) (hG := hG))
    (wp_Changer_makeLearner : confchange.Changer.makeLearner.spec (GF := GF) (hG := hG))
    (wp_Changer_remove : confchange.Changer.remove.spec (GF := GF) (hG := hG))
    (wp_confchange_incoming : confchange.incoming.spec (GF := GF) (hG := hG))
    (wp_fmt_Errorf : fmt.Errorf.spec (GF := GF) (hG := hG))
    (wp_ConfChangeType_String : raftpb.ConfChangeType.String.spec (GF := GF) (hG := hG))
    (wp_ConfChangeSingle_GetNodeId : raftpb.ConfChangeSingle.GetNodeId.spec (GF := GF) (hG := hG))
    (wp_ConfChangeSingle_GetType : raftpb.ConfChangeSingle.GetType.spec (GF := GF) (hG := hG)) :
    confchange.Changer.apply.spec (GF := GF) (hG := hG) := by
  intro p cfgp trk chg base s ccs ls l dq dqs Hmi
  wp_start as ⟨Hp, Hccs, #Hcl, Hw⟩
  wp_auto
  wp_method_call
  wp_call
  wp_auto
  ihave %Hclen := ownSlice_len $$ Hccs
  ihave %Hll := BigSepL2.bigSepL2_length $$ Hcl
  -- `for _, cc := range ccs`: after `n` changes, the state is `applyAll (l.take n) s`
  ihave IH : iprop(∃ (n : w64) (x : Loc) (s' : CCState),
      "i" ∷ i_ptr ↦ n ∗
      "cc" ∷ cc_ptr ↦ x ∗
      "Hw" ∷ ownWork chg base cfgp trk s' ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z ccs.len ∧
        applyAll (l.take (sint.nat n)) s = some s'⌝) $$ [i cc Hw]
  · iexists W64 0, _, s
    iframe
    ipureintro; refine ⟨by decide, by word, rfl⟩
  wp_for IH
  wp_if_destruct
  · have Hbnd' : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z ccs.len := ⟨Hn.1, Hif⟩
    simp only [Hbnd', _root_.and_self]
    have Hlt : sint.nat n < l.length := by have := Hclen.1; rw [← Hll]; word
    have Hltq : sint.nat n < ls.length := by rw [Hll]; exact Hlt
    obtain ⟨cc, Hcc⟩ : ∃ cc, l[sint.nat n]? = some cc := ⟨_, List.getElem?_eq_getElem Hlt⟩
    obtain ⟨q, Hq⟩ : ∃ q, ls[sint.nat n]? = some q := ⟨_, List.getElem?_eq_getElem Hltq⟩
    ihave #Hcq := BigSepL2.bigSepL2_lookup (Φ := fun _ q c => ccsRO (GF := GF) q c) Hq Hcc $$ Hcl
    wp_apply wp_load_slice_index ccs (sint.Z n) _ _ q Hn.1 $$ [Hccs] with Hccs
    · iframe Hccs; ipureintro; exact Hq
    have Htake : l.take (sint.nat (n + W64 1)) = l.take (sint.nat n) ++ [cc] := by
      rw [show sint.nat (n + W64 1) = sint.nat n + 1 by word, List.take_add_one, Hcc]; rfl
    have Hstep : applyAll (l.take (sint.nat (n + W64 1))) s = applyOne cc s' := by
      rw [Htake, applyAll_snoc, Hn.2.2]; rfl
    wp_apply wp_ConfChangeSingle_GetNodeId.1 q DFrac.discard cc $$ [Hcq] as -
    · iexact Hcq
    wp_if_destruct
    · -- `NodeId == 0`: skipped
      wp_for_post
      iframe
      iexists n + W64 1, q, s'
      iframe
      ipureintro
      refine ⟨by word, by word, ?_⟩
      rw [Hstep]; simp [applyOne, Hif]
    have H0 := Hif
    wp_apply wp_ConfChangeSingle_GetType.1 q DFrac.discard cc $$ [Hcq] as -
    · iexact Hcq
    wp_if_destruct
    · -- `AddNode`
      wp_apply wp_ConfChangeSingle_GetNodeId.1 q DFrac.discard cc $$ [Hcq] as -
      · iexact Hcq
      wp_apply wp_Changer_makeVoter c_ptr cfgp trk chg base s' cc.NodeId' _ Hmi $$ [$c $Hw]
        as ⟨c, Hw⟩
      wp_for_post
      iframe
      iexists n + W64 1, q, _
      iframe
      ipureintro
      refine ⟨by word, by word, ?_⟩
      rw [Hstep]; simp only [applyOne, ite_eq_right H0, ite_eq_left Hif]
    have H1 := Hif
    wp_if_destruct
    · -- `AddLearnerNode`
      wp_apply wp_ConfChangeSingle_GetNodeId.1 q DFrac.discard cc $$ [Hcq] as -
      · iexact Hcq
      wp_apply wp_Changer_makeLearner c_ptr cfgp trk chg base s' cc.NodeId' _ Hmi $$ [$c $Hw]
        as ⟨c, Hw⟩
      wp_for_post
      iframe
      iexists n + W64 1, q, _
      iframe
      ipureintro
      refine ⟨by word, by word, ?_⟩
      rw [Hstep]; simp only [applyOne, ite_eq_right H0, ite_eq_right H1, ite_eq_left Hif]
    have H2 := Hif
    wp_if_destruct
    · -- `RemoveNode`
      wp_apply wp_ConfChangeSingle_GetNodeId.1 q DFrac.discard cc $$ [Hcq] as -
      · iexact Hcq
      wp_apply wp_remove_work wp_Changer_remove c_ptr cfgp trk chg base s' cc.NodeId' _
        $$ [$c $Hw] as ⟨c, Hw⟩
      wp_for_post
      iframe
      iexists n + W64 1, q, _
      iframe
      ipureintro
      refine ⟨by word, by word, ?_⟩
      rw [Hstep]; simp only [applyOne, ite_eq_right H0, ite_eq_right H1, ite_eq_right H2, ite_eq_left Hif]
    have H3 := Hif
    wp_if_destruct
    · -- `UpdateNode`: nothing
      wp_for_post
      iframe
      iexists n + W64 1, q, s'
      iframe
      ipureintro
      refine ⟨by word, by word, ?_⟩
      rw [Hstep]; simp only [applyOne, ite_eq_right H0, ite_eq_right H1, ite_eq_right H2, ite_eq_right H3, ite_eq_left Hif]
    · -- any other type: "unexpected conf type %d"
      wp_apply wp_ConfChangeSingle_GetType.1 q DFrac.discard cc $$ [Hcq] as -
      · iexact Hcq
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %sl' ⟨Hsl', -⟩
      wp_auto
      -- a `ConfChangeType` argument: etcd-grove's `fmt.Errorf` (Perennial's admits basic types
      -- only), with the enum's `String()` at the trust boundary
      ihave #HS := wp_ConfChangeType_String cc.Type'
      wp_apply wp_fmt_Errorf $$ [$Hsl'] as %e -
      · fmt_args_ok
      wp_for_post
      iapply HΦ
      iframe
      have Hnone : applyOne cc s' = none := by
        simp only [applyOne, ite_eq_right H0, ite_eq_right H1, ite_eq_right H2, ite_eq_right H3, ite_eq_right Hif]
      have Hall : applyAll l s = none := by
        have hl : l = l.take (sint.nat (n + W64 1)) ++ l.drop (sint.nat (n + W64 1)) :=
          (List.take_append_drop _ _).symm
        rw [hl, applyAll_append, Hstep, Hnone]; rfl
      simp only [applyM, Hall, Option.bind_none]
      ipureintro; intro h; cases h
  · -- the loop is over: `len(incoming(cfg.Voters)) == 0`?
    have Hall : l.take (sint.nat n) = l := by
      apply List.take_of_length_le; have := Hclen.1; word
    rw [Hall] at Hn
    icases ownWork_elim _ _ _ _ _ $$ Hw with
      ⟨%cfg, %prs, %pvs, Hcfgp, Hc, Htrk, Hprs, %Hflags, Hnew⟩
    icases ownCfgCC_elim _ _ _ $$ Hc with ⟨%vin, %vout, %Harr, Hin, Hout, Hl, Hln, %Hal⟩
    wp_auto
    wp_apply wp_confchange_incoming _ vin vout Harr
    wp_apply wp_map_len_lt $$ Hin as ⟨Hin, %Hlt⟩
    ihave Hc := ownCfgCC_intro cfg (DFrac.own 1) s'.cfg vin vout Harr Hal $$ Hin Hout Hl Hln
    ihave Hw := ownWork_intro chg base cfgp trk s' cfg prs pvs Hflags $$ Hcfgp Hc Htrk Hprs Hnew
    wp_if_destruct
    · -- "removed all voters"
      wp_apply errors.wp_New as %e #He
      iapply HΦ
      iframe
      have Hempty : s'.cfg.incoming = ∅ := by
        apply GMap.map_size_empty_inv
        have := congrArg sint.Z Hif
        word
      simp only [applyM, Hn.2.2, Option.bind_some, Hempty, ite_true]
      ipureintro; intro h; cases h
    · iapply HΦ
      iframe
      have Hne : s'.cfg.incoming ≠ ∅ := by
        intro h; rw [h, GMap.map_size_empty] at Hif; exact Hif rfl
      simp only [applyM, Hn.2.2, Option.bind_some, Hne, ite_false]
      iframe

end proof

end EtcdGrove
end Perennial
