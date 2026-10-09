/-
Proof of `Spec/Changer__apply.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.raft.v3.confchange.Changer__apply
public import Spec.go_etcd_io.raft.v3.confchange.Changer__makeVoter
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

theorem confchange.Changer.apply.wp_proof
    (wp_Changer_makeVoter : confchange.Changer.makeVoter.spec (GF := GF) (hG := hG))
    (wp_confchange_incoming : confchange.incoming.spec (GF := GF) (hG := hG)) :
    confchange.Changer.apply.spec (GF := GF) (hG := hG) := by
  intro p cfgp trk v chg cfg ccs id vm prs dq dqc Hid Hsz Hcfg Hdom Hmi
  have Hcfg' := Hcfg
  obtain ⟨⟨Harr, Hl, Hln⟩, Hal⟩ := Hcfg'
  wp_start as ⟨Hp, Hcfgp, Hccs, Hv, Htrk, Hprogs⟩
  wp_auto
  wp_method_call
  wp_call
  wp_auto
  ihave %Hclen := ownSlice_len $$ Hccs
  have Hlen1 : sint.Z ccs.len = 1 := by
    have h : [addNodeCC id].length = (sint.Z ccs.len).toNat := Hclen.1
    simp only [List.length_singleton] at h
    omega
  -- `for _, cc := range ccs`: the one change, `AddNode id`, goes through `makeVoter`
  ihave IH : iprop(∃ (n : w64) (x : raftpb.ConfChangeSingle) (vm' : GMap w64 Unit)
      (prs' : GMap w64 Loc),
      "i" ∷ i_ptr ↦ n ∗
      "cc" ∷ cc_ptr ↦ x ∗
      "Hv" ∷ v ↦$ vm' ∗
      "Htrk" ∷ trk ↦$ prs' ∗
      "Hprogs" ∷ ([∗map] _k ↦ pr ∈ prs', ∃ pp, ownProgress pr pp) ∗
      "%Hn" ∷ ⌜(n = W64 0 ∧ vm = vm' ∧ prs = prs') ∨
        (n = W64 1 ∧ vm' = <[id := ()]> vm ∧ domSet prs' = domSet vm')⌝) $$ [i cc Hv Htrk Hprogs]
  · iexists W64 0, _, vm, prs
    iframe
    ipureintro; exact .inl ⟨rfl, rfl, rfl⟩
  wp_for IH
  wp_if_destruct
  all_goals cleanup_bool_decide
  · rcases Hn with ⟨h0, h1, h2⟩ | ⟨h0, -, -⟩
    · have Hbnd' : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z ccs.len := ⟨by rw [h0]; decide, Hif⟩
      simp only [Hbnd', _root_.and_self]
      wp_apply wp_load_slice_index ccs (sint.Z n) _ _ (addNodeCC id) Hbnd'.1
        $$ [Hccs] with Hccs
      · iframe Hccs; ipureintro; rw [h0]; rfl
      -- `cc.NodeID == 0`: no
      wp_if_destruct
      · exact absurd rfl Hid
      -- `cc.Type == ConfChangeAddNode`: yes
      have Hdom0 : domSet prs' = domSet vm' := by rw [← h1, ← h2]; exact Hdom
      wp_apply wp_Changer_makeVoter c_ptr cfgp trk v _ cfg id vm' prs' _ Hcfg Hdom0 Hmi
        $$ [$c $Hcfgp $Hv $Htrk $Hprogs] as %prs'' ⟨c, Hcfgp, Hv, Htrk, %Hdom'', Hprogs⟩
      wp_for_post
      iframe
      iexists n + W64 1, addNodeCC id, <[id := ()]> vm', prs''
      iframe
      ipureintro
      exact .inr ⟨by rw [h0]; rfl, by rw [h1], Hdom''⟩
    · exfalso
      have h : sint.Z (W64 1) < sint.Z ccs.len := h0 ▸ Hif
      rw [Hlen1, show sint.Z (W64 1) = 1 by decide] at h
      omega
  · rcases Hn with ⟨h0, -, -⟩ | ⟨h0, h1, Hdom'⟩
    · exfalso
      have h : ¬ sint.Z (W64 0) < sint.Z ccs.len := h0 ▸ Hif
      rw [Hlen1, show sint.Z (W64 0) = 0 by decide] at h
      omega
    -- `len(incoming(cfg.Voters)) == 0`: no, `id` is in it
    wp_apply wp_confchange_incoming _ v map.nil Harr
    wp_apply wp_map_len $$ Hv as Hv
    have Hpos : 0 < GMap.size vm' := by
      rw [h1]; exact GMap.map_size_nonzero _ id (by rw [GMap.lookup_insert_eq]; rfl)
    have Hle : GMap.size vm' ≤ GMap.size vm + 1 := by
      rw [h1]
      rcases h : vm !! id with _ | ⟨⟩
      · rw [GMap.map_size_insert_None _ _ _ h]; omega
      · rw [GMap.insert_id _ _ _ h]; omega
    wp_if_destruct
    · exfalso
      have e1 : sint.Z (W64 ((GMap.size vm' : Nat) : Int)) = GMap.size vm' := by word
      have := congrArg sint.Z Hif
      rw [e1, show sint.Z (W64 0) = 0 by decide] at this
      omega
    iapply HΦ
    rw [h1]
    rw [h1] at Hdom'
    iframe
    ipureintro
    exact Hdom'

end proof

end EtcdGrove
end Perennial
