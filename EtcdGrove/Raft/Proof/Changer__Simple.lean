/-
Proof of `Spec/Changer__Simple.lean`. Lean-first (no Rocq counterpart).
-/
import EtcdGrove.Raft.Spec.Changer__Simple
import EtcdGrove.Raft.Spec.Changer__checkAndCopy
import EtcdGrove.Raft.Spec.confchange_joint
import EtcdGrove.Raft.Spec.Changer__apply
import EtcdGrove.Raft.Spec.confchange_incoming
import EtcdGrove.Raft.Spec.confchange_symdiff
import EtcdGrove.Raft.Spec.confchange_checkAndReturn

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

theorem confchange.Changer.Simple.wp_proof
    (wp_Changer_checkAndCopy : confchange.Changer.checkAndCopy.spec (GF := GF) (hG := hG))
    (wp_confchange_joint : confchange.joint.spec (GF := GF) (hG := hG))
    (wp_Changer_apply : confchange.Changer.apply.spec (GF := GF) (hG := hG))
    (wp_confchange_incoming : confchange.incoming.spec (GF := GF) (hG := hG))
    (wp_confchange_symdiff : confchange.symdiff.spec (GF := GF) (hG := hG))
    (wp_confchange_checkAndReturn : confchange.checkAndReturn.spec (GF := GF) (hG := hG)) :
    confchange.Changer.Simple.spec (GF := GF) (hG := hG) := by
  intro p chg ccs id v vm prs dq dqc dqv dqp Hid Hsz Hcfg Hdom Hmi
  have Hcfg' := Hcfg
  obtain ⟨Harr, Hl, Hln⟩ := Hcfg'
  wp_start as ⟨Hp, Hccs, Hv, Hpm, Hprogs⟩
  wp_load; wp_pures
  wp_method_call
  wp_call
  wp_call; wp_alloc c_ptr as c; wp_pures; wp_alloc ccs_ptr as ccs; wp_pures
  -- `cfg, trk, err := c.checkAndCopy()`, on the local copy of the receiver
  wp_apply wp_Changer_checkAndCopy c_ptr _ v vm prs _ _ _ Hcfg Hdom $$ [$c $Hv $Hpm $Hprogs]
    as %cfg' %trk %v' %prs' ⟨c, Hv, Hpm, %Hcfg', Hv', Htrk, %Hdom', Hprogs'⟩
  wp_pures; wp_alloc err_ptr as err; wp_pures; wp_alloc trk_ptr as trk; wp_pures
  wp_alloc cfg_ptr as cfg; wp_pures; wp_store; wp_pures; wp_store; wp_pures; wp_store; wp_pures
  wp_load; wp_pures; wp_load; wp_pures; iclear err
  -- `joint(cfg)`: no
  wp_apply wp_confchange_joint _ v' Hcfg'.1.1
  wp_pures; wp_load; wp_pures; wp_load; wp_pures; iclear ccs
  -- `c.apply(&cfg, trk, ccs...)`
  wp_apply wp_Changer_apply c_ptr cfg_ptr trk v' _ cfg' ccs id vm prs' _ _ Hid Hsz Hcfg' Hdom' Hmi
    $$ [$c $cfg $Hccs $Hv' $Htrk $Hprogs'] as %prs'' ⟨c, cfg, Hccs, Hv', Htrk, %Hdom'', Hprogs''⟩
  wp_pures; wp_alloc err_ptr as err; wp_pures; wp_store; wp_pures; wp_load; wp_pures; wp_load
  wp_pures; iclear c err
  -- `symdiff(incoming(c.Tracker.Voters), incoming(cfg.Voters))`: at most one voter changed
  wp_apply wp_confchange_incoming _ v map.nil Harr
  wp_pures; wp_load; wp_pures
  wp_apply wp_confchange_incoming _ v' map.nil Hcfg'.1.1
  wp_pures
  wp_apply wp_confchange_symdiff _ _ vm (<[id := ()]> vm) _ _ $$ [$Hv $Hv'] as %n ⟨Hv, Hv', %Hn⟩
  wp_pures; wp_alloc n_ptr as n; wp_pures; wp_store; wp_pures; wp_load; wp_pures; iclear n
  have Hn1 : 0 ≤ sint.Z n ∧ sint.Z n ≤ 1 := by
    refine Hn ?_ id ?_
    · intro k hk
      by_cases h : id = k
      · subst h; rw [GMap.lookup_insert_eq]; rfl
      · rw [GMap.lookup_insert_ne _ _ h]; exact hk
    · intro k hk
      by_cases h : id = k
      · exact .inr h.symm
      · rw [GMap.lookup_insert_ne _ _ h] at hk; exact .inl hk
  wp_if_destruct
  · exfalso; word
  wp_load; wp_pures; wp_load; wp_pures; iclear trk cfg
  -- `checkAndReturn(cfg, trk)`
  wp_apply wp_confchange_checkAndReturn _ _ v' (<[id := ()]> vm) prs'' _ _ Hcfg' Hdom''
    $$ [$Hv' $Htrk] as ⟨Hv', Htrk⟩
  wp_pures
  iapply HΦ
  iframe
  ipureintro
  exact ⟨Hcfg', Hdom''⟩

end proof

end EtcdGrove
end Perennial
