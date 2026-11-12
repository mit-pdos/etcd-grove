/-
Port of election_proof/proof_traceConfChangeEvent.v; both modes since 2026-11-12 (trace-check step 4:
the traced branch, until then `TracedConfChangeHook.lean`'s proof of the Draft's statement): untraced,
the nil check; traced, the `TracingConfChange` built from the new configuration's incoming voters
(`cfg.Voters[0].Slice()`, formatted), the properties' map `{"cc": cc}` made read-only, and `traceEvent`
with the caller's read-only lending of raft's state (at the old configuration).
-/
module

public import Spec.go_etcd_io.raft.v3.traceConfChangeEvent
public import Spec.go_etcd_io.raft.v3.traceEvent
public import Spec.go_etcd_io.raft.v3.formatConf
public import Spec.go_etcd_io.raft.v3.quorum.MajorityConfig__Slice

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem traceConfChangeEvent.wp_proof
    (wp_traceEvent : traceEvent.spec (GF := GF) (hG := hG))
    (wp_Slice : quorum.MajorityConfig.Slice.spec (GF := GF) (hG := hG))
    (wp_formatConf : formatConf.spec (GF := GF) (hG := hG)) :
    traceConfChangeEvent.spec (GF := GF) (hG := hG) := by
  intro cfgv r tl tr E Q R
  wp_start as ⟨#Htl, Hown, Hfire⟩
  cases tr with
  | none =>
    icases (traceFire_none tl _ Q).1 $$ Hfire with ⟨%Hok, HQ⟩
    unfold TraceLoggerOk at Hok; subst Hok
    wp_auto
    iapply HΦ
    iframe
    iapply trOwn_none_intro
  | some γd =>
    icases (trOwn_some γd _).1 $$ Hown
      with ⟨%c, %cn, %id, %s, %prsm, %prs, %pvs, %P, HP, #HRL, Hnew, %HE, HR⟩
    dsimp only [TraceFire]
    icases Hfire with ⟨%tn, #Hdir, #Hlog, %Hnn, Hau⟩
    cases tl with
    | nil => exact absurd rfl Hnn
    | ok i =>
    wp_auto
    iunfold ownConfigC at Hnew
    iNamed Hnew
    icases ownCfgCC_elim _ _ _ $$ Hcfg with ⟨%vin, %vout, %Harr, Hin, Hout, Hl, Hln, %Hal⟩
    icases (Access.access
        (A := cfg_ptr.[tracker.Config, go!"Voters"] ↦ cfgv.Voters')
        (A' := cfg_ptr.[tracker.Config, go!"Voters"] ↦ cfgv.Voters')
        (P := cfg_ptr ↦ cfgv)) $$ cfg with ⟨Hvf, Hcfgback⟩
    icases array_acc _ (sint.Z (W64 0)) _ _ _ vin (by decide) (by rw [Harr]; rfl)
      $$ Hvf with ⟨Hc0, Hcback⟩
    wp_apply wp_slice_literal (V := SingleConfChange) []
    isplitr
    · ipureintro; rfl
    iintro %sl0 Hsl0
    wp_auto
    rw [method_unfold (t := go.GoType.PointerType quorum.MajorityConfig.ty)]
    wp_call
    wp_auto
    have Hsz : (GMap.size cn.incoming : Int) ≤ 2 ^ 62 := by
      have := size_le_of_sub_dom cn.incoming prs (by rw [Hdom]; exact incoming_sub_ids cn)
      omega
    ihave %Hvin_nn := ownMap_not_nil $$ Hin
    wp_apply wp_Slice vin cn.incoming $$ [Hin] as %sl1 %xs ⟨Hin, Hsl1, -, %Hxs⟩
    · isplitl
      · unfold ownIdsetOpt; iright; iexact Hin
      · ipureintro; exact Hsz
    wp_apply wp_formatConf $$ [$Hsl1] as %a ⟨-, Ha⟩
    wp_apply wp_map_make1 (K := GoString) (V := GoInterface) go.string go.any as %mp Hmp
    try wp_auto
    wp_apply wp_mapInsert $$ [$Hmp] as Hmp
    try wp_auto
    imod ownMap_persist mp _ _ $$ Hmp with #Hmp
    icases Hsl0 with ⟨Hsl0, -⟩
    ipersist Hsl0
    ipersist Ha
    ipersist «$r0»
    rw [domSet_gset] at Hxs
    -- the properties: `{"cc": cc}`, `cc` the new configuration's incoming voters
    ihave #Hprops : tracingPropsRep (GF := GF) mp
        { noProps with propCC := some ⟨[], xs.map decStr⟩ } $$ []
    · unfold tracingPropsRep
      iright
      iexists _, «$r0_ptr»
      iframe Hmp
      isplitr
      · ipureintro
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp
        · intro h; simp at h
        · intro w; simp [noProps]
        · intro _; simp
        · intro w; simp [noProps]
        · intro _; simp
        · intro k hk
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk
          rw [GMap.lookup_insert_ne _ _ (Ne.symm hk.1)]
          rfl
      simp only [tracingCCRep]
      iexists _, []
      iframe «$r0» Hsl0 Ha
      ipureintro; rfl
    wp_apply wp_traceEvent (W64 7) r null mp (GoInterface.ok i) (some γd) E Q
        P $$ [HP Hau] as HR0
    · iframe Htl
      isplitl [HP]
      · iapply (trOwn_some γd _).2
        iexists c, id, s, P, none,
          { noProps with propCC := some ⟨[], xs.map decStr⟩ }
        iframe HP Hprops
        isplitr
        · iexact HRL
        isplitr
        · iapply msgLend_nil
        isplitr
        · ipureintro
          refine ⟨by decide, ?_⟩
          intro e h hm hc h1 h2 h3
          obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8⟩ := h
          exact HE e ⟨g1, g2, g3, g4, g5, g6, g7, g8, hm, hc, ⟨xs, Hxs, h1⟩, h2, h3⟩
        iintro H; iexact H
      dsimp only [TraceFire]
      iexists tn
      iframe Hdir Hlog Hau
      ipureintro; exact Hnn
    icases HR0 with ⟨HR0, HQ⟩
    ihave HP := (trOwn_some γd _).1 $$ HR0
    ihave Hin : ownIdsetQ (GF := GF) vin (DFrac.own 1) cn.incoming $$ [Hin]
    · unfold ownIdsetQ; iunfold ownIdsetOpt at Hin; iexact Hin
    ihave Hin := ownIdsetQ_not_nil _ _ _ Hvin_nn $$ Hin
    ihave Hcfg := ownCfgCC_intro cfgv (DFrac.own 1) cn vin vout Harr Hal $$ Hin Hout Hl Hln
    iapply HΦ
    iframe HQ
    iapply (trOwn_some γd _).2
    iapply HR
    iframe HP
    iunfold ownConfigC
    iframe Hcfg Hprsm Hprogs
    ipureintro; exact ⟨Hinv, Hdom, Hflags, Hsize⟩

end proof

end EtcdGrove
end Perennial
