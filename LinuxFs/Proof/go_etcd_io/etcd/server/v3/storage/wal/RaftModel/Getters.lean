/-
**The getters of raftpb's `HardState` and `Entry` over the raftpb instance's objects** (W4c U4 b; the
proto2 optional fields' getters, nil-safe, `raftpb/raft.pb.go`): a cell `nil` reads as zero, a nil
`*HardState` as the zero state. Over a field at any fraction (`wp_hs*_raw`), over `hsGet`
(`wp_hsGet*`) and over `entRoC` (`wp_entRoC*`). Lean-first.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.RaftModel.Pb

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 WalEnc WalFs

section getters
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [raftpb_sem : go_etcd_io.raft.v3.raftpb.Assumptions]

/-! ## `HardState`, at a field -/

theorem wp_hsGetTerm_raw (p pt : Loc) (dq : DFrac) (o : Option w64) :
    {{ ⌜p ≠ null⌝ ∗ p.[raftpb.HardState, go!"Term"] ↦{dq} pt ∗ optCell (GF := GF) pt o }}
      (App (Val (p @!! go.GoType.PointerType raftpb.HardState.ty @!! go!"GetTerm")) (Val #()))
    {{ RET #(o.getD (W64 0)); p.[raftpb.HardState, go!"Term"] ↦{dq} pt }} := by
  wp_start as ⟨%Hn, Hf, #Hc⟩
  wp_auto
  simp only [decide_eq_false Hn]
  wp_auto
  rcases o with _ | v
  · iunfold optCell at Hc
    icases Hc with %Hpt
    subst Hpt
    wp_auto
    simp only [Option.getD]
    iapply HΦ; iframe
  · iunfold optCell at Hc
    ihave %Hn' := typedPointsto_not_null pt _ _ $$ Hc
    simp only [decide_eq_false Hn']
    wp_auto
    simp only [Option.getD]
    iapply HΦ; iframe

theorem wp_hsGetVote_raw (p pv : Loc) (dq : DFrac) (o : Option w64) :
    {{ ⌜p ≠ null⌝ ∗ p.[raftpb.HardState, go!"Vote"] ↦{dq} pv ∗ optCell (GF := GF) pv o }}
      (App (Val (p @!! go.GoType.PointerType raftpb.HardState.ty @!! go!"GetVote")) (Val #()))
    {{ RET #(o.getD (W64 0)); p.[raftpb.HardState, go!"Vote"] ↦{dq} pv }} := by
  wp_start as ⟨%Hn, Hf, #Hc⟩
  wp_auto
  simp only [decide_eq_false Hn]
  wp_auto
  rcases o with _ | v
  · iunfold optCell at Hc
    icases Hc with %Hpt
    subst Hpt
    wp_auto
    simp only [Option.getD]
    iapply HΦ; iframe
  · iunfold optCell at Hc
    ihave %Hn' := typedPointsto_not_null pv _ _ $$ Hc
    simp only [decide_eq_false Hn']
    wp_auto
    simp only [Option.getD]
    iapply HΦ; iframe

theorem wp_hsGetCommit_raw (p pc : Loc) (dq : DFrac) (o : Option w64) :
    {{ ⌜p ≠ null⌝ ∗ p.[raftpb.HardState, go!"Commit"] ↦{dq} pc ∗ optCell (GF := GF) pc o }}
      (App (Val (p @!! go.GoType.PointerType raftpb.HardState.ty @!! go!"GetCommit")) (Val #()))
    {{ RET #(o.getD (W64 0)); p.[raftpb.HardState, go!"Commit"] ↦{dq} pc }} := by
  wp_start as ⟨%Hn, Hf, #Hc⟩
  wp_auto
  simp only [decide_eq_false Hn]
  wp_auto
  rcases o with _ | v
  · iunfold optCell at Hc
    icases Hc with %Hpt
    subst Hpt
    wp_auto
    simp only [Option.getD]
    iapply HΦ; iframe
  · iunfold optCell at Hc
    ihave %Hn' := typedPointsto_not_null pc _ _ $$ Hc
    simp only [decide_eq_false Hn']
    wp_auto
    simp only [Option.getD]
    iapply HΦ; iframe

theorem wp_hsGetTerm_nil :
    {{ (True : IProp GF) }}
      (App (Val ((null : Loc) @!! go.GoType.PointerType raftpb.HardState.ty @!! go!"GetTerm")) (Val #()))
    {{ RET #(W64 0); True }} := by
  wp_start
  wp_auto
  iapply HΦ; ipureintro; trivial

theorem wp_hsGetVote_nil :
    {{ (True : IProp GF) }}
      (App (Val ((null : Loc) @!! go.GoType.PointerType raftpb.HardState.ty @!! go!"GetVote")) (Val #()))
    {{ RET #(W64 0); True }} := by
  wp_start
  wp_auto
  iapply HΦ; ipureintro; trivial

theorem wp_hsGetCommit_nil :
    {{ (True : IProp GF) }}
      (App (Val ((null : Loc) @!! go.GoType.PointerType raftpb.HardState.ty @!! go!"GetCommit")) (Val #()))
    {{ RET #(W64 0); True }} := by
  wp_start
  wp_auto
  iapply HΦ; ipureintro; trivial

/-! ## `HardState`, over `hsGet` -/

theorem wp_hsGetTerm (p : Loc) (h : HardStateM) :
    {{ hsGet (GF := GF) p h }}
      (App (Val (p @!! go.GoType.PointerType raftpb.HardState.ty @!! go!"GetTerm")) (Val #()))
    {{ RET #h.Term'; True }} := by
  wp_start_folded as #Hh
  iunfold hsGet at Hh
  icases Hh with (%Hz | ⟨%c, #Hc, %Hm⟩)
  · obtain ⟨rfl, rfl⟩ := Hz
    wp_apply wp_hsGetTerm_nil
    iapply HΦ; ipureintro; trivial
  · iunfold hsCells at Hc
    icases Hc with ⟨%pt, %pv, %pc, %Hn, #HT, #cT, -⟩
    wp_apply (wp_hsGetTerm_raw p pt DFrac.discard c.term) $$ [] as -
    · iframe HT cT; ipureintro; exact Hn
    subst Hm
    simp only [WalHsC.model]
    iapply HΦ; ipureintro; trivial

theorem wp_hsGetVote (p : Loc) (h : HardStateM) :
    {{ hsGet (GF := GF) p h }}
      (App (Val (p @!! go.GoType.PointerType raftpb.HardState.ty @!! go!"GetVote")) (Val #()))
    {{ RET #h.Vote'; True }} := by
  wp_start_folded as #Hh
  iunfold hsGet at Hh
  icases Hh with (%Hz | ⟨%c, #Hc, %Hm⟩)
  · obtain ⟨rfl, rfl⟩ := Hz
    wp_apply wp_hsGetVote_nil
    iapply HΦ; ipureintro; trivial
  · iunfold hsCells at Hc
    icases Hc with ⟨%pt, %pv, %pc, %Hn, -, -, #HV, #cV, -⟩
    wp_apply (wp_hsGetVote_raw p pv DFrac.discard c.vote) $$ [] as -
    · iframe HV cV; ipureintro; exact Hn
    subst Hm
    simp only [WalHsC.model]
    iapply HΦ; ipureintro; trivial

theorem wp_hsGetCommit (p : Loc) (h : HardStateM) :
    {{ hsGet (GF := GF) p h }}
      (App (Val (p @!! go.GoType.PointerType raftpb.HardState.ty @!! go!"GetCommit")) (Val #()))
    {{ RET #h.Commit'; True }} := by
  wp_start_folded as #Hh
  iunfold hsGet at Hh
  icases Hh with (%Hz | ⟨%c, #Hc, %Hm⟩)
  · obtain ⟨rfl, rfl⟩ := Hz
    wp_apply wp_hsGetCommit_nil
    iapply HΦ; ipureintro; trivial
  · iunfold hsCells at Hc
    icases Hc with ⟨%pt, %pv, %pc, %Hn, -, -, -, -, #HC, #cC⟩
    wp_apply (wp_hsGetCommit_raw p pc DFrac.discard c.commit) $$ [] as -
    · iframe HC cC; ipureintro; exact Hn
    subst Hm
    simp only [WalHsC.model]
    iapply HΦ; ipureintro; trivial

/-! ## `Entry`, over `entRoC` -/

theorem wp_entRoC_GetIndex (l : Loc) (c : EntryC) :
    {{ entRoC (GF := GF) l c }}
      (App (Val (l @!! go.GoType.PointerType raftpb.Entry.ty @!! go!"GetIndex")) (Val #()))
    {{ RET #(c.index.getD (W64 0)); True }} := by
  wp_start as #Hc
  iunfold entRoC at Hc
  icases Hc with ⟨%pt, %pi, %pty, %ds, %Hn, -, -, #HI, #cI, -⟩
  wp_auto
  simp only [decide_eq_false Hn]
  wp_auto
  rcases ho : c.index with _ | v
  · iunfold optCell at cI
    icases cI with %Hpi
    subst Hpi
    wp_auto
    simp only [Option.getD]
    iapply HΦ; ipureintro; trivial
  · iunfold optCell at cI
    ihave %Hn' := typedPointsto_not_null pi _ _ $$ cI
    simp only [decide_eq_false Hn']
    wp_auto
    simp only [Option.getD]
    iapply HΦ; ipureintro; trivial

theorem wp_entRoC_GetTerm (l : Loc) (c : EntryC) :
    {{ entRoC (GF := GF) l c }}
      (App (Val (l @!! go.GoType.PointerType raftpb.Entry.ty @!! go!"GetTerm")) (Val #()))
    {{ RET #(c.term.getD (W64 0)); True }} := by
  wp_start as #Hc
  iunfold entRoC at Hc
  icases Hc with ⟨%pt, %pi, %pty, %ds, %Hn, #HT, #cT, -⟩
  wp_auto
  simp only [decide_eq_false Hn]
  wp_auto
  rcases ho : c.term with _ | v
  · iunfold optCell at cT
    icases cT with %Hpt
    subst Hpt
    wp_auto
    simp only [Option.getD]
    iapply HΦ; ipureintro; trivial
  · iunfold optCell at cT
    ihave %Hn' := typedPointsto_not_null pt _ _ $$ cT
    simp only [decide_eq_false Hn']
    wp_auto
    simp only [Option.getD]
    iapply HΦ; ipureintro; trivial

theorem wp_entRoC_GetData (l : Loc) (c : EntryC) :
    {{ entRoC (GF := GF) l c }}
      (App (Val (l @!! go.GoType.PointerType raftpb.Entry.ty @!! go!"GetData")) (Val #()))
    {{ (ds : GoSlice), RET #ds; ds ↦*□ c.data.getD [] }} := by
  wp_start as #Hc
  iunfold entRoC at Hc
  icases Hc with ⟨%pt, %pi, %pty, %ds, %Hn, -, -, -, -, -, -, #HD, #cD, -⟩
  wp_auto
  simp only [decide_eq_false Hn]
  wp_auto
  rcases ho : c.data with _ | bs
  · iunfold bytesC at cD
    icases cD with %Hds
    subst Hds
    iapply HΦ
    simp only [Option.getD]
    iapply ownSlice_nil
  · iunfold bytesC at cD
    icases cD with ⟨-, #Hb⟩
    iapply HΦ
    simp only [Option.getD]
    iexact Hb

end getters

end EtcdGrove
end Perennial
