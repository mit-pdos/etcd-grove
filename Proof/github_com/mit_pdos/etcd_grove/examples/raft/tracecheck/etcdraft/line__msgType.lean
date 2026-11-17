/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `line__msgType`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.line__msgType

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Etcdraft

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Assumptions]

theorem line.msgType.wp_proof : line.msgType.spec (GF := GF) (hG := hG) := by
  intro q x
  wp_start as #Hlp
  ihave #Hinit := etcdraftInit_get $$ Hpkg
  icases Hinit with ⟨⟨%mt, #Hmt, #Hmtm⟩, -⟩
  open_lineP
  wp_auto
  cases hm : x.ev.msg with
  | none =>
    icases Hemsg with %Hnull
    rw [Hnull]
    wp_auto
    simp only [Option.bind_none, Option.map_none, Option.getD_none, Option.isSome_none]
    iapply HΦ; ipureintro; trivial
  | some mm =>
    icases Hemsg with ⟨%gm, #Hgm, %Hgmr⟩
    ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hgm
    rw [decide_eq_false Hnn]
    icases typedPointsto_split _ _ _ $$ Hgm with Hgmf
    simp only [TypedPointsto.typedPointstoDef]
    iNamed Hgmf
    wp_auto
    wp_apply wp_map_lookup2 $$ [Hmtm] as -
    · iexact Hmtm
    rw [raftMsgTypeMap_lookup Hgmr.1]
    try wp_auto
    simp only [Option.bind_some]
    cases raftMsgType mm.type <;> (simp only [Option.map_none, Option.map_some, Option.getD_none,
      Option.getD_some, Option.isSome_none, Option.isSome_some, Bool.false_eq_true, _root_.decide_false,
      _root_.decide_true, show (zero_val w8) = W8 0 from rfl]; iapply HΦ; ipureintro; trivial)

end proof

end Etcdraft
end EtcdGrove
end Perennial
