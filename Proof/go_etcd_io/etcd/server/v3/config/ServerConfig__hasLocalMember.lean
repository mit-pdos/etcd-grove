/-
Proof of `config.ServerConfig.hasLocalMember.spec` (claim #34, stage 2, 2026-11-25): the map
lookup, and `fmt.Errorf` of a string on a miss.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.config.ServerConfig__hasLocalMember
public import Spec.fmt.Errorf

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.config.Assumptions]

theorem config.ServerConfig.hasLocalMember.wp_proof
    (hErrorf : fmt.Errorf.spec (GF := GF) (hG := hG)) :
    config.ServerConfig.hasLocalMember.spec (GF := GF) (hG := hG) := by
  intro p cfg m
  wp_start as ⟨#Hname, #Hmapf, #Hm⟩
  try wp_auto
  wp_apply (wp_map_lookup1 (K := GoString) (V := GoSlice) _ _ cfg.InitialPeerURLsMap' m cfg.Name'
    DFrac.discard) $$ [Hm] as -
  · iframe #
  try wp_auto
  wp_if_destruct
  · -- nil: an error
    try wp_auto
    ihave #Hfmt : isPkgInit (PROP := IProp GF) pkg_id.fmt $$ []
    · iPkgInit
    wp_apply wp_slice_literal (V := GoInterface)
    isplitr
    · ipureintro; rfl
    iintro %asl ⟨Hasl, -⟩
    wp_apply hErrorf _ _ _ _ $$ [Hasl] as %e -
    · iframe #; iframe Hasl
      fmt_args_ok
    (try wp_auto)
    iapply HΦ
    ipureintro; left; simp
  · try wp_auto
    iapply HΦ
    ipureintro; right
    refine ⟨rfl, ?_⟩
    cases h : m !! cfg.Name' with
    | none => simp [h] at Hif; exact absurd rfl Hif
    | some _ => rfl

end proof

end EtcdGrove
end Perennial
