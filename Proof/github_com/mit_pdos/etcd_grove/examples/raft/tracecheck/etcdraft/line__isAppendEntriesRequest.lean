/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `line__isAppendEntriesRequest`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.line__isAppendEntriesRequest
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

-- The heartbeat check, then the entries' count (hygiene off).
set_option hygiene false in
local macro "aereq_len" "[" xs:ident,* "]" : tactic => `(tactic| (
  iunfold logRO at Hve
  icases Hve with ⟨%es, #Hes, #Hel⟩
  ihave %Hesl := ownSlice_len $$ Hes
  ihave %Hell := BigSepL2.bigSepL2_length $$ Hel
  have hlen : sint.Z gm.Entries'.len = (m.entries.length : Int) := by rw [← Hell, Hesl.1]; word
  rw [show decide (gm.Entries'.len = gev.Entries') = decide ((m.entries.length : Int) = ev.entries) from
    decide_eq_decide.2 (sint_eq_iff _ _ _ _ hlen Hem.2.2.2.2.1)]
  iapply HΦ'; ipureintro
  simp [Line.isAppendEntriesRequest, hm, ho, hs, h1, h2, h3, hA, $[$xs:ident],*] <;>
    first | rfl | (exfalso; rw [hsn] at hhb; exact absurd hhb (by decide))))

set_option hygiene false in
local macro "aereq_hb" "[" xs:ident,* "]" : tactic => `(tactic| (
  rw [decide_strRel Hv.2.1 strRel_heartbeat]
  by_cases hhb : m.subtype = "heartbeat"
  · rw [decide_eq_true hhb]
    wp_auto
    aereq_len [hhb, $[$xs:ident],*]
  rw [decide_eq_false hhb]
  wp_auto
  rw [decide_eq_decide.2 (sint_eq_iff _ _ _ _ Hv.2.2.2.2.2.2.2.1 Hem.2.2.2.2.2.1)]
  by_cases h5 : m.prevLogTerm = ev.logTerm
  rotate_left
  · rw [decide_eq_false h5]
    wp_auto
    iapply HΦ'; ipureintro
    simp [Line.isAppendEntriesRequest, hm, ho, hs, h1, h2, h3, hA, hhb, h5, $[$xs:ident],*]
  rw [decide_eq_true h5]
  wp_auto
  rw [decide_eq_decide.2 (sint_eq_iff _ _ _ _ Hv.2.2.2.2.2.2.1 Hem.2.2.2.2.2.2.1)]
  by_cases h6 : m.prevLogIndex = ev.index
  rotate_left
  · rw [decide_eq_false h6]
    wp_auto
    iapply HΦ'; ipureintro
    simp [Line.isAppendEntriesRequest, hm, ho, hs, h1, h2, h3, hA, hhb, h5, h6, $[$xs:ident],*]
  rw [decide_eq_true h6]
  wp_auto
  aereq_len [hhb, h5, h6, $[$xs:ident],*]))

theorem line.isAppendEntriesRequest.wp_proof (wp_msgType : line.msgType.spec (GF := GF) (hG := hG)) :
    line.isAppendEntriesRequest.spec (GF := GF) (hG := hG) := by
  intro q x p m
  wp_start as ⟨#Hlp, #Hmsg⟩
  ihave HΦ' : (∀ b : Bool, ⌜b = x.isAppendEntriesRequest m⌝ -∗ Φ #b) $$ [HΦ]
  · iintro %b %hb; rw [hb]; iapply HΦ; ipureintro; trivial
  ihave #Hinit := etcdraftInit_get $$ Hpkg
  icases Hinit with ⟨-, ⟨%msub, #Hmsub, #Hmsubm⟩, -⟩
  read_msg
  wp_auto
  wp_apply wp_msgType q x $$ [Hlp]
  · iframe Hlp
  open_lineP
  try wp_auto
  rw [show decide (gm.Type' = W8 2) = decide (m.type = .appendEntriesRequest) from
    msgTypeW_decide Hv.1 .appendEntriesRequest]
  by_cases hA : m.type = .appendEntriesRequest
  rotate_left
  · rw [decide_eq_false hA]
    wp_auto
    iapply HΦ'; ipureintro
    cases hm : x.ev.msg <;> simp [Line.isAppendEntriesRequest, hm, hA]
  rw [decide_eq_true hA]
  wp_auto
  cases hm : x.ev.msg with
  | none =>
    simp only [Option.bind_none, Option.isSome_none, Bool.not_false]
    wp_auto
    iapply HΦ'; ipureintro; simp [Line.isAppendEntriesRequest, hm]
  | some ev =>
  simp only [Option.bind_some]
  icases Hemsg with ⟨%gev, #Hgev, %Hem⟩
  icases typedPointsto_split _ _ _ $$ Hgev with Hgevf
  simp only [TypedPointsto.typedPointstoDef]
  iNamed Hgevf
  cases ho : raftMsgType ev.type with
  | none =>
    simp only [Option.isSome_none, Bool.not_false]
    wp_auto
    iapply HΦ'; ipureintro; simp [Line.isAppendEntriesRequest, hm, ho]
  | some ty =>
  simp only [Option.isSome_some, Bool.not_true, Option.map_some, Option.getD_some]
  wp_auto
  rw [msgTypeW_decide Hv.1 ty]
  by_cases hty : m.type = ty
  rotate_left
  · rw [decide_eq_false hty]
    wp_auto
    iapply HΦ'; ipureintro; simp [Line.isAppendEntriesRequest, hm, ho, Ne.symm hty]
  rw [decide_eq_true hty]
  subst hty
  wp_auto
  -- the subtype
  wp_apply wp_map_lookup2 $$ [Hmsubm] as -
  · iexact Hmsubm
  obtain ⟨hsome, hrel⟩ := raftMsgSubtypeMap_lookup Hem.1
  cases hs : raftMsgSubtype ev.type with
  | none =>
    rw [hs] at hsome
    have : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.raftMsgSubtypeMap !! gev.Type' = none := by
      cases h : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.raftMsgSubtypeMap !! gev.Type' <;> simp_all
    rw [this]
    wp_auto
    iapply HΦ'; ipureintro; simp [Line.isAppendEntriesRequest, hm, ho, hs]
  | some st =>
  obtain ⟨gsub, hgsub⟩ : ∃ g, github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.raftMsgSubtypeMap !! gev.Type' = some g := by
    rw [hs] at hsome; cases h : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.raftMsgSubtypeMap !! gev.Type' <;> simp_all
  have hgst := hrel gsub st hgsub hs
  rw [hgsub]
  simp only [Option.getD_some, Option.isSome_some, _root_.decide_true, Bool.not_true]
  wp_auto
  rw [decide_strRel Hv.2.1 hgst]
  by_cases hsub : m.subtype = st
  rotate_left
  · rw [decide_eq_false hsub]
    wp_auto
    iapply HΦ'; ipureintro; simp [Line.isAppendEntriesRequest, hm, ho, hs, Ne.symm hsub]
  rw [decide_eq_true hsub]
  subst hsub
  wp_auto
  rw [decide_eq_decide.2 (uint_eq_iff _ _ _ _ Hv.2.2.2.2.2.2.2.2.2.2.2.2 Hlf.2.2.2.2)]
  by_cases h1 : m.dest = x.to
  rotate_left
  · rw [decide_eq_false h1]
    wp_auto
    iapply HΦ'; ipureintro; simp [Line.isAppendEntriesRequest, hm, ho, hs, h1]
  rw [decide_eq_true h1]
  wp_auto
  rw [decide_eq_decide.2 (uint_eq_iff _ _ _ _ Hv.2.2.2.2.2.2.2.2.2.2.2.1 Hlf.2.2.2.1)]
  by_cases h2 : m.source = x.from
  rotate_left
  · rw [decide_eq_false h2]
    wp_auto
    iapply HΦ'; ipureintro; simp [Line.isAppendEntriesRequest, hm, ho, hs, h1, h2]
  rw [decide_eq_true h2]
  wp_auto
  rw [decide_eq_decide.2 (sint_eq_iff _ _ _ _ Hv.2.2.1 Hem.2.1)]
  by_cases h3 : m.term = ev.term
  rotate_left
  · rw [decide_eq_false h3]
    wp_auto
    iapply HΦ'; ipureintro; simp [Line.isAppendEntriesRequest, hm, ho, hs, h1, h2, h3]
  rw [decide_eq_true h3]
  wp_auto
  rw [decide_strRel Hv.2.1 strRel_snapshot]
  by_cases hsn : m.subtype = "snapshot"
  · rw [decide_eq_true hsn]
    wp_auto
    aereq_hb [hsn]
  rw [decide_eq_false hsn]
  wp_auto
  rw [decide_eq_decide.2 (sint_eq_iff _ _ _ _ Hv.2.2.2.2.2.2.2.2.1 Hem.2.2.2.2.2.2.2.1)]
  by_cases h4 : m.commitIndex = ev.commit
  rotate_left
  · rw [decide_eq_false h4]
    wp_auto
    iapply HΦ'; ipureintro
    simp [Line.isAppendEntriesRequest, hm, ho, hs, h1, h2, h3, hA, hsn, h4]
  rw [decide_eq_true h4]
  wp_auto
  aereq_hb [hsn, h4]

end proof

end Etcdraft
end EtcdGrove
end Perennial
