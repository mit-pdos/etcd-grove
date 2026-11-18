/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): the proof of `Msg__Equal`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Msg__Equal
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.EntriesEqual

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Etcdraft

open Iris Iris.BI Iris.ProofMode

section pure

/-- The Go's message types are distinct. -/
theorem msgTypeW_inj (s t : MsgType) (h : msgTypeW s = msgTypeW t) : s = t := by
  cases s <;> cases t <;> first | rfl | exact absurd h (by decide)

theorem sint_eq_of {x y : w64} {k : Int} (hx : sint.Z x = k) (hy : sint.Z y = k) : x = y := by
  have : sint.Z x = sint.Z y := hx.trans hy.symm
  word

theorem uint_eq_of {x y : w64} {k : Nat} (hx : uint.nat x = k) (hy : uint.nat y = k) : x = y := by
  have : uint.nat x = uint.nat y := hx.trans hy.symm
  word

/-- Two messages are equal when their fields are. -/
theorem Msg.eq_of_fields (m n : Msg) (h1 : m.type = n.type) (h2 : m.subtype = n.subtype)
    (h3 : m.term = n.term) (h4 : m.lastLogTerm = n.lastLogTerm) (h5 : m.lastLogIndex = n.lastLogIndex)
    (h6 : m.voteGranted = n.voteGranted) (h7 : m.prevLogIndex = n.prevLogIndex)
    (h8 : m.prevLogTerm = n.prevLogTerm) (h9 : m.commitIndex = n.commitIndex)
    (h10 : m.success = n.success) (h11 : m.matchIndex = n.matchIndex) (h12 : m.source = n.source)
    (h13 : m.dest = n.dest) (h14 : m.entries = n.entries) : m = n := by
  cases m; cases n; simp only at *; subst_vars; rfl

end pure

-- A field differs (`Hif`, closed by `close`): the messages differ, `Equal` returns false
-- (hygiene off: it names the proof's hypotheses).
set_option hygiene false in
local macro "msg_false " e:ident close:term : tactic => `(tactic| (
  try wp_auto
  rw [decide_eq_false (show ¬ m = n from fun h => by subst h; exact $e $close)]
  iapply HΦ; ipureintro; trivial))

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Assumptions]

theorem Msg.Equal.wp_proof (wp_EntriesEqual : EntriesEqual.spec (GF := GF) (hG := hG)) :
    Msg.Equal.spec (GF := GF) (hG := hG) := by
  intro p m q n
  wp_start as ⟨#Hm, #Hn⟩
  iunfold msgRO at Hm Hn
  icases Hm with ⟨%v, #Hp, %Hv, #Hve⟩
  icases Hn with ⟨%w, #Hq, %Hw, #Hwe⟩
  wp_auto
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13⟩ := Hv
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13⟩ := Hw
  icases typedPointsto_split _ _ _ $$ Hp with Hpf
  icases typedPointsto_split _ _ _ $$ Hq with Hqf
  simp only [TypedPointsto.typedPointstoDef]
  icases Hpf with ⟨#P1, #P2, #P3, #P4, #P5, #P6, #P7, #P8, #P9, #P10, #P11, #P12, #P13, #P14, -⟩
  icases Hqf with ⟨#Q1, #Q2, #Q3, #Q4, #Q5, #Q6, #Q7, #Q8, #Q9, #Q10, #Q11, #Q12, #Q13, #Q14, -⟩
  wp_auto
  by_cases e1 : v.Type' = w.Type'
  case neg =>
    rw [decide_eq_false e1]
    msg_false e1 (a1.trans b1.symm)
  rw [decide_eq_true e1]
  try wp_auto
  by_cases e2 : v.Subtype' = w.Subtype'
  case neg =>
    rw [decide_eq_false e2]
    msg_false e2 ((strRel_eq_iff a2 b2).2 rfl)
  rw [decide_eq_true e2]
  try wp_auto
  by_cases e3 : v.Term' = w.Term'
  case neg =>
    rw [decide_eq_false e3]
    msg_false e3 (sint_eq_of a3 b3)
  rw [decide_eq_true e3]
  try wp_auto
  by_cases e4 : v.LastLogTerm' = w.LastLogTerm'
  case neg =>
    rw [decide_eq_false e4]
    msg_false e4 (sint_eq_of a4 b4)
  rw [decide_eq_true e4]
  try wp_auto
  by_cases e5 : v.LastLogIndex' = w.LastLogIndex'
  case neg =>
    rw [decide_eq_false e5]
    msg_false e5 (sint_eq_of a5 b5)
  rw [decide_eq_true e5]
  try wp_auto
  by_cases e6 : v.VoteGranted' = w.VoteGranted'
  case neg =>
    rw [decide_eq_false e6]
    msg_false e6 (a6.trans b6.symm)
  rw [decide_eq_true e6]
  try wp_auto
  by_cases e7 : v.PrevLogIndex' = w.PrevLogIndex'
  case neg =>
    rw [decide_eq_false e7]
    msg_false e7 (sint_eq_of a7 b7)
  rw [decide_eq_true e7]
  try wp_auto
  by_cases e8 : v.PrevLogTerm' = w.PrevLogTerm'
  case neg =>
    rw [decide_eq_false e8]
    msg_false e8 (sint_eq_of a8 b8)
  rw [decide_eq_true e8]
  try wp_auto
  by_cases e9 : v.CommitIndex' = w.CommitIndex'
  case neg =>
    rw [decide_eq_false e9]
    msg_false e9 (sint_eq_of a9 b9)
  rw [decide_eq_true e9]
  try wp_auto
  by_cases e10 : v.Success' = w.Success'
  case neg =>
    rw [decide_eq_false e10]
    msg_false e10 (a10.trans b10.symm)
  rw [decide_eq_true e10]
  try wp_auto
  by_cases e11 : v.MatchIndex' = w.MatchIndex'
  case neg =>
    rw [decide_eq_false e11]
    msg_false e11 (sint_eq_of a11 b11)
  rw [decide_eq_true e11]
  try wp_auto
  by_cases e12 : v.Source' = w.Source'
  case neg =>
    rw [decide_eq_false e12]
    msg_false e12 (uint_eq_of a12 b12)
  rw [decide_eq_true e12]
  try wp_auto
  by_cases e13 : v.Dest' = w.Dest'
  case neg =>
    rw [decide_eq_false e13]
    msg_false e13 (uint_eq_of a13 b13)
  rw [decide_eq_true e13]
  try wp_auto
  wp_apply wp_EntriesEqual $$ [Hve Hwe]
  · iframe Hve Hwe
  iintro -
  try wp_auto
  have : decide (m = n) = decide (m.entries = n.entries) := by
    apply decide_eq_decide.2
    refine ⟨fun h => h ▸ rfl, fun he => Msg.eq_of_fields m n ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ he⟩
    · exact msgTypeW_inj _ _ (a1.symm.trans (e1.trans b1))
    · exact (strRel_eq_iff a2 b2).1 e2
    · rw [← a3, ← b3, e3]
    · rw [← a4, ← b4, e4]
    · rw [← a5, ← b5, e5]
    · rw [← a6, ← b6, e6]
    · rw [← a7, ← b7, e7]
    · rw [← a8, ← b8, e8]
    · rw [← a9, ← b9, e9]
    · rw [← a10, ← b10, e10]
    · rw [← a11, ← b11, e11]
    · rw [← a12, ← b12, e12]
    · rw [← a13, ← b13, e13]
  rw [this]
  iapply HΦ; ipureintro; trivial

end proof

end Etcdraft
end EtcdGrove
end Perennial
