/-
Lean-first (no Rocq counterpart). #33 S3b W4b (2026-11-23): the proof of `s.OnDisk(n, q, more, ro, ld, ll,
ch, tl, vi)` (B 290-436, `State.onDisk`), over the 33 `onDisk` methods' specs and the binding's operators.
The premise `s.onDisk … = .ok o` is taken apart in the Go's order by `OnDiskProofLaws`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__OnDisk
public import Perennial.Golang.Theory.Join
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__w
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__isApp
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__fm
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__T1
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__T0
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__elect
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__adopt
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__hasM
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__m
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__voted
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__V1
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__snaps
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__leads
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__stores
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__first
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__L0
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__f
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__k_i
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__es
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__moved
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__L1
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__conf1
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__acks
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__ackAt
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__ch1
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__adv
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__old
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__newC
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.SendableIn
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Event__vote
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Event__snap
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Event__commit
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg__term
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg__typ
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg__from
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg__index
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg__logTerm
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.factsHas
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.VoteFact
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__UpToDate
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.SnapOk
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__PrevOk
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__HasFirst
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.EntriesEqual
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.SubSeq
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.At
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.IsReq
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__clone
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.setInt
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.setStr
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.setLog
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.setConfirmed
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.factsAdd
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.State__VoteRequest
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.AckFact
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.votesAdd
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.factsMinus
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.votesMinus
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.setPre
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Min
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Concat
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.factsUnion
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.votesUnion
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Lowest
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.TermInts__With
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Max
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.violAdd
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Comparable
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.IsPrefix
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Matching
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.StateLaws
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.EvalLaws
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.OnDiskLaws
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.OnDiskLaws2
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Within.Parts
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.OnDiskProofLaws

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntCheck

open Iris Iris.BI Iris.ProofMode OnDiskLaws2

section proof
set_option linter.unusedSimpArgs false
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

/-- `x.<m>()` on the `*onDisk` variable: unfold the pointer method to the value one. -/
macro "odm" m:ident : tactic => do
  let base := Lean.Name.mkStr `github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions
    ("ptr_unfold'" ++ m.getId.toString)
  let n := Lean.Name.mkStr base "method_unfold"
  `(tactic| (rw [$(Lean.mkIdent n):ident]; try wp_auto))

/-- A method on a `*State`/`*Event`/... pointer receiver: `smu State VoteRequest`. -/
macro "smu" t:ident m:ident : tactic => do
  let base := Lean.Name.mkStr (Lean.Name.mkStr `github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check t.getId.toString)
    "TypeAssumptions"
  let base := Lean.Name.mkStr base ("ptr_unfold'" ++ m.getId.toString)
  let n := Lean.Name.mkStr base "method_unfold"
  `(tactic| (rw [$(Lean.mkIdent n):ident]; try wp_auto))

set_option hygiene false in
/-- The Go returns `nil, false` (the Lean's `none`). -/
macro "odret" : tactic => `(tactic| (try wp_auto; iapply HΦ; iunfold succOwn; ipureintro; rfl))

set_option hygiene false in
/-- A guard `if c { return nil, false }`: join after it, at its Lean value `c` (the Go returns, or
falls through; `nil, false` are the result variables' zero values, so they are the join's frame). -/
macro "odguard " c:term:max : tactic => do
  let r0p := Lean.mkIdent (Lean.Name.mkSimple "$res0_ptr")
  let r1p := Lean.mkIdent (Lean.Name.mkSimple "$res1_ptr")
  let r0 := Lean.mkIdent (Lean.Name.mkSimple "$res0")
  let r1 := Lean.mkIdent (Lean.Name.mkSimple "$res1")
  `(tactic| (wp_join (Q := fun v => iprop(
    ⌜($c = true ∧ v = returnVal #()) ∨ ($c = false ∧ v = executeVal)⌝ ∗
      $r0p ↦ zero_val Loc ∗ $r1p ↦ zero_val Bool)) at next with [$r0 $r1]))

/-- In a guard's case: the Go falls through (`odskip`) or returns (`odretc`); leaves the Lean
condition's value (`c = false`, `c = true`). -/
macro "odskip " h:term:max : tactic => `(tactic| (
  try wp_auto
  iframe
  ipureintro
  first | (right; exact ⟨$h, rfl⟩) | simp))
macro "odretc " h:term:max : tactic => `(tactic| (
  try wp_auto
  iframe
  ipureintro
  first | (left; exact ⟨$h, rfl⟩) | simp))

set_option hygiene false in
/-- After a guard: the join's facts; where the Go returned, so does the proof (`o = none`). -/
macro "odafter " c:ident : tactic => do
  let r0 := Lean.mkIdent (Lean.Name.mkSimple "$res0")
  let r1 := Lean.mkIdent (Lean.Name.mkSimple "$res1")
  `(tactic| (
    iintro ⟨%Hv, $r0:ident, $r1:ident⟩
    cases $c:ident
    rotate_left
    simp only [Bool.true_eq_false, _root_.false_and, _root_.or_false, _root_.true_and] at Hv
    subst Hv
    simp only [ite_true, pure_ok, Except.ok.injEq] at Ho
    subst Ho
    odret
    simp only [Bool.false_eq_true, _root_.false_and, _root_.false_or, _root_.true_and] at Hv
    subst Hv
    simp only [Bool.false_eq_true, ite_false] at Ho
    try wp_auto))

set_option hygiene false in
/-- A section `if … { … return nil, false … }` of the Lean's continuation `K`: join after it (the
Go returned, and the Lean's result is `none`; or it fell through, and the Lean continues with `K`). -/
macro "odjoin " K:term:max : tactic => do
  let r0p := Lean.mkIdent (Lean.Name.mkSimple "$res0_ptr")
  let r1p := Lean.mkIdent (Lean.Name.mkSimple "$res1_ptr")
  let r0 := Lean.mkIdent (Lean.Name.mkSimple "$res0")
  let r1 := Lean.mkIdent (Lean.Name.mkSimple "$res1")
  `(tactic| (wp_join (Q := fun v => iprop(
    ⌜(o = none ∧ v = returnVal #()) ∨ ($K = .ok o ∧ v = executeVal)⌝ ∗
      $r0p ↦ zero_val Loc ∗ $r1p ↦ zero_val Bool)) at next with [$r0 $r1]))

macro "odjskip " h:term:max : tactic => `(tactic| (
  try wp_auto
  iframe
  ipureintro
  exact Or.inr ⟨$h, rfl⟩))
macro "odjret " h:term:max : tactic => `(tactic| (
  try wp_auto
  iframe
  ipureintro
  exact Or.inl ⟨$h, rfl⟩))

set_option hygiene false in
/-- In a section's case: the guard's condition `ok` is false (`h : ok = false`), the Go returns. -/
macro "odjno " h:term:max : tactic => `(tactic| (
  rw [$h:term] at Ho
  simp only [Bool.not_false, ite_true, pure_ok, Except.ok.injEq] at Ho
  odjret (by subst Ho; rfl)))

set_option hygiene false in
/-- `odafter` inside a section's case (`odjoin`): where the Go returned, the case ends (`odjret`). -/
macro "odafterj " c:ident : tactic => do
  let r0 := Lean.mkIdent (Lean.Name.mkSimple "$res0")
  let r1 := Lean.mkIdent (Lean.Name.mkSimple "$res1")
  `(tactic| (
    iintro ⟨%Hv, $r0:ident, $r1:ident⟩
    cases $c:ident
    rotate_left
    simp only [Bool.true_eq_false, _root_.false_and, _root_.or_false, _root_.true_and] at Hv
    subst Hv
    simp only [ite_true, pure_ok, Except.ok.injEq] at Ho
    odjret (by subst Ho; rfl)
    simp only [Bool.false_eq_true, _root_.false_and, _root_.false_or, _root_.true_and] at Hv
    subst Hv
    simp only [Bool.false_eq_true, ite_false] at Ho
    try wp_auto))

set_option hygiene false in
/-- g5's guard A after `app || snap` held (`hor : or1 = true`): `x.m().term() == x.T1()`. -/
macro "odAterm " hor:term:max : tactic => `(tactic| (
  have hA3 := hA2t $hor
  obtain ⟨m', hm', hA3⟩ := bind_ok hA3
  rw [hm] at hm'; cases hm'
  obtain ⟨mt, hmt, hA3⟩ := bind_ok hA3
  obtain ⟨t1', ht1', hA3⟩ := bind_ok hA3
  rw [ht1] at ht1'; cases ht1'
  simp only [pure_ok, Except.ok.injEq] at hA3
  subst hA3
  try wp_auto
  odm m
  wp_apply wp_m _ X m $$ [Hx] as %gmA #HmA
  · iframe Hx; ipureintro; exact hm
  try wp_auto
  wp_apply wp_Msg_term gmA m mt $$ [HmA] as %ut %Hut
  · iframe HmA; ipureintro; exact hmt
  try wp_auto
  odm T1
  wp_apply wp_T1 _ X t1 $$ [Hx] as %u1 %Hu1
  · iframe Hx; ipureintro; exact ht1
  try wp_auto
  rw [decide_w64_eq, Hut, Hu1]
  by_cases hmt1 : mt = t1
  · rw [decide_eq_true hmt1]
    odskip (by rw [← hcA, hmt1]; simp)
  · rw [decide_eq_false hmt1]
    odretc (by rw [← hcA]; simpa using hmt1)))

set_option hygiene false in
/-- g6's last guard (`app || snap` held, `hor`): `!(s.PrevOk(n, x.f()) && (x.stores() || s.HasFirst(n, x.f(), len(x.f().Entries))))`. -/
macro "odM5body" : tactic => `(tactic| (
  obtain ⟨ok5, hok5, Ho⟩ := bind_ok Ho
  obtain ⟨pv, hpv, h6t, h6f⟩ := andM_ok hok5
  obtain ⟨f', hf', hpv⟩ := bind_ok hpv
  rw [hf] at hf'; cases hf'
  try wp_auto
  odm f
  wp_apply wp_f _ X f $$ [Hx] as %gf5 #Hf5
  · iframe Hx; ipureintro; exact hf
  try wp_auto
  wp_apply wp_SPrevOk p s n gf5 f pv $$ [Hs Hf5]
  · iframe Hs Hf5; ipureintro; exact ⟨Hn, Hlt, hpv⟩
  cases pv
  · odjno (h6f rfl)
  have h6 := h6t rfl
  obtain ⟨st5, hst5, h7t, h7f⟩ := orM_ok h6
  try wp_auto
  odm stores
  wp_apply wp_stores _ X st5 $$ [Hx]
  · iframe Hx; ipureintro; exact hst5
  cases st5
  case true =>
    simp only [h7t rfl, Bool.not_true, Bool.false_eq_true, ite_false] at Ho
    odjskip Ho
  have h7 := h7f rfl
  obtain ⟨f', hf', h7⟩ := bind_ok h7
  rw [hf] at hf'; cases hf'
  try wp_auto
  odm f
  wp_apply wp_f _ X f $$ [Hx] as %gf6 #Hf6
  · iframe Hx; ipureintro; exact hf
  try wp_auto
  odm f
  wp_apply wp_f _ X f $$ [Hx] as %gf7 #Hf7
  · iframe Hx; ipureintro; exact hf
  try wp_auto
  iunfold appendFactRO at Hf7
  icases Hf7 with ⟨%-, #Hfes7⟩
  ihave %Hl7 := logRO_len _ _ $$ Hfes7
  wp_apply wp_SHasFirst p s n gf6 f gf7.Entries'.len ok5 $$ [Hs Hf6]
  · iframe Hs Hf6; ipureintro
    refine ⟨Hn, Hlt, by rw [Hl7]; exact h7, hpli, ?_⟩
    rw [Hl7]; unfold numOk numBound; unfold numBound at hb; omega
  cases ok5
  · odjno (rfl : false = false)
  simp only [Bool.not_true, Bool.false_eq_true, ite_false] at Ho
  odjskip Ho))

set_option hygiene false in
macro "odjafter" : tactic => do
  let r0 := Lean.mkIdent (Lean.Name.mkSimple "$res0")
  let r1 := Lean.mkIdent (Lean.Name.mkSimple "$res1")
  `(tactic| (
    iintro ⟨%Hv, $r0:ident, $r1:ident⟩
    clear Ho
    rcases Hv with ⟨rfl, rfl⟩ | ⟨Ho, rfl⟩
    · odret
    try wp_auto))

set_option hygiene false in
/-- v4's second conjunct, where the first held (`hoc1 : oc = true`):
`!IsPrefix(SubSeq(x.ch1(), 1, w.commit()), l1)`, then the violation or not, and the join. -/
macro "odv4tail" : tactic => `(tactic| (
  have h2 := hoct hoc1
  unfold notM at h2
  obtain ⟨ip, hip, h2⟩ := bind_ok h2
  simp only [pure_ok, Except.ok.injEq] at h2
  obtain ⟨c1', hc1', hip⟩ := bind_ok hip
  obtain ⟨cm', hcm', hip⟩ := bind_ok hip
  obtain ⟨ss, hss, hip⟩ := bind_ok hip
  try wp_auto
  odm ch1
  wp_apply wp_ch1 _ X c1' $$ [Hx] as %gc1' #Hc1'
  · iframe Hx; ipureintro; exact hc1'
  try wp_auto
  wp_apply wp_Event_commit pw X.w cm' $$ [Hw] as %uc' %Huc'
  · iframe Hw; ipureintro; exact hcm'
  try wp_auto
  wp_apply wp_SubSeq gc1' c1' (W64 1) uc' ss $$ [Hc1'] as %gss #Hss
  · iframe Hc1'; ipureintro; rw [Huc', sint_one]; exact hss
  try wp_auto
  wp_apply wp_IsPrefix gss ss gl1 l1v ip $$ [Hss Hgl1]
  · iframe Hss Hgl1; ipureintro; exact hip
  subst h2
  cases ip
  · try wp_auto
    wp_apply wp_violAdd vl3 _ _ $$ [Hvl3] as %vl #Hvl
    · iframe Hvl3; ipureintro; omega
    try wp_auto
    wp_join_done
    simp only [Bool.not_false, ite_true]
    iexists _; iframe; iexact Hvl
  · try wp_auto
    wp_join_done
    simp only [Bool.not_true, Bool.false_eq_true, ite_false]
    iexists _; iframe; iexact Hvl3))

set_option maxHeartbeats 0 in
theorem State.OnDisk.wp_proof
    (wp_w : onDisk.w.spec (GF := GF) (hG := hG))
    (wp_isApp : onDisk.isApp.spec (GF := GF) (hG := hG))
    (wp_fm : onDisk.fm.spec (GF := GF) (hG := hG))
    (wp_T1 : onDisk.T1.spec (GF := GF) (hG := hG))
    (wp_T0 : onDisk.T0.spec (GF := GF) (hG := hG))
    (wp_elect : onDisk.elect.spec (GF := GF) (hG := hG))
    (wp_adopt : onDisk.adopt.spec (GF := GF) (hG := hG))
    (wp_hasM : onDisk.hasM.spec (GF := GF) (hG := hG))
    (wp_m : onDisk.m.spec (GF := GF) (hG := hG))
    (wp_voted : onDisk.voted.spec (GF := GF) (hG := hG))
    (wp_V1 : onDisk.V1.spec (GF := GF) (hG := hG))
    (wp_snaps : onDisk.snaps.spec (GF := GF) (hG := hG))
    (wp_leads : onDisk.leads.spec (GF := GF) (hG := hG))
    (wp_stores : onDisk.stores.spec (GF := GF) (hG := hG))
    (wp_first : onDisk.first.spec (GF := GF) (hG := hG))
    (wp_L0 : onDisk.L0.spec (GF := GF) (hG := hG))
    (wp_f : onDisk.f.spec (GF := GF) (hG := hG))
    (wp_k : onDisk.k.spec (GF := GF) (hG := hG))
    (wp_es : onDisk.es.spec (GF := GF) (hG := hG))
    (wp_moved : onDisk.moved.spec (GF := GF) (hG := hG))
    (wp_L1 : onDisk.L1.spec (GF := GF) (hG := hG))
    (wp_conf1 : onDisk.conf1.spec (GF := GF) (hG := hG))
    (wp_acks : onDisk.acks.spec (GF := GF) (hG := hG))
    (wp_ackAt : onDisk.ackAt.spec (GF := GF) (hG := hG))
    (wp_ch1 : onDisk.ch1.spec (GF := GF) (hG := hG))
    (wp_adv : onDisk.adv.spec (GF := GF) (hG := hG))
    (wp_old : onDisk.old.spec (GF := GF) (hG := hG))
    (wp_newC : onDisk.newC.spec (GF := GF) (hG := hG))
    (wp_SendableIn : SendableIn.spec (GF := GF) (hG := hG))
    (wp_Event_vote : Event.vote.spec (GF := GF) (hG := hG))
    (wp_Event_snap : Event.snap.spec (GF := GF) (hG := hG))
    (wp_Event_commit : Event.commit.spec (GF := GF) (hG := hG))
    (wp_Msg_term : Msg.term.spec (GF := GF) (hG := hG))
    (wp_Msg_typ : Msg.typ.spec (GF := GF) (hG := hG))
    (wp_Msg_from : Msg.from.spec (GF := GF) (hG := hG))
    (wp_Msg_index : Msg.index.spec (GF := GF) (hG := hG))
    (wp_Msg_logTerm : Msg.logTerm.spec (GF := GF) (hG := hG))
    (wp_factsHas : factsHas.spec (GF := GF) (hG := hG))
    (wp_VoteFact : VoteFact.spec (GF := GF) (hG := hG))
    (wp_SUpToDate : State.UpToDate.spec (GF := GF) (hG := hG))
    (wp_SnapOk : SnapOk.spec (GF := GF) (hG := hG))
    (wp_SPrevOk : State.PrevOk.spec (GF := GF) (hG := hG))
    (wp_SHasFirst : State.HasFirst.spec (GF := GF) (hG := hG))
    (wp_EntriesEqual : EntriesEqual.spec (GF := GF) (hG := hG))
    (wp_SubSeq : SubSeq.spec (GF := GF) (hG := hG))
    (wp_At : At.spec (GF := GF) (hG := hG))
    (wp_IsReq : IsReq.spec (GF := GF) (hG := hG))
    (wp_Sclone : State.clone.spec (GF := GF) (hG := hG))
    (wp_setInt : setInt.spec (GF := GF) (hG := hG))
    (wp_setStr : setStr.spec (GF := GF) (hG := hG))
    (wp_setLog : setLog.spec (GF := GF) (hG := hG))
    (wp_setConfirmed : setConfirmed.spec (GF := GF) (hG := hG))
    (wp_factsAdd : factsAdd.spec (GF := GF) (hG := hG))
    (wp_SVoteRequest : State.VoteRequest.spec (GF := GF) (hG := hG))
    (wp_AckFact : AckFact.spec (GF := GF) (hG := hG))
    (wp_votesAdd : votesAdd.spec (GF := GF) (hG := hG))
    (wp_factsMinus : factsMinus.spec (GF := GF) (hG := hG))
    (wp_votesMinus : votesMinus.spec (GF := GF) (hG := hG))
    (wp_setPre : setPre.spec (GF := GF) (hG := hG))
    (wp_Min : Min.spec (GF := GF) (hG := hG))
    (wp_Concat : Concat.spec (GF := GF) (hG := hG))
    (wp_factsUnion : factsUnion.spec (GF := GF) (hG := hG))
    (wp_votesUnion : votesUnion.spec (GF := GF) (hG := hG))
    (wp_Lowest : Lowest.spec (GF := GF) (hG := hG))
    (wp_TermInts_With : TermInts.With.spec (GF := GF) (hG := hG))
    (wp_Max : Max.spec (GF := GF) (hG := hG))
    (wp_violAdd : violAdd.spec (GF := GF) (hG := hG))
    (wp_Comparable : Comparable.spec (GF := GF) (hG := hG))
    (wp_IsPrefix : IsPrefix.spec (GF := GF) (hG := hG))
    (wp_Matching : Matching.spec (GF := GF) (hG := hG)) :
    State.OnDisk.spec (GF := GF) (hG := hG) := by
  intro p s n gq q more rol ro ldl ld lll ll chl ch tll tl vil vi o
  wp_start as ⟨#Hs, #Hq, #Hro, #Hld, #Hll, #Hch, #Htl, #Hvi, %Hpre⟩
  obtain ⟨Hn, Hlt, Hrol, HB, Ho⟩ := Hpre
  ihave #Hs' := Hs
  iunfold stateRO at Hs'
  iNamed Hs'
  iNamed Hf
  iStructNamed Hp
  obtain ⟨X, hX⟩ : ∃ X : OnDisk, X = { s, n := sint.nat n, q, more, ro, ld, ll, ch, tl, vi } := ⟨_, rfl⟩
  rw [← hX] at HB
  have Hnn : (sint.nat n : Int) = sint.Z n := sint_nat_cast Hn
  have HnL : sint.nat n < s.cfg.server.length := by omega
  ihave #Hx : onDiskRO (GF := GF) { s' := p, n' := n, q' := gq, more' := more, ro' := rol, ld' := ldl, ll' := lll, ch' := chl, tl' := tll, vi' := vil } X $$ []
  · subst hX; iunfold onDiskRO; dsimp only; iframe Hs Hq Hro Hld Hll Hch Htl Hvi; ipureintro; exact ⟨Hnn.symm, HnL, rfl, Hrol, HB⟩
  rw [onDisk_eq] at Ho
  dsimp only at Ho
  rw [← hX] at Ho
  have Ho0 := Ho
  wp_auto
  odm w
  wp_apply wp_w _ X $$ [Hx] as %pw #Hw
  · iexact Hx
  try wp_auto
  -- the read-only locals, persistent
  ipersist s; ipersist vi; ipersist tl; ipersist ch; ipersist ll; ipersist ld; ipersist ro
  ipersist more; ipersist n; ipersist x; ipersist w
  have hXs : X.s = s := by rw [hX]
  have hXn : X.n = sint.nat n := by rw [hX]
  have hXmore : X.more = more := by rw [hX]
  have hXld : X.ld = ld := by rw [hX]
  have hXll : X.ll = ll := by rw [hX]
  have hXch : X.ch = ch := by rw [hX]
  have hXtl : X.tl = tl := by rw [hX]
  have hXro : X.ro = ro := by rw [hX]
  have hXvi : X.vi = vi := by rw [hX]
  -- `me := s.Cfg.Server[n]`
  iunfold configRO at HCfg
  icases HCfg with ⟨%gc, #Hgc, #Hsrv, #-, %-⟩
  iStructNamed Hgc
  ihave #Hme := strsRO_at gc.Server' s.cfg.server n ⟨Hn, Hlt⟩ $$ Hsrv
  try wp_auto
  wp_apply wp_load_at _ _ _ Hn $$ [Hme] as -
  · iexact Hme
  try wp_auto
  ipersist me
  -- `more && s.Undo[n] == nil`
  unfold g1 at Ho
  dsimp only at Ho
  rw [hXmore, hXs, hXn] at Ho
  icases undoRO_at g.Undo' s.undo n ⟨Hn, by rw [HWf.len_undo]; exact Hlt⟩ $$ HUndo with ⟨%uu0, #Hua, #Hu⟩
  cases hcu : (more && s.undo[sint.nat n]!.isNone)
  case true =>
    simp only [hcu, ite_true, pure_ok, Except.ok.injEq] at Ho
    subst Ho
    simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hcu
    obtain ⟨rfl, hu⟩ := hcu
    rw [hu]
    iunfold preRO at Hu
    icases Hu with %Hnull
    subst Hnull
    try wp_auto
    wp_apply wp_load_at _ _ _ Hn $$ [Hua] as -
    · iexact Hua
    odret
  simp only [hcu, Bool.false_eq_true, ite_false] at Ho
  wp_join at next with [«$res0» «$res1»]
  · cases more
    · try wp_auto
      wp_join_done
    · have hu : ∃ pu, s.undo[sint.nat n]! = some pu := by
        cases h : s.undo[sint.nat n]! with
        | none => rw [h] at hcu; simp at hcu
        | some pu => exact ⟨pu, rfl⟩
      obtain ⟨pu, hu⟩ := hu
      rw [hu]
      iunfold preRO at Hu
      icases Hu with ⟨%gp, #Hgp, #-⟩
      ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hgp
      try wp_auto
      wp_apply wp_load_at _ _ _ Hn $$ [Hua] as -
      · iexact Hua
      rw [decide_eq_false Hnn]
      try wp_auto
      wp_join_done
  -- `x.isApp() && !SendableIn(ld, ll, ch, tl, x.fm())`
  obtain ⟨b, E, hb, HW⟩ := HB.get
  have hb' := hb; unfold numBound at hb'
  obtain ⟨c, hc, Ho⟩ := bind_ok Ho
  obtain ⟨ia, hia, hiat, hiaf⟩ := andM_ok hc
  odguard c
  · odm isApp
    wp_apply wp_isApp _ X ia $$ [Hx]
    · iframe Hx; ipureintro; exact hia
    cases ia
    · odskip (hiaf rfl)
    have h2 := hiat rfl
    unfold notM at h2
    obtain ⟨sd, hsd, h2⟩ := bind_ok h2
    simp only [pure_ok, Except.ok.injEq] at h2
    obtain ⟨fm, hfm, hsd⟩ := bind_ok hsd
    obtain ⟨hpli, hfl, -, -, -⟩ := OnDisk.fm_within HW hfm
    try wp_auto
    odm fm
    wp_apply wp_fm _ X fm $$ [Hx] as %gfm #Hfm
    · iframe Hx; ipureintro; exact hfm
    try wp_auto
    wp_apply wp_SendableIn ldl ld lll ll chl ch tll tl gfm fm sd $$ [Hld Hll Hch Htl Hfm]
    · iframe Hld Hll Hch Htl Hfm; ipureintro
      refine ⟨by rw [← hXld, ← hXll, ← hXch, ← hXtl]; exact hsd, numOk_bigOk hpli, by omega⟩
    subst h2
    cases sd
    · odretc rfl
    · odskip rfl
  odafter c
  -- `!(x.T1() >= x.T0())`
  have hT0b : bigOk X.T0 := getElem!_bigOk HW.1.currentTerm
  obtain ⟨t1, ht1, Ho⟩ := bind_ok Ho
  have ht1b : bigOk t1 := T1_bigOk HW ht1
  odm T1
  wp_apply wp_T1 _ X t1 $$ [Hx] as %u1 %Hu1
  · iframe Hx; ipureintro; exact ht1
  try wp_auto
  odm T0
  wp_apply wp_T0 _ X $$ [Hx] as %u0 %Hu0
  · iexact Hx
  try wp_auto
  rw [Hu0, Hu1]
  by_cases hge : X.T0 ≤ t1
  case neg =>
    rw [decide_eq_false hge]
    simp only [ge_iff_le, decide_eq_false hge, Bool.not_false, ite_true, pure_ok, Except.ok.injEq] at Ho
    subst Ho
    odret
  rw [decide_eq_true hge]
  simp only [ge_iff_le, decide_eq_true hge, Bool.not_true, Bool.false_eq_true, ite_false] at Ho
  try wp_auto
  -- `x.T1() != x.T0() && ro[n] == Leader`
  obtain ⟨t1', ht1', Ho⟩ := bind_ok Ho
  rw [ht1] at ht1'; cases ht1'
  generalize hc : (t1 != X.T0 && X.ro[sint.nat n]! == leader) = c at Ho
  ihave #Hron := strsRO_at rol ro n ⟨Hn, by rw [Hrol]; exact Hlt⟩ $$ Hro
  odguard c
  · odm T1
    wp_apply wp_T1 _ X t1 $$ [Hx] as %u1 %Hu1
    · iframe Hx; ipureintro; exact ht1
    try wp_auto
    odm T0
    wp_apply wp_T0 _ X $$ [Hx] as %u0 %Hu0
    · iexact Hx
    try wp_auto
    rw [decide_w64_eq, Hu0, Hu1]
    by_cases he : t1 = X.T0
    · rw [decide_eq_true he]
      try wp_auto
      odskip (by rw [← hc, he]; simp only [bne_self_eq_false, Bool.false_and])
    rw [decide_eq_false he]
    try wp_auto
    wp_apply wp_load_at _ _ _ Hn $$ [Hron] as -
    · iexact Hron
    try wp_auto
    by_cases hl : ro[sint.nat n]! = leader
    · rw [show decide (ro[sint.nat n]! = [108#8, 101#8, 97#8, 100#8, 101#8, 114#8]) = true from decide_eq_true hl]
      odretc (by rw [← hc, hXro, hl]; simp only [show (t1 != X.T0) = true by simpa using he, beq_self_eq_true, Bool.and_self])
    · rw [show decide (ro[sint.nat n]! = [108#8, 101#8, 97#8, 100#8, 101#8, 114#8]) = false from decide_eq_false hl]
      odskip (by rw [← hc, hXro]; simp only [show (t1 != X.T0) = true by simpa using he,
        show (ro[sint.nat n]! == leader) = false by simpa using hl, Bool.and_false])
  odafter c
  -- `x.elect() && !(x.T1() == x.T0()+1 && w.vote() == me)`
  obtain ⟨c, hc, Ho⟩ := bind_ok Ho
  obtain ⟨el, hel, helt, helf⟩ := andM_ok hc
  odguard c
  · odm elect
    wp_apply wp_elect _ X el $$ [Hx]
    · iframe Hx; ipureintro; exact hel
    cases el
    · odskip (helf rfl)
    have h2 := helt rfl
    unfold notM at h2
    obtain ⟨a2, ha2, h2⟩ := bind_ok h2
    simp only [pure_ok, Except.ok.injEq] at h2
    subst h2
    obtain ⟨e1, he1, he1t, he1f⟩ := andM_ok ha2
    obtain ⟨t1', ht1', he1⟩ := bind_ok he1
    rw [ht1] at ht1'; cases ht1'
    simp only [pure_ok, Except.ok.injEq] at he1
    subst he1
    try wp_auto
    odm T1
    wp_apply wp_T1 _ X t1 $$ [Hx] as %u1 %Hu1
    · iframe Hx; ipureintro; exact ht1
    try wp_auto
    odm T0
    wp_apply wp_T0 _ X $$ [Hx] as %u0 %Hu0
    · iexact Hx
    try wp_auto
    have hadd : sint.Z (u0 + W64 1) = X.T0 + 1 := by
      rw [sint_add_one (by unfold bigOk at hT0b; omega), Hu0]
    rw [decide_w64_eq, hadd, Hu1]
    by_cases he : t1 = X.T0 + 1
    case neg =>
      rw [decide_eq_false he]
      have : (t1 == X.T0 + 1) = false := by simpa using he
      rw [this] at he1f
      rw [he1f rfl]
      odretc rfl
    rw [decide_eq_true he]
    have : (t1 == X.T0 + 1) = true := by simpa using he
    rw [this] at he1t
    have hv := he1t rfl
    obtain ⟨vt, hvt, hvr⟩ := fieldEq_ok hv
    try wp_auto
    wp_apply wp_Event_vote pw X.w vt $$ [Hw]
    · iframe Hw; ipureintro; exact hvt
    try wp_auto
    subst hvr
    by_cases hvm : vt = s.cfg.server[sint.nat n]!
    · rw [decide_eq_true hvm]
      odskip (by simp [hvm])
    · rw [decide_eq_false hvm]
      odretc (by simpa using hvm)
  odafter c
  -- g2: `if x.adopt() { … }`
  clear hc hel helt helf
  unfold g2 at Ho
  dsimp only at Ho
  rw [hXs, hXn] at Ho
  obtain ⟨ad, had, Ho⟩ := bind_ok Ho
  generalize hK : g3 X (g4 X (g5 X (g6 X (succ X)))) = K at Ho
  odjoin K
  · odm adopt
    wp_apply wp_adopt _ X ad $$ [Hx]
    · iframe Hx; ipureintro; exact had
    cases ad
    · simp only [Bool.false_eq_true, ite_false] at Ho
      odjskip Ho
    simp only [ite_true] at Ho
    obtain ⟨c1, hc1, Ho⟩ := bind_ok Ho
    obtain ⟨hm, hhm, hmt, hmf⟩ := andM_ok hc1
    simp only [pure_ok, Except.ok.injEq] at hhm
    try wp_auto
    odm hasM
    wp_apply wp_hasM _ X $$ [Hx]
    · iexact Hx
    rw [hhm]
    cases hm
    · rw [hmf rfl] at Ho
      simp only [Bool.not_false, ite_true, pure_ok, Except.ok.injEq] at Ho
      odjret (by subst Ho; rfl)
    have h1 := hmt rfl
    obtain ⟨m, hm, h1⟩ := bind_ok h1
    obtain ⟨mt, hmt', h1⟩ := bind_ok h1
    obtain ⟨t1', ht1', h1⟩ := bind_ok h1
    rw [ht1] at ht1'; cases ht1'
    simp only [pure_ok, Except.ok.injEq] at h1
    subst h1
    try wp_auto
    odm m
    wp_apply wp_m _ X m $$ [Hx] as %gm #Hm
    · iframe Hx; ipureintro; exact hm
    try wp_auto
    wp_apply wp_Msg_term gm m mt $$ [Hm] as %ut %Hut
    · iframe Hm; ipureintro; exact hmt'
    try wp_auto
    odm T1
    wp_apply wp_T1 _ X t1 $$ [Hx] as %u1 %Hu1
    · iframe Hx; ipureintro; exact ht1
    try wp_auto
    rw [decide_w64_eq, Hut, Hu1]
    by_cases hmt1 : mt = t1
    case neg =>
      rw [decide_eq_false hmt1]
      simp only [show (mt == t1) = false by simpa using hmt1, Bool.not_false, ite_true, pure_ok,
        Except.ok.injEq] at Ho
      odjret (by subst Ho; rfl)
    rw [decide_eq_true hmt1]
    simp only [hmt1, beq_self_eq_true, Bool.not_true, Bool.false_eq_true, ite_false] at Ho
    obtain ⟨t1', ht1', Ho⟩ := bind_ok Ho
    rw [ht1] at ht1'; cases ht1'
    try wp_auto
    -- `for j := range s.Cfg.Server { if j != n && s.CurrentTerm[j] >= x.T1() { found = true; break } }`
    ihave #Hsrv2 := Hsrv
    iunfold strsRO at Hsrv2
    ihave %Hsl := ownSlice_len $$ Hsrv2
    ihave IH : iprop(∃ (i jv : w64),
        "i" ∷ i_ptr ↦ i ∗ "j" ∷ j_ptr ↦ jv ∗ "found" ∷ found_ptr ↦ false ∗
        "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z gc.Server'.len ∧
          ∀ j, j < sint.nat i → ¬(j ≠ sint.nat n ∧ t1 ≤ s.currentTerm[j]!)⌝) $$ [i j found]
    · iexists _, _
      iframe
      ipureintro
      refine ⟨by word, by word, fun j hj => absurd hj (by simp)⟩
    wp_for IH
    obtain ⟨hi0, hi1, hall⟩ := Hi
    wp_if_destruct
    · have Hil : sint.nat i < s.cfg.server.length := by rw [Hsl.1]; word
      obtain ⟨sv, Hsv⟩ : ∃ sv, s.cfg.server[sint.nat i]? = some sv := ⟨_, List.getElem?_eq_getElem Hil⟩
      rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z i ∧ sint.Z i < sint.Z gc.Server'.len from ⟨hi0, Hif⟩))]
      wp_apply wp_load_slice_index gc.Server' (sint.Z i) s.cfg.server DFrac.discard sv hi0 $$ [Hsrv2] as -
      · isplitr
        · iexact Hsrv2
        ipureintro; exact Hsv
      try wp_auto
      have hstep : ∀ j, j < sint.nat (i + W64 1) → j ≠ sint.nat i → ¬(j ≠ sint.nat n ∧ t1 ≤ s.currentTerm[j]!) := by
        intro j hj hji
        rw [show sint.nat (i + W64 1) = sint.nat i + 1 by word] at hj
        exact hall j (by omega)
      by_cases hin : i = n
      · rw [decide_eq_true hin]
        try wp_auto
        wp_for_post
        iframe
        iexists _, _
        iframe
        ipureintro
        refine ⟨by word, by word, fun j hj => ?_⟩
        by_cases hji : j = sint.nat i
        · subst hji hin; exact fun h => h.1 rfl
        · exact hstep j hj hji
      rw [decide_eq_false hin]
      try wp_auto
      icases intsRO_at g.CurrentTerm' s.currentTerm i ⟨hi0, by rw [HWf.len_currentTerm]; word⟩ $$ HCurrentTerm
        with ⟨%ct, #Hcta, %Hct⟩
      wp_apply wp_load_at _ _ ct hi0 $$ [Hcta]
      · iexact Hcta
      try wp_auto
      odm T1
      wp_apply wp_T1 _ X t1 $$ [Hx] as %u1 %Hu1
      · iframe Hx; ipureintro; exact ht1
      try wp_auto
      rw [Hu1, Hct]
      by_cases hge2 : t1 ≤ s.currentTerm[sint.nat i]!
      · rw [decide_eq_true hge2]
        try wp_auto
        wp_for_post
        have hin' : sint.nat i ≠ sint.nat n := fun h => hin (by word)
        have hany : (List.range s.cfg.server.length).any
            (fun j => j != sint.nat n && decide (s.currentTerm[j]! ≥ t1)) = true := by
          rw [List.any_eq_true]
          refine ⟨sint.nat i, List.mem_range.2 Hil, ?_⟩
          simp only [ge_iff_le, decide_eq_true hge2, Bool.and_true]
          simpa using hin'
        simp only [hany, Bool.not_true, Bool.false_eq_true, ite_false] at Ho
        odjskip Ho
      rw [decide_eq_false hge2]
      try wp_auto
      wp_for_post
      iframe
      iexists _, _
      iframe
      ipureintro
      refine ⟨by word, by word, fun j hj => ?_⟩
      by_cases hji : j = sint.nat i
      · subst hji; exact fun h => hge2 h.2
      · exact hstep j hj hji
    · try wp_auto
      have hil : sint.nat i = s.cfg.server.length := by rw [Hsl.1]; word
      have hany : (List.range s.cfg.server.length).any
          (fun j => j != sint.nat n && decide (s.currentTerm[j]! ≥ t1)) = false := by
        rw [List.any_eq_false]
        intro j hj
        have := hall j (by rw [hil]; exact List.mem_range.1 hj)
        simpa using this
      simp only [hany, Bool.not_false, ite_true, pure_ok, Except.ok.injEq] at Ho
      iframe; ipureintro; left; exact ⟨by subst Ho; rfl, trivial⟩
  odjafter
  subst hK
  -- g3: `if x.voted() { … }`
  unfold g3 at Ho
  dsimp only at Ho
  rw [hXs, hXn] at Ho
  obtain ⟨vd, hvd, Ho⟩ := bind_ok Ho
  generalize hK : g4 X (g5 X (g6 X (succ X))) = K at Ho
  odjoin K
  · odm voted
    wp_apply wp_voted _ X vd $$ [Hx]
    · iframe Hx; ipureintro; exact hvd
    cases vd
    · simp only [Bool.false_eq_true, ite_false] at Ho
      odjskip Ho
    simp only [ite_true] at Ho
    obtain ⟨v1, hv1, Ho⟩ := bind_ok Ho
    try wp_auto
    odm V1
    wp_apply wp_V1 _ X v1 $$ [Hx]
    · iframe Hx; ipureintro; exact hv1
    by_cases hv1e : v1 = []
    case neg =>
      simp only [show (v1 != []) = true by simpa using hv1e, ite_true, pure_ok, Except.ok.injEq] at Ho
      rw [decide_eq_false hv1e]
      odjret (by subst Ho; rfl)
    subst hv1e
    simp only [bne_self_eq_false, Bool.false_eq_true, ite_false] at Ho
    rw [decide_eq_true (rfl : ([] : Str) = [])]
    try wp_auto
    obtain ⟨el, hel, Ho⟩ := bind_ok Ho
    odm elect
    wp_apply wp_elect _ X el $$ [Hx]
    · iframe Hx; ipureintro; exact hel
    cases el
    case true =>
      simp only [Bool.not_true, Bool.false_eq_true, ite_false] at Ho
      odjskip Ho
    simp only [Bool.not_false, ite_true] at Ho
    obtain ⟨ok, hok, Ho⟩ := bind_ok Ho
    obtain ⟨hm, hhm, hokt, hokf⟩ := andM_ok hok
    simp only [pure_ok, Except.ok.injEq] at hhm
    try wp_auto
    odm hasM
    wp_apply wp_hasM _ X $$ [Hx]
    · iexact Hx
    rw [hhm]
    cases hm
    · odjno (hokf rfl)
    have h1 := hokt rfl
    -- `x.m().typ() == "vote"`
    obtain ⟨a2, ha2, h2t, h2f⟩ := andM_ok h1
    obtain ⟨m, hm, ha2⟩ := bind_ok ha2
    obtain ⟨ty, hty, ha2⟩ := bind_ok ha2
    simp only [pure_ok, Except.ok.injEq] at ha2
    subst ha2
    try wp_auto
    odm m
    wp_apply wp_m _ X m $$ [Hx] as %gm #Hm
    · iframe Hx; ipureintro; exact hm
    try wp_auto
    wp_apply wp_Msg_typ gm m ty $$ [Hm]
    · iframe Hm; ipureintro; exact hty
    by_cases htv : ty = go!"vote"
    case neg =>
      rw [decide_eq_false htv]
      odjno (h2f (by simpa using htv))
    rw [decide_eq_true htv]
    have h2 := h2t (by simp [htv])
    -- `x.m().from() == w.vote()`
    obtain ⟨a3, ha3, h3t, h3f⟩ := andM_ok h2
    obtain ⟨m', hm', ha3⟩ := bind_ok ha3
    rw [hm] at hm'; cases hm'
    obtain ⟨fr, hfr, ha3⟩ := bind_ok ha3
    obtain ⟨vt, hvt, ha3⟩ := bind_ok ha3
    simp only [pure_ok, Except.ok.injEq] at ha3
    subst ha3
    try wp_auto
    odm m
    wp_apply wp_m _ X m $$ [Hx] as %gm' #Hm'
    · iframe Hx; ipureintro; exact hm
    try wp_auto
    wp_apply wp_Msg_from gm' m fr $$ [Hm']
    · iframe Hm'; ipureintro; exact hfr
    try wp_auto
    wp_apply wp_Event_vote pw X.w vt $$ [Hw]
    · iframe Hw; ipureintro; exact hvt
    try wp_auto
    by_cases hfv : fr = vt
    case neg =>
      rw [decide_eq_false hfv]
      odjno (h3f (by simpa using hfv))
    rw [decide_eq_true hfv]
    have h3 := h3t (by simp [hfv])
    -- `x.m().term() == x.T1()`
    obtain ⟨a4, ha4, h4t, h4f⟩ := andM_ok h3
    obtain ⟨m', hm', ha4⟩ := bind_ok ha4
    rw [hm] at hm'; cases hm'
    obtain ⟨mt, hmt, ha4⟩ := bind_ok ha4
    obtain ⟨t1', ht1', ha4⟩ := bind_ok ha4
    rw [ht1] at ht1'; cases ht1'
    simp only [pure_ok, Except.ok.injEq] at ha4
    subst ha4
    try wp_auto
    odm m
    wp_apply wp_m _ X m $$ [Hx] as %gm2 #Hm2
    · iframe Hx; ipureintro; exact hm
    try wp_auto
    wp_apply wp_Msg_term gm2 m mt $$ [Hm2] as %ut %Hut
    · iframe Hm2; ipureintro; exact hmt
    try wp_auto
    odm T1
    wp_apply wp_T1 _ X t1 $$ [Hx] as %u1 %Hu1
    · iframe Hx; ipureintro; exact ht1
    try wp_auto
    rw [decide_w64_eq, Hut, Hu1]
    by_cases hmt1 : mt = t1
    case neg =>
      rw [decide_eq_false hmt1]
      odjno (h4f (by simpa using hmt1))
    rw [decide_eq_true hmt1]
    have h4 := h4t (by simp [hmt1])
    -- `factsHas(s.Msgs, VoteFact(x.m())) && s.UpToDate(VoteFact(x.m()), n)`
    obtain ⟨a5, ha5, h5t, h5f⟩ := andM_ok h4
    obtain ⟨m', hm', ha5⟩ := bind_ok ha5
    rw [hm] at hm'; cases hm'
    obtain ⟨vf, hvf, ha5⟩ := bind_ok ha5
    simp only [pure_ok, Except.ok.injEq] at ha5
    subst ha5
    try wp_auto
    odm m
    wp_apply wp_m _ X m $$ [Hx] as %gm3 #Hm3
    · iframe Hx; ipureintro; exact hm
    try wp_auto
    wp_apply wp_VoteFact gm3 m vf $$ [Hm3] as %gvf %Hgvf
    · iframe Hm3; ipureintro; exact hvf
    try wp_auto
    wp_apply wp_factsHas g.Msgs' s.msgs gvf vf $$ [HMsgs]
    · iframe HMsgs; ipureintro; exact Hgvf
    cases hcont : s.msgs.contains vf
    · try wp_auto
      odjno (h5f hcont)
    have h5 := h5t hcont
    obtain ⟨m', hm', h5⟩ := bind_ok h5
    rw [hm] at hm'; cases hm'
    obtain ⟨vf', hvf', h5⟩ := bind_ok h5
    rw [hvf] at hvf'; cases hvf'
    simp only [pure_ok, Except.ok.injEq] at h5
    subst h5
    try wp_auto
    odm m
    wp_apply wp_m _ X m $$ [Hx] as %gm4 #Hm4
    · iframe Hx; ipureintro; exact hm
    try wp_auto
    wp_apply wp_VoteFact gm4 m vf $$ [Hm4] as %gvf' %Hgvf'
    · iframe Hm4; ipureintro; exact hvf
    try wp_auto
    wp_apply wp_SUpToDate p s gvf' vf n $$ [Hs]
    · iframe Hs; ipureintro; exact ⟨Hgvf', Hn, Hlt⟩
    cases hup : s.upToDate vf (sint.nat n)
    · odjno hup
    simp only [hup, Bool.not_true, Bool.false_eq_true, ite_false] at Ho
    odjskip Ho
  odjafter
  subst hK
  -- g4: `if x.snaps() { if !(!x.leads() && x.hasM() && … && w.commit() == x.m().index()) { return } }`
  unfold g4 at Ho
  dsimp only at Ho
  generalize hK : g5 X (g6 X (succ X)) = K at Ho
  odjoin K
  · odm snaps
    wp_apply wp_snaps _ X $$ [Hx]
    · iexact Hx
    cases hsn : X.snaps
    · simp only [hsn, Bool.false_eq_true, ite_false] at Ho
      odjskip Ho
    simp only [hsn, ite_true] at Ho
    obtain ⟨ok, hok, Ho⟩ := bind_ok Ho
    -- `!x.leads()`
    obtain ⟨a1, ha1, h1t, h1f⟩ := andM_ok hok
    unfold notM at ha1
    obtain ⟨ld1, hld1, ha1⟩ := bind_ok ha1
    simp only [pure_ok, Except.ok.injEq] at ha1
    subst ha1
    try wp_auto
    odm leads
    wp_apply wp_leads _ X ld1 $$ [Hx]
    · iframe Hx; ipureintro; exact hld1
    cases ld1
    case true =>
      try wp_auto
      odjno (h1f rfl)
    have h1 := h1t rfl
    -- `x.hasM()`
    obtain ⟨a2, ha2, h2t, h2f⟩ := andM_ok h1
    simp only [pure_ok, Except.ok.injEq] at ha2
    try wp_auto
    odm hasM
    wp_apply wp_hasM _ X $$ [Hx]
    · iexact Hx
    rw [ha2]
    cases a2
    · odjno (h2f rfl)
    have h2 := h2t rfl
    -- `x.m().typ() == "snap"`
    obtain ⟨a3, ha3, h3t, h3f⟩ := andM_ok h2
    obtain ⟨m, hm, ha3⟩ := bind_ok ha3
    obtain ⟨ty, hty, ha3⟩ := bind_ok ha3
    simp only [pure_ok, Except.ok.injEq] at ha3
    subst ha3
    try wp_auto
    odm m
    wp_apply wp_m _ X m $$ [Hx] as %gm #Hm
    · iframe Hx; ipureintro; exact hm
    try wp_auto
    wp_apply wp_Msg_typ gm m ty $$ [Hm]
    · iframe Hm; ipureintro; exact hty
    by_cases hts : ty = go!"snap"
    case neg =>
      rw [decide_eq_false hts]
      odjno (h3f (by simpa using hts))
    rw [decide_eq_true hts]
    have h3 := h3t (by simp [hts])
    -- `x.stores()`
    obtain ⟨st, hst, h4t, h4f⟩ := andM_ok h3
    try wp_auto
    odm stores
    wp_apply wp_stores _ X st $$ [Hx]
    · iframe Hx; ipureintro; exact hst
    cases st
    · try wp_auto
      odjno (h4f rfl)
    have h4 := h4t rfl
    -- `w.snap().Index == x.m().index()`
    obtain ⟨a5, ha5, h5t, h5f⟩ := andM_ok h4
    obtain ⟨sn, hsn', ha5⟩ := bind_ok ha5
    obtain ⟨m', hm', ha5⟩ := bind_ok ha5
    rw [hm] at hm'; cases hm'
    obtain ⟨mi, hmi, ha5⟩ := bind_ok ha5
    simp only [pure_ok, Except.ok.injEq] at ha5
    subst ha5
    try wp_auto
    wp_apply wp_Event_snap pw X.w sn $$ [Hw] as %gsn %Hgsn
    · iframe Hw; ipureintro; exact hsn'
    try wp_auto
    odm m
    wp_apply wp_m _ X m $$ [Hx] as %gm2 #Hm2
    · iframe Hx; ipureintro; exact hm
    try wp_auto
    wp_apply wp_Msg_index gm2 m mi $$ [Hm2] as %ui %Hui
    · iframe Hm2; ipureintro; exact hmi
    try wp_auto
    rw [decide_w64_eq, Hgsn.1, Hui]
    by_cases hsi : sn.index = mi
    case neg =>
      rw [decide_eq_false hsi]
      odjno (h5f (by simpa using hsi))
    rw [decide_eq_true hsi]
    have h5 := h5t (by simp [hsi])
    -- `w.snap().Term == x.m().logTerm()`
    obtain ⟨a6, ha6, h6t, h6f⟩ := andM_ok h5
    obtain ⟨sn', hsn'', ha6⟩ := bind_ok ha6
    rw [hsn'] at hsn''; cases hsn''
    obtain ⟨m', hm', ha6⟩ := bind_ok ha6
    rw [hm] at hm'; cases hm'
    obtain ⟨mlt, hmlt, ha6⟩ := bind_ok ha6
    simp only [pure_ok, Except.ok.injEq] at ha6
    subst ha6
    try wp_auto
    wp_apply wp_Event_snap pw X.w sn $$ [Hw] as %gsn2 %Hgsn2
    · iframe Hw; ipureintro; exact hsn'
    try wp_auto
    odm m
    wp_apply wp_m _ X m $$ [Hx] as %gm3 #Hm3
    · iframe Hx; ipureintro; exact hm
    try wp_auto
    wp_apply wp_Msg_logTerm gm3 m mlt $$ [Hm3] as %ult %Hult
    · iframe Hm3; ipureintro; exact hmlt
    try wp_auto
    rw [decide_w64_eq, Hgsn2.2, Hult]
    by_cases hst' : sn.term = mlt
    case neg =>
      rw [decide_eq_false hst']
      odjno (h6f (by simpa using hst'))
    rw [decide_eq_true hst']
    have h6 := h6t (by simp [hst'])
    -- `w.commit() == x.m().index()`
    obtain ⟨cm, hcm, h6⟩ := bind_ok h6
    obtain ⟨m', hm', h6⟩ := bind_ok h6
    rw [hm] at hm'; cases hm'
    obtain ⟨mi', hmi', h6⟩ := bind_ok h6
    rw [hmi] at hmi'; cases hmi'
    simp only [pure_ok, Except.ok.injEq] at h6
    subst h6
    try wp_auto
    wp_apply wp_Event_commit pw X.w cm $$ [Hw] as %uc %Huc
    · iframe Hw; ipureintro; exact hcm
    try wp_auto
    odm m
    wp_apply wp_m _ X m $$ [Hx] as %gm4 #Hm4
    · iframe Hx; ipureintro; exact hm
    try wp_auto
    wp_apply wp_Msg_index gm4 m mi $$ [Hm4] as %ui2 %Hui2
    · iframe Hm4; ipureintro; exact hmi
    try wp_auto
    rw [decide_w64_eq, Huc, Hui2]
    by_cases hci : cm = mi
    case neg =>
      rw [decide_eq_false hci]
      odjno (show (cm == mi) = false by simpa using hci)
    rw [decide_eq_true hci]
    simp only [hci, beq_self_eq_true, Bool.not_true, Bool.false_eq_true, ite_false] at Ho
    odjskip Ho
  odjafter
  subst hK
  -- g5: `if x.stores() { … }`
  unfold g5 at Ho
  dsimp only at Ho
  rw [hXs, hXn, hXld, hXll, hXch, hXtl] at Ho
  obtain ⟨st, hst, Ho⟩ := bind_ok Ho
  generalize hK : g6 X (succ X) = K at Ho
  odjoin K
  · odm stores
    wp_apply wp_stores _ X st $$ [Hx]
    · iframe Hx; ipureintro; exact hst
    cases st
    · simp only [Bool.false_eq_true, ite_false] at Ho
      odjskip Ho
    simp only [ite_true] at Ho
    obtain ⟨ld1, hld1, Ho⟩ := bind_ok Ho
    try wp_auto
    odm leads
    wp_apply wp_leads _ X ld1 $$ [Hx]
    · iframe Hx; ipureintro; exact hld1
    cases ld1
    case true =>
      -- `!(x.T1() == x.T0() && x.first() == len(x.L0())+1 && SendableIn(ld, ll, ch, tl, x.f()))`
      simp only [ite_true] at Ho
      obtain ⟨ok, hok, Ho⟩ := bind_ok Ho
      obtain ⟨a1, ha1, h1t, h1f⟩ := andM_ok hok
      obtain ⟨t1', ht1', ha1⟩ := bind_ok ha1
      rw [ht1] at ht1'; cases ht1'
      simp only [pure_ok, Except.ok.injEq] at ha1
      subst ha1
      try wp_auto
      odm T1
      wp_apply wp_T1 _ X t1 $$ [Hx] as %u1 %Hu1
      · iframe Hx; ipureintro; exact ht1
      try wp_auto
      odm T0
      wp_apply wp_T0 _ X $$ [Hx] as %u0 %Hu0
      · iexact Hx
      try wp_auto
      rw [decide_w64_eq, Hu0, Hu1]
      by_cases he : t1 = X.T0
      case neg =>
        rw [decide_eq_false he]
        odjno (h1f (by simpa using he))
      rw [decide_eq_true he]
      have h1 := h1t (by simp [he])
      obtain ⟨a2, ha2, h2t, h2f⟩ := andM_ok h1
      obtain ⟨fi, hfi, ha2⟩ := bind_ok ha2
      simp only [pure_ok, Except.ok.injEq] at ha2
      subst ha2
      have hfib := first_bigOk HW hb hfi
      try wp_auto
      odm first
      wp_apply wp_first _ X fi $$ [Hx] as %ufi %Hufi
      · iframe Hx; ipureintro; exact hfi
      try wp_auto
      odm L0
      wp_apply wp_L0 _ X $$ [Hx] as %l0 #Hl0
      · iexact Hx
      ihave %Hl0l := logRO_len _ _ $$ Hl0
      have hl0b := OnDisk.L0_le HW
      try wp_auto
      have hadd : sint.Z (l0.len + W64 1) = (X.L0.length : Int) + 1 := by
        rw [sint_add_one (by omega), Hl0l]
      rw [decide_w64_eq, hadd, Hufi]
      by_cases hfe : fi = (X.L0.length : Int) + 1
      case neg =>
        rw [decide_eq_false hfe]
        odjno (h2f (by simpa using hfe))
      rw [decide_eq_true hfe]
      have h2 := h2t (by simp [hfe])
      obtain ⟨f, hf, h2⟩ := bind_ok h2
      obtain ⟨hfp, hfe', -⟩ := OnDisk.f_within hb HW hf
      try wp_auto
      odm f
      wp_apply wp_f _ X f $$ [Hx] as %gf #Hf
      · iframe Hx; ipureintro; exact hf
      try wp_auto
      wp_apply wp_SendableIn ldl ld lll ll chl ch tll tl gf f ok $$ [Hld Hll Hch Htl Hf]
      · iframe Hld Hll Hch Htl Hf; ipureintro; exact ⟨h2, hfp, by omega⟩
      cases ok
      · odjno (rfl : false = false)
      simp only [Bool.not_true, Bool.false_eq_true, ite_false] at Ho
      odjskip Ho
    simp only [Bool.false_eq_true, ite_false] at Ho
    -- A: `!(x.hasM() && (x.m().typ() == "app" || x.m().typ() == "snap") && x.m().term() == x.T1())`
    obtain ⟨okA, hokA, Ho⟩ := bind_ok Ho
    generalize hcA : (!okA) = cA at Ho
    obtain ⟨hm, hhm, hAt, hAf⟩ := andM_ok hokA
    simp only [pure_ok, Except.ok.injEq] at hhm
    try wp_auto
    odguard cA
    · odm hasM
      wp_apply wp_hasM _ X $$ [Hx]
      · iexact Hx
      rw [hhm]
      cases hm
      · odretc (by rw [← hcA, hAf rfl]; rfl)
      have hA1 := hAt rfl
      obtain ⟨or1, hor1, hA2t, hA2f⟩ := andM_ok hA1
      obtain ⟨oa, hoa, hoat, hoaf⟩ := orM_ok hor1
      obtain ⟨m, hm, hoa⟩ := bind_ok hoa
      obtain ⟨ty, hty, hoa⟩ := bind_ok hoa
      simp only [pure_ok, Except.ok.injEq] at hoa
      subst hoa
      try wp_auto
      odm m
      wp_apply wp_m _ X m $$ [Hx] as %gm #Hm
      · iframe Hx; ipureintro; exact hm
      try wp_auto
      wp_apply wp_Msg_typ gm m ty $$ [Hm]
      · iframe Hm; ipureintro; exact hty
      by_cases hta : ty = go!"app"
      · rw [decide_eq_true hta]
        have hor : or1 = true := hoat (by simp [hta])
        subst hor
        odAterm rfl
      rw [decide_eq_false hta]
      have hor := hoaf (by simpa using hta)
      obtain ⟨m', hm', hor⟩ := bind_ok hor
      rw [hm] at hm'; cases hm'
      obtain ⟨ty', hty', hor⟩ := bind_ok hor
      rw [hty] at hty'; cases hty'
      simp only [pure_ok, Except.ok.injEq] at hor
      subst hor
      try wp_auto
      odm m
      wp_apply wp_m _ X m $$ [Hx] as %gm' #Hm'
      · iframe Hx; ipureintro; exact hm
      try wp_auto
      wp_apply wp_Msg_typ gm' m ty $$ [Hm']
      · iframe Hm'; ipureintro; exact hty
      by_cases hts : ty = go!"snap"
      · rw [decide_eq_true hts]
        odAterm (by simp [hts])
      rw [decide_eq_false hts]
      odretc (by rw [← hcA, hA2f (by simpa using hts)]; rfl)
    odafterj cA
    -- B: `x.m().typ() == "snap" && !x.snaps()`
    obtain ⟨cB, hcB, Ho⟩ := bind_ok Ho
    obtain ⟨b1, hb1, hBt, hBf⟩ := andM_ok hcB
    obtain ⟨m, hm, hb1⟩ := bind_ok hb1
    obtain ⟨ty, hty, hb1⟩ := bind_ok hb1
    simp only [pure_ok, Except.ok.injEq] at hb1
    subst hb1
    odguard cB
    · odm m
      wp_apply wp_m _ X m $$ [Hx] as %gm #Hm
      · iframe Hx; ipureintro; exact hm
      try wp_auto
      wp_apply wp_Msg_typ gm m ty $$ [Hm]
      · iframe Hm; ipureintro; exact hty
      by_cases hts : ty = go!"snap"
      case neg =>
        rw [decide_eq_false hts]
        odskip (hBf (by simpa using hts))
      rw [decide_eq_true hts]
      have hB := hBt (by simp [hts])
      simp only [pure_ok, Except.ok.injEq] at hB
      try wp_auto
      odm snaps
      wp_apply wp_snaps _ X $$ [Hx]
      · iexact Hx
      subst hB
      cases X.snaps
      · odretc rfl
      · odskip rfl
    odafterj cB
    -- C: `!(SnapOk(ll, x.m()) && SendableIn(ld, ll, ch, tl, x.f()))`
    have hfnl : X.f = X.fm := f_notLeads hld1
    obtain ⟨okC, hokC, Ho⟩ := bind_ok Ho
    generalize hcC : (!okC) = cC at Ho
    obtain ⟨c1, hc1, hCt, hCf⟩ := andM_ok hokC
    obtain ⟨m, hm, hc1⟩ := bind_ok hc1
    odguard cC
    · odm m
      wp_apply wp_m _ X m $$ [Hx] as %gm #Hm
      · iframe Hx; ipureintro; exact hm
      try wp_auto
      wp_apply wp_SnapOk lll ll gm m c1 $$ [Hll Hm]
      · iframe Hll Hm; ipureintro; exact hc1
      cases c1
      · odretc (by rw [← hcC, hCf rfl]; rfl)
      have hC := hCt rfl
      obtain ⟨f, hf, hC⟩ := bind_ok hC
      obtain ⟨hfp, hfe', -⟩ := OnDisk.f_within hb HW hf
      try wp_auto
      odm f
      wp_apply wp_f _ X f $$ [Hx] as %gf #Hf
      · iframe Hx; ipureintro; exact hf
      try wp_auto
      wp_apply wp_SendableIn ldl ld lll ll chl ch tll tl gf f okC $$ [Hld Hll Hch Htl Hf]
      · iframe Hld Hll Hch Htl Hf; ipureintro; exact ⟨hC, hfp, by omega⟩
      subst hcC
      cases okC
      · odretc rfl
      · odskip rfl
    odafterj cC
    -- D: `!s.PrevOk(n, x.f())`
    obtain ⟨f, hf, Ho⟩ := bind_ok Ho
    obtain ⟨pv, hpv, Ho⟩ := bind_ok Ho
    obtain ⟨hfp, hfe', hfc⟩ := OnDisk.f_within hb HW hf
    odm f
    wp_apply wp_f _ X f $$ [Hx] as %gf #Hf
    · iframe Hx; ipureintro; exact hf
    try wp_auto
    wp_apply wp_SPrevOk p s n gf f pv $$ [Hs Hf]
    · iframe Hs Hf; ipureintro; exact ⟨Hn, Hlt, hpv⟩
    cases pv
    · simp only [Bool.not_false, ite_true, pure_ok, Except.ok.injEq] at Ho
      odjret (by subst Ho; rfl)
    simp only [Bool.not_true, Bool.false_eq_true, ite_false] at Ho
    try wp_auto
    -- `k := x.k()`; E: `!(1 <= k && k <= len(x.f().Entries))`
    obtain ⟨k, hk, Ho⟩ := bind_ok Ho
    obtain ⟨f', hf', Ho⟩ := bind_ok Ho
    rw [hf] at hf'; cases hf'
    generalize hcE : (!(decide (1 ≤ k) && decide (k ≤ (f.entries.length : Int)))) = cE at Ho
    odm k
    wp_apply wp_k _ X k $$ [Hx] as %uk %Huk
    · iframe Hx; ipureintro; exact hk
    try wp_auto
    iunfold appendFactRO at Hf
    icases Hf with ⟨%Hfr, #Hfes⟩
    ihave %Hfesl := logRO_len _ _ $$ Hfes
    ipersist k
    odguard cE
    · rw [Huk, sint_one]
      by_cases hk1 : 1 ≤ k
      case neg =>
        rw [decide_eq_false hk1]
        odretc (by rw [← hcE]; simp [hk1])
      rw [decide_eq_true hk1]
      try wp_auto
      odm f
      wp_apply wp_f _ X f $$ [Hx] as %gf' #Hf'
      · iframe Hx; ipureintro; exact hf
      try wp_auto
      iunfold appendFactRO at Hf'
      icases Hf' with ⟨%-, #Hfes'⟩
      ihave %Hl' := logRO_len _ _ $$ Hfes'
      rw [Huk, Hl']
      by_cases hkl : k ≤ (f.entries.length : Int)
      · rw [decide_eq_true hkl]
        odskip (by rw [← hcE]; simp [hk1, hkl])
      · rw [decide_eq_false hkl]
        odretc (by rw [← hcE]; simp [hk1, hkl])
    odafterj cE
    have hkb : 1 ≤ k ∧ k ≤ (f.entries.length : Int) := by simpa using hcE
    -- F: `!s.HasFirst(n, x.f(), k-1)`
    obtain ⟨f', hf', Ho⟩ := bind_ok Ho
    rw [hf] at hf'; cases hf'
    obtain ⟨hy, hhy, Ho⟩ := bind_ok Ho
    obtain ⟨hpli, -, -, -, -⟩ := OnDisk.fm_within HW (hfnl ▸ hf)
    odm f
    wp_apply wp_f _ X f $$ [Hx] as %gf2 #Hf2
    · iframe Hx; ipureintro; exact hf
    try wp_auto
    have hk1 : sint.Z (uk - W64 1) = k - 1 := by rw [sint_sub_one (by omega), Huk]
    wp_apply wp_SHasFirst p s n gf2 f (uk - W64 1) hy $$ [Hs Hf2]
    · iframe Hs Hf2; ipureintro
      refine ⟨Hn, Hlt, by rw [hk1]; exact hhy, hpli, ?_⟩
      rw [hk1]; unfold numOk numBound; unfold numBound at hb; omega
    cases hy
    · simp only [Bool.not_false, ite_true, pure_ok, Except.ok.injEq] at Ho
      odjret (by subst Ho; rfl)
    simp only [Bool.not_true, Bool.false_eq_true, ite_false] at Ho
    try wp_auto
    -- G: `!EntriesEqual(x.es(), SubSeq(x.f().Entries, k, len(x.f().Entries)))`
    obtain ⟨f', hf', Ho⟩ := bind_ok Ho
    rw [hf] at hf'; cases hf'
    obtain ⟨es, hes, Ho⟩ := bind_ok Ho
    obtain ⟨sub, hsub, Ho⟩ := bind_ok Ho
    obtain ⟨ee, hee, Ho⟩ := bind_ok Ho
    odm es
    wp_apply wp_es _ X es $$ [Hx] as %esl #Hes
    · iframe Hx; ipureintro; exact hes
    try wp_auto
    odm f
    wp_apply wp_f _ X f $$ [Hx] as %gf3 #Hf3
    · iframe Hx; ipureintro; exact hf
    try wp_auto
    odm f
    wp_apply wp_f _ X f $$ [Hx] as %gf4 #Hf4
    · iframe Hx; ipureintro; exact hf
    try wp_auto
    iunfold appendFactRO at Hf3 Hf4
    icases Hf3 with ⟨%-, #Hfes3⟩
    icases Hf4 with ⟨%-, #Hfes4⟩
    ihave %Hl4 := logRO_len _ _ $$ Hfes4
    wp_apply wp_SubSeq gf3.Entries' f.entries uk gf4.Entries'.len sub $$ [Hfes3] as %subl #Hsub
    · iframe Hfes3; ipureintro; rw [Huk, Hl4]; exact hsub
    try wp_auto
    wp_apply wp_EntriesEqual esl es subl sub ee $$ [Hes Hsub]
    · iframe Hes Hsub; ipureintro; exact hee
    cases ee
    · simp only [Bool.not_false, ite_true, pure_ok, Except.ok.injEq] at Ho
      odjret (by subst Ho; rfl)
    simp only [Bool.not_true, Bool.false_eq_true, ite_false] at Ho
    try wp_auto
    -- H: `x.first() <= len(x.L0())`: `At(x.L0(), x.first()).Term == At(x.es(), 1).Term`, else
    -- `x.first() != len(x.L0())+1`
    obtain ⟨fi, hfi, Ho⟩ := bind_ok Ho
    have hfib := first_bigOk HW hb hfi
    have hl0b := OnDisk.L0_le HW
    odm first
    wp_apply wp_first _ X fi $$ [Hx] as %ufi %Hufi
    · iframe Hx; ipureintro; exact hfi
    try wp_auto
    odm L0
    wp_apply wp_L0 _ X $$ [Hx] as %l0 #Hl0
    · iexact Hx
    ihave %Hl0l := logRO_len _ _ $$ Hl0
    try wp_auto
    rw [Hufi, Hl0l]
    by_cases hfl : fi ≤ (X.L0.length : Int)
    · rw [decide_eq_true hfl]
      simp only [hfl, decide_true, ite_true] at Ho
      obtain ⟨ea, hea, Ho⟩ := bind_ok Ho
      obtain ⟨es', hes', Ho⟩ := bind_ok Ho
      rw [hes] at hes'; cases hes'
      obtain ⟨eb, heb, Ho⟩ := bind_ok Ho
      try wp_auto
      odm L0
      wp_apply wp_L0 _ X $$ [Hx] as %l0' #Hl0'
      · iexact Hx
      try wp_auto
      odm first
      wp_apply wp_first _ X fi $$ [Hx] as %ufi' %Hufi'
      · iframe Hx; ipureintro; exact hfi
      try wp_auto
      wp_apply wp_At l0' X.L0 ufi' ea $$ [Hl0'] as %gea #Hgea
      · iframe Hl0'; ipureintro; rw [Hufi']; exact hea
      try wp_auto
      odm es
      wp_apply wp_es _ X es $$ [Hx] as %esl' #Hes'
      · iframe Hx; ipureintro; exact hes
      try wp_auto
      wp_apply wp_At esl' es (W64 1) eb $$ [Hes'] as %geb #Hgeb
      · iframe Hes'; ipureintro; rw [sint_one]; exact heb
      try wp_auto
      iunfold entryRO at Hgea Hgeb
      icases Hgea with ⟨%Hgea1, #-⟩
      icases Hgeb with ⟨%Hgeb1, #-⟩
      rw [decide_w64_eq, Hgea1.1, Hgeb1.1]
      by_cases hte : ea.term = eb.term
      · rw [decide_eq_true hte]
        simp only [hte, beq_self_eq_true, ite_true, pure_ok, Except.ok.injEq] at Ho
        odjret (by subst Ho; rfl)
      rw [decide_eq_false hte]
      simp only [show (ea.term == eb.term) = false by simpa using hte, Bool.false_eq_true, ite_false] at Ho
      odjskip Ho
    rw [decide_eq_false hfl]
    simp only [hfl, decide_false, Bool.false_eq_true, ite_false] at Ho
    try wp_auto
    odm first
    wp_apply wp_first _ X fi $$ [Hx] as %ufi' %Hufi'
    · iframe Hx; ipureintro; exact hfi
    try wp_auto
    odm L0
    wp_apply wp_L0 _ X $$ [Hx] as %l0' #Hl0'
    · iexact Hx
    ihave %Hl0l' := logRO_len _ _ $$ Hl0'
    try wp_auto
    have hadd : sint.Z (l0'.len + W64 1) = (X.L0.length : Int) + 1 := by
      rw [sint_add_one (by omega), Hl0l']
    rw [decide_w64_eq, hadd, Hufi']
    by_cases hfe : fi = (X.L0.length : Int) + 1
    · rw [decide_eq_true hfe]
      simp only [hfe, bne_self_eq_false, Bool.false_eq_true, ite_false] at Ho
      odjskip Ho
    rw [decide_eq_false hfe]
    simp only [show (fi != (X.L0.length : Int) + 1) = true by simpa using hfe, ite_true, pure_ok,
      Except.ok.injEq] at Ho
    odjret (by subst Ho; rfl)
  odjafter
  subst hK
  -- g6: `if x.moved() { … }`
  unfold g6 at Ho
  dsimp only at Ho
  rw [hXs, hXn, hXld, hXll, hXch, hXtl] at Ho
  obtain ⟨mv, hmv, Ho⟩ := bind_ok Ho
  generalize hK : succ X = K at Ho
  odjoin K
  · odm moved
    wp_apply wp_moved _ X mv $$ [Hx]
    · iframe Hx; ipureintro; exact hmv
    cases mv
    · simp only [Bool.false_eq_true, ite_false] at Ho
      odjskip Ho
    simp only [ite_true] at Ho
    -- M1: `!(w.commit() > s.CommitIndex[n] && w.commit() <= len(x.L1()))`
    obtain ⟨ok1, hok1, Ho⟩ := bind_ok Ho
    generalize hc1 : (!ok1) = c1 at Ho
    obtain ⟨a1, ha1, h1t, h1f⟩ := andM_ok hok1
    obtain ⟨cm, hcm, ha1⟩ := bind_ok ha1
    simp only [pure_ok, Except.ok.injEq] at ha1
    subst ha1
    have hcmb : bigOk cm := commit_bigOk HW hcm
    icases intsRO_at g.CommitIndex' s.commitIndex n ⟨Hn, by rw [HWf.len_commitIndex]; exact Hlt⟩ $$ HCommitIndex
      with ⟨%ci, #Hcia, %Hci⟩
    try wp_auto
    odguard c1
    · wp_apply wp_Event_commit pw X.w cm $$ [Hw] as %uc %Huc
      · iframe Hw; ipureintro; exact hcm
      try wp_auto
      wp_apply wp_load_at _ _ ci Hn $$ [Hcia]
      · iexact Hcia
      try wp_auto
      rw [Huc, Hci]
      by_cases hgt : s.commitIndex[sint.nat n]! < cm
      case neg =>
        rw [decide_eq_false hgt]
        odretc (by rw [← hc1, h1f (by simpa using hgt)]; rfl)
      rw [decide_eq_true hgt]
      have h1 := h1t (by simpa using hgt)
      obtain ⟨cm', hcm', h1⟩ := bind_ok h1
      rw [hcm] at hcm'; cases hcm'
      obtain ⟨L1, hL1, h1⟩ := bind_ok h1
      simp only [pure_ok, Except.ok.injEq] at h1
      try wp_auto
      wp_apply wp_Event_commit pw X.w cm $$ [Hw] as %uc' %Huc'
      · iframe Hw; ipureintro; exact hcm
      try wp_auto
      odm L1
      wp_apply wp_L1 _ X L1 $$ [Hx] as %l1 #Hl1
      · iframe Hx; ipureintro; exact hL1
      ihave %Hl1l := logRO_len _ _ $$ Hl1
      try wp_auto
      rw [Huc', Hl1l]
      subst h1
      by_cases hle : cm ≤ (L1.length : Int)
      · rw [decide_eq_true hle]
        odskip (by rw [← hc1]; simp [hle])
      · rw [decide_eq_false hle]
        odretc (by rw [← hc1]; simp [hle])
    odafterj c1
    obtain ⟨ld1, hld1, Ho⟩ := bind_ok Ho
    odm leads
    wp_apply wp_leads _ X ld1 $$ [Hx]
    · iframe Hx; ipureintro; exact hld1
    cases ld1
    case true =>
      -- `!(x.T1() == x.T0() && SendableIn(ld, ll, ch, tl, x.f()))`
      simp only [ite_true] at Ho
      obtain ⟨ok, hok, Ho⟩ := bind_ok Ho
      obtain ⟨a1, ha1, h1t, h1f⟩ := andM_ok hok
      obtain ⟨t1', ht1', ha1⟩ := bind_ok ha1
      rw [ht1] at ht1'; cases ht1'
      simp only [pure_ok, Except.ok.injEq] at ha1
      subst ha1
      try wp_auto
      odm T1
      wp_apply wp_T1 _ X t1 $$ [Hx] as %u1 %Hu1
      · iframe Hx; ipureintro; exact ht1
      try wp_auto
      odm T0
      wp_apply wp_T0 _ X $$ [Hx] as %u0 %Hu0
      · iexact Hx
      try wp_auto
      rw [decide_w64_eq, Hu0, Hu1]
      by_cases he : t1 = X.T0
      case neg =>
        rw [decide_eq_false he]
        odjno (h1f (by simpa using he))
      rw [decide_eq_true he]
      have h1 := h1t (by simp [he])
      obtain ⟨f, hf, h1⟩ := bind_ok h1
      obtain ⟨hfp, hfe', -⟩ := OnDisk.f_within hb HW hf
      try wp_auto
      odm f
      wp_apply wp_f _ X f $$ [Hx] as %gf #Hf
      · iframe Hx; ipureintro; exact hf
      try wp_auto
      wp_apply wp_SendableIn ldl ld lll ll chl ch tll tl gf f ok $$ [Hld Hll Hch Htl Hf]
      · iframe Hld Hll Hch Htl Hf; ipureintro; exact ⟨h1, hfp, by omega⟩
      cases ok
      · odjno (rfl : false = false)
      simp only [Bool.not_true, Bool.false_eq_true, ite_false] at Ho
      odjskip Ho
    simp only [Bool.false_eq_true, ite_false] at Ho
    have hfnl : X.f = X.fm := f_notLeads hld1
    try wp_auto
    -- M2: `!(x.hasM() && IsReq(x.m()) && x.m().term() == x.T1())`
    obtain ⟨ok2, hok2, Ho⟩ := bind_ok Ho
    generalize hc2 : (!ok2) = c2 at Ho
    obtain ⟨hm, hhm, h2t, h2f⟩ := andM_ok hok2
    simp only [pure_ok, Except.ok.injEq] at hhm
    odguard c2
    · odm hasM
      wp_apply wp_hasM _ X $$ [Hx]
      · iexact Hx
      rw [hhm]
      cases hm
      · odretc (by rw [← hc2, h2f rfl]; rfl)
      have h2 := h2t rfl
      obtain ⟨rq, hrq, h3t, h3f⟩ := andM_ok h2
      obtain ⟨m, hm, hrq⟩ := bind_ok hrq
      try wp_auto
      odm m
      wp_apply wp_m _ X m $$ [Hx] as %gm #Hm
      · iframe Hx; ipureintro; exact hm
      try wp_auto
      wp_apply wp_IsReq gm m rq $$ [Hm]
      · iframe Hm; ipureintro; exact hrq
      cases rq
      · odretc (by rw [← hc2, h3f rfl]; rfl)
      have h3 := h3t rfl
      obtain ⟨m', hm', h3⟩ := bind_ok h3
      rw [hm] at hm'; cases hm'
      obtain ⟨mt, hmt, h3⟩ := bind_ok h3
      obtain ⟨t1', ht1', h3⟩ := bind_ok h3
      rw [ht1] at ht1'; cases ht1'
      simp only [pure_ok, Except.ok.injEq] at h3
      try wp_auto
      odm m
      wp_apply wp_m _ X m $$ [Hx] as %gm' #Hm'
      · iframe Hx; ipureintro; exact hm
      try wp_auto
      wp_apply wp_Msg_term gm' m mt $$ [Hm'] as %ut %Hut
      · iframe Hm'; ipureintro; exact hmt
      try wp_auto
      odm T1
      wp_apply wp_T1 _ X t1 $$ [Hx] as %u1 %Hu1
      · iframe Hx; ipureintro; exact ht1
      try wp_auto
      rw [decide_w64_eq, Hut, Hu1]
      subst h3
      by_cases hmt1 : mt = t1
      · rw [decide_eq_true hmt1]
        odskip (by rw [← hc2, hmt1]; simp)
      · rw [decide_eq_false hmt1]
        odretc (by rw [← hc2]; simpa using hmt1)
    odafterj c2
    -- M3: `!(SnapOk(ll, x.m()) && SendableIn(ld, ll, ch, tl, x.f()))`
    obtain ⟨okC, hokC, Ho⟩ := bind_ok Ho
    generalize hcC : (!okC) = cC at Ho
    obtain ⟨c1', hc1', hCt, hCf⟩ := andM_ok hokC
    obtain ⟨m, hm, hc1'⟩ := bind_ok hc1'
    odguard cC
    · odm m
      wp_apply wp_m _ X m $$ [Hx] as %gm #Hm
      · iframe Hx; ipureintro; exact hm
      try wp_auto
      wp_apply wp_SnapOk lll ll gm m c1' $$ [Hll Hm]
      · iframe Hll Hm; ipureintro; exact hc1'
      cases c1'
      · odretc (by rw [← hcC, hCf rfl]; rfl)
      have hC := hCt rfl
      obtain ⟨f, hf, hC⟩ := bind_ok hC
      obtain ⟨hfp, hfe', -⟩ := OnDisk.f_within hb HW hf
      try wp_auto
      odm f
      wp_apply wp_f _ X f $$ [Hx] as %gf #Hf
      · iframe Hx; ipureintro; exact hf
      try wp_auto
      wp_apply wp_SendableIn ldl ld lll ll chl ch tll tl gf f okC $$ [Hld Hll Hch Htl Hf]
      · iframe Hld Hll Hch Htl Hf; ipureintro; exact ⟨hC, hfp, by omega⟩
      subst hcC
      cases okC
      · odretc rfl
      · odskip rfl
    odafterj cC
    -- M4: `!(w.commit() <= x.f().Commit)`
    obtain ⟨cm, hcm, Ho⟩ := bind_ok Ho
    obtain ⟨f, hf, Ho⟩ := bind_ok Ho
    obtain ⟨hpli, hfel, -, -, -⟩ := OnDisk.fm_within HW (hfnl ▸ hf)
    wp_apply wp_Event_commit pw X.w cm $$ [Hw] as %uc %Huc
    · iframe Hw; ipureintro; exact hcm
    try wp_auto
    odm f
    wp_apply wp_f _ X f $$ [Hx] as %gf #Hf
    · iframe Hx; ipureintro; exact hf
    try wp_auto
    iunfold appendFactRO at Hf
    icases Hf with ⟨%Hfr, #-⟩
    rw [Huc, Hfr.2.2.2.2.2]
    by_cases hcf : cm ≤ f.commit
    case neg =>
      rw [decide_eq_false hcf]
      simp only [decide_eq_false hcf, Bool.not_false, ite_true, pure_ok, Except.ok.injEq] at Ho
      odjret (by subst Ho; rfl)
    rw [decide_eq_true hcf]
    simp only [decide_eq_true hcf, Bool.not_true, Bool.false_eq_true, ite_false] at Ho
    try wp_auto
    -- M5: `if x.m().typ() == "app" || x.m().typ() == "snap" { … }`
    obtain ⟨o5, ho5, Ho⟩ := bind_ok Ho
    obtain ⟨oa, hoa, hoat, hoaf⟩ := orM_ok ho5
    obtain ⟨m, hm, hoa⟩ := bind_ok hoa
    obtain ⟨ty, hty, hoa⟩ := bind_ok hoa
    simp only [pure_ok, Except.ok.injEq] at hoa
    subst hoa
    odm m
    wp_apply wp_m _ X m $$ [Hx] as %gm #Hm
    · iframe Hx; ipureintro; exact hm
    try wp_auto
    wp_apply wp_Msg_typ gm m ty $$ [Hm]
    · iframe Hm; ipureintro; exact hty
    by_cases hta : ty = go!"app"
    · rw [decide_eq_true hta]
      rw [hoat (by simp [hta])] at Ho
      simp only [ite_true] at Ho
      odM5body
    rw [decide_eq_false hta]
    have hor := hoaf (by simpa using hta)
    obtain ⟨m', hm', hor⟩ := bind_ok hor
    rw [hm] at hm'; cases hm'
    obtain ⟨ty', hty', hor⟩ := bind_ok hor
    rw [hty] at hty'; cases hty'
    simp only [pure_ok, Except.ok.injEq] at hor
    subst hor
    try wp_auto
    odm m
    wp_apply wp_m _ X m $$ [Hx] as %gm' #Hm'
    · iframe Hx; ipureintro; exact hm
    try wp_auto
    wp_apply wp_Msg_typ gm' m ty $$ [Hm']
    · iframe Hm'; ipureintro; exact hty
    by_cases hts : ty = go!"snap"
    · rw [decide_eq_true hts]
      simp only [hts, beq_self_eq_true, ite_true] at Ho
      odM5body
    rw [decide_eq_false hts]
    simp only [show (ty == go!"snap") = false by simpa using hts, Bool.false_eq_true, ite_false] at Ho
    odjskip Ho
  odjafter
  subst hK
  -- The successor. u0: `ns := s.clone(); ns.CurrentTerm = …; if x.voted() { ns.VoteTerm = …; ns.VoteFor = … }`
  unfold succ at Ho
  obtain ⟨t1', vd, ht1', hvd, hvv, Ho⟩ := OnDiskProofLaws.u0_ok' Ho
  rw [ht1] at ht1'; cases ht1'
  wp_apply wp_Sclone p s $$ [Hs] as %q Hq
  · iexact Hs
  try wp_auto
  ipersist ns
  odm T1
  wp_apply wp_T1 _ X t1 $$ [Hx] as %u1 %Hu1
  · iframe Hx; ipureintro; exact ht1
  try wp_auto
  wp_apply wp_setInt g.CurrentTerm' s.currentTerm n u1 $$ [HCurrentTerm] as %ctl #Hctl
  · iframe HCurrentTerm; ipureintro; exact ⟨Hn, by rw [HWf.len_currentTerm]; exact Hlt⟩
  try wp_auto
  rw [Hu1]
  wp_apply wp_set_currentTerm q s ctl (s.currentTerm.set (sint.nat n) t1)
    (by rw [List.length_set, HWf.len_currentTerm]) $$ [Hq Hctl] as Hq
  · iframe Hq Hctl
  try wp_auto
  wp_join (v := executeVal) iprop(stateOwn q (ns0 X t1 vd (OnDiskProofLaws.vf0 X vd))) at next with [Hq] as Hq
  · odm voted
    wp_apply wp_voted _ X vd $$ [Hx]
    · iframe Hx; ipureintro; exact hvd
    cases vd
    · try wp_auto
      wp_join_done
      have : ({ s with currentTerm := s.currentTerm.set (sint.nat n) t1 } : State) =
          ns0 X t1 false (OnDiskProofLaws.vf0 X false) := by subst hX; rfl
      rw [this]; iexact Hq
    obtain ⟨v, hv⟩ := hvv rfl
    try wp_auto
    odm T1
    wp_apply wp_T1 _ X t1 $$ [Hx] as %u1' %Hu1'
    · iframe Hx; ipureintro; exact ht1
    try wp_auto
    wp_apply wp_setInt g.VoteTerm' s.voteTerm n u1' $$ [HVoteTerm] as %vtl #Hvtl
    · iframe HVoteTerm; ipureintro; exact ⟨Hn, by rw [HWf.len_voteTerm]; exact Hlt⟩
    try wp_auto
    rw [Hu1']
    wp_apply wp_set_voteTerm q { s with currentTerm := s.currentTerm.set (sint.nat n) t1 } vtl (s.voteTerm.set (sint.nat n) t1)
      (by rw [List.length_set, HWf.len_voteTerm]) $$ [Hq Hvtl] as Hq
    · iframe Hq Hvtl
    try wp_auto
    wp_apply wp_Event_vote pw X.w v $$ [Hw]
    · iframe Hw; ipureintro; exact hv
    try wp_auto
    wp_apply wp_setStr g.VoteFor' s.voteFor n v $$ [HVoteFor] as %vfl #Hvfl
    · iframe HVoteFor; ipureintro; exact ⟨Hn, by rw [HWf.len_voteFor]; exact Hlt⟩
    try wp_auto
    wp_apply wp_set_voteFor q { { s with currentTerm := s.currentTerm.set (sint.nat n) t1 } with
        voteTerm := s.voteTerm.set (sint.nat n) t1 } vfl (s.voteFor.set (sint.nat n) v)
      (by rw [List.length_set, HWf.len_voteFor]) $$ [Hq Hvfl] as Hq
    · iframe Hq Hvfl
    try wp_auto
    wp_join_done
    have : ({ { { s with currentTerm := s.currentTerm.set (sint.nat n) t1 } with
        voteTerm := s.voteTerm.set (sint.nat n) t1 } with voteFor := s.voteFor.set (sint.nat n) v } : State) =
        ns0 X t1 true (OnDiskProofLaws.vf0 X true) := by
      have hw : X.w.vote = some v := need_ok hv
      simp only [ns0, OnDiskProofLaws.vf0, ite_true, hw, Option.getD_some]
      subst hX; rfl
    rw [this]; iexact Hq
  -- u1: `ns.Log = setLog(s.Log, n, x.L1()); ns.CommitIndex = …; ns.Role = ro; ns.Confirmed = …`
  obtain ⟨L1, cm, cf1, el, hL1, hcm, hcf1, hel, Ho⟩ := u1_ok Ho
  rw [hXs, hXn, hXro] at Ho
  generalize hS1 : ns0 X t1 vd (OnDiskProofLaws.vf0 X vd) = S1 at Ho ⊢
  odm L1
  wp_apply wp_L1 _ X L1 $$ [Hx] as %l1 #Hl1
  · iframe Hx; ipureintro; exact hL1
  try wp_auto
  wp_apply wp_setLog g.Log' s.log n l1 L1 $$ [HLog Hl1] as %lgl #Hlgl
  · iframe HLog Hl1; ipureintro; exact ⟨Hn, by rw [HWf.len_log]; exact Hlt⟩
  try wp_auto
  wp_apply wp_set_log q S1 lgl (s.log.set (sint.nat n) L1)
    (by rw [List.length_set, HWf.len_log, ← hS1]; subst hX; rfl) $$ [Hq Hlgl] as Hq
  · iframe Hq Hlgl
  try wp_auto
  wp_apply wp_Event_commit pw X.w cm $$ [Hw] as %uc %Huc
  · iframe Hw; ipureintro; exact hcm
  try wp_auto
  wp_apply wp_setInt g.CommitIndex' s.commitIndex n uc $$ [HCommitIndex] as %cil #Hcil
  · iframe HCommitIndex; ipureintro; exact ⟨Hn, by rw [HWf.len_commitIndex]; exact Hlt⟩
  try wp_auto
  rw [Huc]
  wp_apply wp_set_commitIndex q { S1 with log := s.log.set (sint.nat n) L1 } cil (s.commitIndex.set (sint.nat n) cm)
    (by rw [List.length_set, HWf.len_commitIndex, ← hS1]; subst hX; rfl) $$ [Hq Hcil] as Hq
  · iframe Hq Hcil
  try wp_auto
  wp_apply wp_set_role q { { S1 with log := s.log.set (sint.nat n) L1 } with
      commitIndex := s.commitIndex.set (sint.nat n) cm } rol ro
    (by rw [Hrol, ← hS1]; subst hX; rfl) $$ [Hq Hro] as Hq
  · iframe Hq Hro
  try wp_auto
  have hcfg1 : S1.cfg = s.cfg := by rw [← hS1]; subst hX; rfl
  generalize hS2 : ({ { { S1 with log := s.log.set (sint.nat n) L1 } with
      commitIndex := s.commitIndex.set (sint.nat n) cm } with role := ro } : State) = S2
  have hcfg2 : S2.cfg = s.cfg := by rw [← hS2]; exact hcfg1
  odm conf1
  wp_apply wp_conf1 _ X cf1 $$ [Hx] as %gcf %Hgcf
  · iframe Hx; ipureintro; exact hcf1
  try wp_auto
  wp_apply wp_setConfirmed g.Confirmed' s.confirmed n gcf cf1 $$ [HConfirmed] as %cfl #Hcfl
  · iframe HConfirmed; ipureintro; exact ⟨Hgcf, Hn, by rw [HWf.len_confirmed]; exact Hlt⟩
  try wp_auto
  wp_apply wp_set_confirmed q S2 cfl (s.confirmed.set (sint.nat n) cf1)
    (by rw [List.length_set, HWf.len_confirmed, hcfg2]) $$ [Hq Hcfl] as Hq
  · iframe Hq Hcfl
  try wp_auto
  generalize hS3 : ({ S2 with confirmed := s.confirmed.set (sint.nat n) cf1 } : State) = S3
  have hcfg3 : S3.cfg = s.cfg := by rw [← hS3]; exact hcfg2
  -- `msgs := s.Msgs; if x.elect() { msgs = factsAdd(msgs, s.VoteRequest(n, x.T1())) }`
  have hml := HW.1.msgs_len; rw [hXs] at hml
  wp_join (v := executeVal) iprop(∃ ml, msgs_ptr ↦ ml ∗
      factsRO ml (if el then lset.add s.msgs (s.voteRequest (sint.nat n) t1) else s.msgs))
    at next with [msgs] as ⟨%ml, msgs, #Hml⟩
  · odm elect
    wp_apply wp_elect _ X el $$ [Hx]
    · iframe Hx; ipureintro; exact hel
    cases el
    · try wp_auto
      wp_join_done
      simp only [Bool.false_eq_true, ite_false]
      iexists _; iframe; iexact HMsgs
    try wp_auto
    odm T1
    wp_apply wp_T1 _ X t1 $$ [Hx] as %u1 %Hu1
    · iframe Hx; ipureintro; exact ht1
    try wp_auto
    wp_apply wp_SVoteRequest p s n u1 $$ [Hs] as %gvr %Hgvr
    · iframe Hs; ipureintro; exact ⟨Hn, Hlt⟩
    rw [Hu1] at Hgvr
    try wp_auto
    wp_apply wp_factsAdd g.Msgs' s.msgs gvr _ $$ [HMsgs] as %ml1 #Hml1
    · iframe HMsgs; ipureintro; exact ⟨Hgvr, by unfold numBound at hb; omega⟩
    try wp_auto
    wp_join_done
    simp only [ite_true]
    iexists _; iframe; iexact Hml1
  -- u2: `if x.acks() { msgs = factsAdd(msgs, AckFact(me, x.f().Src, x.T1(), x.ackAt())) }`
  obtain ⟨msgs2, Ho, hmsgs2⟩ := u2_ok Ho
  rw [hXs, hXn] at hmsgs2
  have hm1l : ((if el then lset.add s.msgs (s.voteRequest (sint.nat n) t1) else s.msgs).length : Int) ≤ 2 * b + 1 := by
    split
    · have := lset_add_len s.msgs (s.voteRequest (sint.nat n) t1); omega
    · omega
  wp_join (v := executeVal) iprop(∃ ml, msgs_ptr ↦ ml ∗ factsRO ml msgs2) at next with [msgs] as ⟨%ml2, msgs, #Hml2⟩
  · rcases hmsgs2 with ⟨hac, rfl⟩ | ⟨f, a, hac, hf, ha, rfl⟩
    · odm acks
      wp_apply wp_acks _ X false $$ [Hx]
      · iframe Hx; ipureintro; exact hac
      try wp_auto
      wp_join_done
      iexists _; iframe; iexact Hml
    odm acks
    wp_apply wp_acks _ X true $$ [Hx]
    · iframe Hx; ipureintro; exact hac
    try wp_auto
    odm f
    wp_apply wp_f _ X f $$ [Hx] as %gf #Hf
    · iframe Hx; ipureintro; exact hf
    try wp_auto
    odm T1
    wp_apply wp_T1 _ X t1 $$ [Hx] as %u1 %Hu1
    · iframe Hx; ipureintro; exact ht1
    try wp_auto
    odm ackAt
    wp_apply wp_ackAt _ X a $$ [Hx] as %ua %Hua
    · iframe Hx; ipureintro; exact ha
    try wp_auto
    iunfold appendFactRO at Hf
    icases Hf with ⟨%Hfr, #-⟩
    rw [Hfr.1]
    wp_apply wp_AckFact (s.cfg.server[sint.nat n]!) f.src u1 ua as %gak %Hgak
    rw [Hu1, Hua] at Hgak
    try wp_auto
    wp_apply wp_factsAdd ml _ gak _ $$ [Hml] as %ml1 #Hml1
    · iframe Hml; ipureintro; exact ⟨Hgak, by unfold numBound at hb; omega⟩
    try wp_auto
    wp_join_done
    iexists _; iframe; iexact Hml1
  wp_apply wp_set_msgs q S3 ml2 msgs2 $$ [Hq Hml2] as Hq
  · iframe Hq Hml2
  try wp_auto
  generalize hS4 : ({ S3 with msgs := msgs2 } : State) = S4
  have hcfg4 : S4.cfg = s.cfg := by rw [← hS4]; exact hcfg3
  -- u3: `votes := s.Votes; if x.voted() { votes = votesAdd(votes, VoteRec{me, x.T1(), w.vote()}) }`
  obtain ⟨hvv3, Ho⟩ := OnDiskProofLaws.u3_ok'' Ho
  have hvl := HW.1.votes_len; rw [hXs] at hvl
  wp_join (v := executeVal) iprop(∃ vl, votes_ptr ↦ vl ∗ votesRO vl (OnDiskProofLaws.votes3 X t1 vd))
    at next with [votes] as ⟨%vl3, votes, #Hvl3⟩
  · odm voted
    wp_apply wp_voted _ X vd $$ [Hx]
    · iframe Hx; ipureintro; exact hvd
    cases vd
    · try wp_auto
      wp_join_done
      unfold OnDiskProofLaws.votes3
      simp only [Bool.false_eq_true, ite_false]
      rw [hXs]
      iexists _; iframe; iexact HVotes
    obtain ⟨v, hv⟩ := hvv3 rfl
    try wp_auto
    odm T1
    wp_apply wp_T1 _ X t1 $$ [Hx] as %u1 %Hu1
    · iframe Hx; ipureintro; exact ht1
    try wp_auto
    wp_apply wp_Event_vote pw X.w v $$ [Hw]
    · iframe Hw; ipureintro; exact hv
    try wp_auto
    wp_apply wp_votesAdd g.Votes' s.votes _ { voter := s.cfg.server[sint.nat n]!, term := t1, cand := v } $$ [HVotes]
      as %vl1 #Hvl1
    · iframe HVotes; ipureintro
      refine ⟨⟨rfl, Hu1, rfl⟩, by unfold numBound at hb; omega⟩
    try wp_auto
    wp_join_done
    have hw : X.w.vote = some v := need_ok hv
    unfold OnDiskProofLaws.votes3
    simp only [ite_true, hw, Option.getD_some, hXs, hXn]
    iexists _; iframe; iexact Hvl1
  wp_apply wp_set_votes q S4 vl3 _ $$ [Hq Hvl3] as Hq
  · iframe Hq Hvl3
  try wp_auto
  wp_apply wp_set_leaders q { S4 with votes := OnDiskProofLaws.votes3 X t1 vd } ldl ld $$ [Hq Hld] as Hq
  · iframe Hq Hld
  try wp_auto
  wp_apply wp_set_ledLog q { { S4 with votes := OnDiskProofLaws.votes3 X t1 vd } with leaders := ld } lll ll
    $$ [Hq Hll] as Hq
  · iframe Hq Hll
  try wp_auto
  generalize hS5 : ({ { { S4 with votes := OnDiskProofLaws.votes3 X t1 vd } with leaders := ld } with
    ledLog := ll } : State) = S5
  have hcfg5 : S5.cfg = s.cfg := by rw [← hS5]; exact hcfg4
  have hS5m : S5.msgs = msgs2 := by rw [← hS5, ← hS4]
  have hS5v : S5.votes = OnDiskProofLaws.votes3 X t1 vd := by rw [← hS5]
  -- `pre := &Pre{Term: x.T0(), VoteTerm: s.VoteTerm[n], …, Msgs: factsMinus(ns.Msgs, s.Msgs), Votes: …}`
  odm T0
  wp_apply wp_T0 _ X $$ [Hx] as %ut0 %Hut0
  · iexact Hx
  icases intsRO_at g.VoteTerm' s.voteTerm n ⟨Hn, by rw [HWf.len_voteTerm]; exact Hlt⟩ $$ HVoteTerm
    with ⟨%wvt, #Hwvta, %Hwvt⟩
  try wp_auto
  wp_apply wp_load_at _ _ wvt Hn $$ [Hwvta]
  · iexact Hwvta
  ihave #Hwvfa := strsRO_at g.VoteFor' s.voteFor n ⟨Hn, by rw [HWf.len_voteFor]; exact Hlt⟩ $$ HVoteFor
  try wp_auto
  wp_apply wp_load_at _ _ _ Hn $$ [Hwvfa] as -
  · iexact Hwvfa
  icases intsRO_at g.CommitIndex' s.commitIndex n ⟨Hn, by rw [HWf.len_commitIndex]; exact Hlt⟩ $$ HCommitIndex
    with ⟨%wci, #Hwcia, %Hwci⟩
  try wp_auto
  wp_apply wp_load_at _ _ wci Hn $$ [Hwcia]
  · iexact Hwcia
  icases confirmedsRO_at g.Confirmed' s.confirmed n ⟨Hn, by rw [HWf.len_confirmed]; exact Hlt⟩ $$ HConfirmed
    with ⟨%wcf, #Hwcfa, %Hwcf⟩
  try wp_auto
  wp_apply wp_load_at _ _ wcf Hn $$ [Hwcfa]
  · iexact Hwcfa
  icases OnDiskProofLaws.stateOwn_msgs_votes q S5 $$ Hq with ⟨%gq, Hqp, #HqM, #HqV, Hqc⟩
  try wp_auto
  wp_apply wp_factsMinus gq.Msgs' S5.msgs g.Msgs' s.msgs $$ [HqM HMsgs] as %pm #Hpm
  · iframe HqM HMsgs
  try wp_auto
  wp_apply wp_votesMinus gq.Votes' S5.votes g.Votes' s.votes $$ [HqV HVotes] as %pv #Hpv
  · iframe HqV HVotes
  ihave Hq := Hqc $$ Hqp
  try wp_auto
  ihave Hpo : OnDiskProofLaws.preOwn «$r0_ptr» (OnDiskProofLaws.pre0' X S5.msgs S5.votes) $$ [«$r0»]
  · iunfold OnDiskProofLaws.preOwn
    iexists _
    iframe «$r0»
    unfold OnDiskProofLaws.pre0'
    rw [hXs, hXn]
    dsimp only
    isplitr
    · ipureintro; exact ⟨Hut0, Hwvt, rfl, Hwci, rfl, Hwcf, rfl, rfl⟩
    isplitl []
    · iapply Init0_logNil
    iframe Hpm Hpv
    iapply Init0_factsNil
  ipersist pre
  -- u4: `if x.stores() { pre.Keep = x.first() - 1; pre.Suffix = SubSeq(x.L0(), x.first(), len(x.L0())) } else { pre.Keep = len(x.L0()) }`
  obtain ⟨pre4, Ho, hpre4⟩ := u4_ok Ho
  rw [OnDiskProofLaws.pre0_eq] at hpre4
  dsimp only at hpre4
  rw [← hS5m, ← hS5v] at hpre4
  wp_join (v := executeVal) iprop(OnDiskProofLaws.preOwn «$r0_ptr» pre4) at next with [Hpo] as Hpo
  · iunfold OnDiskProofLaws.preOwn at Hpo
    icases Hpo with ⟨%gp, Hpl, %Hpr, #Hps, #Hpms, #Hpvs, #Hpas⟩
    obtain ⟨h1, h2, h3, h4, -, h6, h7, h8⟩ := Hpr
    rcases hpre4 with ⟨hst, rfl⟩ | ⟨fi, suf, hst, hfi, hsuf, rfl⟩
    · odm stores
      wp_apply wp_stores _ X false $$ [Hx]
      · iframe Hx; ipureintro; exact hst
      try wp_auto
      odm L0
      wp_apply wp_L0 _ X $$ [Hx] as %gl0 #Hl0
      · iexact Hx
      ihave %Hl0l := logRO_len _ _ $$ Hl0
      try wp_auto
      wp_join_done
      iunfold OnDiskProofLaws.preOwn
      iexists _; iframe Hpl Hps Hpms Hpvs Hpas
      ipureintro
      exact ⟨h1, h2, h3, h4, Hl0l, h6, h7, h8⟩
    have hfb := first_bigOk HW hb hfi
    unfold bigOk at hfb
    odm stores
    wp_apply wp_stores _ X true $$ [Hx]
    · iframe Hx; ipureintro; exact hst
    try wp_auto
    odm first
    wp_apply wp_first _ X fi $$ [Hx] as %ufi %Hufi
    · iframe Hx; ipureintro; exact hfi
    try wp_auto
    odm L0
    wp_apply wp_L0 _ X $$ [Hx] as %gl0 #Hl0
    · iexact Hx
    try wp_auto
    odm first
    wp_apply wp_first _ X fi $$ [Hx] as %ufi' %Hufi'
    · iframe Hx; ipureintro; exact hfi
    try wp_auto
    odm L0
    wp_apply wp_L0 _ X $$ [Hx] as %gl0' #Hl0'
    · iexact Hx
    ihave %Hl0l := logRO_len _ _ $$ Hl0'
    try wp_auto
    wp_apply wp_SubSeq gl0 X.L0 ufi' gl0'.len suf $$ [Hl0] as %gsuf #Hsuf
    · iframe Hl0; ipureintro; rw [Hufi', Hl0l]; exact hsuf
    try wp_auto
    wp_join_done
    iunfold OnDiskProofLaws.preOwn
    iexists _; iframe Hpl Hsuf Hpms Hpvs Hpas
    ipureintro
    refine ⟨h1, h2, h3, h4, ?_, h6, h7, h8⟩
    dsimp only
    rw [sint_sub (by rw [Hufi, sint_one]; omega) (by rw [Hufi, sint_one]; omega), Hufi, sint_one]
  -- u5: `if x.acks() { pre.Acks = []Fact{AckFact(me, x.f().Src, x.T1(), x.ackAt())} }`
  obtain ⟨pre5, Ho, hpre5⟩ := u5_ok Ho
  rw [hXs, hXn] at hpre5
  wp_join (v := executeVal) iprop(OnDiskProofLaws.preOwn «$r0_ptr» pre5) at next with [Hpo] as Hpo
  · rcases hpre5 with ⟨hac, rfl⟩ | ⟨f, a, hac, hf, ha, rfl⟩
    · odm acks
      wp_apply wp_acks _ X false $$ [Hx]
      · iframe Hx; ipureintro; exact hac
      try wp_auto
      wp_join_done
    iunfold OnDiskProofLaws.preOwn at Hpo
    icases Hpo with ⟨%gp, Hpl, %Hpr, #Hps, #Hpms, #Hpvs, #-⟩
    odm acks
    wp_apply wp_acks _ X true $$ [Hx]
    · iframe Hx; ipureintro; exact hac
    try wp_auto
    odm f
    wp_apply wp_f _ X f $$ [Hx] as %gf #Hf
    · iframe Hx; ipureintro; exact hf
    try wp_auto
    odm T1
    wp_apply wp_T1 _ X t1 $$ [Hx] as %u1 %Hu1
    · iframe Hx; ipureintro; exact ht1
    try wp_auto
    odm ackAt
    wp_apply wp_ackAt _ X a $$ [Hx] as %ua %Hua
    · iframe Hx; ipureintro; exact ha
    try wp_auto
    iunfold appendFactRO at Hf
    icases Hf with ⟨%Hfr, #-⟩
    rw [Hfr.1]
    wp_apply wp_AckFact (s.cfg.server[sint.nat n]!) f.src u1 ua as %gak %Hgak
    rw [Hu1, Hua] at Hgak
    try wp_auto
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sla ⟨Hsla, -⟩
    imod ownSlice_persist $$ Hsla with #Hsla
    try wp_auto
    wp_join_done
    iunfold OnDiskProofLaws.preOwn
    iexists _; iframe Hpl Hps Hpms Hpvs
    isplitr
    · ipureintro; exact Hpr
    iunfold factsRO
    iexists [gak]; iframe Hsla
    ipureintro; exact List.Forall₂.cons Hgak List.Forall₂.nil
  -- u6: `if x.stores() { pre.Low = x.first() }`
  obtain ⟨pre6, Ho, hpre6⟩ := u6_ok Ho
  wp_join (v := executeVal) iprop(OnDiskProofLaws.preOwn «$r0_ptr» pre6) at next with [Hpo] as Hpo
  · rcases hpre6 with ⟨hst, rfl⟩ | ⟨fi, hst, hfi, rfl⟩
    · odm stores
      wp_apply wp_stores _ X false $$ [Hx]
      · iframe Hx; ipureintro; exact hst
      try wp_auto
      wp_join_done
    iunfold OnDiskProofLaws.preOwn at Hpo
    icases Hpo with ⟨%gp, Hpl, %Hpr, #Hps, #Hpms, #Hpvs, #Hpas⟩
    obtain ⟨h1, h2, h3, h4, h5, h6, -, h8⟩ := Hpr
    odm stores
    wp_apply wp_stores _ X true $$ [Hx]
    · iframe Hx; ipureintro; exact hst
    try wp_auto
    odm first
    wp_apply wp_first _ X fi $$ [Hx] as %ufi %Hufi
    · iframe Hx; ipureintro; exact hfi
    try wp_auto
    wp_join_done
    iunfold OnDiskProofLaws.preOwn
    iexists _; iframe Hpl Hps Hpms Hpvs Hpas
    ipureintro
    exact ⟨h1, h2, h3, h4, h5, h6, Hufi, h8⟩
  -- u7: `if !more { ns.Undo = setPre(s.Undo, n, pre) } else { u := *s.Undo[n]; nu := u; … ns.Undo = setPre(s.Undo, n, &nu) }`
  have hmm : (lset.minus S5.msgs X.s.msgs).length ≤ 2 := by
    rw [hS5m, hXs]
    refine OnDiskProofLaws.minus_two (el := el) (v := s.voteRequest (sint.nat n) t1) ?_
    rcases hmsgs2 with ⟨_, h⟩ | ⟨f, a, _, _, _, h⟩
    · exact .inl h
    · exact .inr ⟨_, h⟩
  have hvv : (S5.votes.length : Int) ≤ b + 1 := by
    rw [hS5v]; unfold OnDiskProofLaws.votes3; rw [hXs]
    split
    · refine Int.le_trans (Int.ofNat_le.2 (lset_add_len _ _)) ?_; push_cast; omega
    · omega
  obtain ⟨hk6, huk, hL0b, husb, hum6, huv6, hua6⟩ := OnDiskProofLaws.u7_bounds HW hb hmm hvv hpre4 hpre5 hpre6
  rw [hXs, hXn] at huk husb hum6 huv6 hua6
  obtain ⟨p7, Ho, hp7⟩ := u7_ok Ho
  rw [hXs, hXn, hXmore] at hp7
  rw [hXs, hXn] at Ho
  wp_join (v := executeVal) iprop(stateOwn q { S5 with undo := s.undo.set (sint.nat n) (some p7) })
    at next with [Hq Hpo] as Hq
  · iunfold OnDiskProofLaws.preOwn at Hpo
    icases Hpo with ⟨%gp, Hpl, %Hpr, #Hps, #Hpms, #Hpvs, #Hpas⟩
    rcases hp7 with ⟨hmf, rfl⟩ | ⟨suf, hmt, rfl, hsuf⟩
    · subst hmf
      try wp_auto
      ipersist Hpl
      ihave #Hpre : preRO «$r0_ptr» (some p7) $$ []
      · iunfold preRO; iexists gp; iframe Hpl Hps Hpms Hpvs Hpas; ipureintro; exact Hpr
      wp_apply wp_setPre g.Undo' s.undo n «$r0_ptr» (some p7) $$ [HUndo Hpre] as %ul #Hul
      · iframe HUndo Hpre; ipureintro; exact ⟨Hn, by rw [HWf.len_undo]; exact Hlt⟩
      try wp_auto
      wp_apply wp_set_undo q S5 ul (s.undo.set (sint.nat n) (some p7)) (by rw [List.length_set, HWf.len_undo, hcfg5]) $$ [Hq Hul] as Hq
      · iframe Hq Hul
      try wp_auto
      wp_join_done
    subst hmt
    have hpu : ∃ pu, s.undo[sint.nat n]! = some pu := by
      cases h : s.undo[sint.nat n]! with
      | none => rw [h] at hcu; simp at hcu
      | some pu => exact ⟨pu, rfl⟩
    obtain ⟨pu, hpu⟩ := hpu
    rw [hpu] at hsuf huk husb hum6 huv6 hua6
    simp only [Option.getD_some] at hsuf huk husb hum6 huv6 hua6
    rw [hpu]
    simp only [Option.getD_some]
    iunfold preRO at Hu
    icases Hu with ⟨%gu, #Hgu, %Hgur, #Hgus, #Hgum, #Hguv, #Hgua⟩
    try wp_auto
    wp_apply wp_load_at _ _ _ Hn $$ [Hua] as -
    · iexact Hua
    try wp_auto
    have hgk : sint.Z gu.Keep' = pu.keep := Hgur.2.2.2.2.1
    have hpk : sint.Z gp.Keep' = pre6.keep := Hpr.2.2.2.2.1
    wp_apply wp_Min gu.Keep' gp.Keep' as %wk %Hwk
    try wp_auto
    wp_join (v := executeVal) iprop(∃ sl, nu_ptr ↦ ({ gu with Keep' := wk, Suffix' := sl } : G.Pre) ∗ logRO sl suf ∗ u_ptr ↦ gu ∗ «$r0_ptr» ↦ gp)
      at next with [nu u Hpl] as ⟨%sls, nu, #Hsls, u, Hpl⟩
    · try wp_auto
      wp_if_destruct
      · obtain ⟨-, rfl⟩ : pre6.keep ≥ pu.keep ∧ suf = pu.suffix := by
          rcases hsuf with h | ⟨hlt, -⟩
          · exact h
          · exfalso; rw [← hgk, ← hpk] at hlt; omega
        try wp_auto
        wp_join_done
        iexists _; iframe nu u Hpl; iexact Hgus
      rcases hsuf with ⟨hge, -⟩ | ⟨hlt, l, hl, rfl⟩
      · exfalso; rw [← hgk, ← hpk] at hge; omega
      odm L0
      wp_apply wp_L0 _ X $$ [Hx] as %gl0 #Hl0
      · iexact Hx
      try wp_auto
      wp_apply wp_SubSeq gl0 X.L0 (gp.Keep' + W64 1) gu.Keep' l $$ [Hl0] as %gsl #Hsl
      · iframe Hl0; ipureintro
        unfold bigOk at hk6
        rw [sint_add_one (by omega), hpk, hgk]; exact hl
      try wp_auto
      have hll := subSeq_length_le hl
      wp_apply wp_Concat gsl l gu.Suffix' pu.suffix $$ [Hsl Hgus] as %gcat #Hcat
      · iframe Hsl Hgus; ipureintro; omega
      try wp_auto
      wp_join_done
      iexists _; iframe nu u Hpl; iexact Hcat
    wp_apply wp_factsUnion gu.Msgs' pu.msgs gp.Msgs' pre6.msgs $$ [Hgum Hpms] as %gm7 #Hgm7
    · iframe Hgum Hpms; ipureintro; exact hum6
    try wp_auto
    wp_apply wp_votesUnion gu.Votes' pu.votes gp.Votes' pre6.votes $$ [Hguv Hpvs] as %gv7 #Hgv7
    · iframe Hguv Hpvs; ipureintro; exact huv6
    try wp_auto
    wp_apply wp_factsUnion gu.Acks' pu.acks gp.Acks' pre6.acks $$ [Hgua Hpas] as %ga7 #Hga7
    · iframe Hgua Hpas; ipureintro; exact hua6
    try wp_auto
    wp_apply wp_Lowest gu.Low' gp.Low' as %wl %Hwl
    try wp_auto
    ipersist nu
    ihave #Hnu : preRO nu_ptr (some (nuOf pu pre6 suf)) $$ []
    · iunfold preRO
      iexists ({ gu with Keep' := wk, Suffix' := sls, Msgs' := gm7, Votes' := gv7, Acks' := ga7, Low' := wl } : G.Pre)
      dsimp only [nuOf]
      isplitr
      · iexact nu
      isplitr
      · ipureintro
        refine ⟨Hgur.1, Hgur.2.1, Hgur.2.2.1, Hgur.2.2.2.1, ?_, Hgur.2.2.2.2.2.1, ?_, Hgur.2.2.2.2.2.2.2⟩
        · rw [Hwk, hgk, hpk]
        · rw [Hwl, Hgur.2.2.2.2.2.2.1, Hpr.2.2.2.2.2.2.1]
      isplitr
      · iexact Hsls
      isplitr
      · iexact Hgm7
      isplitr
      · iexact Hgv7
      iexact Hga7
    wp_apply wp_setPre g.Undo' s.undo n nu_ptr (some (nuOf pu pre6 suf)) $$ [HUndo Hnu] as %ul #Hul
    · iframe HUndo Hnu; ipureintro; exact ⟨Hn, by rw [HWf.len_undo]; exact Hlt⟩
    try wp_auto
    wp_apply wp_set_undo q S5 ul (s.undo.set (sint.nat n) (some (nuOf pu pre6 suf)))
      (by rw [List.length_set, HWf.len_undo, hcfg5]) $$ [Hq Hul] as Hq
    · iframe Hq Hul
    try wp_auto
    wp_join_done
  -- u8: `ns.Chain = x.ch1(); if x.adv() { ns.TermLen = tl.With(x.T1(), Max(x.old(), len(x.newC()))) } else { ns.TermLen = tl }`
  obtain ⟨c1, tl', hc1, Ho, htl'⟩ := u8_ok Ho
  generalize hS6 : ({ S5 with undo := s.undo.set (sint.nat n) (some p7) } : State) = S6 at Ho ⊢
  have hcfg6 : S6.cfg = s.cfg := by rw [← hS6]; exact hcfg5
  odm ch1
  wp_apply wp_ch1 _ X c1 $$ [Hx] as %gc1 #Hc1
  · iframe Hx; ipureintro; exact hc1
  try wp_auto
  wp_apply wp_set_chain q S6 gc1 c1 $$ [Hq Hc1] as Hq
  · iframe Hq Hc1
  try wp_auto
  have htlw := HW.2.2.2.2.2.2.2.2.2.1
  rw [hXtl] at htlw
  wp_join (v := executeVal) iprop(stateOwn q { { S6 with chain := c1 } with termLen := tl' }) at next with [Hq] as Hq
  · rcases htl' with ⟨had, rfl⟩ | ⟨o', nc, had, ho, hnc, rfl⟩
    · odm adv
      wp_apply wp_adv _ X false $$ [Hx]
      · iframe Hx; ipureintro; exact had
      try wp_auto
      try rw [hXtl]
      wp_apply wp_set_termLen q { S6 with chain := c1 } tll tl $$ [Hq Htl] as Hq
      · iframe Hq Htl
      try wp_auto
      wp_join_done
    odm adv
    wp_apply wp_adv _ X true $$ [Hx]
    · iframe Hx; ipureintro; exact had
    try wp_auto
    odm T1
    wp_apply wp_T1 _ X t1 $$ [Hx] as %u1 %Hu1
    · iframe Hx; ipureintro; exact ht1
    try wp_auto
    odm old
    wp_apply wp_old _ X o' $$ [Hx] as %uo %Huo
    · iframe Hx; ipureintro; exact ho
    try wp_auto
    odm newC
    wp_apply wp_newC _ X nc $$ [Hx] as %gnc #Hnc
    · iframe Hx; ipureintro; exact hnc
    ihave %Hncl := logRO_len _ _ $$ Hnc
    try wp_auto
    wp_apply wp_Max uo gnc.len as %um %Hum
    try wp_auto
    smu TermInts With
    wp_apply wp_TermInts_With tll tl u1 um $$ [Htl] as %tl2 #Htl2
    · iframe Htl; ipureintro; have := htlw.1; omega
    try wp_auto
    rw [Hu1, Hum, Huo, Hncl]
    try rw [hXtl]
    wp_apply wp_set_termLen q { S6 with chain := c1 } tl2 _ $$ [Hq Htl2] as Hq
    · iframe Hq Htl2
    try wp_auto
    wp_join_done
  -- v1: `viol := vi; if x.adv() && !Comparable(ch, x.newC()) { viol = violAdd(viol, "CommitSafety") }`
  generalize hS7 : ({ { S6 with chain := c1 } with termLen := tl' } : State) = S7 at Ho ⊢
  obtain ⟨sF, hoF⟩ := OnDiskProofLaws.u9_isSome Ho
  have hSF : StoresFit X := (chain_some (hoF ▸ Ho0)).2
  unfold u9 at Ho
  obtain ⟨cs, hcs, Ho⟩ := OnDiskProofLaws.v1_ok' Ho
  have hvil := HW.2.2.2.2.2.2.2.2.2.2
  rw [hXvi] at hvil Ho
  try wp_auto
  wp_join (v := executeVal) iprop(∃ vl, viol_ptr ↦ vl ∗ strsRO vl (if cs then setAdd vi go!"CommitSafety" else vi))
    at next with [viol] as ⟨%vl1, viol, #Hvl1⟩
  · obtain ⟨ad, had, hadt, hadf⟩ := andM_ok hcs
    odm adv
    wp_apply wp_adv _ X ad $$ [Hx]
    · iframe Hx; ipureintro; exact had
    cases ad
    · rw [hadf rfl]
      try wp_auto
      wp_join_done
      simp only [Bool.false_eq_true, ite_false]
      iexists _; iframe; iexact Hvi
    have h2 := hadt rfl
    unfold notM at h2
    obtain ⟨cp, hcp, h2⟩ := bind_ok h2
    simp only [pure_ok, Except.ok.injEq] at h2
    obtain ⟨nc, hnc, hcp⟩ := bind_ok hcp
    try wp_auto
    odm newC
    wp_apply wp_newC _ X nc $$ [Hx] as %gnc #Hnc
    · iframe Hx; ipureintro; exact hnc
    try wp_auto
    wp_apply wp_Comparable chl ch gnc nc cp $$ [Hch Hnc]
    · iframe Hch Hnc; ipureintro; rw [← hXch]; exact hcp
    subst h2
    cases cp
    · try wp_auto
      wp_apply wp_violAdd vil vi _ $$ [Hvi] as %vl #Hvl
      · iframe Hvi; ipureintro; omega
      try wp_auto
      wp_join_done
      simp only [Bool.not_false, ite_true]
      iexists _; iframe; iexact Hvl
    · try wp_auto
      wp_join_done
      simp only [Bool.not_true, Bool.false_eq_true, ite_false]
      iexists _; iframe; iexact Hvi
  -- v2: `if x.adv() { for _, p := range ll { if p.T > x.T1() && !IsPrefix(x.newC(), p.L) {
  --   viol = violAdd(viol, "LeaderCompleteness"); break } } }`
  obtain ⟨viol2, Ho, ad2, had2, had2f, had2t⟩ := OnDiskProofLaws.v2_ok'' Ho
  rw [hXll] at had2t
  have hv1l := OnDiskProofLaws.setAddIf_len cs vi go!"CommitSafety"
  wp_join (v := executeVal) iprop(∃ vl, viol_ptr ↦ vl ∗ strsRO vl viol2) at next with [viol] as ⟨%vl2, viol, #Hvl2⟩
  · odm adv
    wp_apply wp_adv _ X ad2 $$ [Hx]
    · iframe Hx; ipureintro; exact had2
    cases ad2
    · rw [had2f rfl]
      try wp_auto
      wp_join_done
      iexists _; iframe; iexact Hvl1
    obtain ⟨lc, hlc, rfl⟩ := had2t rfl
    try wp_auto
    ihave #Hll2 := Hll
    iunfold termLogsRO at Hll2
    icases Hll2 with ⟨%gls, #Hgls, #Hglb⟩
    ihave %Hlll := sliceRO_len (fun (g : G.TermLog) (p : Int × List Entry) => iprop(⌜sint.Z g.T' = p.1⌝ ∗ logRO g.L' p.2))
      lll gls ll $$ [Hgls Hglb]
    · iframe Hgls Hglb
    ihave IH : iprop(∃ (i : w64) (gpv : G.TermLog),
        "i" ∷ i_ptr ↦ i ∗ "p" ∷ p_ptr ↦ gpv ∗ "viol" ∷ viol_ptr ↦ vl1 ∗
        "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z lll.len ∧ anyM (ll.drop (sint.nat i))
          (fun p => andM (pure (decide (p.1 > t1))) (notM (do isPrefix (← X.newC) p.2))) = .ok lc⌝) $$ [i p viol]
    · iexists _, _
      iframe
      ipureintro
      refine ⟨by word, by word, ?_⟩
      rw [show sint.nat (W64 0) = 0 by word, List.drop_zero]; exact hlc
    wp_for IH
    obtain ⟨hi0, hi1, hany⟩ := Hi
    wp_if_destruct
    · have Hil : sint.nat i < ll.length := by have := sint_nat_cast hi0; omega
      icases sliceRO_at (fun (g : G.TermLog) (p : Int × List Entry) => iprop(⌜sint.Z g.T' = p.1⌝ ∗ logRO g.L' p.2))
        lll gls ll i ⟨hi0, by omega⟩ $$ [Hgls Hglb] with ⟨%gi, #Hgi, %HgiT, #HgiL⟩
      · iframe Hgls Hglb
      wp_apply wp_load_at _ _ _ hi0 $$ [Hgi] as -
      · iexact Hgi
      try wp_auto
      obtain ⟨y, hy, hyt, hyf⟩ := OnDiskProofLaws.anyM_drop_step Hil hany
      have hget : ll[sint.nat i]! = ll[sint.nat i] := by
        rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem Hil]; rfl
      rw [← hget] at hy
      obtain ⟨gt, hgt, hgtt, hgtf⟩ := andM_ok hy
      simp only [pure_ok, Except.ok.injEq] at hgt
      odm T1
      wp_apply wp_T1 _ X t1 $$ [Hx] as %u1 %Hu1
      · iframe Hx; ipureintro; exact ht1
      try wp_auto
      have hcont : y = false → ∀ gpv : G.TermLog,
          (i_ptr ↦ (i + W64 1) ∗ p_ptr ↦ gpv ∗ viol_ptr ↦ vl1 : IProp GF) ⊢ iprop(∃ (i : w64) (gpv : G.TermLog),
            "i" ∷ i_ptr ↦ i ∗ "p" ∷ p_ptr ↦ gpv ∗ "viol" ∷ viol_ptr ↦ vl1 ∗
            "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z lll.len ∧ anyM (ll.drop (sint.nat i))
              (fun p => andM (pure (decide (p.1 > t1))) (notM (do isPrefix (← X.newC) p.2))) = .ok lc⌝) := by
        intro hy0 gpv
        iintro ⟨Hi, Hp, Hv⟩
        iexists _, gpv
        iframe Hi Hp Hv
        ipureintro
        refine ⟨by word, by word, ?_⟩
        rw [show sint.nat (i + W64 1) = sint.nat i + 1 by word]; exact hyf hy0
      wp_if_destruct
      · have hgt' : gt = true := by rw [← hgt]; simp only [decide_eq_true_eq]; rw [← HgiT, ← Hu1]; omega
        have h2 := hgtt hgt'
        unfold notM at h2
        obtain ⟨ip, hip, h2⟩ := bind_ok h2
        simp only [pure_ok, Except.ok.injEq] at h2
        obtain ⟨nc, hnc, hip⟩ := bind_ok hip
        odm newC
        wp_apply wp_newC _ X nc $$ [Hx] as %gnc #Hnc
        · iframe Hx; ipureintro; exact hnc
        try wp_auto
        wp_apply wp_IsPrefix gnc nc gi.L' ll[sint.nat i]!.2 ip $$ [Hnc HgiL]
        · iframe Hnc HgiL; ipureintro; exact hip
        cases ip
        · have hlc' : lc = true := hyt (by rw [← h2]; try rfl)
          subst hlc'
          try wp_auto
          wp_apply wp_violAdd vl1 _ _ $$ [Hvl1] as %vl #Hvl
          · iframe Hvl1; ipureintro; omega
          try wp_auto
          wp_for_post
          try wp_auto
          wp_join_done
          iexists _; iframe; simp only [ite_true]; iexact Hvl
        · try wp_auto
          wp_for_post
          iframe
          iapply hcont (by rw [← h2]; try rfl)
          iframe
      · have hgt' : gt = false := by rw [← hgt]; simp only [decide_eq_false_iff_not]; rw [← HgiT, ← Hu1]; omega
        try wp_auto
        wp_for_post
        iframe
        iapply hcont (hgtf hgt')
        iframe
    · try wp_auto
      have hil : sint.nat i = ll.length := by have := sint_nat_cast hi0; omega
      rw [hil] at hany
      have := OnDiskProofLaws.anyM_drop_end hany
      subst this
      wp_join_done
      iexists _; iframe; simp only [Bool.false_eq_true, ite_false]; iexact Hvl1
  -- v3: `l1 := x.L1(); l0 := x.L0(); changed := !EntriesEqual(l1, l0); if changed {
  --   for b := range s.Cfg.Server { if b != n && !Matching(l1, s.Log[b]) { viol = violAdd(viol, "LogMatching"); break } } }`
  have hv2l : (viol2.length : Int) ≤ vi.length + 2 := by
    cases ad2
    · rw [had2f rfl]; omega
    · obtain ⟨lc, -, rfl⟩ := had2t rfl
      have := OnDiskProofLaws.setAddIf_len lc (if cs then setAdd vi go!"CommitSafety" else vi) go!"LeaderCompleteness"
      omega
  obtain ⟨l1v, ee, v3v, hl1v, hee, Ho, hee_t, hee_f⟩ := OnDiskProofLaws.v3_ok'' Ho
  rw [hXs, hXn] at hee_f
  have hl1w := (L1_within HW hSF hl1v).1
  odm L1
  wp_apply wp_L1 _ X l1v $$ [Hx] as %gl1 #Hgl1
  · iframe Hx; ipureintro; exact hl1v
  try wp_auto
  odm L0
  wp_apply wp_L0 _ X $$ [Hx] as %gl0 #Hgl0
  · iexact Hx
  try wp_auto
  wp_apply wp_EntriesEqual gl1 l1v gl0 X.L0 ee $$ [Hgl1 Hgl0]
  · iframe Hgl1 Hgl0; ipureintro; exact hee
  try wp_auto
  try ipersist l1
  try ipersist l0
  try ipersist changed
  wp_join (v := executeVal) iprop(∃ vl, viol_ptr ↦ vl ∗ strsRO vl v3v) at next with [viol] as ⟨%vl3, viol, #Hvl3⟩
  · cases ee
    case true =>
      rw [hee_t rfl]
      try wp_auto
      wp_join_done
      iexists _; iframe; iexact Hvl2
    obtain ⟨lm, hlm, rfl⟩ := hee_f rfl
    try wp_auto
    ihave #Hsrv3 := Hsrv
    iunfold strsRO at Hsrv3
    ihave %Hsl3 := ownSlice_len $$ Hsrv3
    ihave IH : iprop(∃ (i bv : w64), "i" ∷ i_ptr ↦ i ∗ "b" ∷ b_ptr ↦ bv ∗ "viol" ∷ viol_ptr ↦ vl2 ∗
        "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z gc.Server'.len ∧
          anyM ((List.range s.cfg.server.length).drop (sint.nat i))
            (fun b => andM (pure (b != sint.nat n)) (notM (matching l1v (s.log[b]!)))) = .ok lm⌝) $$ [i b viol]
    · iexists _, _
      iframe
      ipureintro
      refine ⟨by word, by word, ?_⟩
      rw [show sint.nat (W64 0) = 0 by word, List.drop_zero]; exact hlm
    wp_for IH
    obtain ⟨hi0, hi1, hany⟩ := Hi
    wp_if_destruct
    · have Hil : sint.nat i < s.cfg.server.length := by rw [Hsl3.1]; word
      obtain ⟨sv, Hsv⟩ : ∃ sv, s.cfg.server[sint.nat i]? = some sv := ⟨_, List.getElem?_eq_getElem Hil⟩
      rw [ite_eq_left_of_eq_true _ _ (eq_true (show 0 ≤ sint.Z i ∧ sint.Z i < sint.Z gc.Server'.len from ⟨hi0, Hif⟩))]
      wp_apply wp_load_slice_index gc.Server' (sint.Z i) s.cfg.server DFrac.discard sv hi0 $$ [Hsrv3] as -
      · isplitr
        · iexact Hsrv3
        ipureintro; exact Hsv
      try wp_auto
      obtain ⟨y, hy, hyt, hyf⟩ := OnDiskProofLaws.anyM_drop_step (by rw [List.length_range]; exact Hil) hany
      simp only [List.getElem_range] at hy
      obtain ⟨gb, hgb, hgbt, hgbf⟩ := andM_ok hy
      simp only [pure_ok, Except.ok.injEq] at hgb
      have hcont : y = false → ∀ bv : w64,
          (i_ptr ↦ (i + W64 1) ∗ b_ptr ↦ bv ∗ viol_ptr ↦ vl2 : IProp GF) ⊢ iprop(∃ (i bv : w64),
            "i" ∷ i_ptr ↦ i ∗ "b" ∷ b_ptr ↦ bv ∗ "viol" ∷ viol_ptr ↦ vl2 ∗
            "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z gc.Server'.len ∧
              anyM ((List.range s.cfg.server.length).drop (sint.nat i))
                (fun b => andM (pure (b != sint.nat n)) (notM (matching l1v (s.log[b]!)))) = .ok lm⌝) := by
        intro hy0 bv
        iintro ⟨Hi, Hb, Hv⟩
        iexists _, bv
        iframe Hi Hb Hv
        ipureintro
        refine ⟨by word, by word, ?_⟩
        rw [show sint.nat (i + W64 1) = sint.nat i + 1 by word]; exact hyf hy0
      by_cases hin : i = n
      · rw [decide_eq_true hin]
        have hgb' : gb = false := by rw [← hgb, hin]; simp
        try wp_auto
        wp_for_post
        iframe
        iapply hcont (hgbf hgb')
        iframe
      rw [decide_eq_false hin]
      have hgb' : gb = true := by
        rw [← hgb]; have : sint.nat i ≠ sint.nat n := fun h => hin (by word)
        simpa using this
      have h2 := hgbt hgb'
      unfold notM at h2
      obtain ⟨mt, hmt, h2⟩ := bind_ok h2
      simp only [pure_ok, Except.ok.injEq] at h2
      try wp_auto
      icases logsRO_at g.Log' s.log i ⟨hi0, by rw [HWf.len_log]; word⟩ $$ HLog with ⟨%lgi, #Hlgia, #Hlgi⟩
      wp_apply wp_load_at _ _ lgi hi0 $$ [Hlgia]
      · iexact Hlgia
      try wp_auto
      wp_apply wp_Matching gl1 l1v lgi (s.log[sint.nat i]!) mt $$ [Hgl1 Hlgi]
      · iframe Hgl1 Hlgi; ipureintro; exact ⟨hmt, by omega⟩
      cases mt
      · have hlm' : lm = true := hyt (by rw [← h2]; try rfl)
        subst hlm'
        try wp_auto
        wp_apply wp_violAdd vl2 _ _ $$ [Hvl2] as %vl #Hvl
        · iframe Hvl2; ipureintro; omega
        try wp_auto
        wp_for_post
        try wp_auto
        wp_join_done
        iexists _; iframe; simp only [ite_true]; iexact Hvl
      · try wp_auto
        wp_for_post
        iframe
        iapply hcont (by rw [← h2]; try rfl)
        iframe
    · try wp_auto
      have hil : sint.nat i = s.cfg.server.length := by rw [Hsl3.1]; word
      rw [hil] at hany
      have := OnDiskProofLaws.anyM_drop_end (xs := List.range s.cfg.server.length) (by rwa [List.length_range])
      subst this
      wp_join_done
      iexists _; iframe; simp only [Bool.false_eq_true, ite_false]; iexact Hvl2
  -- v4: `if (changed || x.adv()) && !IsPrefix(SubSeq(x.ch1(), 1, w.commit()), l1) {
  --   viol = violAdd(viol, "CommittedEntriesPreserved") }`
  have hv3l : (v3v.length : Int) ≤ vi.length + 3 := by
    cases ee
    · obtain ⟨lm, -, rfl⟩ := hee_f rfl
      have := OnDiskProofLaws.setAddIf_len lm viol2 go!"LogMatching"
      omega
    · rw [hee_t rfl]; omega
  obtain ⟨cp, hcp, Ho⟩ := OnDiskProofLaws.v4_ok' Ho
  wp_join (v := executeVal)
    iprop(∃ vl, viol_ptr ↦ vl ∗ strsRO vl (if cp then setAdd v3v go!"CommittedEntriesPreserved" else v3v))
    at next with [viol] as ⟨%vl4, viol, #Hvl4⟩
  · obtain ⟨oc, hoc, hoct, hocf⟩ := andM_ok hcp
    obtain ⟨c0, hc0, hc0t, hc0f⟩ := orM_ok hoc
    simp only [pure_ok, Except.ok.injEq] at hc0
    cases ee
    · have hoc1 : oc = true := hc0t (by rw [← hc0]; try rfl)
      try wp_auto
      odv4tail
    · have hadv := hc0f (by rw [← hc0]; try rfl)
      try wp_auto
      odm adv
      wp_apply wp_adv _ X oc $$ [Hx]
      · iframe Hx; ipureintro; exact hadv
      cases oc
      · rw [hocf rfl]
        try wp_auto
        wp_join_done
        simp only [Bool.false_eq_true, ite_false]
        iexists _; iframe; iexact Hvl3
      have hoc1 : true = true := rfl
      odv4tail
  -- v5: `c1 := x.conf1(); if x.adv() && (c1.Term != x.T1() || w.commit() > c1.Index) {
  --   viol = violAdd(viol, "CommitBeyondConfirmed") }; ns.Viol = viol; return ns, true`
  have hv4l := OnDiskProofLaws.setAddIf_len cp v3v go!"CommittedEntriesPreserved"
  generalize hv4 : (if cp then setAdd v3v go!"CommittedEntriesPreserved" else v3v) = viol4 at Ho hv4l ⊢
  -- `Ho`'s successor is the record `u1`-`u8` build (with `X.ld`, `X.ll`), `S7` the one the stores
  -- built (with `ld`, `ll`): the same once `X` is unfolded.
  have Ho7 : v5 X t1 S7 viol4 = .ok o := by
    rw [hXld, hXll] at Ho
    subst hS7 hS6 hS5 hS4 hS3 hS2; exact Ho
  obtain ⟨cf, cb, hcf, hcb, hoeq⟩ := OnDiskProofLaws.v5_ok' Ho7
  odm conf1
  wp_apply wp_conf1 _ X cf $$ [Hx] as %gcf %Hgcf
  · iframe Hx; ipureintro; exact hcf
  try wp_auto
  wp_join (v := executeVal)
    iprop(∃ vl, viol_ptr ↦ vl ∗ strsRO vl (if cb then setAdd viol4 go!"CommitBeyondConfirmed" else viol4) ∗
      c1_ptr ↦ gcf)
    at next with [viol c1] as ⟨%vl5, viol, #Hvl5, -⟩
  · obtain ⟨ad5, had5, had5t, had5f⟩ := andM_ok hcb
    odm adv
    wp_apply wp_adv _ X ad5 $$ [Hx]
    · iframe Hx; ipureintro; exact had5
    cases ad5
    · rw [had5f rfl]
      try wp_auto
      wp_join_done
      simp only [Bool.false_eq_true, ite_false]
      iexists _; iframe; iexact Hvl4
    have h5 := had5t rfl
    obtain ⟨cm5, hcm5, h5⟩ := bind_ok h5
    simp only [pure_ok, Except.ok.injEq] at h5
    try wp_auto
    odm T1
    wp_apply wp_T1 _ X t1 $$ [Hx] as %u1 %Hu1
    · iframe Hx; ipureintro; exact ht1
    try wp_auto
    rw [decide_w64_eq, Hgcf.1, Hu1]
    by_cases hte : cf.term = t1
    · rw [decide_eq_true hte]
      try wp_auto
      wp_apply wp_Event_commit pw X.w cm5 $$ [Hw] as %uc5 %Huc5
      · iframe Hw; ipureintro; exact hcm5
      try wp_auto
      wp_if_destruct
      · have hcb' : cb = true := by
          rw [← h5, hte]; simp only [bne_self_eq_false, Bool.false_or, decide_eq_true_eq]
          rw [← Hgcf.2, ← Huc5]; omega
        subst hcb'
        wp_apply wp_violAdd vl4 _ _ $$ [Hvl4] as %vl #Hvl
        · iframe Hvl4; ipureintro; omega
        try wp_auto
        wp_join_done
        simp only [ite_true]
        iexists _; iframe; iexact Hvl
      · have hcb' : cb = false := by
          rw [← h5, hte]; simp only [bne_self_eq_false, Bool.false_or, decide_eq_false_iff_not]
          rw [← Hgcf.2, ← Huc5]; omega
        subst hcb'
        try wp_auto
        wp_join_done
        simp only [Bool.false_eq_true, ite_false]
        iexists _; iframe; iexact Hvl4
    · rw [decide_eq_false hte]
      have hcb' : cb = true := by rw [← h5]; simp [hte]
      subst hcb'
      try wp_auto
      wp_apply wp_violAdd vl4 _ _ $$ [Hvl4] as %vl #Hvl
      · iframe Hvl4; ipureintro; omega
      try wp_auto
      wp_join_done
      simp only [ite_true]
      iexists _; iframe; iexact Hvl
  wp_apply wp_set_viol q S7 vl5 (if cb then setAdd viol4 go!"CommitBeyondConfirmed" else viol4) $$ [Hq Hvl5] as Hq
  · iframe Hq Hvl5
  try wp_auto
  subst hoeq
  iapply HΦ
  iunfold succOwn
  isplitr
  · ipureintro; rfl
  iexact Hq

end proof

end AntCheck
end EtcdGrove
end Perennial
