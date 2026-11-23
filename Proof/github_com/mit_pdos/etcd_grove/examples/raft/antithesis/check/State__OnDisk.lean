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
    ("ptr_" ++ m.getId.toString ++ "_unfold")
  let n := Lean.Name.mkStr base "method_unfold"
  `(tactic| (rw [$(Lean.mkIdent n):ident]; try wp_auto))

/-- A method on a `*State`/`*Event`/... pointer receiver: `smu State VoteRequest`. -/
macro "smu" t:ident m:ident : tactic => do
  let base := Lean.Name.mkStr (Lean.Name.mkStr `github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check t.getId.toString)
    "TypeAssumptions"
  let base := Lean.Name.mkStr base ("ptr_" ++ m.getId.toString ++ "_unfold")
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
  icases undoRO_at g.Undo' s.undo n ⟨Hn, by rw [HWf.len_undo]; exact Hlt⟩ $$ HUndo with ⟨%u0, #Hua, #Hu⟩
  cases hc : (more && s.undo[sint.nat n]!.isNone)
  case true =>
    simp only [hc, ite_true, pure_ok, Except.ok.injEq] at Ho
    subst Ho
    simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hc
    obtain ⟨rfl, hu⟩ := hc
    rw [hu]
    iunfold preRO at Hu
    icases Hu with %Hnull
    subst Hnull
    try wp_auto
    wp_apply wp_load_at _ _ _ Hn $$ [Hua] as -
    · iexact Hua
    odret
  simp only [hc, Bool.false_eq_true, ite_false] at Ho
  wp_join at next with [«$res0» «$res1»]
  · cases more
    · try wp_auto
      wp_join_done
    · have hu : ∃ pu, s.undo[sint.nat n]! = some pu := by
        cases h : s.undo[sint.nat n]! with
        | none => rw [h] at hc; simp at hc
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
  done

end proof

end AntCheck
end EtcdGrove
end Perennial
