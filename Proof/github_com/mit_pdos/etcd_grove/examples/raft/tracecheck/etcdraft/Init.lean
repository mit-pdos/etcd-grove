/-
Package initialization of `github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact (`etcdraftInit`, `Base.lean`): `Invariants` holds the seven named invariants of
`Traceetcdraft.cfg`, in order, each with its closure of `Closures.lean` (read-only). Its initializer
runs its variables' translated initializers (`Invariants`' slice literal of func literals, the
tables' map literals, `EmptyBag`'s struct literal).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Base
public import Perennial.Proof.fmt.Link
public import Perennial.Proof.strconv.Link
public import Perennial.Proof.strings.Link
public import Proof.runtime.PkgInitExt

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option linter.iris.dupNamespace false

noncomputable section

namespace Perennial

/-- `x ∈ [a, ..., x, ...]`, linear in the list (`simp` overflows on the long ones). -/
local macro "mem_tac" : tactic =>
  `(tactic| repeat (first | exact List.Mem.head _ | apply List.Mem.tail))

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Assumptions]

namespace github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft

theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  iapply wp_fupd
  wp_apply wp_GlobalAlloc (V := Bag) EmptyBag _ as HEmptyBag
  wp_apply wp_GlobalAlloc (V := Loc) ReceiveMessageTraceNames _ as HReceiveMessageTraceNames
  wp_apply wp_GlobalAlloc (V := Loc) RaftMsgSubtype _ as HRaftMsgSubtype
  wp_apply wp_GlobalAlloc (V := Loc) RaftMsgType _ as HRaftMsgType
  wp_apply wp_GlobalAlloc (V := GoSlice) Invariants _ as HInvariants
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.strconv _root_.Perennial.strconv.initialize'
      EtcdGrove.ExternalInit.strconv _root_.Perennial.strconv.wp_initialize' _ Hinit.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd3⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.strings _root_.Perennial.strings.initialize'
      EtcdGrove.ExternalInit.strings _root_.Perennial.strings.wp_initialize' _ Hinit.2.2.1) _ $$ Hown as ⟨Hown, #Hd2⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.fmt _root_.Perennial.fmt.initialize'
      EtcdGrove.ExternalInit.fmt _root_.Perennial.fmt.wp_initialize' _ Hinit.2.1) _ $$ Hown as ⟨Hown, #Hd1⟩
  -- translated initializer of Invariants))
  try wp_auto
  rw [← logInvV_val, ← moreThanOneLeaderInvV_val, ← electionSafetyInvV_val, ← logMatchingInvV_val, ← quorumLogInvV_val, ← leaderCompletenessInvV_val, ← committedIsDurableInvV_val]
  try wp_auto
  wp_apply wp_slice_literal (l := invariantsV)
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, -⟩
  try wp_auto
  -- translated initializer of RaftMsgType))
  wp_apply (wp_map_make1 (K := GoString) (V := MsgType) go.string MsgType.ty) as %m1 Hm1
  try wp_auto
  repeat (wp_apply (wp_mapInsert (K := GoString) (V := MsgType) go.string) $$ Hm1 as Hm1; try wp_auto)
  -- translated initializer of RaftMsgSubtype))
  wp_apply (wp_map_make1 (K := GoString) (V := GoString) go.string go.string) as %m2 Hm2
  try wp_auto
  repeat (wp_apply (wp_mapInsert (K := GoString) (V := GoString) go.string) $$ Hm2 as Hm2; try wp_auto)
  -- translated initializer of ReceiveMessageTraceNames))
  wp_apply (wp_map_make1 (K := GoString) (V := Bool) go.string go.bool) as %m3 Hm3
  try wp_auto
  repeat (wp_apply (wp_mapInsert (K := GoString) (V := Bool) go.string) $$ Hm3 as Hm3; try wp_auto)
  -- translated initializer of EmptyBag))
  try wp_auto
  ipersist HInvariants
  ipersist Hsl
  iframe Hown
  imodintro
  isplitr
  · ipureintro
    exact isPanic_intoVal _
  is_pkg_init_finish
  imodintro
  unfold etcdraftInit
  iexists _
  iframe HInvariants
  iexact Hsl

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft

end init

end Perennial
