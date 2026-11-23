/-
Package initialization of `rabia.examples.rabianet.cmd.server1`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact is `True`. Its initializer initializes its imports (it has no initialized
variable).
-/
module

public import Dsverify.Proof.rabia.examples.rabianet.cmd.server1.Base
public import Dsverify.Proof.rabia.examples.rabianet.Init
public import Net.Proof.runtime.PkgInitExt
public import Dsverify.Proof.github_com.rs.zerolog.Init
public import Dsverify.Proof.github_com.gogo.protobuf.proto.Init
public import Dsverify.Proof.github_com.gogo.protobuf.gogoproto.Init
public import Dsverify.Proof.github_com.go_redis.redis.v8.Init
public import Dsverify.Proof.os.signal.Init
public import Dsverify.Proof.math.rand.Init

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
variable [_root_.Perennial.math.rand.InitHyp GF]
variable [_root_.Perennial.os.signal.InitHyp GF]
variable [_root_.Perennial.github_com.go_redis.redis.v8.InitHyp GF]
variable [_root_.Perennial.github_com.gogo.protobuf.gogoproto.InitHyp GF]
variable [_root_.Perennial.github_com.gogo.protobuf.proto.InitHyp GF]
variable [_root_.Perennial.github_com.rs.zerolog.InitHyp GF]
variable [package_sem : _root_.Perennial.rabia.examples.rabianet.cmd.server1.Assumptions]

namespace rabia.examples.rabianet.cmd.server1

theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.rabia.examples.rabianet.cmd.server1 get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.rabia.examples.rabianet.cmd.server1 }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply (_root_.Perennial.rabia.examples.rabianet.wp_initialize'_lb _ Hinit.2.1) _ $$ Hown as ⟨Hown, #Hd1⟩
  iframe Hown
  is_pkg_init_finish

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.rabia.examples.rabianet.cmd.server1 get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.rabia.examples.rabianet.cmd.server1 }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end rabia.examples.rabianet.cmd.server1

end init

end Perennial
