/-
Package initialization of `gryff.src.gryff`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact is `True`. Its initializer initializes its imports, allocates its variables, stores
`stack` (`make([]*Instance, 0, 100)`), `cpcounter` (0) and `deferMap` (`make(map[uint64]uint64)`), and
runs its `init()` (the trace prophecy, `traceProph` from `primitive.NewProph()`: prophecy-only code
of the prophecy patch `etc/proph-patches/dsv-gryff/01-trace-prophecy.patch`, notes/dsv-gryff.md). The variables and the prophecy are dropped here: a replica node keeps them
from its own boot (`Dsverify/Proof/gryff/Boot/Defs.lean`, `cmd/server{2,3,4}/Boot.lean`; notes/dsv-gryff.md, "Package
initializers").
-/
module

public import Dsverify.Proof.gryff.src.gryff.Base
public import Perennial.Proof.encoding.binary.Link
public import Perennial.Proof.fmt.Link
public import Perennial.Proof.github_com.goose_lang.primitive.Link
public import Perennial.Proof.io.Link
public import Perennial.Proof.log.Link
public import Perennial.Proof.math.Link
public import Dsverify.Proof.math.rand.Init
public import Perennial.Proof.sort.Link
public import Perennial.Proof.sync.Link
public import Perennial.Proof.sync.atomic.Link
public import Perennial.Proof.time.Link
public import Proof.bufio.Init
public import Dsverify.Proof.gryff.src.bloomfilter.Init
public import Dsverify.Proof.gryff.src.clientproto.Init
public import Dsverify.Proof.gryff.src.dlog.Init
public import Dsverify.Proof.gryff.src.epaxosproto.Init
public import Dsverify.Proof.gryff.src.fastrpc.Init
public import Dsverify.Proof.gryff.src.genericsmr.Init
public import Dsverify.Proof.gryff.src.genericsmrproto.Init
public import Dsverify.Proof.gryff.src.gryffcommon.Init
public import Dsverify.Proof.gryff.src.gryffproto.Init
public import Dsverify.Proof.gryff.src.state.Init
public import Dsverify.Proof.gryff.src.stats.Init
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
variable [_root_.Perennial.math.rand.InitHyp GF]
variable [package_sem : _root_.Perennial.gryff.src.gryff.Assumptions]

namespace gryff.src.gryff

theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.gryff.src.gryff get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply wp_GlobalAlloc (V := github_com.goose_lang.primitive.ProphId) traceProph _ as HtraceProph
  wp_apply wp_GlobalAlloc (V := GoMap) deferMap _ as HdeferMap
  wp_apply wp_GlobalAlloc (V := src.gryffproto.AcceptOKReply) aokr _ as Haokr
  wp_apply wp_GlobalAlloc (V := src.gryffproto.PreAcceptOKReply) paokr _ as Hpaokr
  wp_apply wp_GlobalAlloc (V := src.epaxosproto.CommitShort) ecs _ as Hecs
  wp_apply wp_GlobalAlloc (V := src.gryffproto.ECommit) ec _ as Hec
  wp_apply wp_GlobalAlloc (V := src.gryffproto.EAccept) ea _ as Hea
  wp_apply wp_GlobalAlloc (V := src.gryffproto.TryPreAccept) tpa _ as Htpa
  wp_apply wp_GlobalAlloc (V := src.gryffproto.PreAccept) pa _ as Hpa
  wp_apply wp_GlobalAlloc (V := w64) happy _ as Hhappy
  wp_apply wp_GlobalAlloc (V := w64) slow _ as Hslow
  wp_apply wp_GlobalAlloc (V := w64) weird _ as Hweird
  wp_apply wp_GlobalAlloc (V := w64) conflicted _ as Hconflicted
  wp_apply wp_GlobalAlloc (V := w64) cpcounter _ as Hcpcounter
  wp_apply wp_GlobalAlloc (V := GoSlice) cpMarker _ as HcpMarker
  wp_apply wp_GlobalAlloc (V := w32) bf_PT _ as Hbf_PT
  wp_apply wp_GlobalAlloc (V := GoSlice) stack _ as Hstack
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.sync _root_.Perennial.sync.initialize'
      EtcdGrove.ExternalInit.sync _root_.Perennial.sync.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd23⟩
  wp_apply (_root_.Perennial.gryff.src.stats.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd22⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.math.rand _root_.Perennial.math.rand.initialize'
      EtcdGrove.ExternalInit.math_rand _root_.Perennial.math.rand.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd21⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.fmt _root_.Perennial.fmt.initialize'
      EtcdGrove.ExternalInit.fmt _root_.Perennial.fmt.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd20⟩
  wp_apply (_root_.Perennial.gryff.src.clientproto.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd19⟩
  wp_apply (_root_.Perennial.bufio.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd18⟩
  wp_apply (_root_.Perennial.gryff.src.gryffcommon.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd17⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.sync.atomic _root_.Perennial.sync.atomic.initialize'
      EtcdGrove.ExternalInit.sync_atomic _root_.Perennial.sync.atomic.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd16⟩
  wp_apply (_root_.Perennial.gryff.src.state.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd15⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.math _root_.Perennial.math.initialize'
      EtcdGrove.ExternalInit.math _root_.Perennial.math.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd14⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.log _root_.Perennial.log.initialize'
      EtcdGrove.ExternalInit.log _root_.Perennial.log.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd13⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.io _root_.Perennial.io.initialize'
      EtcdGrove.ExternalInit.io _root_.Perennial.io.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd12⟩
  wp_apply (_root_.Perennial.gryff.src.genericsmrproto.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd11⟩
  wp_apply (_root_.Perennial.gryff.src.genericsmr.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd10⟩
  wp_apply (_root_.Perennial.gryff.src.fastrpc.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd9⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.encoding.binary _root_.Perennial.encoding.binary.initialize'
      EtcdGrove.ExternalInit.encoding_binary _root_.Perennial.encoding.binary.wp_initialize' _ Hinit.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd8⟩
  wp_apply (_root_.Perennial.gryff.src.bloomfilter.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd7⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.github_com.goose_lang.primitive _root_.Perennial.github_com.goose_lang.primitive.initialize'
      EtcdGrove.ExternalInit.github_com_goose_lang_primitive _root_.Perennial.github_com.goose_lang.primitive.wp_initialize' _ Hinit.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd6⟩
  wp_apply (_root_.Perennial.gryff.src.gryffproto.wp_initialize'_lb _ Hinit.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd5⟩
  wp_apply (_root_.Perennial.gryff.src.dlog.wp_initialize'_lb _ Hinit.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd4⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.time _root_.Perennial.time.initialize'
      EtcdGrove.ExternalInit.time _root_.Perennial.time.wp_initialize' _ Hinit.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd3⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.sort _root_.Perennial.sort.initialize'
      EtcdGrove.ExternalInit.sort _root_.Perennial.sort.wp_initialize' _ Hinit.2.2.1) _ $$ Hown as ⟨Hown, #Hd2⟩
  wp_apply (_root_.Perennial.gryff.src.epaxosproto.wp_initialize'_lb _ Hinit.2.1) _ $$ Hown as ⟨Hown, #Hd1⟩
  -- translated initializer of stack))
  try wp_auto
  wp_apply (wp_slice_make3 (V := Loc) (W64 0) (W64 100) (by decide)) as %stk -
  try wp_auto
  -- translated initializer of cpcounter))
  -- translated initializer of deferMap))
  try wp_auto
  wp_apply (wp_map_make1 (K := w64) (V := w64) go.uint64 go.uint64) as %dm -
  try wp_auto
  -- the translated init.«0»
  wp_func_call
  wp_call
  try wp_auto
  wp_apply github_com.goose_lang.primitive.wp_NewProph as %pvs %p -
  try wp_auto
  iframe Hown
  is_pkg_init_finish

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.gryff.src.gryff get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end gryff.src.gryff

end init

end Perennial
