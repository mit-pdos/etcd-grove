/-
Package initialization of `go_etcd_io.etcd.api.v3.mvccpb`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact (`mvccpbInit`, `cache/v3/Base.lean`; etcd-grove#39, 2026-11-23, `True` until then):
`Event_EventType_name` holds a map with `mvccpb.eventTypeNames` (`0` `PUT`, `1` `DELETE`), both
read-only for good: `Event_EventType.String`'s trusted model reads it. Its initializer allocates and
sets the translated name map (a `map[int32]string` literal, `kv.pb.go`), initializes its imports and
runs its trusted `init` (a no-op model).
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.Base
public import Proof.google_golang_org.protobuf.runtime.protoimpl.Init
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
variable [package_sem : _root_.Perennial.go_etcd_io.etcd.api.v3.mvccpb.Assumptions]

namespace go_etcd_io.etcd.api.v3.mvccpb

theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.go_etcd_io.etcd.api.v3.mvccpb get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.mvccpb }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  iapply wp_fupd
  wp_apply wp_GlobalAlloc (V := Loc) Event_EventType_name _ as HEvent_EventType_name
  wp_apply (_root_.Perennial.google_golang_org.protobuf.runtime.protoimpl.wp_initialize'_lb _ Hinit.2.1) _ $$ Hown as ⟨Hown, #Hd1⟩
  -- translated initializer of Event_EventType_name))
  try wp_auto
  wp_apply (wp_map_make1 (K := w32) (V := GoString) go.int32 go.string) as %mn Hmn
  try wp_auto
  repeat (wp_apply (wp_mapInsert (K := w32) (V := GoString) go.int32) $$ Hmn as Hmn; try wp_auto)
  -- the translated init.«0»
  wp_func_call
  wp_call
  try wp_auto
  ipersist HEvent_EventType_name
  ipersist Hmn
  iframe Hown
  imodintro
  isplitr
  · ipureintro
    exact isPanic_intoVal _
  is_pkg_init_finish
  try (isplitl []; · (imodintro; itrivial))
  imodintro
  unfold go_etcd_io.etcd.cache.v3.mvccpbInit go_etcd_io.etcd.cache.v3.mvccpb.eventTypeNames
  iexists _
  iframe #

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.go_etcd_io.etcd.api.v3.mvccpb get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.mvccpb }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end go_etcd_io.etcd.api.v3.mvccpb

end init

end Perennial
