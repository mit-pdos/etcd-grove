/-
Package initialization of `go_etcd_io.etcd.api.v3.authpb`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact (`authpbInit`, `cache/v3/Base.lean`): `Permission_Type_name` holds a map, read-only
for good, whose entries are the permission types' names (`0` `READ`, `1` `WRITE`, `2`
`READWRITE`). Its initializer allocates and sets the two translated name maps
(`Permission_Type_name`, `Permission_Type_value`: `map[int32]string`/`map[string]int32` literals,
`auth.pb.go`), initializes its imports and runs its other variables' untranslated initializers (the
generated protobuf descriptors), which the trust-boundary axiom `opaqueInitsOk` says run.
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.Base
public import Proof.google_golang_org.protobuf.reflect.protoreflect.Init
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

section opaqueInits
namespace go_etcd_io.etcd.api.v3.authpb
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The trust boundary: `go_etcd_io.etcd.api.v3.authpb`'s untranslated variable initializers run.**
Goose translates them names-only, so each `X.init` is an axiom of the translation; Go
runs them at program start, and etcd starts, so each returns without panicking.
Satisfiable whatever the semantics (the `X.init`s are uninterpreted constants). -/
axiom opaqueInitsOk :
    ∀ v ∈ ([file_auth_proto_enumTypes.init,
        file_auth_proto_msgTypes.init,
        file_auth_proto_goTypes.init,
        file_auth_proto_depIdxs.init] : List val),
    {{ (True : IProp GF) }} (App (Val v) (Val #())) {{ RET #(); True }}

/-- **The trust boundary: `go_etcd_io.etcd.api.v3.authpb`'s untranslated `init` functions return.** Goose
names a package's `func init()`s `init.<k>`, as gc does, and translates them names-only
here, so the model does not unfold them (`@! init.<k>`: the semantics' `functions`, which
the package's `Assumptions` do not constrain for them). Go runs them at program start, and
etcd starts, so each returns without panicking. A fact about the Go code, as the axioms of
other names-only functions (`EtcdGrove.prometheus.MustRegister.wp_proof`). -/
axiom initFuncsOk :
    ∀ f ∈ ([init.«0»] : List GoString),
    {{ (True : IProp GF) }} (App (Val (@! f)) (Val #())) {{ RET #(); True }}

end go_etcd_io.etcd.api.v3.authpb
end opaqueInits

section init
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.go_etcd_io.etcd.api.v3.authpb.Assumptions]

namespace go_etcd_io.etcd.api.v3.authpb

theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.go_etcd_io.etcd.api.v3.authpb get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.authpb }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  iapply wp_fupd
  wp_apply wp_GlobalAlloc (V := Loc) Permission_Type_value _ as HPermission_Type_value
  wp_apply wp_GlobalAlloc (V := Loc) Permission_Type_name _ as HPermission_Type_name
  wp_apply (_root_.Perennial.google_golang_org.protobuf.runtime.protoimpl.wp_initialize'_lb _ Hinit.2.2.1) _ $$ Hown as ⟨Hown, #Hd2⟩
  wp_apply (_root_.Perennial.google_golang_org.protobuf.reflect.protoreflect.wp_initialize'_lb _ Hinit.2.1) _ $$ Hown as ⟨Hown, #Hd1⟩
  -- translated initializer of Permission_Type_name))
  try wp_auto
  wp_apply (wp_map_make1 (K := w32) (V := GoString) go.int32 go.string) as %mn Hmn
  try wp_auto
  repeat (wp_apply (wp_mapInsert (K := w32) (V := GoString) go.int32) $$ Hmn as Hmn; try wp_auto)
  -- translated initializer of Permission_Type_value))
  try wp_auto
  wp_apply (wp_map_make1 (K := GoString) (V := w32) go.string go.int32) as %mv Hmv
  try wp_auto
  repeat (wp_apply (wp_mapInsert (K := GoString) (V := w32) go.string) $$ Hmv as Hmv; try wp_auto)
  wp_apply (opaqueInitsOk file_auth_proto_enumTypes.init (by mem_tac))
  wp_apply (opaqueInitsOk file_auth_proto_msgTypes.init (by mem_tac))
  wp_apply (opaqueInitsOk file_auth_proto_goTypes.init (by mem_tac))
  wp_apply (opaqueInitsOk file_auth_proto_depIdxs.init (by mem_tac))
  wp_apply (initFuncsOk init.«0» (by mem_tac))
  ipersist HPermission_Type_name
  ipersist Hmn
  iframe Hown
  imodintro
  isplitr
  · ipureintro
    exact isPanic_intoVal _
  is_pkg_init_finish
  try (isplitl []; · (imodintro; itrivial))
  imodintro
  unfold go_etcd_io.etcd.cache.v3.authpbInit
  iexists _, _
  iframe #
  ipureintro
  simp (config := {decide := true})

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.go_etcd_io.etcd.api.v3.authpb get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.authpb }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end go_etcd_io.etcd.api.v3.authpb

end init

end Perennial
