/-
Package initialization of `k8s_io.apimachinery.pkg.apis.«meta».v1`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact is `True`. Its initializer initializes its imports, runs the untranslated
initializers of its variables (`X.init`, axioms of the translation), which the
trust-boundary axiom `opaqueInitsOk` says run without panicking, and its untranslated
`init` functions, which the trust-boundary axiom `initFuncsOk` says return.
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Base
public import Perennial.Proof.time.Link
public import Proof.k8s_io.apimachinery.pkg.runtime.Init
public import Proof.k8s_io.apimachinery.pkg.runtime.schema.Init
public import Proof.k8s_io.apimachinery.pkg.types.Init
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
namespace k8s_io.apimachinery.pkg.apis.«meta».v1
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The trust boundary: `k8s_io.apimachinery.pkg.apis.«meta».v1`'s untranslated variable initializers run.**
Goose translates them names-only, so each `X.init` is an axiom of the translation; Go
runs them at program start, and etcd starts, so each returns without panicking.
Satisfiable whatever the semantics (the `X.init`s are uninterpreted constants). -/
axiom opaqueInitsOk :
    ∀ v ∈ ([ErrInvalidLengthGenerated.init,
        ErrIntOverflowGenerated.init,
        ErrUnexpectedEndOfGroupGenerated.init,
        «_».init,
        «_».init,
        cborNull.init,
        «_».init,
        «_».init,
        localSchemeBuilder.init,
        SchemeGroupVersion.init,
        Unversioned.init,
        scheme.init,
        ParameterCodec.init,
        optionsTypes.init,
        «_».init,
        map_APIGroup.init,
        map_APIGroupList.init,
        map_APIResource.init,
        map_APIResourceList.init,
        map_APIVersions.init,
        map_ApplyOptions.init,
        map_Condition.init,
        map_CreateOptions.init,
        map_DeleteOptions.init,
        map_FieldSelectorRequirement.init,
        map_GetOptions.init,
        map_GroupVersionForDiscovery.init,
        map_LabelSelector.init,
        map_LabelSelectorRequirement.init,
        map_List.init,
        map_ListMeta.init,
        map_ListOptions.init,
        map_ManagedFieldsEntry.init,
        map_ObjectMeta.init,
        map_OwnerReference.init,
        map_PartialObjectMetadata.init,
        map_PartialObjectMetadataList.init,
        map_Patch.init,
        map_PatchOptions.init,
        map_Preconditions.init,
        map_RootPaths.init,
        map_ServerAddressByClientCIDR.init,
        map_ShardInfo.init,
        map_Status.init,
        map_StatusCause.init,
        map_StatusDetails.init,
        map_Table.init,
        map_TableColumnDefinition.init,
        map_TableOptions.init,
        map_TableRow.init,
        map_TableRowCondition.init,
        map_TypeMeta.init,
        map_UpdateOptions.init] : List val),
    {{ (True : IProp GF) }} (App (Val v) (Val #())) {{ RET #(); True }}

/-- **The trust boundary: `k8s_io.apimachinery.pkg.apis.«meta».v1`'s untranslated `init` functions return.** Goose
names a package's `func init()`s `init.<k>`, as gc does, and translates them names-only
here, so the model does not unfold them (`@! init.<k>`: the semantics' `functions`, which
the package's `Assumptions` do not constrain for them). Go runs them at program start, and
etcd starts, so each returns without panicking. A fact about the Go code, as the axioms of
other names-only functions (`EtcdGrove.prometheus.MustRegister.wp_proof`). -/
axiom initFuncsOk :
    ∀ f ∈ ([init.«0», init.«1»] : List GoString),
    {{ (True : IProp GF) }} (App (Val (@! f)) (Val #())) {{ RET #(); True }}

end k8s_io.apimachinery.pkg.apis.«meta».v1
end opaqueInits

section init
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.k8s_io.apimachinery.pkg.apis.«meta».v1.Assumptions]

namespace k8s_io.apimachinery.pkg.apis.«meta».v1

set_option maxHeartbeats 8000000 in
theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.k8s_io.apimachinery.pkg.apis.«meta».v1 get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.apis.«meta».v1 }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.time _root_.Perennial.time.initialize'
      EtcdGrove.ExternalInit.time _root_.Perennial.time.wp_initialize' _ Hinit.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd4⟩
  wp_apply (_root_.Perennial.k8s_io.apimachinery.pkg.runtime.wp_initialize'_lb _ Hinit.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd3⟩
  wp_apply (_root_.Perennial.k8s_io.apimachinery.pkg.types.wp_initialize'_lb _ Hinit.2.2.1) _ $$ Hown as ⟨Hown, #Hd2⟩
  wp_apply (_root_.Perennial.k8s_io.apimachinery.pkg.runtime.schema.wp_initialize'_lb _ Hinit.2.1) _ $$ Hown as ⟨Hown, #Hd1⟩
  wp_apply (opaqueInitsOk ErrInvalidLengthGenerated.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrIntOverflowGenerated.init (by mem_tac))
  wp_apply (opaqueInitsOk ErrUnexpectedEndOfGroupGenerated.init (by mem_tac))
  wp_apply (opaqueInitsOk «_».init (by mem_tac))
  wp_apply (opaqueInitsOk «_».init (by mem_tac))
  wp_apply (opaqueInitsOk cborNull.init (by mem_tac))
  wp_apply (opaqueInitsOk «_».init (by mem_tac))
  wp_apply (opaqueInitsOk «_».init (by mem_tac))
  wp_apply (opaqueInitsOk localSchemeBuilder.init (by mem_tac))
  wp_apply (opaqueInitsOk SchemeGroupVersion.init (by mem_tac))
  wp_apply (opaqueInitsOk Unversioned.init (by mem_tac))
  wp_apply (opaqueInitsOk scheme.init (by mem_tac))
  wp_apply (opaqueInitsOk ParameterCodec.init (by mem_tac))
  wp_apply (opaqueInitsOk optionsTypes.init (by mem_tac))
  wp_apply (opaqueInitsOk «_».init (by mem_tac))
  wp_apply (opaqueInitsOk map_APIGroup.init (by mem_tac))
  wp_apply (opaqueInitsOk map_APIGroupList.init (by mem_tac))
  wp_apply (opaqueInitsOk map_APIResource.init (by mem_tac))
  wp_apply (opaqueInitsOk map_APIResourceList.init (by mem_tac))
  wp_apply (opaqueInitsOk map_APIVersions.init (by mem_tac))
  wp_apply (opaqueInitsOk map_ApplyOptions.init (by mem_tac))
  wp_apply (opaqueInitsOk map_Condition.init (by mem_tac))
  wp_apply (opaqueInitsOk map_CreateOptions.init (by mem_tac))
  wp_apply (opaqueInitsOk map_DeleteOptions.init (by mem_tac))
  wp_apply (opaqueInitsOk map_FieldSelectorRequirement.init (by mem_tac))
  wp_apply (opaqueInitsOk map_GetOptions.init (by mem_tac))
  wp_apply (opaqueInitsOk map_GroupVersionForDiscovery.init (by mem_tac))
  wp_apply (opaqueInitsOk map_LabelSelector.init (by mem_tac))
  wp_apply (opaqueInitsOk map_LabelSelectorRequirement.init (by mem_tac))
  wp_apply (opaqueInitsOk map_List.init (by mem_tac))
  wp_apply (opaqueInitsOk map_ListMeta.init (by mem_tac))
  wp_apply (opaqueInitsOk map_ListOptions.init (by mem_tac))
  wp_apply (opaqueInitsOk map_ManagedFieldsEntry.init (by mem_tac))
  wp_apply (opaqueInitsOk map_ObjectMeta.init (by mem_tac))
  wp_apply (opaqueInitsOk map_OwnerReference.init (by mem_tac))
  wp_apply (opaqueInitsOk map_PartialObjectMetadata.init (by mem_tac))
  wp_apply (opaqueInitsOk map_PartialObjectMetadataList.init (by mem_tac))
  wp_apply (opaqueInitsOk map_Patch.init (by mem_tac))
  wp_apply (opaqueInitsOk map_PatchOptions.init (by mem_tac))
  wp_apply (opaqueInitsOk map_Preconditions.init (by mem_tac))
  wp_apply (opaqueInitsOk map_RootPaths.init (by mem_tac))
  wp_apply (opaqueInitsOk map_ServerAddressByClientCIDR.init (by mem_tac))
  wp_apply (opaqueInitsOk map_ShardInfo.init (by mem_tac))
  wp_apply (opaqueInitsOk map_Status.init (by mem_tac))
  wp_apply (opaqueInitsOk map_StatusCause.init (by mem_tac))
  wp_apply (opaqueInitsOk map_StatusDetails.init (by mem_tac))
  wp_apply (opaqueInitsOk map_Table.init (by mem_tac))
  wp_apply (opaqueInitsOk map_TableColumnDefinition.init (by mem_tac))
  wp_apply (opaqueInitsOk map_TableOptions.init (by mem_tac))
  wp_apply (opaqueInitsOk map_TableRow.init (by mem_tac))
  wp_apply (opaqueInitsOk map_TableRowCondition.init (by mem_tac))
  wp_apply (opaqueInitsOk map_TypeMeta.init (by mem_tac))
  wp_apply (opaqueInitsOk map_UpdateOptions.init (by mem_tac))
  wp_apply (initFuncsOk init.«0» (by mem_tac))
  wp_apply (initFuncsOk init.«1» (by mem_tac))
  iframe Hown
  is_pkg_init_finish

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.k8s_io.apimachinery.pkg.apis.«meta».v1 get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.apis.«meta».v1 }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end k8s_io.apimachinery.pkg.apis.«meta».v1

end init

end Perennial
