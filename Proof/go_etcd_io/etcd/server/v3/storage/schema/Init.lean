/-
Package initialization of `go_etcd_io.etcd.server.v3.storage.schema`
(item 8, 2026-10-17): its `wp_initialize'`.

Its fact (`schemaInit`, `etcdserver/Base.lean`): the `Meta`, `Key`, `Auth`, `AuthUsers` and
`AuthRoles` buckets, as `bucket.go` makes them, the consistent index's two key names (`cindex.go`),
the auth bucket's two key names and the auth backend's `authEnabled`/`authDisabled` values
(`auth.go`; the auth plan's S1, 2026-10-23), and the lessor's `Lease` bucket (leases T3,
2026-10-25). Its initializer allocates and sets those translated variables (with the buckets'
names), initializes its imports and runs its other variables' untranslated initializers, which
the trust-boundary axiom `opaqueInitsOk` says run.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.Base
public import Perennial.Proof.bytes.Link
public import Perennial.Proof.encoding.binary.Link
public import Proof.go_etcd_io.etcd.api.v3.authpb.Init
public import Proof.go_etcd_io.etcd.api.v3.etcdserverpb.Init
public import Proof.go_etcd_io.etcd.client.pkg.v3.verify.Init
public import Proof.go_etcd_io.etcd.server.v3.auth.Init
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.Init
public import Proof.go_etcd_io.raft.v3.Init
public import Proof.go_uber_org.zap.Init
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
namespace go_etcd_io.etcd.server.v3.storage.schema
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **The trust boundary: `go_etcd_io.etcd.server.v3.storage.schema`'s untranslated variable initializers run.**
Goose translates them names-only, so each `X.init` is an axiom of the translation; Go
runs them at program start, and etcd starts, so each returns without panicking.
Satisfiable whatever the semantics (the `X.init`s are uninterpreted constants). -/
axiom opaqueInitsOk :
    ∀ v ∈ ([«_».init,
        «_».init,
        «_».init,
        alarmBucketName.init,
        clusterBucketName.init,
        membersBucketName.init,
        membersRemovedBucketName.init,
        testBucketName.init,
        Alarm.init,
        Cluster.init,
        Members.init,
        MembersRemoved.init,
        Test.init,
        MetaConfStateName.init,
        ClusterClusterVersionKeyName.init,
        ClusterDowngradeKeyName.init,
        MetaStorageVersionName.init,
        emptyStorageVersion.init,
        schemaChanges.init] : List val),
    {{ (True : IProp GF) }} (App (Val v) (Val #())) {{ RET #(); True }}

/-- **The trust boundary: `go_etcd_io.etcd.server.v3.storage.schema`'s untranslated `init` functions return.** Goose
names a package's `func init()`s `init.<k>`, as gc does, and translates them names-only
here, so the model does not unfold them (`@! init.<k>`: the semantics' `functions`, which
the package's `Assumptions` do not constrain for them). Go runs them at program start, and
etcd starts, so each returns without panicking. A fact about the Go code, as the axioms of
other names-only functions (`EtcdGrove.prometheus.MustRegister.wp_proof`). -/
axiom initFuncsOk :
    ∀ f ∈ ([init.«0»] : List GoString),
    {{ (True : IProp GF) }} (App (Val (@! f)) (Val #())) {{ RET #(); True }}

/-- `AllBuckets = []backend.Bucket{Key, Meta, ...}` (`bucket.go`): a slice. -/
axiom AllBuckets_init :
    {{ (True : IProp GF) }} (App (Val AllBuckets.init) (Val #()))
    {{ RET #(); ∃ sl : GoSlice, globalAddr AllBuckets ↦ sl }}

/-- `ScheduledCompactKeyName = []byte("scheduledCompactRev")` (`bucket.go`). -/
axiom ScheduledCompactKeyName_init :
    {{ (True : IProp GF) }} (App (Val ScheduledCompactKeyName.init) (Val #()))
    {{ RET #(); ∃ s : GoSlice, globalAddr ScheduledCompactKeyName ↦ s ∗ s ↦*□ (go!"scheduledCompactRev" : GoString) }}

/-- `FinishedCompactKeyName = []byte("finishedCompactRev")` (`bucket.go`). -/
axiom FinishedCompactKeyName_init :
    {{ (True : IProp GF) }} (App (Val FinishedCompactKeyName.init) (Val #()))
    {{ RET #(); ∃ s : GoSlice, globalAddr FinishedCompactKeyName ↦ s ∗ s ↦*□ (go!"finishedCompactRev" : GoString) }}

end go_etcd_io.etcd.server.v3.storage.schema
end opaqueInits

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.go_etcd_io.etcd.server.v3.storage.schema.Assumptions]
variable [_root_.Perennial.errors.Assumptions]

namespace go_etcd_io.etcd.server.v3.storage.schema

set_option maxHeartbeats 8000000 in
theorem wp_initialize'_lb (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.go_etcd_io.etcd.server.v3.storage.schema get_is_pkg_init) (σ0 : GMap GoString Bool) :
    {{ EtcdGrove.ownInitLb get_is_pkg_init σ0 }}
      (App (Val initialize') (Val #()))
    {{ RET #(); EtcdGrove.ownInitLb get_is_pkg_init σ0 ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema }} := by
  wp_start as Hown
  iapply EtcdGrove.wp_package_init_lb (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  iapply wp_fupd
  wp_apply wp_GlobalAlloc (V := GoSlice) MetaTermKeyName _ as HMetaTermKeyName
  wp_apply wp_GlobalAlloc (V := GoSlice) AuthRevisionKeyName _ as HAuthRevisionKeyName
  wp_apply wp_GlobalAlloc (V := GoSlice) AuthEnabledKeyName _ as HAuthEnabledKeyName
  wp_apply wp_GlobalAlloc (V := GoSlice) MetaConsistentIndexKeyName _ as HMetaConsistentIndexKeyName
  wp_apply wp_GlobalAlloc (V := GoInterface) AuthRoles _ as HAuthRoles
  wp_apply wp_GlobalAlloc (V := GoInterface) AuthUsers _ as HAuthUsers
  wp_apply wp_GlobalAlloc (V := GoInterface) Auth _ as HAuth
  wp_apply wp_GlobalAlloc (V := GoInterface) Lease _ as HLease
  wp_apply wp_GlobalAlloc (V := GoInterface) Meta _ as HMeta
  wp_apply wp_GlobalAlloc (V := GoInterface) Key _ as HKey
  wp_apply wp_GlobalAlloc (V := GoSlice) authRolesBucketName _ as HauthRolesBucketName
  wp_apply wp_GlobalAlloc (V := GoSlice) authUsersBucketName _ as HauthUsersBucketName
  wp_apply wp_GlobalAlloc (V := GoSlice) authBucketName _ as HauthBucketName
  wp_apply wp_GlobalAlloc (V := GoSlice) leaseBucketName _ as HleaseBucketName
  wp_apply wp_GlobalAlloc (V := GoSlice) metaBucketName _ as HmetaBucketName
  wp_apply wp_GlobalAlloc (V := GoSlice) keyBucketName _ as HkeyBucketName
  wp_apply wp_GlobalAlloc (V := GoSlice) authDisabled _ as HauthDisabled
  wp_apply wp_GlobalAlloc (V := GoSlice) authEnabled _ as HauthEnabled
  wp_apply (_root_.Perennial.go_etcd_io.etcd.client.pkg.v3.verify.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd9⟩
  wp_apply (_root_.Perennial.go_etcd_io.etcd.api.v3.authpb.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd8⟩
  wp_apply (_root_.Perennial.go_etcd_io.etcd.server.v3.auth.wp_initialize'_lb _ Hinit.2.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd7⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.encoding.binary _root_.Perennial.encoding.binary.initialize'
      EtcdGrove.ExternalInit.encoding_binary _root_.Perennial.encoding.binary.wp_initialize' _ Hinit.2.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd6⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.bytes _root_.Perennial.bytes.initialize'
      EtcdGrove.ExternalInit.bytes _root_.Perennial.bytes.wp_initialize' _ Hinit.2.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd5⟩
  wp_apply (_root_.Perennial.go_etcd_io.etcd.api.v3.etcdserverpb.wp_initialize'_lb _ Hinit.2.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd4⟩
  wp_apply (EtcdGrove.initLb_of_spec pkg_id.google_golang_org.protobuf.proto _root_.Perennial.google_golang_org.protobuf.proto.initialize'
      EtcdGrove.ExternalInit.google_golang_org_protobuf_proto _root_.Perennial.google_golang_org.protobuf.proto.wp_initialize' _ Hinit.2.2.2.1) _ $$ Hown as ⟨Hown, #Hd3⟩
  wp_apply (_root_.Perennial.go_etcd_io.etcd.server.v3.storage.backend.wp_initialize'_lb _ Hinit.2.2.1) _ $$ Hown as ⟨Hown, #Hd2⟩
  wp_apply (_root_.Perennial.go_uber_org.zap.wp_initialize'_lb _ Hinit.2.1) _ $$ Hown as ⟨Hown, #Hd1⟩
  -- translated initializer of authEnabled))
  -- translated initializer of authDisabled))
  wp_apply (wp_slice_literal (l := _)); isplitr; (· ipureintro; rfl); iintro %sen ⟨Hsen, -⟩
  simp only [go.arrayLiteralSize, List.foldl]
  try wp_auto
  wp_apply (wp_slice_literal (l := _)); isplitr; (· ipureintro; rfl); iintro %sdis ⟨Hsdis, -⟩
  simp only [go.arrayLiteralSize, List.foldl]
  try wp_auto
  wp_apply (opaqueInitsOk «_».init (by mem_tac))
  wp_apply (opaqueInitsOk «_».init (by mem_tac))
  wp_apply (opaqueInitsOk «_».init (by mem_tac))
  -- translated initializer of keyBucketName))
  -- translated initializer of metaBucketName))
  -- translated initializer of leaseBucketName))
  wp_apply wp_string_to_bytes go!"key" as %skey ⟨Hskey, -⟩
  try wp_auto
  wp_apply wp_string_to_bytes go!"meta" as %smeta ⟨Hsmeta, -⟩
  try wp_auto
  wp_apply wp_string_to_bytes go!"lease" as %slease ⟨Hslease, -⟩
  try wp_auto
  wp_apply (opaqueInitsOk alarmBucketName.init (by mem_tac))
  wp_apply (opaqueInitsOk clusterBucketName.init (by mem_tac))
  wp_apply (opaqueInitsOk membersBucketName.init (by mem_tac))
  wp_apply (opaqueInitsOk membersRemovedBucketName.init (by mem_tac))
  -- translated initializer of authBucketName))
  -- translated initializer of authUsersBucketName))
  -- translated initializer of authRolesBucketName))
  wp_apply wp_string_to_bytes go!"auth" as %sauth ⟨Hsauth, -⟩
  try wp_auto
  wp_apply wp_string_to_bytes go!"authUsers" as %sausers ⟨Hsausers, -⟩
  try wp_auto
  wp_apply wp_string_to_bytes go!"authRoles" as %saroles ⟨Hsaroles, -⟩
  try wp_auto
  wp_apply (opaqueInitsOk testBucketName.init (by mem_tac))
  -- translated initializer of Key))
  -- translated initializer of Meta))
  -- translated initializer of Lease))
  try wp_auto
  wp_apply (opaqueInitsOk Alarm.init (by mem_tac))
  wp_apply (opaqueInitsOk Cluster.init (by mem_tac))
  wp_apply (opaqueInitsOk Members.init (by mem_tac))
  wp_apply (opaqueInitsOk MembersRemoved.init (by mem_tac))
  -- translated initializer of Auth))
  -- translated initializer of AuthUsers))
  -- translated initializer of AuthRoles))
  try wp_auto
  wp_apply (opaqueInitsOk Test.init (by mem_tac))
  wp_apply AllBuckets_init as ⟨%slAllBuckets, HAllBuckets⟩
  wp_apply ScheduledCompactKeyName_init as ⟨%sScheduledCompactKeyName, HScheduledCompactKeyName, #SScheduledCompactKeyName⟩
  wp_apply FinishedCompactKeyName_init as ⟨%sFinishedCompactKeyName, HFinishedCompactKeyName, #SFinishedCompactKeyName⟩
  -- translated initializer of MetaConsistentIndexKeyName))
  -- translated initializer of AuthEnabledKeyName))
  -- translated initializer of AuthRevisionKeyName))
  -- translated initializer of MetaTermKeyName))
  wp_apply wp_string_to_bytes go!"consistent_index" as %sci ⟨Hsci, -⟩
  try wp_auto
  wp_apply wp_string_to_bytes go!"authEnabled" as %sae ⟨Hsae, -⟩
  try wp_auto
  wp_apply wp_string_to_bytes go!"authRevision" as %sar ⟨Hsar, -⟩
  try wp_auto
  wp_apply wp_string_to_bytes go!"term" as %sterm ⟨Hsterm, -⟩
  try wp_auto
  wp_apply (opaqueInitsOk MetaConfStateName.init (by mem_tac))
  wp_apply (opaqueInitsOk ClusterClusterVersionKeyName.init (by mem_tac))
  wp_apply (opaqueInitsOk ClusterDowngradeKeyName.init (by mem_tac))
  wp_apply (opaqueInitsOk MetaStorageVersionName.init (by mem_tac))
  wp_apply (opaqueInitsOk emptyStorageVersion.init (by mem_tac))
  wp_apply (opaqueInitsOk schemaChanges.init (by mem_tac))
  wp_apply (initFuncsOk init.«0» (by mem_tac))
  -- translated initializer of authRolesBucketName))
  -- translated initializer of authUsersBucketName))
  -- translated initializer of authBucketName))
  -- translated initializer of leaseBucketName))
  -- translated initializer of metaBucketName))
  -- translated initializer of keyBucketName))
  ipersist Hskey
  ipersist Hsmeta
  ipersist Hsci
  ipersist Hsterm
  ipersist Hsen
  ipersist Hsdis
  ipersist Hsauth
  ipersist Hsausers
  ipersist HAllBuckets
  ipersist HScheduledCompactKeyName
  ipersist HFinishedCompactKeyName
  ipersist Hsaroles
  ipersist Hsae
  ipersist Hsar
  ipersist HKey
  ipersist HMeta
  ipersist HMetaConsistentIndexKeyName
  ipersist HMetaTermKeyName
  ipersist HAuth
  ipersist HAuthUsers
  ipersist HAuthRoles
  ipersist HAuthEnabledKeyName
  ipersist HAuthRevisionKeyName
  ipersist HauthEnabled
  ipersist HauthDisabled
  ipersist Hslease
  ipersist HLease
  iframe Hown
  imodintro
  isplitr
  · ipureintro
    exact isPanic_intoVal _
  is_pkg_init_finish
  imodintro
  unfold schemaInit bucketIs metaName ciKeyBytes termKeyBytes keyName authName authUsersName authRolesName leaseName
  iframe #
  repeat (first | (isplitl []; · (ipureintro; rfl)) | (ipureintro; rfl))

/-- Perennial's form, from `wp_initialize'_lb`. -/
theorem wp_initialize' (get_is_pkg_init : GoString → IProp GF)
    (Hinit : GetIsPkgInitProp pkg_id.go_etcd_io.etcd.server.v3.storage.schema get_is_pkg_init) :
    {{ ownInitializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema }} :=
  EtcdGrove.wp_init_of_lb _ _ _ (wp_initialize'_lb get_is_pkg_init Hinit)


end go_etcd_io.etcd.server.v3.storage.schema

end init

end Perennial
