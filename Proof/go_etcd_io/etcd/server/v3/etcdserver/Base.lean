/-
Package initialization instances for etcd's consistent index (`server/v3/etcdserver/cindex`)
and the packages it imports: `storage/schema` (partly translated: its `cindex.go`). The
backend's and `client/pkg/v3/verify`'s are in `storage/backend/Base.lean` (2026-10-12: moved
there when the backend got bodies). The standard-library ones (`sync`, `sync/atomic`,
`encoding/binary`) are Perennial's.

As in `Cache/Base.lean`, the package facts are assumptions about package initialization,
not proved from `initialize'` (schema's initializer runs the axiomatized initializers of
its untranslated variables). They are `True` except for the `schema` variables the consistent
index and the mvcc store read: the `Meta` and `Key` buckets (the values `bucket.go` makes,
`bucketIs`) and the two key names of `cindex.go`, each a fixed read-only value
(`globalAddr X ↦□ v`), the key names holding their bytes.
-/
module

public import Code.go_etcd_io.etcd.server.v3.etcdserver.cindex
public import GeneratedProof.go_etcd_io.etcd.server.v3.etcdserver.cindex
public import Perennial.Proof.ProofPrelude
public import Perennial.Proof.sync
public import Perennial.Proof.sync.atomic
public import Perennial.Proof.encoding.binary
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.Base

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section init
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

namespace go_etcd_io.etcd.server.v3.storage.schema

/-- The bytes of the key under which the consistent index is stored. -/
def ciKeyBytes : GoString := go!"consistent_index"

/-- The bytes of the key under which its term is stored. -/
def termKeyBytes : GoString := go!"term"

/-- The name of the `Key` bucket (`keyBucketName`). -/
def keyName : GoString := go!"key"

/-- The name of the `Meta` bucket (`metaBucketName`). -/
def metaName : GoString := go!"meta"

/-- `b` is the `Bucket` value `bucket{id, name, safeRangeBucket: safe}` (`bucket.go`'s
`backend.Bucket(bucket{...})`), its name's slice holding `name`, read-only. -/
def bucketIs (b : GoInterface) (id : w64) (name : GoString) (safe : Bool) : IProp GF :=
  iprop(∃ s : GoSlice,
    ⌜b = interface.mkOk bucket.ty #({ id' := id, name' := s, safeRangeBucket' := safe } : bucket)⌝ ∗
    s ↦*□ name)

instance bucketIs_persistent (b : GoInterface) (id : w64) (name : GoString) (safe : Bool) :
    Persistent (bucketIs (GF := GF) b id name safe) := by
  unfold bucketIs; infer_instance

/-- `schema`'s package facts: the `Meta` bucket and the two key names of `cindex.go`, and the
`Key` bucket (the mvcc store's), the two buckets as `bucket.go` makes them (`bucketIs`: id 2,
`"meta"`, not safe-range; id 1, `"key"`, safe-range; 2026-10-13: they were only some values,
before `bucket.go` was translated). -/
abbrev schemaInit : IProp GF :=
  iprop((∃ b : GoInterface, globalAddr Meta ↦□ b ∗ bucketIs b (W64 2) metaName false) ∗
    (∃ s : GoSlice, globalAddr MetaConsistentIndexKeyName ↦□ s ∗ s ↦*□ ciKeyBytes) ∗
    (∃ s : GoSlice, globalAddr MetaTermKeyName ↦□ s ∗ s ↦*□ termKeyBytes) ∗
    (∃ b : GoInterface, globalAddr Key ↦□ b ∗ bucketIs b (W64 1) keyName true))

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema :=
  define_is_pkg_init schemaInit
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.server.v3.storage.schema

namespace go_etcd_io.etcd.server.v3.etcdserver.cindex

instance isPkgInit_inst :
    IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.cindex :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.cindex :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.server.v3.etcdserver.cindex

end init

end Perennial
