/-
Package initialization instances for etcd's consistent index (`server/v3/etcdserver/cindex`)
and the packages it imports: `storage/schema` (partly translated: its `cindex.go`),
`storage/backend` and `client/pkg/v3/verify` (names and types only). The standard-library
ones (`sync`, `sync/atomic`, `encoding/binary`) are Perennial's.

As in `Cache/Base.lean`, the package facts are assumptions about package initialization,
not proved from `initialize'` (schema's initializer runs the axiomatized initializers of
its untranslated variables). They are `True` except for the three `schema` variables the
consistent index reads: the `Meta` bucket and the two key names of `cindex.go`, each a
fixed read-only value (`globalAddr X ↦□ v`), the key names holding their bytes.
-/
import EtcdCache.Code.go_etcd_io.etcd.server.v3.etcdserver.cindex
import EtcdCache.GeneratedProof.go_etcd_io.etcd.server.v3.etcdserver.cindex
import Perennial.Proof.ProofPrelude
import Perennial.Proof.sync
import Perennial.Proof.sync.atomic
import Perennial.Proof.encoding.binary

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

namespace go_etcd_io.etcd.server.v3.storage.backend

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.server.v3.storage.backend

namespace go_etcd_io.etcd.client.pkg.v3.verify

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.verify :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.verify :=
  build_get_is_pkg_init_wf

end go_etcd_io.etcd.client.pkg.v3.verify

namespace go_etcd_io.etcd.server.v3.storage.schema

/-- The bytes of the key under which the consistent index is stored. -/
def ciKeyBytes : GoString := go!"consistent_index"

/-- The bytes of the key under which its term is stored. -/
def termKeyBytes : GoString := go!"term"

/-- `schema`'s package facts: the `Meta` bucket and the two key names of `cindex.go`. -/
abbrev schemaInit : IProp GF :=
  iprop((∃ b : GoInterface, globalAddr Meta ↦□ b) ∗
    (∃ s : GoSlice, globalAddr MetaConsistentIndexKeyName ↦□ s ∗ s ↦*□ ciKeyBytes) ∗
    (∃ s : GoSlice, globalAddr MetaTermKeyName ↦□ s ∗ s ↦*□ termKeyBytes))

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
