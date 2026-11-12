/-
`(*keyIndex).restore(lg, created, modified, ver)` (`key_index.go:105`) on a key index with no
generation (`lg.Panic` otherwise): one generation `{created, ver, [modified]}` (`kiRestore`).
Internal (`restoreIntoIndex`). **Changes**: the panic excluded by a premise; `created` kept whole.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.storage.mvcc.InternalIdx

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Mvcc

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

local notation "pkgInit" => isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc

/-- `ki.restore(lg, created, modified, ver)` on a key index with no generation. -/
def keyIndex.restore.spec : Prop :=
  ∀ (p lg : Loc) (k : GoString) (ki : KeyIndexM) (created modified : Revision) (ver : w64),
  {{ pkgInit ∗ ⌜ki.gens = []⌝ ∗ ownKi p k ki (DFrac.own 1) }}
    (App (App (App (App (Val (p @!! go.GoType.PointerType keyIndex.ty @!! go!"restore")) (Val #lg))
      (Val #created)) (Val #modified)) (Val #ver))
  {{ RET #(); ownKi p k (kiRestore (revOf created) (revOf modified) ver) (DFrac.own 1) }}

end spec
end Mvcc
end EtcdGrove
end Perennial
