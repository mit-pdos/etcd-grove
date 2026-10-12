module
public import Proof.go_etcd_io.bbolt.DBClose

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]
variable [hash_sem : _root_.Perennial.hash.Hash64.TypeAssumptions]

/-- `db.Close()` (sequential use): it takes the write lock, the meta lock and the mapping's
write lock, so no transaction is open (one open makes it wait forever); the database is
closed and its file given back to the file system with its bytes. -/
abbrev DB.Close.spec : Prop :=
  ∀ (I : FLImpl (GF := GF)) (dbl : Loc) (γ : DBNames) (σ : DBState),
  σ.file ≠ null →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ ownDB I dbl γ σ }}
    (App (Val (dbl @!! go.GoType.PointerType DB.ty @!! go!"Close")) (Val #()))
  {{ (err : GoInterface), RET #err; fsFile σ.path (some σ.bs) }}

end spec

end bbolt
end EtcdGrove
end Perennial
