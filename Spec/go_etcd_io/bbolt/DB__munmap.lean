module
public import Proof.go_etcd_io.bbolt.Init
public import Proof.os.FileModel

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `db.munmap()`: unmaps the file (if mapped: `munmap`) and forgets the mapping and the
metas (`invalidate`, deferred). -/
abbrev DB.munmap.spec : Prop :=
  ∀ (dbl : Loc) (d : DB) (fd : w64) (bs : List w8) (n : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ dbl ↦ d ∗ fileBytes fd bs ∗
      ((⌜d.dataref' = slice.nil⌝ ∗ fileMap fd none) ∨
       (⌜d.dataref'.ptr ≠ null ∧ d.dataref'.len = W64 n ∧ d.dataref'.cap = W64 n⌝ ∗
        fileMap fd (some (d.dataref'.ptr, n)) ∗ mapRange (some (d.dataref'.ptr, n)) bs 0 n)) }}
    (App (Val (dbl @!! go.GoType.PointerType DB.ty @!! go!"munmap")) (Val #()))
  {{ (d' : DB), RET #interface.nil; ⌜d' = ({ d with dataref' := slice.nil, data' := null, datasz' := W64 0, meta0' := null, meta1' := null } : DB)⌝ ∗ dbl ↦ d' ∗ fileBytes fd bs ∗ fileMap fd none }}

end spec

end bbolt
end EtcdGrove
end Perennial
