module
public import Proof.go_etcd_io.bbolt.DBOpen
public import Spec.go_etcd_io.bbolt.DB__getPageSizeFromSecondMeta

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt go_etcd_io.bbolt.internal.freelist

section defs
variable [ext : FfiSyntax]

/-- `getPageSize` finds the page size `ps` in the file `bs`: the first meta, if valid, says
`ps`; so does any valid meta at the offsets it probes when the first meta cannot be read (an
I/O error; the forged-meta finding: data that looks like a valid meta there would set the page
size). -/
def pageSizeOK (bs : List w8) (ps : Nat) : Prop :=
  (4096 ≤ bs.length → metaValid (metaAt bs 16) → uint.Z (metaAt bs 16).pageSize' = ps) ∧
  ∀ i < 15, 1024 * 2 ^ i + 1024 < bs.length → metaValid (metaAt (probeAt bs (1024 * 2 ^ i)) 16) →
    uint.Z (metaAt (probeAt bs (1024 * 2 ^ i)) 16).pageSize' = ps

end defs

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]
variable [hash_sem : _root_.Perennial.hash.Hash64.TypeAssumptions]

/-- `bbolt.Open(path, mode, options)` of an existing well-formed file `bs` of pages of `ps`
bytes (sequential use; options: no logger, the `array` freelist, the file's page size, no
`OpenFile`, read-write, `NoFreelistSync` and `Mlock` off): the database, open (no transaction),
or an error and the file as it was. -/
abbrev Open.spec : Prop :=
  ∀ (path : GoString) (mode : w32) (ol : Loc) (ov : Options) (dq : DFrac) (bs : List w8)
    (ps : Nat),
  (∀ a, (arrayImpl (GF := GF) a).IfaceContract) →
  ov.ReadOnly' = false → ov.Logger' = interface.nil → ov.OpenFile' = zero_val GoFunc →
  ov.FreelistType' ≠ go!"hashmap" → ov.NoFreelistSync' = false → ov.Mlock' = false →
  ov.PageSize' = W64 (ps : Int) → 0 ≤ sint.Z ov.InitialMmapSize' →
  sint.Z ov.InitialMmapSize' < 2 ^ 62 →
  bs ≠ [] → fileWF bs ps → pageSizeOK bs ps →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ ol ↦{dq} ov ∗ fsFile path (some bs) }}
    (App (App (App (Val #(functions Open [])) (Val #path)) (Val #mode)) (Val #ol))
  {{ (dbl : Loc) (err : GoInterface), RET (PairV #dbl #err); ol ↦{dq} ov ∗
      ((⌜err = interface.nil⌝ ∗ ∃ (a : Loc) (γ : DBNames) (σ : DBState),
          ⌜σ.file ≠ null ∧ σ.bs = bs ∧ σ.ps = ps ∧ σ.readers = ∅ ∧ σ.wr = none ∧ σ.rwtx = null⌝ ∗
          ownDB (arrayImpl a) dbl γ σ) ∨
       (⌜err ≠ interface.nil⌝ ∗ fsFile path (some bs))) }}

end spec

end bbolt
end EtcdGrove
end Perennial
