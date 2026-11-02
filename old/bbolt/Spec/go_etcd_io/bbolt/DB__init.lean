module
public import Proof.go_etcd_io.bbolt.Init
public import Proof.os.FileModel
public import Proof.os.ErrWF
public import Spec.go_etcd_io.bbolt.getDiscardLogger
public import Spec.go_etcd_io.bbolt.DefaultLogger__Errorf
public import Spec.go_etcd_io.bbolt.internal.common.Meta__Validate
public import Proof.runtime.GOOS

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section defs
variable [ext : FfiSyntax]

/-- The meta `init` writes on page `i` (before its checksum). -/
def initMeta0 (ps : Nat) (i : Nat) : Meta :=
  Meta.mk (W32 3977042669) (W32 2) (W32 (ps : Int)) (W32 0) (InBucket.mk (W64 3) (W64 0)) (W64 2)
    (W64 4) (W64 (i : Int)) (W64 0)

/-- The meta `init` writes on page `i`: a fresh database's (root page 3, freelist page 2,
high-water mark 4, txid `i`), its checksum set. -/
def initMeta (ps : Nat) (i : Nat) : Meta :=
  { initMeta0 ps i with checksum' := fnv64a ((metaBytes (initMeta0 ps i)).take 56) }

/-- Meta page `i` of a fresh database. -/
def initMetaPage (ps : Nat) (i : Nat) : List w8 :=
  pageBytes (Page.mk (W64 (i : Int)) (W16 4) (W16 0) (W32 0)) ++ metaBytes (initMeta ps i) ++
    List.replicate (ps - 80) (W8 0)

/-- An empty page `id` with page flags `fl` (no elements). -/
def initEmptyPage (ps : Nat) (id : Nat) (fl : w16) : List w8 :=
  pageBytes (Page.mk (W64 (id : Int)) fl (W16 0) (W32 0)) ++ List.replicate (ps - 16) (W8 0)

/-- A fresh database's file: two metas, an empty freelist (page 2), an empty leaf (page 3,
the root). -/
def initBytes (ps : Nat) : List w8 :=
  initMetaPage ps 0 ++ initMetaPage ps 1 ++ initEmptyPage ps 2 (W16 16) ++
    initEmptyPage ps 3 (W16 2)

end defs

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]
variable [hash_sem : _root_.Perennial.hash.Hash64.TypeAssumptions]
variable [linux : GOOSLinux]

/-- `db.init()` of an empty, unmapped file (Linux): writes a fresh database (`initBytes`) at
its start and syncs it. On an error the file has some bytes. The page size is at least a
meta page's and fits a meta. Over the fields it reads; `db.ops.writeAt` is the file's
`WriteAt` (as `Open` sets it). -/
abbrev DB.init.spec : Prop :=
  ∀ (dbl f : Loc) (fd : w64) (ps : Nat) (lg : GoInterface) (dl : Loc) (wa : GoFunc) (dq : DFrac),
  dbl ≠ null → 80 ≤ ps → ps < 2 ^ 32 → (lg = interface.nil ∨ lg = discardIface dl) →
  (#wa : val) = (f @!! go.GoType.PointerType _root_.Perennial.os.File.ty @!! go!"WriteAt") →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗
      structFieldRef DB go!"logger" dbl ↦□ lg ∗ (globalAddr discardLogger ↦□ dl : IProp GF) ∗
      defaultLoggerOK dl ∗ structFieldRef DB go!"pageSize" dbl ↦{dq} W64 (ps : Int) ∗
      structFieldRef DB go!"file" dbl ↦{dq} f ∗
      structFieldRef anonStruct_f41ae3ebe286c14c go!"writeAt" (structFieldRef DB go!"ops" dbl) ↦{dq} wa ∗
      osFile f fd ∗ fileBytes fd [] ∗ fileMap fd none }}
    (App (Val (dbl @!! go.GoType.PointerType DB.ty @!! go!"init")) (Val #()))
  {{ (err : GoInterface), RET #err;
      structFieldRef DB go!"pageSize" dbl ↦{dq} W64 (ps : Int) ∗
      structFieldRef DB go!"file" dbl ↦{dq} f ∗
      structFieldRef anonStruct_f41ae3ebe286c14c go!"writeAt" (structFieldRef DB go!"ops" dbl) ↦{dq} wa ∗
      fileMap fd none ∗
      ((⌜err = interface.nil⌝ ∗ fileBytes fd (initBytes ps)) ∨
       (⌜err ≠ interface.nil⌝ ∗ ∃ bs', fileBytes fd bs')) }}

end spec

end bbolt
end EtcdGrove
end Perennial
