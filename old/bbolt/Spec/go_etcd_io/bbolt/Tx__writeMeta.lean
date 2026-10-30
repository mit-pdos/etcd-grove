module
public import Proof.go_etcd_io.bbolt.Init
public import Proof.os.FileModel
public import Proof.go_etcd_io.bbolt.TxModel
public import Spec.go_etcd_io.bbolt.getDiscardLogger
public import Spec.go_etcd_io.bbolt.DefaultLogger__Errorf
public import Spec.go_etcd_io.bbolt.internal.common.Meta__Write
public import Perennial.Proof.sync_proof.mutex
public import Proof.runtime.GOOS

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section defs
variable [ext : FfiSyntax]

/-- The meta `mv` with its checksum set (what `Meta.Write` writes, and leaves in `mv`). -/
def metaSummed (mv : Meta) : Meta := { mv with checksum' := fnv64a ((metaBytes mv).take 56) }

/-- The meta page `writeMeta` writes for the meta `mv`: its header (id `txid % 2`, the meta
flag), the meta with its checksum, zeros. -/
def metaPage (mv : Meta) (ps : Nat) : List w8 :=
  pageBytes (Page.mk (mv.txid' % W64 2) (W16 4) (W16 0) (W32 0)) ++ metaBytes (metaSummed mv) ++
    List.replicate (ps - 80) (W8 0)

end defs

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]
variable [linux : GOOSLinux]

/-- `tx.writeMeta()` (Linux): the transaction's meta `mv` written into a fresh page buffer
(`Meta.Write`: its checksum set, also in the transaction's copy), and the page written to
the file at its meta slot `txid % 2` through `db.ops.writeAt` (the file's `WriteAt`), under
`metalock`; then the file synced (unless `NoSync`), the statistics' write count incremented.
On success the slot holds the meta page (`metaPage`); on an error (of the write or of the
sync) some prefix of it. Over raw resources (the caller holds the database's predicate open:
after this the new meta may be the current one): the mapped cells of the slot (the caller's
half, no reader holding a part) are lent to `WriteAt`. `Meta.Write` validates the meta: its
root and freelist below its high-water mark. -/
abbrev Tx.writeMeta.spec : Prop :=
  ∀ (txl dbl ml : Loc) (mv : Meta) (f : Loc) (fd : w64) (bs : List w8) (m : Option (Loc × Nat))
    (ps : Nat) (lg : GoInterface) (dl : Loc) (ns : Bool) (st : TxStats) (dq : DFrac),
  dbl ≠ null → ml.locCar ≠ 0 → 80 ≤ ps → ps < 2 ^ 32 → (lg = interface.nil ∨ lg = discardIface dl) →
  uint.Z mv.root'.root' < uint.Z mv.pgid' →
  (uint.Z mv.freelist' < uint.Z mv.pgid' ∨ mv.freelist' = W64 18446744073709551615) →
  (uint.nat (mv.txid' % W64 2) + 1) * ps ≤ bs.length →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗
      structFieldRef Tx go!"db" txl ↦ dbl ∗ structFieldRef Tx go!"meta" txl ↦ ml ∗
      structFieldRef Tx go!"stats" txl ↦ st ∗ ml ↦ mv ∗
      structFieldRef DB go!"logger" dbl ↦{dq} lg ∗ (globalAddr discardLogger ↦□ dl : IProp GF) ∗
      defaultLoggerOK dl ∗ structFieldRef DB go!"pageSize" dbl ↦{dq} W64 (ps : Int) ∗
      structFieldRef DB go!"file" dbl ↦{dq} f ∗ structFieldRef DB go!"NoSync" dbl ↦{dq} ns ∗
      structFieldRef anonStruct_f41ae3ebe286c14c go!"writeAt" (structFieldRef DB go!"ops" dbl) ↦{dq}
        methods _root_.Perennial.os.File.ty.PointerType go!"WriteAt" #f ∗
      sync.isMutex (structFieldRef DB go!"metalock" dbl) iprop(True) ∗
      osFile f fd ∗ fileBytes fd bs ∗ fileMap fd m ∗
      mapRange m bs (uint.nat (mv.txid' % W64 2) * ps) (uint.nat (mv.txid' % W64 2) * ps + ps) }}
    (App (Val (txl @!! go.GoType.PointerType Tx.ty @!! go!"writeMeta")) (Val #()))
  {{ (err : GoInterface), RET #err; ∃ (k : Nat) (st' : TxStats) (bs' : List w8),
      ⌜bs' = writeBytes bs (uint.nat (mv.txid' % W64 2) * ps) ((metaPage mv ps).take k) ∧
        k ≤ ps ∧ (err = interface.nil → k = ps)⌝ ∗
      structFieldRef Tx go!"db" txl ↦ dbl ∗ structFieldRef Tx go!"meta" txl ↦ ml ∗
      structFieldRef Tx go!"stats" txl ↦ st' ∗ ml ↦ metaSummed mv ∗
      structFieldRef DB go!"logger" dbl ↦{dq} lg ∗ structFieldRef DB go!"pageSize" dbl ↦{dq} W64 (ps : Int) ∗
      structFieldRef DB go!"file" dbl ↦{dq} f ∗ structFieldRef DB go!"NoSync" dbl ↦{dq} ns ∗
      structFieldRef anonStruct_f41ae3ebe286c14c go!"writeAt" (structFieldRef DB go!"ops" dbl) ↦{dq}
        methods _root_.Perennial.os.File.ty.PointerType go!"WriteAt" #f ∗
      fileBytes fd bs' ∗ fileMap fd m ∗
      mapRange m bs' (uint.nat (mv.txid' % W64 2) * ps) (uint.nat (mv.txid' % W64 2) * ps + ps) }}

end spec

end bbolt
end EtcdGrove
end Perennial
