/-
`(*keyIndex).get(lg, atRev)` (`key_index.go:149`). Internal (the index's `unsafeGet`, `Revisions`,
`Range`, `CountRevisions`); mirrors its code over `KeyIndexM` (`kiGet`).

**Changes** from `specs-ref`'s file: over `Internal.lean`'s model (`ownKi`, `kiGet`).
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Internal

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

/-- `ki.get(lg, atRev)` (a non-`nil` logger, a non-empty key index: `lg.Panic` otherwise): the key's
revision, creation revision and version at `atRev` (`kiGet`), or `ErrRevisionNotFound`. A read, at
any fraction. -/
def keyIndex.get.spec : Prop :=
  ∀ (p lg : Loc) (k : GoString) (ki : KeyIndexM) (dq : DFrac) (atRev : w64) (e : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      ⌜lg ≠ null ∧ kiIsEmpty ki = false⌝ ∗ ownKi p k ki dq ∗ globalAddr ErrRevisionNotFound ↦□ e }}
    (App (App (Val (p @!! go.GoType.PointerType keyIndex.ty @!! go!"get")) (Val #lg)) (Val #atRev))
  {{ (m c : Revision) (ver : w64) (err : GoInterface),
      RET (PairV (PairV (PairV #m #c) #ver) #err); ownKi p k ki dq ∗
      ⌜match kiGet ki atRev with
        | some (m', c', v') => revOf m = m' ∧ revOf c = c' ∧ ver = v' ∧ err = GoInterface.nil
        | none => m = revVal Rev.zero ∧ c = revVal Rev.zero ∧ ver = W64 0 ∧ err = e⌝ }}

end spec
end Mvcc
end EtcdGrove
end Perennial
