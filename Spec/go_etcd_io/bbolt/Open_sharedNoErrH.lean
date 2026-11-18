/-
**Pending S3f** (branch `bbolt-noerr-final`; S3d found the first shapes false): the statements of
bbolt's error-free `Open` in the shared mode (`Open_sharedNoErr.spec`) and of `DB.Close_ownNoErr.spec`
(the file always given back), in the shapes the coordinator decided (2026-11-17), as S3e
(`notes/bbolt-integration-plan.md`) states its proofs against them until they land: `Open`'s success
gives an exclusive close token (`boltCloserH γ`, S3f's `boltCloser`), which `Close` requires. Not yet
here: `Open`'s new option constraints (`Timeout = 0`, `NoFreelistSync = true`, `InitialMmapSize ≤
2 ^ 48 - 1`), stated on bbolt's options record, which S3f extends; the backend's `optsAt` will fix
them as etcd's backend sets them once bbolt's `optsAt` tracks those fields. To be replaced by S3f's
spec files (and this file deleted) when S3f is merged.
-/
module

public import Spec.go_etcd_io.bbolt.Open_shared
public import GooseLang.Ext.Fs.Premises
public import GooseLang.Ext.Fs.FilteredSem

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- **The right to close the database `γ`** (pending S3f's `boltCloser`; exclusive there). -/
opaque boltCloserH (γ : BoltName) : IProp GF

/-- `Open_shared.spec` when the semantics' steps do not fail on files: no error, and the close
token. -/
abbrev Open_sharedNoErrH.spec : Prop :=
  ∀ [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] [ThreadBoundLe GF (2 ^ 29)]
    [ReceiptBoundLe GF (2 ^ 62)] (Sio : IoSet) [FsStepSat (NoIoErr Sio)] [FsStepSat (NoMapLockErr Sio)],
  (∀ st i, Sio.ino st i) → (∀ p, Sio.path p) →
  ∀ (N : Namespace) (R : Roots) (d b : GoString) (dq : DFrac) (j : Ino)
    (qc : Qp) (h : NamesH) (mode : w32) (opts : Loc) (dqo : DFrac) (o : OptsM) (D : Data),
  NameOk b →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ osInv ∗ ⌜↑N ## ↑osN⌝ ∗
      osSharedInv R ∗ osPathS R d dq j ∗ osCallPerm qc ∗ osNames j (.only [b]) (DFrac.own 1) h ∗
      nameHolds h b D ∗
      optsAt opts dqo o ∗ ⌜o.ok⌝ ∗ (⌜o.logger = GoInterface.nil⌝ ∨ boltLogger o.logger) }}
    (App (App (App (Val (@! go_etcd_io.bbolt.Open)) (Val #(child d b))) (Val #mode)) (Val #opts))
  {{ (db : Loc) (err : GoInterface), RET (PairV #db #err); optsAt opts dqo o ∗
      osPathS R d dq j ∗ osCallPerm qc ∗ ⌜err = GoInterface.nil⌝ ∗
      ∃ (oc : Option (Nat × Nat × Ino)) (γ : BoltName) (i : Ino), crOut j b h (DFrac.own 1) oc ∗ ⌜γ.ns = N ∧ crIno b h oc i⌝ ∗
        isBolt db γ ∗ boltIno γ i ∗ boltState γ 1 D ∗ boltCloserH γ }}

/-- `DB.Close_ownNoErr.spec` with the close token: the file always given back. -/
abbrev DB.Close_ownNoErrH.spec : Prop :=
  ∀ [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
    (Sio : IoSet) [FsStepSat (NoIoErr Sio)] [FsStepSat (NoMapLockErr Sio)],
  (∀ st i, Sio.ino st i) → ∀ (db : Loc) (γ : BoltName) (i : Ino) (D : Data),
  {{ isBolt (GF := GF) db γ ∗ boltIno γ i ∗ boltState γ 1 D ∗ boltCloserH γ }}
    (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"Close")) (Val #()))
  {{ (err : GoInterface), RET #err; ⌜err = GoInterface.nil⌝ ∗ fileHolds i D }}

/-- **Pending S3f** (an interim axiom of branch `bbolt-files-backend`, never to land on `lean`):
S3f's `Open_sharedNoErr.wp_proof`, linked (bbolt's `Link.lean`, with its `fs.FileMode.String`
hypothesis), once S3f is merged. -/
axiom Open_sharedNoErrH.pendingS3d [os.file.FieldAssumptions] [os.fileStat.FieldAssumptions] :
  Open_sharedNoErrH.spec (GF := GF) (hG := hG)

/-- **Pending S3f** (an interim axiom, as `Open_sharedNoErrH.pendingS3d`): S3f's
`DB.Close_ownNoErr.wp_proof`, linked. -/
axiom DB.Close_ownNoErrH.pendingS3d [os.file.FieldAssumptions] [os.fileStat.FieldAssumptions] :
  DB.Close_ownNoErrH.spec (GF := GF) (hG := hG)

end spec

end bbolt
end EtcdGrove
end Perennial
