/-
**Pending S3d** (branch `bbolt-open-noerr`): the statements of bbolt's error-free `Open` in the shared
mode (`Open_sharedNoErr.spec`) and of `DB.Close_ownNoErr.spec` strengthened (the file always given
back), as S3e (`notes/bbolt-integration-plan.md`) states its proofs against them until they land:
`bbolt.Open_kv.wp_proof` and `bbolt.DB.Close_kv.wp_proof` take them as hypotheses. To be replaced by
S3d's spec files (and this file deleted) when S3d is merged into `bbolt-integrate`.
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

/-- `Open_shared.spec` when the semantics' steps do not fail on files: no error. -/
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
        isBolt db γ ∗ boltIno γ i ∗ boltState γ 1 D }}

/-- `DB.Close_ownNoErr.spec` strengthened: the file always given back. -/
abbrev DB.Close_ownNoErrH.spec : Prop :=
  ∀ [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
    (Sio : IoSet) [FsStepSat (NoIoErr Sio)] [FsStepSat (NoMapLockErr Sio)],
  (∀ st i, Sio.ino st i) → ∀ (db : Loc) (γ : BoltName) (i : Ino) (D : Data),
  {{ isBolt (GF := GF) db γ ∗ boltIno γ i ∗ boltState γ 1 D }}
    (App (Val (db @!! go.GoType.PointerType DB.ty @!! go!"Close")) (Val #()))
  {{ (err : GoInterface), RET #err; ⌜err = GoInterface.nil⌝ ∗ fileHolds i D }}

/-- **Pending S3d** (an interim axiom of branch `bbolt-files-backend`, never to land on `lean`):
S3d's `Open_sharedNoErr.wp_proof`, linked (bbolt's `Link.lean`, with its `fs.FileMode.String`
hypothesis), once S3d is merged. -/
axiom Open_sharedNoErrH.pendingS3d [os.file.FieldAssumptions] [os.fileStat.FieldAssumptions] :
  Open_sharedNoErrH.spec (GF := GF) (hG := hG)

/-- **Pending S3d** (an interim axiom, as `Open_sharedNoErrH.pendingS3d`): S3d's strengthened
`DB.Close_ownNoErr.wp_proof`, linked. -/
axiom DB.Close_ownNoErrH.pendingS3d [os.file.FieldAssumptions] [os.fileStat.FieldAssumptions] :
  DB.Close_ownNoErrH.spec (GF := GF) (hG := hG)

end spec

end bbolt
end EtcdGrove
end Perennial
