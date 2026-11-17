/-
`Open` (bbolt) over the **shared mode of the tree** (S3a, `notes/bbolt-integration-plan.md`, D-I5):
`Open.spec` with a whole claim on the database file's name in place of the whole tree, so that
several databases (several etcd members) are opened and closed concurrently. Proof:
`Proof/go_etcd_io/bbolt/Open_shared.lean` (`Open`'s proof, `Open.wp_proofG`, over
`os.OpenFile.specCreateS`).
-/
module

public import Spec.go_etcd_io.bbolt.ApiS
public import Spec.go_etcd_io.bbolt.Options
public import Spec.go_etcd_io.bbolt.Logger
public import Spec.os.OpenFileS

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

/-- `bolt.Open(d/b, mode, opts)` in the shared mode: `Open.spec` (its options, logger, namespace and
bounds the same), with the directory `d`'s shared path (`osPathS R d dq j`), a call permission and the
whole claim on the name `b` (`osNames j (.only [b]) 1 h`) in place of the tree, and `nameHolds h b D`
in place of `pathHolds`: a file holding `D` at `b`, or nothing (and `D = ∅`).
- The path, the permission and the claim come back on every exit, the claim as the open left it
  (`crOut`, `Spec/os/OpenFileS.lean`: unchanged, or with the create of `b` logged, `o = some (x, s, i)`).
- On success, the database at the file the open left at `b` (`crIno b h o i`) and all of its data. -/
abbrev Open_shared.spec : Prop :=
  ∀ [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] [ThreadBoundLe GF (2 ^ 29)]
    [ReceiptBoundLe GF (2 ^ 62)] (N : Namespace) (R : Roots) (d b : GoString) (dq : DFrac) (j : Ino)
    (qc : Qp) (h : NamesH) (mode : w32) (opts : Loc) (dqo : DFrac) (o : OptsM) (D : Data),
  NameOk b →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ osInv ∗ ⌜↑N ## ↑osN⌝ ∗
      osSharedInv R ∗ osPathS R d dq j ∗ osCallPerm qc ∗ osNames j (.only [b]) (DFrac.own 1) h ∗
      nameHolds h b D ∗
      optsAt opts dqo o ∗ ⌜o.ok⌝ ∗ (⌜o.logger = GoInterface.nil⌝ ∨ boltLogger o.logger) }}
    (App (App (App (Val (@! go_etcd_io.bbolt.Open)) (Val #(child d b))) (Val #mode)) (Val #opts))
  {{ (db : Loc) (err : GoInterface), RET (PairV #db #err); optsAt opts dqo o ∗
      osPathS R d dq j ∗ osCallPerm qc ∗
      (∃ oc, crOut j b h (DFrac.own 1) oc ∗
        ((⌜err = GoInterface.nil⌝ ∗ ∃ (γ : BoltName) (i : Ino),
            ⌜γ.ns = N ∧ crIno b h oc i⌝ ∗ isBolt db γ ∗ boltIno γ i ∗ boltState γ 1 D) ∨
         ⌜err ≠ GoInterface.nil⌝)) }}

end spec

end bbolt
end EtcdGrove
end Perennial
