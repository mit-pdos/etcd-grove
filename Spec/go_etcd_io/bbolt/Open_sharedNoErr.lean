/-
`Open` (bbolt) over the shared mode of the tree **with no error** (session S3f,
`notes/bbolt-integration-plan.md`): `Open_shared.spec` over a semantics whose steps satisfy no I/O
error and no `flock`/`mmap`/`munmap`/`madvise`/`open` error (`NoIoErr Sio`, `NoMapLockErr Sio`) on
every file and path, for options that leave no other error (`optsAtNoErr`: no `Timeout`,
`NoFreelistSync`, `InitialMmapSize` at most `maxMapSize`) and a mappable file (`nameHoldsM`): `nil`.
Proof: `Proof/go_etcd_io/bbolt/Open_sharedNoErr.lean` (`Open`'s proof generic in the environment's
errors, `Open.wp_proofG`, every error exit refuted).
-/
module

public import Spec.go_etcd_io.bbolt.ApiS
public import Spec.go_etcd_io.bbolt.Options
public import Spec.go_etcd_io.bbolt.Logger
public import Spec.os.OpenFileS
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

/-- `bolt.Open(d/b, mode, opts)` returns `nil` when the environment's calls do not fail:
`Open_shared.spec`'s success, with
- the premises on steps (`NoIoErr`, `NoMapLockErr`) for an `IoSet` covering every inode and path
  (`Open` opens `d/b`, reads, writes and syncs its file, locks it with `flock`, maps it and
  `madvise`s the mapping);
- options under which `Open` has no error of its own (`optsAtNoErr`, `Spec/go_etcd_io/bbolt/Options.lean`);
- the file at `b` mappable (`nameHoldsM`: at most `maxMapSize` bytes) or absent.
A `flock` conflict with another description of the file is not refuted: with no `Timeout` the
loop retries, so `Open` does not return then (a WP allows it). -/
abbrev Open_sharedNoErr.spec : Prop :=
  ∀ [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] [ThreadBoundLe GF (2 ^ 29)]
    [ReceiptBoundLe GF (2 ^ 62)] (Sio : IoSet) [FsStepSat (NoIoErr Sio)]
    [FsStepSat (NoMapLockErr Sio)],
  (∀ st i, Sio.ino st i) → (∀ p, Sio.path p) →
  ∀ (N : Namespace) (R : Roots) (d b : GoString) (dq : DFrac) (j : Ino)
    (qc : Qp) (h : NamesH) (mode : w32) (opts : Loc) (dqo : DFrac) (o : OptsM) (D : Data),
  NameOk b →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ osInv ∗ ⌜↑N ## ↑osN⌝ ∗
      osSharedInv R ∗ osPathS R d dq j ∗ osCallPerm qc ∗ osNames j (.only [b]) (DFrac.own 1) h ∗
      nameHoldsM h b D ∗
      optsAtNoErr opts dqo o ∗ ⌜o.ok⌝ ∗ (⌜o.logger = GoInterface.nil⌝ ∨ boltLogger o.logger) }}
    (App (App (App (Val (@! go_etcd_io.bbolt.Open)) (Val #(child d b))) (Val #mode)) (Val #opts))
  {{ (db : Loc) (err : GoInterface), RET (PairV #db #err); ⌜err = GoInterface.nil⌝ ∗
      optsAtNoErr opts dqo o ∗ osPathS R d dq j ∗ osCallPerm qc ∗
      ∃ (oc : Option (Nat × Nat × Ino)) (γ : BoltName) (i : Ino), crOut j b h (DFrac.own 1) oc ∗
        ⌜γ.ns = N ∧ crIno b h oc i⌝ ∗ isBolt db γ ∗ boltIno γ i ∗ boltState γ 1 D ∗
        boltCloser γ }}

end spec

end bbolt
end EtcdGrove
end Perennial
