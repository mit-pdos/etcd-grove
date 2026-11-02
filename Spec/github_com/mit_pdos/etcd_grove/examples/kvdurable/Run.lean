/- kvreconf's, with the files and the crashes. Lean-first (no Rocq counterpart).

`Run(cfg, clock, dir)` (check.go): starts a cluster of `cfg.Options` with its files in `dir`
(`StartCluster`), runs `cfg.Proposers` proposers of configuration changes (`Reconfigure`) and, if
their pauses are not zero, disruptions of leadership (`Disrupt`) and crashes (`Crash`), until the
clients are done; the clients are `lintest.Run`'s, `cfg.Clients` of `cfg.Ops` operations of `Gen`'s
traffic (`Put`, `Get`, `Read`) traced with `clock`, and porcupine checks the trace against `Model`
with no timeout. For options a cluster may run with (`kdOptsOk`), any clock with `clockSpec` (whose
invariants are not `lintestN`), under `lintest.Run`'s bounds on the clients and operations, fewer
than `2^31 - 2` proposers (the `WaitGroup`'s counter, the disruptions' and the crashes' goroutines
added), raft's step bound (`StartCluster`'s), and the files of every replica id `1 … 9` in `dir`
absent, owned in a files' invariant (`durableFilesInv`, `dfile`: what `Main` allocates from the
program's files): porcupine answers `Ok`, and the cluster is returned running, with the crasher's
token (the crashes are over; what `Stop` takes).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvdurable.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.lintest.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.Alloc

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvdurable

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt durableExt]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvdurable.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [AllG GF] [KdStor GF]

attribute [local instance] kdStorageModel

/-- See the file header. -/
abbrev Run.spec : Prop :=
  ∀ (cfg : github_com.mit_pdos.etcd_grove.examples.kvdurable.Config) (clockVal : w64 → IProp GF)
    (t0 : w64) (Eclk : CoPset) (clock : GoFunc) (dir : GoString) (γf : GName),
  kdOptsOk cfg.Options' → receiptBound GF ≤ 2 ^ 61 →
  (↑lintest.lintestN : CoPset) ⊆ ⊤ \ Eclk →
  0 ≤ sint.Z cfg.Clients' → sint.Z cfg.Clients' < 2 ^ 31 → 0 ≤ sint.Z cfg.Ops' →
  sint.Z cfg.Clients' * sint.Z cfg.Ops' < 2 ^ 60 → sint.Z cfg.Proposers' < 2 ^ 31 - 2 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kvdurable ∗
      context.isClosedchanInit ∗ kdStorInv ∗ lintest.clockSpec clockVal Eclk clock ∗ clockVal t0 ∗
      durableFilesInv γf kdFilesN ∗
      [∗list] i ∈ kvreconf.allIds, dfile γf (kdFileName dir i) none }}
    (App (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.kvdurable.Run)) (Val #cfg))
      (Val #clock)) (Val #dir))
  {{ (res : GoString) (c : Loc), RET (PairV #res #c);
      ⌜res = go!"Ok"⌝ ∗ ∃ (γ : KdNames) (vs : List w64), isClusterC γ vs dir c ∗ crasher γ }}

end spec

end kvdurable
end EtcdGrove
end Perennial
