/- Lean-first (no Rocq counterpart).

`Run(cfg, clock)` (check.go): starts a cluster of `cfg.Options` (`StartCluster`), runs
`cfg.Proposers` proposers of configuration changes (`Reconfigure`) and, if `cfg.DisruptPause` is
not zero, disruptions of leadership (`Disrupt`), until the clients are done; the clients are
`lintest.Run`'s, `cfg.Clients` of `cfg.Ops` operations of `Gen`'s traffic (`Put`, `Get`, `Read`)
traced with `clock`, and porcupine checks the trace against `Model` with no timeout. For options a
cluster may run with (`OptsOk`), any clock with `clockSpec` (whose invariants are not `lintestN`),
under `lintest.Run`'s bounds on the clients and operations, fewer than `2^31 - 1` proposers (the
`WaitGroup`'s counter), and raft's step bound (`StartCluster`'s): porcupine answers `Ok`, and the
cluster is returned running, with the stopper's token (what `Stop` takes).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.DefsCluster
public import Proof.github_com.mit_pdos.etcd_grove.examples.lintest.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvreconf

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvreconf.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [AllG GF] [KvrStor GF]

attribute [local instance] kvrStorageModel

/-- See the file header. -/
abbrev Run.spec : Prop :=
  ∀ (cfg : github_com.mit_pdos.etcd_grove.examples.kvreconf.Config) (clockVal : w64 → IProp GF)
    (t0 : w64) (Eclk : CoPset) (clock : GoFunc),
  OptsOk cfg.Options' → receiptBound GF ≤ 2 ^ 64 - 2 →
  (↑lintest.lintestN : CoPset) ⊆ ⊤ \ Eclk →
  0 ≤ sint.Z cfg.Clients' → sint.Z cfg.Clients' < 2 ^ 31 → 0 ≤ sint.Z cfg.Ops' →
  sint.Z cfg.Clients' * sint.Z cfg.Ops' < 2 ^ 60 → sint.Z cfg.Proposers' < 2 ^ 31 - 1 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kvreconf ∗
      context.isClosedchanInit ∗ kvrStorInv ∗ lintest.clockSpec clockVal Eclk clock ∗ clockVal t0 }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.kvreconf.Run)) (Val #cfg))
      (Val #clock))
  {{ (res : GoString) (c : Loc), RET (PairV #res #c);
      ⌜res = go!"Ok"⌝ ∗ ∃ (γr : RNames) (vs : List w64), isClusterC γr vs c ∗ stopper γr }}

end spec

end kvreconf
end EtcdGrove
end Perennial
