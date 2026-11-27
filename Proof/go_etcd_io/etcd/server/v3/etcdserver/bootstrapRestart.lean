/-
**The interim restart axiom** (2026-11-27; premises to axioms: until then the Iris premise
`etcdstart.bootPremiseR` of the closed single-process theorem): `bootstrap(cfg)` on a stopped member's
data directory (`Spec/.../etcdserver/bootstrapRestart.lean`). **Interim: retired when #34's stage 5
proves `bootstrap`'s restart branch** over its callees (`bootstrapWALFromSnapshot`, `bootstrapClusterWithWAL`,
`bootstrapRaftFromWAL`, `Finalize`'s `cl.Recover`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.bootstrapRestart

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [MemStorReg GF]

/-- **Interim trust boundary: `bootstrap(cfg)` on a stopped member's data directory**
(`bootstrap.specRestart`; interim, retired when #34 proves the restart branch). Its content is the restart
contract `bootstrapRestartContract` (`InvRestart.lean`: its docstring says what each premise, precondition
and post row is and why), which the closed theorems took as an Iris premise at the stopped member's id and
directory; here at Go's values (`bootGo.id`, `bootGo.dir`) under `bootstrap.spec`'s premises.

Why it is true of Go (`server/etcdserver/bootstrap.go` at the etcd pin): with a WAL in the dedicated WAL
directory (`srvFiles`: the files of an earlier incarnation of member `id`, `wal.Exist` true) `bootstrap` takes
the `haveWAL` branch: it opens the snapshot directory and the backend (the image `D`), recovers the WAL's
snapshot and records (`bootstrapWALFromSnapshot`, not forcing a new cluster: `ForceNewCluster` false), builds
the cluster from the WAL's metadata (`bootstrapClusterWithWAL`: the member id and cluster id the WAL's, no
remote, no request sent), finalizes it (`cl.Recover` from the backend's buckets: the image's members at its
committed log, whose peer URLs are the boot log's, so `Members()` answers the directory's `bootGo.dir`; the
cluster version the image's, `clusterVerLogOk`) and builds raft's restart (`bootstrapRaftFromWAL`: no peers,
`RestartNode`, the storage rebuilt from the records). Each step either returns an error (`bootstrap` closing
what it opened) or leaves what `bootOkR` names. The id the WAL records is `id`, Go's for this member, one of
the peers (the premise `bootGo.id cfg U ∈ bootGo.ps U token`), so raft's configuration names a voter of the
boot log. Go evidence: `examples/etcd/restart1` and `examples/etcd/restartN` (`TestRun`) stop a member and
build it again on its data directory through this branch. -/
axiom bootstrap.wp_proofRestart : bootstrap.specRestart (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
