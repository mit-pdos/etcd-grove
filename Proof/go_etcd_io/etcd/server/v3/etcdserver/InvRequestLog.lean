/-
The server's request logger (etcd#21764, pr-verify): the field `requestLogger` NewServer sets
(nil unless `--experimental-log-request-path` is given) and nothing writes afterwards, so its
callers hold it read-only (`srvReqLgAddr s ↦□ rl`). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApplier

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open go_etcd_io.etcd.server.v3.etcdserver

section addrs
variable [FfiSyntax] [GoGlobalContext] [GoSemanticsFunctions]

/-- The address of `s.requestLogger`. -/
abbrev srvReqLgAddr (s : Loc) : Loc := structFieldRef EtcdServer go!"requestLogger" s

end addrs

end EtcdGrove
end Perennial
