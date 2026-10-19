/-
`mvccpb.KeyValue` (etcd's `api/v3/mvccpb/kv.proto`) as a pure record, shared by the server's
state machine (`etcdserver/StateMachine.lean`) and the clients' model of etcd
(`cache/v3/EtcdModel.lean`). Lean-first (no Rocq counterpart).
-/
module

public import Perennial.Golang.Defn.String

@[expose] public section

namespace Perennial
namespace EtcdGrove

/-- A key-value as etcd stores it (`mvccpb.KeyValue`'s fields). -/
structure EtcdKv where
  key : GoString
  createRev : w64
  modRev : w64
  version : w64
  value : GoString
  lease : w64

end EtcdGrove
end Perennial
