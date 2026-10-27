/-
**The server configuration's paths** (D22 S-f, 2026-10-19): `backendPathOf dataDir` (opaque), the
backend's database file of the data directory `dataDir` (`ServerConfig.BackendPath()`:
`datadir.ToBackendFileName(DataDir)`, `<dataDir>/member/snap/db`), which
`Spec/go_etcd_io/etcd/server/v3/config/ServerConfig__BackendPath.lean` returns and the backend's
opening (`storage.OpenBackend`) opens. Lean-first (no Rocq counterpart).
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.Golang.Theory

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace config

/-- **The backend's database file of the data directory `dataDir`** (opaque; see the file
header). -/
opaque backendPathOf [GooseExts] (dataDir : GoString) : GoString

end config
end EtcdGrove
end Perennial
