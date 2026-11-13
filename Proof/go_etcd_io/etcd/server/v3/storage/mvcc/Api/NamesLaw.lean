/-
**`names_nonempty.law`** (track A, 2026-11-06). Lean-first (no Rocq counterpart). Over the sealed
definitions of `Api.lean` (imported with `import all`): a store's and a stream's names are records
of ghost names, a backend instance and a channel, each inhabited.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api
import all Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc
namespace api

section law
variable [GooseExts]

/-- **`names_nonempty.law` holds.** -/
theorem names_nonempty.law_holds : names_nonempty.law := by
  refine ⟨⟨?_⟩, ⟨?_⟩⟩
  · show StoreNames
    constructor <;> first | exact default | (constructor <;> exact default)
  · show WsAbs
    constructor <;> first | exact default |
      (constructor <;> first | exact default | (constructor <;> exact default))

end law

end api
end mvcc
end EtcdGrove
end Perennial
