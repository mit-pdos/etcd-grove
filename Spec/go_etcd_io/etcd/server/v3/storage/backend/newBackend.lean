/-
`newBackend` (`backend.go`). `newBackend(bcfg)`: bbolt's options built from the configuration,
the database at `bcfg.Path` opened (bbolt's `Open`; on an error `lg.Panic`), the backend's
structure, its batch transaction (`newBatchTxBuffered`: its first commit begins bbolt's
transactions), the hooks set, the periodic committer `run` started on a goroutine. Lean-first
(no Rocq counterpart); 2026-10-17, branch `construct` (`notes/STATUS.md`, "Item 6").

The pre: the backend package's facts, `boltOpenOptions` (a package fact not yet in
`backendInit`: `BboltOptions.lean`), the database file's contents `D` (`fileHolds`; a new member's
file: `D = ∅`), the parameters `P` (`P.Wf`, the configuration's batch limit), the hooks'
contract of the configuration's hooks (`hooksOk`: given the backend later; `hooksOk_nil` for no
hooks), and the creator's batch-lock resources `W γ`, `Pk γ`, made from the client's half of the
hook's own keys once the backend's ghost names `γ` exist. The post: the backend (`newPost`), or a
panic (bbolt's `Open` failed: `lg.Panic`). Stated at `HasLC.hasLC` (the `run` goroutine's spec
is).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvNew
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.BboltOptions

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.backend backend

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- `newBackend(bcfg)`: a backend over the database file's data `D`, or a panic. -/
abbrev backend.newBackend.spec : Prop :=
  ∀ (cfg : BackendConfig) (P : BParams) (D : Data) (W Pk : BNames → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      fileHolds cfg.Path' D ∗ ⌜P.Wf ∧ P.limit = cfg.BatchLimit'⌝ ∗
      hooksOk P W Pk cfg.Hooks' ∗ (∀ γ : BNames, hkOwn γ (hkData P D) ={⊤}=∗ W γ ∗ Pk γ) }}
    (App (Val (@! newBackend)) (Val #cfg))
  {{ (r : val), RET r; (∃ (b : Loc) (γ : BNames), ⌜r = #b⌝ ∗ newPost γ P W Pk b D) ∨
      ⌜∃ p : val, r = PanicV p⌝ }}

end spec

end EtcdGrove
end Perennial
