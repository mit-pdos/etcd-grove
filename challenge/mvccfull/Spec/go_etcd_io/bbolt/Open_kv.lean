/-
`Open_kv` (bbolt). `bolt.Open(path, mode, opts)`: the database the file holds, open, or an error.
The trust boundary: bbolt's key-value contract as the backend uses it (`InvBbolt.lean`), from the
Go documentation; an axiom in `Proof/go_etcd_io/bbolt/Open_kv.lean`. Lean-first (no Rocq
counterpart); see `notes/decisions.md`, "The backend: the buffers, bbolt as a key-value contract,
the locks and the views".

2026-10-17 (branch `construct`, the backend's constructor): the options are read (`optsAt`, a
fraction, given back: `Open` copies what it keeps), and must be options under which the contract
holds (`OptsM.ok`): not read-only (a read-only database has no write transaction: `Begin(true)`
fails), the default page size (`Open` initializes a new file with `4 * PageSize` bytes: a negative
one panics) and the default `OpenFile`; their logger nil or one bbolt may call (`boltLogger`).
Until then the spec took no options at all, which was false of bbolt for read-only options. The
database's data is `fileHolds path D`: for a new member's empty file, `D = ∅` (`Open` creates the
file and writes its meta pages). (2026-11-04, R2b-3c, the user's approval) The success case also
records which file the database is (`dbFile db path`), which `DB.Close_kv` gives back.

(2026-11-08, mvccrand's closed theorem, the user's decision) The error case also gives `¬ dbOpenOk`
(`InvBbolt.lean`), as `DB.Close_kv`'s gives `¬ dbCloseOk`: `Open` fails only for the environment's
reasons, which a closed theorem's premise `dbOpenOk` excludes.

(2026-11-06, branch `begin-tok`, the user's approval: `notes/begin-tok-plan.md`, Q2) Under
`[ThreadBoundLe GF (2 ^ 29)]`, as the proved `Open.spec` (`notes/bbolt-spec-decisions.md`, D3): the
read transactions each hold a thread's token (`DB.Begin_kv`): paid readers ≤ tokens < `2 ^ 29`,
and bbolt's transient readers (`View`, `freepages`: one per live thread, released within the call)
< `2 ^ 29`, so `mmaplock`'s readers stay below `sync.RWMutex`'s `2 ^ 30` (`rwmutexMaxReaders`); hence
`2 ^ 29` and not `2 ^ 30` (`notes/axiom-review/begin-tok-restated.md`). Without it a thread could
collect `2 ^ 30` tokens from forks that never exit.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.BboltOptions
public import Perennial.ProgramLogic.Bounds

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.bbolt backend

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `bolt.Open(path, mode, opts)`: the database the file holds, open, or an error; the options
read and given back. Under fewer than `2 ^ 29` live threads (the read transactions' tokens). -/
abbrev bbolt.Open_kv.spec : Prop :=
  ∀ [ThreadBoundLe GF (2 ^ 29)]
    (path : GoString) (mode : w32) (opts : Loc) (dq : DFrac) (o : OptsM) (D : Data),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ fileHolds path D ∗ optsAt opts dq o ∗
      ⌜o.ok⌝ ∗ (⌜o.logger = GoInterface.nil⌝ ∨ boltLogger o.logger) }}
    (App (App (App (Val (@! go_etcd_io.bbolt.Open)) (Val #path)) (Val #mode)) (Val #opts))
  {{ (db : Loc) (err : GoInterface), RET (PairV #db #err); optsAt opts dq o ∗
      -- (2026-11-08) an error only where the environment does not cooperate (`dbOpenOk`)
      (⌜err ≠ GoInterface.nil ∧ ¬ dbOpenOk⌝ ∨
       (⌜err = GoInterface.nil⌝ ∗ ∃ γ : DBNames, ownDB db γ D ∗ wrTok γ ∗ isDB db ∗
          -- (2026-11-04, R2b-3c, the user's approval) which file it is (`DB.Close_kv` gives it back)
          dbFile db path)) }}

end spec

end EtcdGrove
end Perennial
