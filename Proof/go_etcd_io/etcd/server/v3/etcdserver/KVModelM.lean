/-
**The KV model in either auth mode** (`kvModelM`, `logShapeM`; moved out of `ServerOn.lean`,
strict M1, 2026-11-05, so that the server's store invariant over mvcc's API, `KVStoreApi.lean`,
imports the model without the server's proofs). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVAuthModel

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

/-- **The auth state the mode-`on` KV model starts from**: the store's latest at the server's
start (`newAuthStore_boot`: the history `[bootState, bump bootState]`, the revision committed
once). -/
def srvAuthSt0 : auth.AuthState := auth.bump auth.bootState

section pure
variable [GooseExts]

/-- **The committed log's shapes in the auth mode `on`**: `logShape` off, `logShapeOn` on. -/
def logShapeM (on : Bool) (L : List EntryModel) : Prop :=
  match on with
  | false => logShape L
  | true => logShapeOn L

/-- The shapes of either mode give a conf change's id `0`. -/
theorem logShapeM_cc (on : Bool) (L : List EntryModel) (h : logShapeM on L) :
    ∀ m ∈ L, m.typ ≠ W32 0 → ccIdOf m.data = W64 0 := by
  cases on
  · exact fun m hm => (h m hm).2
  · exact fun m hm => (h m hm).2

theorem logShapeM_false (L : List EntryModel) : logShapeM false L = logShape L := rfl

theorem logShapeM_true (L : List EntryModel) : logShapeM true L = logShapeOn L := rfl

theorem logShapeM_append (on : Bool) (A B : List EntryModel) (h : logShapeM on (A ++ B)) :
    logShapeM on A := by
  cases on
  · exact fun m hm => h m (List.mem_append_left _ hm)
  · exact fun m hm => h m (List.mem_append_left _ hm)

/-- **The KV model of the committed log `L` in the auth mode `on`**: `kvModel` off, the mode-`on`
model from the server's start state (`kvModelOn … srvAuthSt0`) on. -/
def kvModelM (on : Bool) (γk : KVNames) (L : List EntryModel) : mvcc.Log :=
  match on with
  | false => kvModel γk L
  | true => kvModelOn γk srvAuthSt0 L

theorem kvModelM_false (γk : KVNames) (L : List EntryModel) :
    kvModelM false γk L = kvModel γk L := rfl

theorem kvModelM_true (γk : KVNames) (L : List EntryModel) :
    kvModelM true γk L = kvModelOn γk srvAuthSt0 L := rfl

end pure

end EtcdGrove
end Perennial
