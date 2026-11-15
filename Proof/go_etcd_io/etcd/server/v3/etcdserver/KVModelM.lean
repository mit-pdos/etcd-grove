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

/-- **The committed log's shapes in the auth mode `on`**: `logShape` off (in a cluster that grants
leases or not, `lg`: the lease-grant stage's §2.8), `logShapeOn lm` on (auth-lease S3a: at the mode). -/
def logShapeM (on : Bool) (lm : lease.Mode) (L : List EntryModel) : Prop :=
  match on with
  | false => logShape lm L
  | true => logShapeOn lm L

/-- The shapes of either mode give a conf change's id `0`. -/
theorem logShapeM_cc (on : Bool) (lm : lease.Mode) (L : List EntryModel) (h : logShapeM on lm L) :
    ∀ m ∈ L, m.typ ≠ W32 0 → ccIdOf m.data = W64 0 := by
  cases on
  · exact fun m hm => (h m hm).2
  · exact fun m hm => (h m hm).2

theorem logShapeM_false (lm : lease.Mode) (L : List EntryModel) : logShapeM false lm L = logShape lm L :=
  rfl

theorem logShapeM_true (lm : lease.Mode) (L : List EntryModel) : logShapeM true lm L = logShapeOn lm L := rfl

theorem logShapeM_append (on : Bool) (lm : lease.Mode) (A B : List EntryModel) (h : logShapeM on lm (A ++ B)) :
    logShapeM on lm A := by
  cases on
  · exact fun m hm => h m (List.mem_append_left _ hm)
  · exact fun m hm => h m (List.mem_append_left _ hm)

/-- **`srvRest`'s lease table in the auth mode `on`** (auth-lease S3a, Draft rev 5 §4): the off table
`appliedTable` (`kvLeases` over the raft prefix and the applied entries, which ignores the auth layer)
off; with auth on the mode-`on` model's table over the same entries (`kvLeasesOn … srvAuthSt0`), which
keeps the table at a revocation the auth layer refused. -/
def appliedTableM (on : Bool) (γr : ReadNames) (A : List EntryModel) : LeaseTable :=
  if on then kvLeasesOn γr.kv srvAuthSt0 (γr.raft.pre ++ A) else appliedTable γr A

theorem appliedTableM_false (γr : ReadNames) (A : List EntryModel) :
    appliedTableM false γr A = appliedTable γr A := by
  simp [appliedTableM]

theorem appliedTableM_true (γr : ReadNames) (A : List EntryModel) :
    appliedTableM true γr A = kvLeasesOn γr.kv srvAuthSt0 (γr.raft.pre ++ A) := by
  simp [appliedTableM]

/-- **The model's table and `srvRest`'s agree at an empty raft prefix** (Draft rev 5 §3, review r4 N1
(a)): the mode-`on` model folds over the applied entries alone, `srvRest`'s table over the prefix and
them. -/
theorem appliedTableM_eq_model (γr : ReadNames) (A : List EntryModel) (h : γr.raft.pre = []) :
    (appliedTableM true γr A).ids =
      (kvRaftOfOn γr.kv.c0 γr.kv.ch0 (srvAuthSt0, γr.kv.log0, []) A).2.2.ids := by
  rw [appliedTableM_true, h, List.nil_append]; rfl

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
