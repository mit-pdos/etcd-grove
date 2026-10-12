/-
The pure model of the backend above its buffers (`batch_tx.go`, `read_tx.go`, `backend.go`):
the batch transaction's state, the readers' view, and what the batch lock keeps true. Lean-first
(no Rocq counterpart); see `notes/decisions.md`, "The backend: the buffers, bbolt as a key-value
contract, the locks and the views".

**Buckets.** The backend's clients name a bucket by a `Bucket` value with an id and a name
(`BucketInfo`); the buffers are keyed by id, bbolt by name. `BParams.BT` is the clients' table of
buckets (name to id, injective: schema's buckets).

**Views.** A view (`VFun`) is a lookup function: bucket name, key, value. `dget D` is bbolt's
data's; `ovB BT B base` overlays the buffer buckets `B` (by id) on `base` (the newest entry of a
key in its bucket wins: `lastVal`). The readers see `viewOf st = ovB BT st.R.bks (dget st.C)`:
the committed data of the batch interval with the read buffer over it. The writer's bbolt
contents `S`, while no delete is pending, are the committed data with the read buffer then the
write buffer over it. `agreeOff HB f g`: the two views agree except on the hook's buckets `HB`.

**The batch transaction's state** (`BSess`): committed data `C`, writer contents `S`, read and
write buffers, `pending` and `pendingDeleteOperations`. `sessWf` holds always; `freeOk` when the
lock is free (no delete pending, `pending` below the limit, the write buffer empty but for the
hook's buckets: the leftovers of the last commit's hook).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBbolt
public import Proof.go_etcd_io.etcd.server.v3.storage.backend.ModelLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace backend

/-- The backend's parameters: the clients' buckets (name to id), the buckets the pre-commit hook
writes, how many entries one run of the hook puts at most, and the configuration's batch
limit. -/
structure BParams where
  BT : GMap GoString w64
  HB : GoString → Bool
  hookMax : Nat
  limit : w64

/-- The parameters are sane: bucket ids distinct, the limit positive and small enough that the
buffers do not overflow (`bufBound`), the hook's puts few. -/
def BParams.Wf (P : BParams) : Prop :=
  (∀ n1 n2 i, P.BT.lookup n1 = some i → P.BT.lookup n2 = some i → n1 = n2) ∧
  0 < sint.Z P.limit ∧ sint.Z P.limit ≤ 2 ^ 57 ∧ P.hookMax ≤ 2 ^ 57

/-- A bucket of the table. -/
def BParams.has (P : BParams) (bi : BucketInfo) : Prop := P.BT.lookup bi.name = some bi.id

/-- A view: bucket name, key, value. -/
abbrev VFun := GoString → GoString → Option GoString

/-- bbolt's data as a view. -/
def dget (D : Data) : VFun := fun n k => (D.lookup n).bind (fun m => m.lookup k)

/-- The buffer buckets `B` (by id, through the table) over the view `base`. -/
def ovB (BT : GMap GoString w64) (B : GMap w64 (List Ent)) (base : VFun) : VFun :=
  fun n k => ((BT.lookup n).bind (fun i => lastVal (bkOf B i) k)).or (base n k)

/-- Two views agree off the hook's buckets. -/
def agreeOff (HB : GoString → Bool) (f g : VFun) : Prop :=
  ∀ n, HB n = false → ∀ k, f n k = g n k

/-- The batch transaction's state. -/
structure BSess where
  C : Data
  S : Data
  R : RBuf
  W : WBuf
  pend : w64
  ndel : w64

/-- What the readers see of a state: the committed data with the read buffer over it. -/
def viewOf (P : BParams) (st : BSess) : VFun := ovB P.BT st.R.bks (dget st.C)

/-- What the readers see, as a value: the committed data of the batch interval and the read
buffer (a ghost variable holds it: a view function is not countable). -/
abbrev RView := Data × RBuf

instance rbuf_countable : Pos.Countable RBuf :=
  countableOfLeftInverse (fun r : RBuf => (r.bks, r.ver)) (fun p => ⟨p.1, p.2⟩) (fun _ => rfl)

/-- The view of a readers' state. -/
def vOf (P : BParams) (rv : RView) : VFun := ovB P.BT rv.2.bks (dget rv.1)

/-- The buffers' buckets are the table's. -/
def idsOk (P : BParams) (B : GMap w64 (List Ent)) : Prop :=
  ∀ i es, B.lookup i = some es → ∃ n, P.BT.lookup n = some i

/-- The state's facts at any time. -/
def sessWf (P : BParams) (st : BSess) : Prop :=
  st.W.Wf ∧ st.R.Wf ∧ idsOk P st.W.bks ∧ idsOk P st.R.bks ∧
  0 ≤ sint.Z st.pend ∧ sint.Z st.pend < 2 ^ 58 ∧ 0 ≤ sint.Z st.ndel ∧
  (∀ i, (bkOf st.R.bks i).length ≤ sint.nat st.pend + P.hookMax ∧
    (bkOf st.W.bks i).length ≤ sint.nat st.pend + P.hookMax) ∧
  (st.pend = W64 0 → ∀ i, bkOf st.R.bks i = []) ∧
  (st.ndel = W64 0 → agreeOff P.HB (dget st.S) (ovB P.BT st.W.bks (viewOf P st)))

/-- The state's facts when the batch lock is free. -/
def freeOk (P : BParams) (st : BSess) : Prop :=
  sessWf P st ∧ sint.Z st.pend < sint.Z P.limit ∧ st.ndel = W64 0 ∧
  ∀ n i, P.BT.lookup n = some i → P.HB n = false → bkOf st.W.bks i = []

end backend
end EtcdGrove
end Perennial
