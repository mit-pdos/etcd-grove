/-
# A backend image as the state machine at a point (batch 4a, integration Y)

What 2d's `beSnap bs γ k` and `dbReader rc γ k` (and 2e's `beHolds γ img ci`) say of an image: **the
image `I` is the state machine at the state `σ`, its consistent index `ci`** (`smImage I σ ci`), each
owner's part of the image decoding to `σ`'s part. A pure relation (no resource): the server's
invariant attaches it to the images it commits (`beCommitted`, through its commit step `commitOk`),
and the snapshot path reads it back (`Backend.beSnapN γ s I n` of a committed `I`, no older than the caller's history prefix:
`backend.Snapshot.spec`'s `beHistLb`).

* mvcc's part (the `key` bucket, `meta`'s compaction keys): an image of `σ.kv`
  (`Mvcc.mvccImage (keyDataOf I) σ.kv u`, its compaction possibly unfinished: `u`);
* the consistent index: `meta` exists and its `consistent_index` key holds `ci` (4b's
  `Schema.ciOf`);
* the lessor's part: the `lease` bucket holds `σ`'s live leases with their TTLs
  (`LeaseBackend.lean`'s `leaseImg`);
* the rest (`smRest`, opaque `Prop`): auth's three buckets decode to `σ.auth` (3d's records over 4b's
  `authpb` decodings, `Schema.userName`/`roleName`: provisional there), membership's and alarms'
  buckets to `σ.members`, `σ.alarms` (2e's, over 4b's `Schema.memberBktsAt`, `alarmsAt`); the
  schema's version. Opaque until their owners state those relations (recorded in
  `notes/specs-only/integration-Y.md`).

For 2d (X): `beSnap bs γ k := ∃ γb s I n σ, ⌜bs = GoInterface.ok (snapshot s)⌝ ∗ Backend.beSnapN γb s I
n ∗ histAt γ k σ ∗ ⌜smImage I σ k⌝`; `dbReader rc γ k := ∃ I σ, Snap.dbReader rc I ∗ histAt γ k σ ∗
⌜smImage I σ k⌝` (2e's `Snap.BeImage` being `Backend.Image`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.LeaseBackend

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Backend

open Iris Iris.BI

section model
variable [GooseExts] [GoGlobalContext]

/-- **The image's other owners' parts are `σ`'s** (auth, membership, alarms, the schema version):
opaque until their owners state their decodings (see the header). -/
opaque smRest (I : Image) (σ : EtcdModel.State) : Prop

/-- **The image `I` is the state machine at the state `σ`, consistent index `ci`** (see the
header). -/
def smImage (I : Image) (σ : EtcdModel.State) (ci : Nat) : Prop :=
  (∃ u, Mvcc.mvccImage (keyDataOf I) σ.kv u) ∧
  I.made metaBkt = true ∧ uint.nat (Schema.ciOf (I.ents metaBkt)).1 = ci ∧
  leaseImg I (fun i => (σ.leases i).map EtcdModel.LeaseRec.ttl) ∧
  smRest I σ

end model

end Backend
end EtcdGrove
end Perennial
