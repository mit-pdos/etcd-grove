/-
**A writer's cursor facts** (maintainer 16, `notes/bbolt-proof-plan.md`; U6aa's `wrCurFacts`, moved
here from `Read/PubWCur` with `nlocCur` from `Read/WCur` so that `Inv/Tx.wtxFrac` holds it): what a
writer cursor's moves read node references and a bucket's root position by. Pure; the producers'
lemmas are `Write/WrCur`'s.
-/
module

public import Proof.go_etcd_io.bbolt.Model.Cursor

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section wrcur
variable [GooseExts]

/-- **The node-location registry is the live buckets' node caches** (U6z): a registered node of a
live bucket is that bucket's materialized node of its position, and every materialized node of a
live bucket is registered at its position (`nodeAdded` does both). Before `Commit` a bucket's node
cache only grows, and a dead bucket (`DeleteBucket`) is out of `liveB`. What lets a writer
cursor's node reference, registered when the cursor moved, be read later (its object is the live
node of its position), and a move register the nodes it reaches (their fragments, `nlFrags`). -/
def nlocCur (X : WX) : Prop :=
  (∀ l b p, X.nloc !! l = some (b, p) → b ∈ X.liveB →
    ∃ B, X.t.bs !! b = some B ∧ B.nm !! W64 (p : Int) = some l) ∧
  ∀ b B c l, X.t.bs !! b = some B → b ∈ X.liveB → B.nm !! c = some l →
    X.nloc !! l = some (b, c.toNat)

/-- The value of the root bucket's entry `n` in the writer's logical tree (its first binding, as
`bktData`'s). -/
def rootEntVal (X : WX) (n : GoString) : Option (List w8) :=
  ((rootEnts X).find? fun e => decide (e.1 = n)).map Prod.snd

/-- The root page the root bucket's entry `n` records (`0`: inline, or no entry). -/
def rootEntRef (X : WX) (n : GoString) : Nat := ((rootEntVal X n).map inBucketRoot).getD 0

/-- **The writer facts a cursor reads under** (U6aa; in `wtxFrac`'s facts, maintainer 16): the
node registry names current nodes (`nlocCur`); a top-level bucket's root position is `wRoot`
(U6y's F5: its base root while its generation is `0`; inline once deleted and re-created); what
keeps the latter across an open: the root bucket's entry of every name records `wRoot` (`rootEntRef`;
`0` for an absent name); and every registered node's bucket is one the transaction opened (what
keeps `nlocCur` across an open, at a fresh location). -/
def wrCurFacts (T : TxView) (X : WX) : Prop :=
  nlocCur X ∧ (∀ n b, bktLoc X n = some b → (X.rootPid b).toNat = wRoot X.v T n) ∧
  (∀ n, rootEntRef X n = wRoot X.v T n) ∧
  ∀ l b p, X.nloc !! l = some (b, p) → (X.t.bobjs !! b).isSome

end wrcur

end bbolt
end EtcdGrove
end Perennial
