/-
**The backend's deletable keys** (the backend-compaction stage, `notes/backend-cmp-plan.md` 3.2,
decisions O1 and O2; Draft, 2026-10-28). Lean-first (no Rocq counterpart).

mvcc's compaction deletes keys from the safe-range `Key` bucket, and readers never look them up
again (Go relies on it: a reader reads at or above the compaction revision). The backend's view
then becomes exact only up to those keys: a reader's physical state is *thin* of the logical view
the clients hold, missing only keys registered as deletable. The keys are registered by a
predicate `Φ` the backend's creator fixes (decision O1: a saved predicate, `dlReg`; mvcc's is its
late-bound `delKey`), so the backend's specs need no new parameter.

D22's clean read, restore over a new backend and snapshot sender rely on an exact view; the
exclusive token `dlNone` (decision O2), which the backend's opener returns and the first deletion
of a safe-range key consumes, gives its holder exactness.

Draft: the definitions the changed statements are written in. `BNames` does not hold the
registration's name yet (`g` is explicit here); folding it in, and the invariants' use of
`thinV` (`rtRest`, `batchGhostAt`, `cacheValid`), are the stage's next Draft step.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvBackend

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace backend

open Iris Iris.BI

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]

/-- **The deletable keys' registration** (persistent): the saved predicate `Φ` of
(bucket, key) pairs at the name `g`, fixed by the backend's creator. -/
def dlReg (g : GName) (Φ : GoString × GoString → IProp GF) : IProp GF :=
  savedPredOwn g DFrac.discard Φ

instance dlReg_persistent (g : GName) (Φ : GoString × GoString → IProp GF) :
    Persistent (dlReg (GF := GF) g Φ) := by
  unfold dlReg; infer_instance

/-- **The key `nk` (bucket, key) is deletable** (persistent): the registered predicate holds of it. -/
def dlIs (g : GName) (nk : GoString × GoString) : IProp GF :=
  iprop(∃ Φ : GoString × GoString → IProp GF, dlReg g Φ ∗ □ Φ nk)

instance dlIs_persistent (g : GName) (nk : GoString × GoString) :
    Persistent (dlIs (GF := GF) g nk) := by
  unfold dlIs; infer_instance

/-- **A physical view thin of the logical view `L`** (persistent): every entry of the physical
view `vd` is `L`'s, and an entry of `L` missing from `vd` is a deletable key. -/
def thinV (g : GName) (vd L : VData) : IProp GF :=
  iprop(⌜∀ nk v, vd.lookup nk = some v → L.lookup nk = some v⌝ ∗
    □ ∀ nk, ⌜L.lookup nk ≠ none ∧ vd.lookup nk = none⌝ -∗ dlIs g nk)

instance thinV_persistent (g : GName) (vd L : VData) : Persistent (thinV (GF := GF) g vd L) := by
  unfold thinV; infer_instance

/-- An exact view is thin. -/
theorem thinV_refl (g : GName) (vd : VData) : ⊢ thinV (GF := GF) g vd vd := by
  iunfold thinV
  isplitr
  · ipureintro; intro nk v h; exact h
  · iintro !> %nk %h
    exact absurd h.2 h.1

/-- **No safe-range key deleted yet** (exclusive; decision O2): its holder knows the view exact
(`thinV … vd L → vd = L`, the stage's next step). The backend's opener returns it; the first
`UnsafeDelete` of a safe-range bucket consumes it. -/
def dlNone (g : GName) : IProp GF := dghostVar g (DFrac.own 1) true

/-- **The safe-range discipline without the "no deletes" clause** (3.1; Draft): `safeSt`'s first two
parts. A committed key of a safe-range bucket need not be in the writer's contents any more
(compaction deletes it); the put condition carries "above the committed keys" itself
(`UnsafeSeqPut.specC`). Replaces `safeSt` when the batch lemmas are re-proved. -/
def safeStC (P : BParams) (st : BSess) : Prop :=
  safeRv P (st.C, st.R) ∧
  ∀ n i, P.BT.lookup n = some i → P.SB n = true →
    ∀ (kc vc : GoString) (e : Ent), (bktOf st.C n).lookup kc = some vc →
      e ∈ bkOf st.W.bks i → strLt kc e.1

/-- `safeSt` gives `safeStC`. -/
theorem safeStC_of (P : BParams) (st : BSess) (h : safeSt P st) : safeStC P st :=
  ⟨h.1, fun n i hi hs => (h.2 n i hi hs).1⟩

/-- **A cached read buffer reads thin of the logical view** (3.2; Draft): `cacheValid` with
"exactly" weakened to "thin of `L`" (a tombstone put and compacted within one commit interval: a
reader of the cached buffer may still see the deleted key, which it never looks up). -/
def cacheValidC (γ : BNames) (g : GName) (P : BParams) (rv : RView) (idx : Nat) (L : VData) :
    IProp GF :=
  iprop(□ ∀ (i : Nat) (rv' : RView), ⌜i ≤ idx⌝ -∗ histAt γ rv.2.ver i rv' -∗
    cachedAt γ rv.2.ver i -∗ thinV g (vData P (rv.1, rv'.2)) L)

/-- **Every entry of the data `D` satisfies the value invariant `VI`** (3.3; Draft: `BParams.VI`'s
use; mvcc's instance, `metaVI`, makes the `Meta` bucket's compaction keys hold revisions, so that
`metaReadTx` is provable). -/
def viOk (VI : GoString → GoString → GoString → Prop) (D : Data) : Prop :=
  ∀ n k v, (bktOf D n).lookup k = some v → VI n k v

end defs

end backend
end EtcdGrove
end Perennial
