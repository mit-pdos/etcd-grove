/-
The `hashMap` freelist as an implementation of the freelist interface (`FLImpl`). It keeps
the free ids as spans of consecutive ids: `forwardMap` maps each span's first id to its size
(`sp`), `backwardMap` its last id to its size, `freemaps` each size to the set of first ids of
the spans of that size, and `freePagesCount` the number of free ids.

`hmRaw` owns these fields and maps, with their contents; `hashOK` says they are consistent
and that the free ids are the spans' ids (`spansFree`): the spans are disjoint, of positive
size, and do not wrap around. Its handle, as `array`'s, is the `shared` field (set once).
-/
module

public import Proof.go_etcd_io.bbolt.internal.freelist.Lemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt.internal.freelist

/-- The spans (first id ↦ size) have positive sizes, do not wrap around, and are disjoint. -/
def spansOK (sp : GMap w64 w64) : Prop :=
  (∀ st sz, sp !! st = some sz → 1 ≤ uint.Z sz ∧ uint.Z st + uint.Z sz ≤ 2 ^ 64) ∧
  (∀ st sz st' sz' x, sp !! st = some sz → sp !! st' = some sz' → st ≠ st' →
    inRun st (uint.nat sz) x → ¬ inRun st' (uint.nat sz') x)

/-- The free ids `free` are the ids of the spans, increasing. -/
def spansFree (sp : GMap w64 w64) (free : List w64) : Prop :=
  PgidsIncr free ∧ ∀ x, x ∈ free ↔ ∃ st sz, sp !! st = some sz ∧ inRun st (uint.nat sz) x

/-- The maps of a `hashMap` agree: `bwm` is `sp` by last ids, `sets` by size (no size with no
span). -/
def mapsOK (sp bwm : GMap w64 w64) (sets : GMap w64 (GMap w64 Unit)) : Prop :=
  (∀ k v, bwm !! k = some v ↔ ∃ st, sp !! st = some v ∧ k = st + v - W64 1) ∧
  (∀ sz st, (∃ set, sets !! sz = some set ∧ (set !! st).isSome) ↔ sp !! st = some sz) ∧
  (∀ sz set, sets !! sz = some set → ∃ st, (set !! st).isSome)

/-- A consistent `hashMap` holding the free ids `free`. -/
def hashOK (cnt : w64) (sp bwm : GMap w64 w64) (sets : GMap w64 (GMap w64 Unit))
    (free : List w64) : Prop :=
  spansOK sp ∧ spansFree sp free ∧ mapsOK sp bwm sets ∧ uint.Z cnt = free.length ∧
  free.length < 2 ^ 63

section preds
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.freelist.Assumptions]

/-- The fields of the `hashMap` at `h` but its `shared`, and its maps' contents. -/
def hmRaw (h : Loc) (cnt : w64) (sp bwm : GMap w64 w64) (sets : GMap w64 (GMap w64 Unit)) :
    IProp GF :=
  iprop(∃ (fm fw bw : Loc) (FM : GMap w64 Loc),
    "Hcnt" ∷ structFieldRef hashMap go!"freePagesCount" h ↦ cnt ∗
    "Hfmf" ∷ structFieldRef hashMap go!"freemaps" h ↦ fm ∗
    "Hfwf" ∷ structFieldRef hashMap go!"forwardMap" h ↦ fw ∗
    "Hbwf" ∷ structFieldRef hashMap go!"backwardMap" h ↦ bw ∗
    "Hfm" ∷ fm ↦$ FM ∗ "Hsets" ∷ ([∗map] _sz ↦ l;st ∈ FM;sets, l ↦$ st) ∗
    "Hfw" ∷ fw ↦$ sp ∗ "Hbw" ∷ bw ↦$ bwm)

/-- The `hashMap` at `h` points to its `shared` at `s`. -/
def hashHdl (h : Loc) (s : Loc) : IProp GF :=
  iprop(structFieldRef hashMap go!"shared" h ↦□ s)

instance hashHdl_persistent (h s : Loc) : Persistent (hashHdl (GF := GF) h s) := by
  unfold hashHdl; infer_instance

/-- The `hashMap` at `h` holds the free ids `free`. -/
def ownHashPart (h : Loc) (_s : Loc) (free : List w64) : IProp GF :=
  iprop(∃ (cnt : w64) (sp bwm : GMap w64 w64) (sets : GMap w64 (GMap w64 Unit)),
    "Hraw" ∷ hmRaw h cnt sp bwm sets ∗ "%Hok" ∷ ⌜hashOK cnt sp bwm sets free⌝)

/-- The `hashMap` at `h` as an implementation of the freelist interface. -/
def hashImpl (h : Loc) : FLImpl (GF := GF) :=
  ⟨go.GoType.PointerType hashMap.ty, #h, ownHashPart h, hashHdl h,
    fun _ => by unfold hashHdl; infer_instance⟩

end preds

end bbolt
end EtcdGrove
end Perennial
