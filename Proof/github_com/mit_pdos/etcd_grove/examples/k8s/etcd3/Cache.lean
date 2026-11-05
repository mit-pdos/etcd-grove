/-
Lean-first (no Rocq counterpart).

# k8setcd3: the clients' cached objects (stage 7b)

`Gen` draws a `Delete` or a `GuaranteedUpdate` with its client's cached object (the test's
`cachedObj`: the client's last answer with a name), which the store takes as its
`cachedExistingObject`: an object the key held at its resource version (`versionAt`, the store's
`cachedOk`). The table `cache` holds them, under its `sync.Mutex`:

- `cachedObjOk c ob`: the object fits a `DObj` (`dobjOf`), its resource version is not `0`, and
  **every** key held it at that resource version (`versionAt`, at every key): `Gen` hands a client's
  cached object to an operation on any key, not only on the one it came from. For another key it
  holds as no key but one changes at a revision (one write per revision: `Apply`'s, the seed's),
  so no other key has that mod revision; for its own key, the answer's object is the one written
  at its resource version (or, for a `Delete`'s answer, none is: the key was deleted there).
- `cacheInv c tbl`: the table's map, owned, every entry `cachedObjOk` (persistent facts: `Apply`
  adds an entry from an answer it has the facts of, `Gen` reads one).
- `isCache c tbl`: the mutex, with `cacheInv` as its lock invariant (persistent).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Inv
public import Perennial.Proof.sync.Base

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProofMode k8s
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Obj item)

section pure
variable [GooseExts]

/-- A Go `Obj`'s store object: its name, UID and value (the zero object if a name or a UID is
256 bytes or longer: never for a cached object, `cachedObjOk`). -/
def dobjOf (ob : Obj) : DObj :=
  if h : ob.Name'.length < 256 ∧ ob.UID'.length < 256 then ⟨(ob.Name', ob.UID', ob.Value'), h⟩
  else dzero

/-- The object `Apply` caches for an answer (`Obj{Name: out.Name, UID: out.UID, Value: out.Value,
ResourceVersion: out.RV}`). -/
def cachedOf (y : Output) : Obj := ⟨y.Name', y.UID', y.Value', y.RV'⟩

end pure

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- **A cached object** (see the file header): it fits a `DObj`, its resource version is not `0`,
and every key held it at that resource version. -/
def cachedObjOk (c : StoreCfg GF DObj) (ob : Obj) : IProp GF :=
  iprop(⌜ob.Name'.length < 256 ∧ ob.UID'.length < 256 ∧ ob.ResourceVersion' ≠ W64 0⌝ ∗
    □ ∀ k : GoString, versionAt c k ob.ResourceVersion' (dobjOf ob))

instance cachedObjOk_persistent (c : StoreCfg GF DObj) (ob : Obj) :
    Persistent (cachedObjOk (GF := GF) c ob) := by
  unfold cachedObjOk; infer_instance

/-- **The table's state** (`cache`'s lock invariant; see the file header): its map, owned, every
entry a cached object. -/
def cacheInv (c : StoreCfg GF DObj) (tbl : Loc) : IProp GF :=
  iprop(∃ (mp : GoMap) (m : GMap w64 Obj),
    tbl.[github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.cache, go!"objs"] ↦ mp ∗ mp ↦$ m ∗
    [∗map] _id ↦ ob ∈ m, cachedObjOk c ob)

/-- **The table** (see the file header; persistent): its mutex, with `cacheInv`. -/
def isCache (c : StoreCfg GF DObj) (tbl : Loc) : IProp GF :=
  iprop(sync.isMutex (tbl.[github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.cache, go!"mu"])
    (cacheInv c tbl))

instance isCache_persistent (c : StoreCfg GF DObj) (tbl : Loc) :
    Persistent (isCache (GF := GF) c tbl) := by
  unfold isCache; infer_instance

/-- **An input's cached object is one** (`Gen`'s output): if the input uses one. -/
def cachedIn (c : StoreCfg GF DObj) (x : Input) : IProp GF :=
  if x.UseCached' then cachedObjOk c x.Cached' else iprop(True)

instance cachedIn_persistent (c : StoreCfg GF DObj) (x : Input) :
    Persistent (cachedIn (GF := GF) c x) := by
  unfold cachedIn; split <;> infer_instance

end defs

end k8s_etcd3
end EtcdGrove
end Perennial
