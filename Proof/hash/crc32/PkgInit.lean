/-
`hash/crc32`'s package fact (prove-etcdint3, 2026-11-21: until then `True`, in the WAL's
`DepsPkgInit.lean`):
- `IEEETable` holds, read-only, a pointer to the IEEE polynomial's table
  (`var IEEETable = simpleMakeTable(IEEE)`, `crc32.go:101`, translated with `simpleMakeTable`'s body),
  which is not the Castagnoli table: what `New(tab)` of a Castagnoli table needs to skip its IEEE
  branch (`if tab == IEEETable { ieeeInitOnce() }`, `crc32.go:146-151`), and `update` its IEEE path;
- (crc32-hooks2, 2026-11-22: `MakeTable` and `update` translated, etcd-grove#14) `castagnoliInitOnce`
  holds, read-only, a function every call of which returns with the Castagnoli table set up
  (`castagnoliReady`: `castagnoliTable` holds, read-only, a pointer to it), the once of
  `sync.OnceFunc` (`crc32.go:83-98`, Perennial's `sync.OnceFunc.spec`);
- the invariant `haveInv`: `haveCastagnoli` is an `atomic.Bool` that, once true, says the table is set
  up and `updateCastagnoli` holds, read-only, a function computing CRC-32C (`updSpec`: the arch hook
  or the slicing-by-8 closure), what `update` reads after `haveCastagnoli.Load()` (`crc32.go:203-205`).
-/
module

public import GeneratedProof.hash.crc32
public import Spec.hash.crc32.Model
public import Perennial.Proof.ProofPrelude
public import Perennial.Proof.sync.Base
public import Perennial.Proof.sync.atomic.Base
public import Proof.hash.PkgInit
public import Proof.internal.byteorder.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace hash.crc32

/-- `crc32.IEEE` (`crc32.go:30`): the reversed IEEE polynomial. -/
def ieeePoly : w32 := 0xedb88320#32

/-- **The IEEE table** (what `simpleMakeTable(IEEE)` builds). -/
def ieeeTableArr : GoArray w32 256 := array.mk 256 (crcTableOf ieeePoly)

/-- Entry `128` of `simplePopulateTable(poly)` is `poly` (`0x80` shifts to `1` in seven steps,
then `(1 >> 1) ^ poly`). -/
theorem crcTableEntry_128 (poly : w32) : crcTableEntry poly 128 = poly := by
  simp [crcTableEntry, crcBits, crcBit]

/-- The IEEE and Castagnoli tables differ (at entry `128`, their polynomials). -/
theorem ieeeTableArr_ne : ieeeTableArr ≠ castagnoliTableArr := by
  intro h
  have h2 := congrArg (fun a : GoArray w32 256 => a.arr[128]?) h
  simp only [ieeeTableArr, castagnoliTableArr, crcTableOf, List.getElem?_map,
    List.getElem?_range (show 128 < 256 by decide), Option.map_some, crcTableEntry_128] at h2
  revert h2; decide

end hash.crc32

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

namespace hash.crc32

/-- The Castagnoli table is set up: `castagnoliTable` holds, read-only, a pointer to it. -/
def castagnoliReady : IProp GF :=
  iprop(∃ t : Loc, globalAddr castagnoliTable ↦□ t ∗ t ↦□ castagnoliTableArr)

instance castagnoliReady_persistent : Persistent (castagnoliReady (GF := GF)) := by
  unfold castagnoliReady; infer_instance

/-- `u` computes CRC-32C (`updateCastagnoli`'s value: `archUpdateCastagnoli` or the slicing-by-8
closure). -/
def updSpec (u : GoFunc) : IProp GF :=
  iprop(∀ (c : w32) (s : GoSlice) (bs : List w8) (dq : DFrac),
    {{ s ↦*{dq} bs }} (App (App (Val #u) (Val #c)) (Val #s)) {{ RET #(crc32c c bs); s ↦*{dq} bs }})

instance updSpec_persistent (u : GoFunc) : Persistent (updSpec (GF := GF) u) := by
  unfold updSpec; infer_instance

/-- `haveCastagnoli`'s invariant: once true, the table is set up and `updateCastagnoli` holds,
read-only, a function computing CRC-32C. -/
def haveInv : IProp GF :=
  iprop(∃ b : Bool, sync.atomic.ownBool (globalAddr haveCastagnoli) (DFrac.own 1) b ∗
    (if b then castagnoliReady ∗ ∃ u : GoFunc, globalAddr updateCastagnoli ↦□ u ∗ updSpec u
     else True))

/-- The namespace of `haveInv`. -/
def crc32N : Namespace := nroot.@"hash_crc32"

/-- **`hash/crc32`'s fact** (see the file header). -/
def crc32Init : IProp GF :=
  iprop((∃ t : Loc, globalAddr IEEETable ↦□ t ∗ t ↦□ ieeeTableArr) ∗
    (∃ g : GoFunc, globalAddr castagnoliInitOnce ↦□ g ∗
      {{ True }} (App (Val #g) (Val #())) {{ RET #(); castagnoliReady }}) ∗
    inv crc32N haveInv)

instance crc32Init_persistent : Persistent (crc32Init (GF := GF)) := by
  unfold crc32Init; infer_instance

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.hash.crc32 :=
  define_is_pkg_init crc32Init
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.hash.crc32 :=
  build_get_is_pkg_init_wf

end hash.crc32

end init

end Perennial
