/-
`hash/crc32`'s package fact (prove-etcdint3, 2026-11-21: until then `True`, in the WAL's
`DepsPkgInit.lean`): `IEEETable` holds, read-only, a pointer to the IEEE polynomial's table
(`var IEEETable = simpleMakeTable(IEEE)`, `crc32.go:101`, translated with `simpleMakeTable`'s body),
which is not the Castagnoli table: what `New(tab)` of a Castagnoli table needs to skip its IEEE
branch (`if tab == IEEETable { ieeeInitOnce() }`, `crc32.go:146-151`).
-/
module

public import GeneratedProof.hash.crc32
public import Spec.hash.crc32.Model
public import Perennial.Proof.ProofPrelude
public import Perennial.Proof.sync.Base
public import Perennial.Proof.sync.atomic.Base
public import Proof.hash.PkgInit

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

/-- **`hash/crc32`'s fact** (see the file header). -/
def crc32Init : IProp GF :=
  iprop(∃ t : Loc, globalAddr IEEETable ↦□ t ∗ t ↦□ ieeeTableArr)

instance crc32Init_persistent : Persistent (crc32Init (GF := GF)) := by
  unfold crc32Init; infer_instance

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.hash.crc32 :=
  define_is_pkg_init crc32Init
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.hash.crc32 :=
  build_get_is_pkg_init_wf

end hash.crc32

end init

end Perennial
