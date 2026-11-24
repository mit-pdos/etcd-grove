/-
The package-initialization instance of this repository's `syscall` (project bboltfs's translation,
`Code/syscall.lean`; Perennial has none), for the packages that import it (bbolt, minibolt). Its fact
is `errorsOk` (2026-11-24): the error table `errors`, which `Errno.Error` reads, held for good, each
message at most `errnoMsgMax` bytes; the rest of what the initializer writes nothing reads.
Its `wp_initialize'` is `Init.lean` (generated, `etc/gen-init.py`).
-/
module

public import GeneratedProof.syscall
public import Perennial.Proof.ProofPrelude
public import Perennial.Proof.sync.Base
public import Perennial.Proof.errors.Base
public import Perennial.Proof.internal.oserror.Base
public import Proof.internal.gomodel.Base
public import Perennial.Proof.internal.strconv.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

namespace syscall

/-- The longest message of the error table `errors` (`zerrors_linux_amd64.go`: 49 bytes) and of
`"errno " + Itoa(e)` (at most 26), rounded up. -/
def errnoMsgMax : Nat := 64

/-- The error table `errors` (`[133]string`), held for good, every message at most `errnoMsgMax`
bytes. -/
def errorsOk : IProp GF :=
  iprop(∃ tbl : GoArray GoString 133, typedPointsto (globalAddr errors) tbl DFrac.discard ∗
    ⌜∀ s ∈ tbl.arr, s.length ≤ errnoMsgMax⌝)

instance errorsOk_persistent : Persistent (errorsOk (GF := GF)) := by
  unfold errorsOk; infer_instance

/-- A bound on every element survives a `set` of an element within it (the table's initializer
writes its entries one by one: `Init.lean`). -/
theorem forall_mem_set_of {P : GoString → Prop} {l : List GoString} (i : Nat) (x : GoString)
    (hx : P x) (hl : ∀ s ∈ l, P s) : ∀ s ∈ l.set i x, P s := fun s hs => by
  rcases List.mem_or_eq_of_mem_set hs with h | h
  · exact hl s h
  · exact h ▸ hx

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.syscall :=
  define_is_pkg_init errorsOk
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.syscall :=
  build_get_is_pkg_init_wf

/-! `internal/strconv`'s package fact is timeless (its own fact is `True`; it imports `math/bits`,
whose fact is a persistent points-to of a table, which imports `unsafe`): `os.ownFile` carries it
(`errnoOk`), and bbolt's invariants need its timelessness. -/

instance isPkgInit_unsafe_timeless : Timeless (isPkgInit (PROP := IProp GF) pkg_id.«unsafe») := by
  rw [isPkgInit_unfold]
  unfold named
  simp only [IsPkgInit.isPkgInitDeps, IsPkgInit.isPkgInitDef]
  infer_instance

instance isPkgInit_bits_timeless : Timeless (isPkgInit (PROP := IProp GF) pkg_id.math.bits) := by
  rw [isPkgInit_unfold]
  unfold named
  simp only [IsPkgInit.isPkgInitDeps, IsPkgInit.isPkgInitDef]
  infer_instance

instance isPkgInit_strconv_timeless :
    Timeless (isPkgInit (PROP := IProp GF) pkg_id.internal.strconv) := by
  rw [isPkgInit_unfold]
  unfold named
  simp only [IsPkgInit.isPkgInitDeps, IsPkgInit.isPkgInitDef]
  infer_instance

/-- What `Errno.Error` needs (`Proof/syscall/ErrorOk.lean`): the error table (`errorsOk`) and
`internal/strconv`'s package fact (`Itoa`). Persistent and timeless; `os.ownFile` carries it. -/
def errnoOk : IProp GF :=
  iprop(errorsOk ∗ isPkgInit (PROP := IProp GF) pkg_id.internal.strconv)

instance errnoOk_persistent : Persistent (errnoOk (GF := GF)) := by
  unfold errnoOk; infer_instance

instance errnoOk_timeless : Timeless (errnoOk (GF := GF)) := by
  unfold errnoOk errorsOk; infer_instance

/-- `syscall`'s package fact. -/
theorem errorsOk_of_isPkgInit :
    isPkgInit (PROP := IProp GF) pkg_id.syscall ⊢ errorsOk (GF := GF) := by
  with_unfolding_all exact isPkgInit_access (PROP := IProp GF) pkg_id.syscall

/-- `errnoOk` from `syscall`'s package fact. -/
theorem errnoOk_of_isPkgInit :
    isPkgInit (PROP := IProp GF) pkg_id.syscall ⊢ errnoOk (GF := GF) := by
  iintro #H
  ihave #Hs : isPkgInit (PROP := IProp GF) pkg_id.internal.strconv $$ [H]
  · iPkgInit
  ihave #He := errorsOk_of_isPkgInit $$ H
  unfold errnoOk
  iframe He Hs

end syscall

end init

end Perennial
