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

end syscall

end init

end Perennial
