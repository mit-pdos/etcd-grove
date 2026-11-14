/-
`klog.argsOk`: the arguments of klog's `printf`-style calls (`klog.Errorf`, `Verbose.Infof`) that
klog formats without panicking (klog-args-fix, 2026-11-14, `notes/klog-args-fix.md`). klog v2.140.0
formats them with `fmt.Fprintf` in `loggingT.printfDepth` (`klog.go:764-784`), which recovers no
panic: an argument whose `Error()` panics with a value whose `String()` panics too escapes `fmt`'s
`catchPanic`, and a map written concurrently makes the runtime throw
(`examples/premisefix/klogargs`). Until then both specs took any arguments.

An argument is `fmt.argOkAt` its directive (`Spec/fmt/Errorf.lean`, `fmt`'s method verbs: what
`Printf` needs), or a `[]string` the caller owns, at any fraction (`klog.strSliceArg`: `fmt` prints
it by reflection, reading its elements and calling no method, under any verb; the compactor's
`c.client.Endpoints()`, a fresh copy). Lean-first (no Rocq counterpart).
-/
module

public import Spec.fmt.Errorf

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **A `[]string` argument the caller owns**, at fraction `dq`: the interface holding the slice
`sl`, whose elements `ss` the caller reads. `fmt` prints a `[]string` by reflection under any verb,
calling no method (a `[]string` has none; `string` neither), reading the elements, which the
ownership keeps from being written meanwhile. -/
def klog.strSliceArg (a : GoInterface) : IProp GF :=
  iprop(∃ (sl : GoSlice) (ss : List GoString) (dq : DFrac),
    ⌜a = interface.mkOk (go.GoType.SliceType go.string) #sl⌝ ∗ sl ↦*{dq} ss)

/-- **One argument of a klog `printf`-style call under the directive `d`**: one `fmt` formats
returning (`fmt.argOkAt` under `fmt`'s method verbs: `nil`, a predeclared basic value, an integer
under a non-method verb, an error or `Stringer` whose method returns under a method verb other
than `%#v`), or a `[]string` the caller owns (`klog.strSliceArg`). -/
def klog.argOkAt (d : fmt.Directive) (a : GoInterface) : IProp GF :=
  iprop(fmt.argOkAt fmt.methodVerbs d a ∨ klog.strSliceArg a)

/-- The arguments under the directives: one each, in order; those left over are printed under
`%v` (`EXTRA`), as in `fmt.argsOkAt`. -/
def klog.argsOkAt : List fmt.Directive → List GoInterface → IProp GF
  | _, [] => iprop(True)
  | d :: ds, a :: xs => iprop(klog.argOkAt d a ∗ klog.argsOkAt ds xs)
  | [], a :: xs => iprop(klog.argOkAt ⟨W8 118, false⟩ a ∗ klog.argsOkAt [] xs)

/-- **The arguments `xs` of the format `format`** of a klog `printf`-style call: the format's
directives parse (`fmt.fmtDirectives`: no `*` width or precision, no argument index), and each
argument is `klog.argOkAt` its directive. -/
def klog.argsOk (format : GoString) (xs : List GoInterface) : IProp GF :=
  iprop(∃ ds : List fmt.Directive, ⌜fmt.fmtDirectives format = some ds⌝ ∗ klog.argsOkAt ds xs)

/-- `klog.argsOk` from the format's directives. -/
theorem klog.argsOk_intro {format : GoString} {ds : List fmt.Directive} {xs : List GoInterface}
    (h : fmt.fmtDirectives format = some ds) :
    klog.argsOkAt (GF := GF) ds xs ⊢ klog.argsOk format xs := by
  unfold klog.argsOk
  iintro H
  iexists ds
  isplitr
  · ipureintro; exact h
  · iexact H

/-- An argument `fmt.argOkAt` its directive is `klog.argOkAt` it. -/
theorem klog.argOkAt_of_fmt {d : fmt.Directive} {a : GoInterface} :
    fmt.argOkAt (GF := GF) fmt.methodVerbs d a ⊢ klog.argOkAt d a := by
  unfold klog.argOkAt
  iintro H
  ileft
  iexact H

/-- A `fmt.argOk` argument (an error whose `Error()` returns, ...) is `klog.argOkAt` a method-verb
directive other than `%#v` (`%v`, `%s`). -/
theorem klog.argOkAt_of_argOk {d : fmt.Directive} {a : GoInterface} :
    ⌜d.verb ∈ fmt.methodVerbs ∧ d.sharpV = false⌝ ∗ fmt.argOk (GF := GF) a ⊢ klog.argOkAt d a := by
  cases a with
  | nil => unfold klog.argOkAt fmt.argOkAt; iintro _; ileft; itrivial
  | ok ii =>
    unfold klog.argOkAt fmt.argOkAt
    iintro ⟨%h, H⟩
    ileft; iright; iright
    isplitr
    · ipureintro; exact h
    · iexact H

/-- A `string` argument is `klog.argOkAt` any directive. -/
theorem klog.argOkAt_string {d : fmt.Directive} (s : GoString) :
    ⊢ klog.argOkAt (GF := GF) d (interface.mkOk go.string #s) := by
  iapply klog.argOkAt_of_fmt
  unfold fmt.argOkAt
  ileft
  ipureintro
  exact (show _root_.Perennial.fmt.ArgsWf [interface.mkOk go.string #s] from
    .cons_string _ _ .nil) _ (List.mem_singleton_self _)

/-- An `int64` argument is `klog.argOkAt` any directive. -/
theorem klog.argOkAt_int64 {d : fmt.Directive} (n : w64) :
    ⊢ klog.argOkAt (GF := GF) d (interface.mkOk go.int64 #n) := by
  iapply klog.argOkAt_of_fmt
  unfold fmt.argOkAt
  ileft
  ipureintro
  exact (show _root_.Perennial.fmt.ArgsWf [interface.mkOk go.int64 #n] from
    .cons_int _ _ _ (.int64 _) .nil) _ (List.mem_singleton_self _)

/-- A `[]string` the caller owns is `klog.argOkAt` any directive. -/
theorem klog.argOkAt_strSlice {d : fmt.Directive} (sl : GoSlice) (ss : List GoString) (dq : DFrac) :
    sl ↦*{dq} ss ⊢ klog.argOkAt (GF := GF) d (interface.mkOk (go.GoType.SliceType go.string) #sl) := by
  iintro H
  unfold klog.argOkAt klog.strSliceArg
  iright
  iexists sl, ss, dq
  isplitr
  · ipureintro; rfl
  · iexact H

end defs

/-- Turns a goal `klog.argsOk format xs` of a literal format into `klog.argsOkAt` its directives,
unfolded over the argument list (as `wp_slice_literal` builds it): one `klog.argOkAt d a` per
argument, then `True`; each closes by `klog.argOkAt_string`, `klog.argOkAt_int64`,
`klog.argOkAt_strSlice` or `klog.argOkAt_of_argOk`. -/
macro "klog_args_intro" : tactic => `(tactic| (
  try rw [show sint.nat (W64 (0 + 1)) = 1 by rfl]
  try simp only [List.set_cons_succ, List.set_cons_zero]
  iapply Perennial.EtcdGrove.klog.argsOk_intro (by rfl)
  try simp only [Perennial.EtcdGrove.klog.argsOkAt]))

end EtcdGrove
end Perennial
