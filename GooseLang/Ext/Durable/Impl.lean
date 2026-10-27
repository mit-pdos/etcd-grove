/-
The durable-state extension of GooseLang [Trusted definitions!].

A node's durable state: named files, each a string read and written whole. It is the
extension of the Go package `github.com/mit-pdos/etcd-grove/examples/durable` (its name),
whose functions are modeled by its operations
(`TrustedCode/github_com/mit_pdos/etcd_grove/examples/durable.lean`).

* `"Read"` of `f` returns the contents of the file `f` and `true`, or `""` and `false` if
  there is no file `f`.
* `"Write"` of `(f, data)` replaces the contents of the file `f` by `data`, creating it if it
  does not exist. The write is atomic and durable: once a read can see it, a crash keeps it,
  and a crash never exposes a partial write.
* Neither operation fails: the Go side retries a failed operation instead of reporting it,
  and serializes the operations, so that a write is durable before any read sees it.
* Crashes (`ExtSemantics.crash`): the files survive unchanged.
* Neither operation changes the heap; file names and contents are passed and returned as Go
  string values (`#f`, `#data`), and a read's results as a pair, as goose returns a Go
  function's two results.

Divergences from the Go side on a real filesystem, where the model is more defined than Go
(the same as Perennial's toy `fsExt`, of which this is the variant with absent files): names
are byte strings, so two names of one file (`x`, `./x`) are two files of the model; files the
operating system changes on its own are constant in the model; the temporary files a `Write`
interrupted by a crash leaves behind are not in the model; a `Read` of a huge file may exhaust
memory in Go and not in the model; a `Write` to a name whose directory does not exist retries
forever in Go and succeeds in the model.
-/
module

public import Perennial.GooseLang.Lang

@[expose] public section

namespace Perennial

/-- The files of a node: name to contents. -/
abbrev DurableState := GMap GoString GoString

instance : Inhabited DurableState := ⟨∅⟩

/-- The durable-state extension. It has no values of its own and no global state. -/
@[reducible] def durableExt : GooseExt where
  name := "github.com/mit-pdos/etcd-grove/examples/durable"
  Val := Empty
  LocalState := DurableState
  GlobalState := Unit

section durable
variable [GooseExts] [GoGlobalContext]

/-- What a read of the file `f` returns: its contents and `true`, or `""` and `false`. -/
def durableReadResult (fs : DurableState) (f : GoString) : val :=
  PairV (#((fs !! f).getD ([] : GoString))) (#((fs !! f).isSome))

/-- The step relation of the durable state. -/
def DurableStep (op : String) (v : val) (h : GMap Loc (NonAtomic val)) (fs : DurableState)
    (_g : Unit) (e' : Expr) (h' : GMap Loc (NonAtomic val)) (fs' : DurableState) (_g' : Unit) :
    Prop :=
  h' = h ∧
  match op with
  | "Read" => ∃ f : GoString, v = #f ∧ e' = Val (durableReadResult fs f) ∧ fs' = fs
  | "Write" => ∃ (f data : GoString),
      v = PairV (#f) (#data) ∧ e' = Val (#()) ∧ fs' = <[f := data]> fs
  | _ => False

end durable

/-- On a crash, the files survive unchanged. -/
instance durable_semantics : ExtSemantics durableExt where
  step := DurableStep
  crash fs fs' := fs' = fs

end Perennial
