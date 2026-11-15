/-
`fs.FileMode.String` (`Open` logs the file mode with `%s`, `db.go`'s `lg.Infof("Opening db file
(%s) with mode %s and with options: %s", path, mode, options)`): its spec, and the `logArgOk` it
gives the mode under a method verb.

**Not proved here.** `Code/io/fs.lean` translates `FileMode`'s type and method set only
(`Code/io/fs.toml`'s `translate` list names `FileMode`, not `FileMode.String`), so the method has no
`MethodUnfold` to prove the spec from: `Open.wp_proof` takes it as a hypothesis. Adding
`"FileMode.String"` to `Code/io/fs.toml` and regenerating (project `bboltfs`) gives the body, a
loop over the mode's bits writing into a `[32]byte` (`io/fs/fileinfo.go`), and the spec a proof.
The spec itself is true of Go's `FileMode.String`: it reads only its receiver, never panics (its
buffer is large enough for every mode: 19 type letters, a hyphen or not, 9 permission letters).
-/
module

public import Spec.go_etcd_io.bbolt.Logger

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode

section s
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **`mode.String()`** returns some string, needing nothing. -/
abbrev fs.FileMode.String.spec : Prop :=
  ∀ (mode : w32),
  {{ (True : IProp GF) }}
    (App (Val #(methods io.fs.FileMode.ty go!"String" #mode)) (Val #()))
  {{ (s : GoString), RET #s; True }}

omit hos in
/-- **The mode, under a method verb**, is an argument a `boltLogger` accepts (a Stringer: no
`Format`, no `Error`, `String() string`), whatever it is lent. -/
theorem fileMode_logArgOk [io.fs.Assumptions] (hStr : fs.FileMode.String.spec (GF := GF) (hG := hG))
    (R : IProp GF) (v : w8) (hv : v ∈ methodVerbs) (mode : w32) :
    ⊢ logArgOk (GF := GF) R v (interface.mkOk io.fs.FileMode.ty #mode) := by
  simp only [logArgOk]
  iright; iright; ileft
  isplitr
  · ipureintro
    have h1 := (go.MethodSetIs.method_set_is (t := io.fs.FileMode.ty) go!"Format")
    have h2 := (go.MethodSetIs.method_set_is (t := io.fs.FileMode.ty) go!"Error")
    have h3 := (go.MethodSetIs.method_set_is (t := io.fs.FileMode.ty) go!"String")
    simp (config := { decide := true }) only [go.methodSetLookup, reduceIte] at h1 h2 h3
    refine ⟨by simpa using h1, by simp [h2], by simpa [noArgStringSig] using h3, hv⟩
  unfold stringMethodWith
  imodintro
  iintro %Φ HR HΦ
  wp_apply hStr mode as %s -
  iapply HΦ $$ HR

end s

end bbolt
end EtcdGrove
end Perennial
