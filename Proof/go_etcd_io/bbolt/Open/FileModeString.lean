/-
`fs.FileMode.String` under a method verb (`Open` logs the file mode with `%s`, `db.go`'s
`lg.Infof("Opening db file (%s) with mode %s and with options: %s", path, mode, options)`): the
`logArgOk` its spec gives the mode. The spec is `Spec/io/fs/FileMode__String.lean`, proved from its
translation (`Proof/io/fs/FileMode__String.lean`; translated with its body since 2026-11-18, session
S3g of `notes/bbolt-integration-plan.md`), which bbolt's `Link` gives `Open`.
-/
module

public import Spec.go_etcd_io.bbolt.Logger
public import Spec.io.fs.FileMode__String

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
