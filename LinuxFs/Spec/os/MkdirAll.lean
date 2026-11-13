/-
`os.MkdirAll(path, perm)` (this repository's `os`, part `LinuxFs`) in the tree's shared mode
(`GooseLang/Ext/Fs/TreeShared.lean`; `notes/wal-fsext-i2-design.md`, "Implementation log,
`os.MkdirAll`"), for the WAL's case: `path = d/b`, `d` an existing directory (a spine to it) and `b`
absent (a claim on it). The model (`TrustedCode/os.lean`) asks `PathKind` (`d/b` is below a root),
`Stat`s `d/b` (absent: an error), runs `MkdirAll(d)` (which changes nothing: `nil` or an error),
then, if that returned `nil`, `Mkdir(d/b)` (`os.Mkdir.specS`), and after a failed `Mkdir`, `Lstat`s
`d/b`: a directory there makes the result `nil`.

* `os.MkdirAll.specS`: logically atomic as `os.Mkdir.specS` (the same claim split caller/update,
  outcome `Option (x, s, J)`, `mkOut`, `mkNew`). `none`: no effect, the error non-nil (`MkdirAll(d)`
  failed, the update committed with `none` without a step; or `Mkdir` failed with no effect).
  `some`: the `mkdir` logged; the error may be non-nil (`Mkdir` took effect and then failed, and
  `Lstat` failed or did not see a directory). The spine to `d` is held at a fraction `DFrac.own qd`
  (statement change from `os.Mkdir.specS`'s any `dq`: the `Lstat` of `d/b` needs a spine to it,
  made of fractions of the spine and of the caller's claim).

Proved in `Proof/os/MkdirAll.lean`. Lean-first (no Rocq counterpart).
-/
module

public import LinuxFs.Spec.os.Mkdir

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI
open Fs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [os.Assumptions]

/-- See the file header. -/
abbrev os.MkdirAll.specS : Prop :=
  ∀ (d b : GoString) (perm : w32) (R : Roots) (j : Ino) (qd : Qp) (h : NamesH) (q r : Qp)
    (Q : Option (Nat × Nat × Ino) → IProp GF),
  NameOk b → h.cur !! b = none → q + r = 1 →
  {{ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R d (DFrac.own qd) j ∗ osCallPerm 1 ∗
      osNames j (.only [b]) (DFrac.own q) h ∗
      osAU (osNames j (.only [b]) (DFrac.own r) h) (mkOut j b h (DFrac.own r)) Q }}
    (App (App (Val (@! os.MkdirAll)) (Val #(child d b))) (Val #perm))
  {{ (err : GoInterface), RET #err; osPathS R d (DFrac.own qd) j ∗ osCallPerm 1 ∗
      ∃ o, ⌜err = interface.nil → o.isSome⌝ ∗ Q o ∗ mkOut j b h (DFrac.own q) o ∗ mkNew o }}

end spec

end EtcdGrove
end Perennial
