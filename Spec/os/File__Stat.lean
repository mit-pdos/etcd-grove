/-
`f.Stat()` on an open `*os.File` (this repository's `os`, project `bboltfs`), with a fraction of
the file's `OsMeta`, so that no change in flight resizes it and the size is exact. The model
(`TrustedCode/os.lean`) is the extension's `Fstat` (`wp_Fstat`), retried on `EINTR`, whose size
it stores in a fresh `fileStat`. On success the result is that `*fileStat` as a `FileInfo`, holding
the size (`os.ownFileStat`, read by `Size`, `Spec/os/fileStat__Size.lean`); on failure a nil
`FileInfo` and a non-nil error. Proved in `Proof/os/File__Stat.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Proof.os.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [os.Assumptions]

/-- See the file header. -/
abbrev os.File.Stat.spec : Prop :=
  ∀ (f : Loc) (fd : w64) (name : GoString) (dqf dq dqm : DFrac) (d : OsFd) (m : OsMeta),
  {{ osInv (GF := GF) ∗ os.ownFile (GF := GF) f fd name dqf ∗ osFd (GF := GF) fd dq d ∗
      osMeta (GF := GF) d.path dqm (some m) }}
    (App (Val (f @!! go.GoType.PointerType os.File.ty @!! go!"Stat")) (Val #()))
  {{ (fi : GoInterface) (err : GoInterface), RET (PairV #fi #err);
      os.ownFile f fd name dqf ∗ osFd fd dq d ∗ osMeta d.path dqm (some m) ∗
      ((∃ fs : Loc, ⌜err = interface.nil ∧
          fi = interface.mkOk (go.GoType.PointerType os.fileStat.ty) #fs⌝ ∗
          os.ownFileStat fs (W64 m.size)) ∨
       ⌜err ≠ interface.nil ∧ fi = interface.nil⌝) }}

end spec

end EtcdGrove
end Perennial
