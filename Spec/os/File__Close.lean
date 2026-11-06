/-
`f.Close()` on an open `*os.File` (this repository's `os`, project `bboltfs`), with the whole fd
and the whole of the `*File`'s fd field: the model (`TrustedCode/os.lean`) sets the field to -1
and calls the extension's `Close` (`wp_osClose`), which frees the fd whatever the errno. The result
is any error; the `*File` keeps its name (`Name` still works). Proved in
`Proof/os/File__Close.lean`. Lean-first (no Rocq counterpart).
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
abbrev os.File.Close.spec : Prop :=
  ∀ (f : Loc) (fd : w64) (name : GoString) (d : OsFd),
  {{ osInv (GF := GF) ∗ os.ownFile (GF := GF) f fd name (DFrac.own 1) ∗
      osFd (GF := GF) fd (DFrac.own 1) d }}
    (App (Val (f @!! go.GoType.PointerType os.File.ty @!! go!"Close")) (Val #()))
  {{ (err : GoInterface), RET #err; os.ownFile f (-1 : w64) name (DFrac.own 1) }}

end spec

end EtcdGrove
end Perennial
