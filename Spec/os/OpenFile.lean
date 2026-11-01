/-
`os.OpenFile(path, O_RDWR|O_CREATE, perm)` (this repository's `os`, project `bboltfs`), as
minibolt opens its file, the file existing or not: with the path's `OsMeta` (whole if there is no
file, so that the open may create it). The model (`TrustedCode/os.lean`) is the extension's `Open`
(`wp_Open`) with `O_CLOEXEC` added, retried on `EINTR`. On success a fresh `*os.File` on a fresh
fd, readable and writable, and the file exists (`openMeta`); on failure `nil` and a non-nil
error, and the file may have been created. Proved in `Proof/os/OpenFile.lean`. Lean-first (no
Rocq counterpart).
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
abbrev os.OpenFile.spec : Prop :=
  ∀ (path : GoString) (perm : w32) (q : DFrac) (mo : Option OsMeta),
  (mo = none → q = DFrac.own 1) →
  {{ osInv (GF := GF) ∗ osMeta (GF := GF) path q mo }}
    (App (App (App (Val (@! os.OpenFile)) (Val #path)) (Val #(W64 0x42))) (Val #perm))
  {{ (f : Loc) (err : GoInterface), RET (PairV #f #err);
      (∃ fd : w64, ⌜err = interface.nil⌝ ∗ os.ownFile f fd path (DFrac.own 1) ∗
          osFd fd (DFrac.own 1) ⟨path, true, true⟩ ∗ osMeta path q (openMeta mo true)) ∨
      (⌜err ≠ interface.nil ∧ f = null⌝ ∗
        ∃ mo' : Option OsMeta, ⌜mo' = mo ∨ mo' = openMeta mo true⌝ ∗ osMeta path q mo') }}

end spec

end EtcdGrove
end Perennial
