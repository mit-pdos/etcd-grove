/-
`(*lazybuf).append` (`path.go`; rafthttp stage 5d). Lean-first; the buffer: `Proof/path/Defs.lean`.
-/
module

public import Proof.path.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `b.append(c)` below the path's length: `c` written at `w`, the bytes before kept. -/
abbrev path.lazybuf.append.spec : Prop :=
  ∀ (b : Loc) (p : GoString) (P : List w8) (w : Nat) (c : w8),
  w < p.length →
  {{ isPkgInit (PROP := IProp GF) pkg_id.path ∗ path.lbOwn b p P w }}
    (App (Val (b @!! go.GoType.PointerType _root_.Perennial.path.lazybuf.ty @!! go!"append"))
      (Val #c))
  {{ RET #(); ∃ P' : List w8, path.lbOwn b p P' (w + 1) ∗
      ⌜P'.take (w + 1) = P.take w ++ [c] ∧ P'.length = p.length⌝ }}

end spec

end EtcdGrove
end Perennial
