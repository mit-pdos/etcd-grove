/-
`(*lazybuf).index` (`path.go`; rafthttp stage 5d). Lean-first; the buffer: `Proof/path/Defs.lean`.
-/
module

public import Proof.path.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `b.index(i)` below the path's length: the buffer's byte `i`. -/
abbrev path.lazybuf.index.spec : Prop :=
  ∀ (b : Loc) (p : GoString) (P : List w8) (w i : Nat),
  i < p.length →
  {{ isPkgInit (PROP := IProp GF) pkg_id.path ∗ path.lbOwn b p P w }}
    (App (Val (b @!! go.GoType.PointerType _root_.Perennial.path.lazybuf.ty @!! go!"index"))
      (Val #(W64 (i : Int))))
  {{ RET #(P.getD i 0); path.lbOwn b p P w }}

end spec

end EtcdGrove
end Perennial
