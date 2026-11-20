/-
Lean-first (no Rocq counterpart).

# `k8s.io/apiserver/pkg/storage`: an error's `*StorageError` code (stage 7g)

`errCodeAt err dq c`: what `isErrCode` reads of `err` (`errors.go:198`, a type assertion to
`*StorageError`, no unwrapping): `c = none` for `nil` or a dynamic type other than
`*StorageError`; `c = some code` for a `*StorageError` held at `dq` with that code.
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`err`'s `*StorageError` code**, if it is one (see the file header). -/
def errCodeAt (err : GoInterface) (dq : DFrac) : Option w64 → IProp GF
  | none => iprop(⌜err = GoInterface.nil ∨ ∃ ii : GoInterfaceOk, err = GoInterface.ok ii ∧
      ii.ty ≠ go.GoType.PointerType k8s_io.apiserver.pkg.storage.StorageError.ty⌝)
  | some code => iprop(∃ (l : Loc) (s : k8s_io.apiserver.pkg.storage.StorageError),
      ⌜err = interface.mkOk (go.GoType.PointerType k8s_io.apiserver.pkg.storage.StorageError.ty) #l ∧
        s.Code' = code⌝ ∗ l ↦{dq} s)

end defs

end k8s
end EtcdGrove
end Perennial
