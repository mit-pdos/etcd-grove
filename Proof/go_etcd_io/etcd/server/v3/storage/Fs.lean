/-
The part of `OpenSnapshotBackend`'s vocabulary (`InvSnapshotBackend.lean`) that the package
fact of `server/v3/storage` needs, in etcd PR #22499 (branch `pr-verify/etcd-22499`), where
`syncSnapDir` is a package-level variable holding a function value, not a function:

```go
var syncSnapDir = func(dir string) error { d, err := fileutil.OpenDir(dir); ...; return fileutil.Fsync(d) }
```

`OpenSnapshotBackend` loads the variable and calls what it holds, so what it can rely on is a
fact about the variable: the package's `isPkgInit` (`storageInit`, the instance in
`etcdserver/apply/Base.lean`) says that the variable holds, read-only (`↦□`), the function
literal of its declaration (`syncSnapDir.lit`, checked against the translated initializer by
`syncSnapDir.lit_in_initialize`). Read-only is what production code gives: nothing outside the
package initializer writes `syncSnapDir` (the PR's tests do, `backend_test.go`; a test is not
part of the verified code). `syncSnapDir.wp_lit` (`storage/syncSnapDirLit.lean`) proves that the
literal syncs a directory (`syncSnapDirFn`, there).

The durability resources are those of etcd PR #22518's verification (branch
`pr-verify/etcd-22518`, `InvSnapshotBackend.lean`), moved here (with #22518's later refinement: both name the rename's source too): `fs.renamePending`,
`fs.entryDurable`, `fs.dirOf`, `fsResult` (see there). Lean-first (no Rocq counterpart).
-/
module

public import Spec.fmt.Errorf
public import GeneratedProof.go_etcd_io.etcd.server.v3.storage

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

/-- The directory containing the path `p` (`filepath.Dir(p)`). -/
opaque fs.dirOf : GoString → GoString

section defs
variable {GF : BundledGFunctors}

/-- The rename of `src` onto `dst` has happened; its directory entry may not be durable yet. -/
opaque fs.renamePending (src dst : GoString) : IProp GF := iprop(True)

/-- The directory entry `dst`, naming the file renamed from `src`, is durable (on stable
storage). -/
opaque fs.entryDurable (src dst : GoString) : IProp GF := iprop(True)

end defs

section lit
variable [FfiSyntax] [GoGlobalContext]

/-- The body of the function literal `func(dir string) error { ... }` that `syncSnapDir`'s
initializer stores (copied from `storage.initialize'`, `Code/go_etcd_io/etcd/server/v3/
storage.lean`; `syncSnapDir.lit_in_initialize` checks the copy against the translation). -/
def syncSnapDir.litBody : Expr :=
  (App (Val wrapDefer)
  (Lam "$defer"
  (Let "dir" (App (Val (GoInstruction (GoAlloc go.string))) (Var "dir"))
  (Let "__p" (Let "$a0" (App (Val (GoInstruction (GoLoad go.string))) (Var "dir"))
  (App (App (Val (GoInstruction (FuncResolve _root_.Perennial.go_etcd_io.etcd.client.pkg.v3.fileutil.OpenDir []))) (Val #())) (Var "$a0")))
  (Let "$ret0" (Fst (Var "__p"))
  (Let "$ret1" (Snd (Var "__p"))
  (Let "$r0" (Var "$ret0")
  (Let "$r1" (Var "$ret1")
  (Let "err" (App (Val (GoInstruction (GoAlloc go.error))) (App (Val (GoInstruction (GoZeroVal go.error))) (Val #())))
  (Let "d" (App (Val (GoInstruction (GoAlloc (go.GoType.PointerType _root_.Perennial.os.File.ty)))) (App (Val (GoInstruction (GoZeroVal (go.GoType.PointerType _root_.Perennial.os.File.ty)))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Let "$a0" (App (Val (GoInstruction (GoLoad (go.GoType.PointerType _root_.Perennial.os.File.ty)))) (Var "d"))
  (App (App (Val (GoInstruction (FuncResolve _root_.Perennial.go_etcd_io.etcd.client.pkg.v3.fileutil.Fsync []))) (Val #())) (Var "$a0"))))))
  (App (Val doExecute)
  (Let "$f" (App (Val (GoInstruction (MethodResolve (go.GoType.PointerType _root_.Perennial.os.File.ty) go!"Close"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType _root_.Perennial.os.File.ty)))) (Var "d")))
  (App (Val (GoInstruction (GoStore deferType))) (Pair (Var "$defer") (Let "$oldf" (App (Val (GoInstruction (GoLoad deferType))) (Var "$defer"))
  (Lam BAnon
  (Seq (App (Var "$f") (Val #()))
  (App (Var "$oldf") (Val #()))))))))))))
  (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoUnOp GoNot go.bool))) (App (Val (GoInstruction (GoOp GoEquals go.error))) (Pair (App (Val (GoInstruction (GoLoad go.error))) (Var "err")) (App (Val (GoInstruction (Convert go.untypedNil go.error))) (Val UntypedNil))))))
  (App (Val doReturn)
  (App (Val (GoInstruction (GoLoad go.error))) (Var "err")))
  (App (Val doExecute)
  (Val #()))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.error))) (Pair (Var "err") (Var "$r1")))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore (go.GoType.PointerType _root_.Perennial.os.File.ty)))) (Pair (Var "d") (Var "$r0")))))))))))))))

/-- The function value of that literal: what `syncSnapDir` holds after initialization. -/
def syncSnapDir.lit : GoFunc := func.mk BAnon (Binder.BNamed "dir") syncSnapDir.litBody

/-- The first function literal bound by a `let` (`Let x (Lam y b) rest`, Goose's `x := func(y)
{...}`) in a left-to-right walk of `e`: its name, parameter, body and scope, in a search
bounded by `n`. -/
def firstLetLit : Nat → Expr → Option (Binder × Binder × Expr × Expr)
  | 0, _ => none
  | _ + 1, App (Rec .BAnon x rest) (Rec .BAnon y b) => some (x, y, b, rest)
  | n + 1, App f a => (firstLetLit n f).orElse (fun _ => firstLetLit n a)
  | n + 1, Rec _ _ e => firstLetLit n e
  | _ + 1, _ => none

/-- The package variable that a pair `(GlobalVarAddr g _, Var x)` (the operands of a store
`*&g = x`, `GoStore t (GlobalVarAddr g #(), Var x)`) names, the first in a left-to-right walk of
`e`, bounded by `n`. (It does not look into values: the initializer's names-only parts are
axioms, which a match on a value cannot reduce.) -/
def firstGlobalStoreOf (x : String) : Nat → Expr → Option GoString
  | 0, _ => none
  | _ + 1, Pair (App (Val (val.GoInstruction (Perennial.GoInstruction.GlobalVarAddr g))) _)
      (Var x') => if x' = x then some g else none
  | n + 1, App f a => (firstGlobalStoreOf x n f).orElse (fun _ => firstGlobalStoreOf x n a)
  | n + 1, Rec _ _ e => firstGlobalStoreOf x n e
  | _ + 1, _ => none

/-- **The literal is the translation's**: the first statement of `server/v3/storage`'s package
initializer binds `$r0` to a function literal of parameter `dir` and body
`syncSnapDir.litBody`, and the first store of `$r0` into a package variable in its scope (the first pair
`(GlobalVarAddr g _, $r0)`, a `GoStore`'s operands) is into `syncSnapDir` (`storage.initialize'`, read with the translation; that nothing rebinds `$r0`
in between is checked by reading it, `Code/go_etcd_io/etcd/server/v3/storage.lean`: the
statements between are the names-only initializers of the quota variables). The initializer is
not proved (see `storageInit`). -/
theorem syncSnapDir.lit_in_initialize :
    (match go_etcd_io.etcd.server.v3.storage.initialize' with
      | RecV _ _ e => (firstLetLit 200 e).map (fun (x, y, b, rest) =>
          (x, y, b, firstGlobalStoreOf "$r0" 200 rest))
      | _ => none) =
    some (Binder.BNamed "$r0", Binder.BNamed "dir", syncSnapDir.litBody,
      some go_etcd_io.etcd.server.v3.storage.syncSnapDir) := by
  rfl

end lit

section defs2
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- A returned error: `nil` with `P`, or an error whose `Error()` returns some string, with
`Q`. -/
def fsResult (err : GoInterface) (P Q : IProp GF) : IProp GF :=
  iprop((⌜err = interface.nil⌝ ∗ P) ∨
    (∃ e : GoInterfaceOk, ⌜err = interface.ok e⌝ ∗ fmt.stringMethodSpec e go!"Error" ∗ Q))

/-- **`server/v3/storage`'s package fact** (etcd PR #22499): the package variable `syncSnapDir`
holds, read-only, the function literal of its declaration (`syncSnapDir.lit`), which syncs a
directory (`syncSnapDir.wp_lit`, `storage/syncSnapDirLit.lean`). An assumption about the
package's initialization, as for the other etcd packages (its initializer runs the
names-only initializers of `quotaBackendBytes`, `DefaultQuotaSize`, `maxQuotaSize`, opaque, so
it cannot be proved): it stores `syncSnapDir.lit` (`syncSnapDir.lit_in_initialize`), and no
code but the package's tests writes the variable afterwards. -/
def storageInit : IProp GF :=
  iprop(globalAddr go_etcd_io.etcd.server.v3.storage.syncSnapDir ↦□ syncSnapDir.lit)

instance storageInit_persistent : Persistent (storageInit (GF := GF)) := by
  unfold storageInit; infer_instance

end defs2

end EtcdGrove
end Perennial
