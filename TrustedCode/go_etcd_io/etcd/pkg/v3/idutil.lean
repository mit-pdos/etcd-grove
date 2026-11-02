/-
Trusted code for etcd's `go.etcd.io/etcd/pkg/v3/idutil` (`id.go`), in the generated package's
namespace (the restart plan's R2c stage 2, 2026-11-02, `notes/restart-plan.md`).

**`(*Generator).Next`**, the Go body, translated (the generated code of `id.go`, with the generator's
type, `lowbit` and `suffixLen` named here: this module is imported by the translation, not the other
way round):

```go
func (g *Generator) Next() uint64 {
	suffix := atomic.AddUint64(&g.suffix, 1)
	id := g.prefix | lowbit(suffix, suffixLen)
	return id
}
```

with **one step added before the return**: `assume` of the issue record's `"Issue"` of `(id, g)`
(`GooseLang/Ext/IdIssue/Impl.lean`), which is `true` exactly when no other generator issued `id`, and
records `id ↦ g`. Perennial's `assume` does not return when its argument is `false` (`wp_assume`), so
the model excludes the executions in which two generators issue one id, and is Go's in every other.

**Why the model is faithful** (the issue's precondition, `issues/etcd-request-id-restart-reuse.md`):
generators of distinct members differ in the prefix (the member ids' 16 low bits distinct, a premise
of the examples, `TestMemberIDs`); a member's generators -- one per start of the member -- issue
distinct ids if the wall clock does not step back across a restart and the earlier generator, started
at millisecond t0, issues in all (handlers of the stopped incarnation may still call it) at most
256·(t1 − t0) ids, t1 the later one's start: the later one's first id is the earlier one's
(256·(t1 − t0) + 1)-th. etcd assumes this and does not check it (Go's comment asks for a restart
"after 1 ms", which is not enough by itself). One generator never issues
an id twice before its 48-bit suffix wraps, which the receipts' bound excludes (`idCred`). Where the
precondition fails (a clock stepped back), Go would hand a new request an old entry's result; the
model excludes that execution instead (the SOSP'26 paper's treatment of such limits,
`/shared/grove-paper/sosp26/rwmutex.tex`: assume the limit is never reached where it is reached).
-/
module

public import Perennial.Golang.Defn
public import Perennial.Golang.Defn.Assume
public import Perennial.Code.sync.atomic
public import GooseLang.Ext.IdIssue.Impl

@[expose] public section

set_option linter.all false

namespace Perennial

namespace go_etcd_io.etcd.pkg.v3.idutil
noncomputable section
variable [GooseExts] [GoGlobalContext]

/-- The generator's type (the translation's `Generator.ty`). -/
@[reducible] def model.Generator : go.GoType :=
  go.GoType.Named go!"go.etcd.io/etcd/pkg/v3/idutil.Generator" []

/-- `lowbit`'s name (the translation's `lowbit`). -/
@[reducible] def model.lowbit : GoString := go!"go.etcd.io/etcd/pkg/v3/idutil.lowbit"

/-- `suffixLen` (the translation's). -/
@[reducible] def model.suffixLen : val := #(48 : Int)

/-- See the file header. -/
noncomputable def Generator.Next.impl : val :=
  (LamV "g"
  (Lam BAnon
  (Let "$res0" (App (Val (GoInstruction (GoAlloc go.uint64))) (App (Val (GoInstruction (GoZeroVal go.uint64))) (Val #())))
  (Seq (App (Val exceptionDo)
  (Let "g" (App (Val (GoInstruction (GoAlloc (go.GoType.PointerType model.Generator)))) (Var "g"))
  (Let "$r0" (Let "$a0" (App (Val (GoInstruction (StructFieldRef model.Generator go!"suffix"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType model.Generator)))) (Var "g")))
  (Let "$a1" (Val #(W64 1))
  (App (App (App (Val (GoInstruction (FuncResolve _root_.Perennial.sync.atomic.AddUint64 []))) (Val #())) (Var "$a0")) (Var "$a1"))))
  (Let "suffix" (App (Val (GoInstruction (GoAlloc go.uint64))) (App (Val (GoInstruction (GoZeroVal go.uint64))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  (Let "$r0" (App (Val (GoInstruction (GoOp GoOr go.uint64))) (Pair (App (Val (GoInstruction (GoLoad go.uint64))) (App (Val (GoInstruction (StructFieldRef model.Generator go!"prefix"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType model.Generator)))) (Var "g")))) (Let "$a0" (App (Val (GoInstruction (GoLoad go.uint64))) (Var "suffix"))
  (Let "$a1" (App (Val (GoInstruction (Convert go.untypedInt go.uint))) (Val model.suffixLen))
  (App (App (App (Val (GoInstruction (FuncResolve model.lowbit []))) (Val #())) (Var "$a0")) (Var "$a1"))))))
  (Let "id" (App (Val (GoInstruction (GoAlloc go.uint64))) (App (Val (GoInstruction (GoZeroVal go.uint64))) (Val #())))
  (App (App (Val exceptionSeq) (Lam BAnon
  -- (the model's one addition) the issue record: no other generator issued the id
  (Seq (App (Val assume) (ExternalOp idIssueExt.name "Issue"
    (Pair (App (Val (GoInstruction (GoLoad go.uint64))) (Var "id"))
      (App (Val (GoInstruction (GoLoad (go.GoType.PointerType model.Generator)))) (Var "g")))))
  (Let "$r0" (App (Val (GoInstruction (GoLoad go.uint64))) (Var "id"))
  (App (App (Val exceptionSeq) (Lam BAnon
  (App (Val doReturn)
  (Val #()))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.uint64))) (Pair (Var "$res0") (Var "$r0")))))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.uint64))) (Pair (Var "id") (Var "$r0")))))))))
  (App (Val doExecute)
  (App (Val (GoInstruction (GoStore go.uint64))) (Pair (Var "suffix") (Var "$r0")))))))))
  (App (Val (GoInstruction (GoLoad go.uint64))) (Var "$res0"))))))

end
end go_etcd_io.etcd.pkg.v3.idutil

end Perennial
