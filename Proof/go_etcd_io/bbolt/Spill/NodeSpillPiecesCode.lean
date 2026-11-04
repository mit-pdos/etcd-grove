/-
`node.spill` after its children's loop (U9l, `notes/bbolt-proof-plan.md`): **the code** of what
follows the loop (`spillTail`: `n.children = nil`, the split, the pieces' loop, the top case's
recursion; one piece's iteration `pieceFn`, its inline free `pieceFree`), copied from
`node.spill.impl` (`Code/go_etcd_io/bbolt.lean`) with the function's variables `n`, `tx`, `$res0`
and `node` replaced by their cells `np`, `txp`, `resp`, `nodep` (what `wp_auto` substitutes;
copied by a script from the translation: redo it if the translation of `node.spill` changes);
and `spillIH`, `node.spill.spec'` as one Iris proposition (Löb's hypothesis, `node__spill`'s
`spillW`).
-/
module

public import Proof.go_etcd_io.bbolt.Spill.NodeSpec

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section code
variable [GooseExts] [GoGlobalContext]

/-- **`node.spill` after its children's loop** (see the module doc). -/
def spillTail (np txp resp : Loc) : Expr :=
    (Let "$r0" (App (Val (GoInstruction (Convert go.untypedNil nodes.ty))) (Val UntypedNil))
      (App (App (Val exceptionSeq) (Lam BAnon
      (Let "$r0" (Let "$a0" (App (Val (GoInstruction (Convert go.int go.uintptr))) (App (Val (GoInstruction (GoLoad go.int))) (App (Val (GoInstruction (StructFieldRef DB.ty go!"pageSize"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType DB.ty)))) (App (Val (GoInstruction (StructFieldRef Tx.ty go!"db"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType Tx.ty)))) (Val #txp)))))))
      (App (App (Val (GoInstruction (MethodResolve (go.GoType.PointerType node.ty) go!"split"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType node.ty)))) (Val #np))) (Var "$a0")))
      (Let "nodes" (App (Val (GoInstruction (GoAlloc (go.GoType.SliceType (go.GoType.PointerType node.ty))))) (App (Val (GoInstruction (GoZeroVal (go.GoType.SliceType (go.GoType.PointerType node.ty))))) (Val #())))
      (App (App (Val exceptionSeq) (Lam BAnon
      (App (App (Val exceptionSeq) (Lam BAnon
      (App (App (Val exceptionSeq) (Lam BAnon
      (Let "$r0" (App (Val (GoInstruction (Convert go.untypedNil go.error))) (Val UntypedNil))
      (App (App (Val exceptionSeq) (Lam BAnon
      (App (Val doReturn)
      (Val #()))))
      (App (Val doExecute)
      (App (Val (GoInstruction (GoStore go.error))) (Pair (Val #resp) (Var "$r0"))))))))
      (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (If (App (Val (GoInstruction (GoUnOp GoNot go.bool))) (App (Val (GoInstruction (GoOp GoEquals (go.GoType.PointerType node.ty)))) (Pair (App (Val (GoInstruction (GoLoad (go.GoType.PointerType node.ty)))) (App (Val (GoInstruction (StructFieldRef node.ty go!"parent"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType node.ty)))) (Val #np)))) (App (Val (GoInstruction (Convert go.untypedNil (go.GoType.PointerType node.ty)))) (Val UntypedNil))))) (App (Val (GoInstruction (GoOp GoEquals _root_.Perennial.go_etcd_io.bbolt.internal.common.Pgid.ty))) (Pair (App (Val (GoInstruction (GoLoad _root_.Perennial.go_etcd_io.bbolt.internal.common.Pgid.ty))) (App (Val (GoInstruction (StructFieldRef node.ty go!"pgid"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType node.ty)))) (App (Val (GoInstruction (StructFieldRef node.ty go!"parent"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType node.ty)))) (Val #np)))))) (Val #(W64 0)))) (Val #false)))
      (Let "$r0" (App (Val (GoInstruction (Convert go.untypedNil nodes.ty))) (Val UntypedNil))
      (App (App (Val exceptionSeq) (Lam BAnon
      (Let "$r0" (App (App (Val (GoInstruction (MethodResolve (go.GoType.PointerType node.ty) go!"spill"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType node.ty)))) (App (Val (GoInstruction (StructFieldRef node.ty go!"parent"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType node.ty)))) (Val #np))))) (Val #()))
      (App (App (Val exceptionSeq) (Lam BAnon
      (App (Val doReturn)
      (Val #()))))
      (App (Val doExecute)
      (App (Val (GoInstruction (GoStore go.error))) (Pair (Val #resp) (Var "$r0"))))))))
      (App (Val doExecute)
      (App (Val (GoInstruction (GoStore nodes.ty))) (Pair (App (Val (GoInstruction (StructFieldRef node.ty go!"children"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType node.ty)))) (Val #np))) (Var "$r0"))))))
      (App (Val doExecute)
      (Val #()))))))
      (Let "$range" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType (go.GoType.PointerType node.ty))))) (Var "nodes"))
      (Let "node" (App (Val (GoInstruction (GoAlloc (go.GoType.PointerType node.ty)))) (App (Val (GoInstruction (GoZeroVal (go.GoType.PointerType node.ty)))) (Val #())))
      (App (App (Val (slice.forRange (go.GoType.PointerType node.ty))) (Var "$range"))
      (Lam "$key"
      (Lam "$value"
      (App (App (Val exceptionSeq) (Lam BAnon
      (App (App (Val exceptionSeq) (Lam BAnon
      (App (App (Val exceptionSeq) (Lam BAnon
      (Let "__p" (Let "$a0" (App (Val (GoInstruction (GoOp GoDiv go.int))) (Pair (App (Val (GoInstruction (GoOp GoSub go.int))) (Pair (App (Val (GoInstruction (GoOp GoPlus go.int))) (Pair (App (App (Val (GoInstruction (MethodResolve (go.GoType.PointerType node.ty) go!"size"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType node.ty)))) (Var "node"))) (Val #())) (App (Val (GoInstruction (GoLoad go.int))) (App (Val (GoInstruction (StructFieldRef DB.ty go!"pageSize"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType DB.ty)))) (App (Val (GoInstruction (StructFieldRef Tx.ty go!"db"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType Tx.ty)))) (Val #txp)))))))) (Val #(W64 1)))) (App (Val (GoInstruction (GoLoad go.int))) (App (Val (GoInstruction (StructFieldRef DB.ty go!"pageSize"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType DB.ty)))) (App (Val (GoInstruction (StructFieldRef Tx.ty go!"db"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType Tx.ty)))) (Val #txp))))))))
      (App (App (Val (GoInstruction (MethodResolve (go.GoType.PointerType Tx.ty) go!"allocate"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType Tx.ty)))) (Val #txp))) (Var "$a0")))
      (Let "$ret0" (Fst (Var "__p"))
      (Let "$ret1" (Snd (Var "__p"))
      (Let "$r0" (Var "$ret0")
      (Let "$r1" (Var "$ret1")
      (Let "err" (App (Val (GoInstruction (GoAlloc go.error))) (App (Val (GoInstruction (GoZeroVal go.error))) (Val #())))
      (Let "p" (App (Val (GoInstruction (GoAlloc (go.GoType.PointerType _root_.Perennial.go_etcd_io.bbolt.internal.common.Page.ty)))) (App (Val (GoInstruction (GoZeroVal (go.GoType.PointerType _root_.Perennial.go_etcd_io.bbolt.internal.common.Page.ty)))) (Val #())))
      (App (App (Val exceptionSeq) (Lam BAnon
      (App (App (Val exceptionSeq) (Lam BAnon
      (App (App (Val exceptionSeq) (Lam BAnon
      (App (App (Val exceptionSeq) (Lam BAnon
      (Let "$r0" (App (App (Val (GoInstruction (MethodResolve (go.GoType.PointerType _root_.Perennial.go_etcd_io.bbolt.internal.common.Page.ty) go!"Id"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType _root_.Perennial.go_etcd_io.bbolt.internal.common.Page.ty)))) (Var "p"))) (Val #()))
      (App (App (Val exceptionSeq) (Lam BAnon
      (App (App (Val exceptionSeq) (Lam BAnon
      (Let "$r0" (Val #true)
      (App (App (Val exceptionSeq) (Lam BAnon
      (App (App (Val exceptionSeq) (Lam BAnon
      (App (Val doExecute)
      (Let "$a0" (Val #(W64 1))
      (App (App (Val (GoInstruction (MethodResolve (go.GoType.PointerType TxStats.ty) go!"IncSpill"))) (App (Val (GoInstruction (StructFieldRef Tx.ty go!"stats"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType Tx.ty)))) (Val #txp)))) (Var "$a0"))))))
      (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoUnOp GoNot go.bool))) (App (Val (GoInstruction (GoOp GoEquals (go.GoType.PointerType node.ty)))) (Pair (App (Val (GoInstruction (GoLoad (go.GoType.PointerType node.ty)))) (App (Val (GoInstruction (StructFieldRef node.ty go!"parent"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType node.ty)))) (Var "node")))) (App (Val (GoInstruction (Convert go.untypedNil (go.GoType.PointerType node.ty)))) (Val UntypedNil))))))
      (Let "$r0" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.byte)))) (App (Val (GoInstruction (StructFieldRef node.ty go!"key"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType node.ty)))) (Var "node"))))
      (Let "key" (App (Val (GoInstruction (GoAlloc (go.GoType.SliceType go.byte)))) (App (Val (GoInstruction (GoZeroVal (go.GoType.SliceType go.byte)))) (Val #())))
      (App (App (Val exceptionSeq) (Lam BAnon
      (App (App (Val exceptionSeq) (Lam BAnon
      (App (App (Val exceptionSeq) (Lam BAnon
      (Let "$r0" (App (App (Val (GoInstruction (MethodResolve (go.GoType.PointerType _root_.Perennial.go_etcd_io.bbolt.internal.common.Inode.ty) go!"Key"))) (App (Val (GoInstruction (IndexRef _root_.Perennial.go_etcd_io.bbolt.internal.common.Inodes.ty))) (Pair (App (Val (GoInstruction (GoLoad _root_.Perennial.go_etcd_io.bbolt.internal.common.Inodes.ty))) (App (Val (GoInstruction (StructFieldRef node.ty go!"inodes"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType node.ty)))) (Var "node")))) (Val #(W64 0))))) (Val #()))
      (App (App (Val exceptionSeq) (Lam BAnon
      (App (Val doExecute)
      (Let "$a0" (App (Val (GoInstruction (GoOp GoGt go.int))) (Pair (Let "$a0" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.byte)))) (App (Val (GoInstruction (StructFieldRef node.ty go!"key"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType node.ty)))) (Var "node"))))
      (App (App (Val (GoInstruction (FuncResolve go.len [(go.GoType.SliceType go.byte)]))) (Val #())) (Var "$a0"))) (Val #(W64 0))))
      (Let "$a1" (Val #(go!"spill: zero-length node key"))
      (Let "$a2" (Val #slice.nil)
      (App (App (App (App (Val (GoInstruction (FuncResolve _root_.Perennial.go_etcd_io.bbolt.internal.common.Assert []))) (Val #())) (Var "$a0")) (Var "$a1")) (Var "$a2"))))))))
      (App (Val doExecute)
      (App (Val (GoInstruction (GoStore (go.GoType.SliceType go.byte)))) (Pair (App (Val (GoInstruction (StructFieldRef node.ty go!"key"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType node.ty)))) (Var "node"))) (Var "$r0"))))))))
      (App (Val doExecute)
      (Let "$a0" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.byte)))) (Var "key"))
      (Let "$a1" (App (App (Val (GoInstruction (MethodResolve (go.GoType.PointerType _root_.Perennial.go_etcd_io.bbolt.internal.common.Inode.ty) go!"Key"))) (App (Val (GoInstruction (IndexRef _root_.Perennial.go_etcd_io.bbolt.internal.common.Inodes.ty))) (Pair (App (Val (GoInstruction (GoLoad _root_.Perennial.go_etcd_io.bbolt.internal.common.Inodes.ty))) (App (Val (GoInstruction (StructFieldRef node.ty go!"inodes"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType node.ty)))) (Var "node")))) (Val #(W64 0))))) (Val #()))
      (Let "$a2" (App (Val (GoInstruction (Convert go.untypedNil (go.GoType.SliceType go.byte)))) (Val UntypedNil))
      (Let "$a3" (App (Val (GoInstruction (GoLoad _root_.Perennial.go_etcd_io.bbolt.internal.common.Pgid.ty))) (App (Val (GoInstruction (StructFieldRef node.ty go!"pgid"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType node.ty)))) (Var "node"))))
      (Let "$a4" (Val #(W32 0))
      (App (App (App (App (App (App (Val (GoInstruction (MethodResolve (go.GoType.PointerType node.ty) go!"put"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType node.ty)))) (App (Val (GoInstruction (StructFieldRef node.ty go!"parent"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType node.ty)))) (Var "node"))))) (Var "$a0")) (Var "$a1")) (Var "$a2")) (Var "$a3")) (Var "$a4")))))))))))
      (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoOp GoEquals (go.GoType.SliceType go.byte)))) (Pair (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.byte)))) (Var "key")) (App (Val (GoInstruction (Convert go.untypedNil (go.GoType.SliceType go.byte)))) (Val UntypedNil)))))
      (Let "$r0" (App (App (Val (GoInstruction (MethodResolve (go.GoType.PointerType _root_.Perennial.go_etcd_io.bbolt.internal.common.Inode.ty) go!"Key"))) (App (Val (GoInstruction (IndexRef _root_.Perennial.go_etcd_io.bbolt.internal.common.Inodes.ty))) (Pair (App (Val (GoInstruction (GoLoad _root_.Perennial.go_etcd_io.bbolt.internal.common.Inodes.ty))) (App (Val (GoInstruction (StructFieldRef node.ty go!"inodes"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType node.ty)))) (Var "node")))) (Val #(W64 0))))) (Val #()))
      (App (Val doExecute)
      (App (Val (GoInstruction (GoStore (go.GoType.SliceType go.byte)))) (Pair (Var "key") (Var "$r0")))))
      (App (Val doExecute)
      (Val #()))))))
      (App (Val doExecute)
      (App (Val (GoInstruction (GoStore (go.GoType.SliceType go.byte)))) (Pair (Var "key") (Var "$r0")))))))
      (App (Val doExecute)
      (Val #()))))))
      (App (Val doExecute)
      (App (Val (GoInstruction (GoStore go.bool))) (Pair (App (Val (GoInstruction (StructFieldRef node.ty go!"spilled"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType node.ty)))) (Var "node"))) (Var "$r0"))))))))
      (App (Val doExecute)
      (Let "$a0" (App (Val (GoInstruction (GoLoad (go.GoType.PointerType _root_.Perennial.go_etcd_io.bbolt.internal.common.Page.ty)))) (Var "p"))
      (App (App (Val (GoInstruction (MethodResolve (go.GoType.PointerType node.ty) go!"write"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType node.ty)))) (Var "node"))) (Var "$a0")))))))
      (App (Val doExecute)
      (App (Val (GoInstruction (GoStore _root_.Perennial.go_etcd_io.bbolt.internal.common.Pgid.ty))) (Pair (App (Val (GoInstruction (StructFieldRef node.ty go!"pgid"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType node.ty)))) (Var "node"))) (Var "$r0"))))))))
      (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoOp GoGe _root_.Perennial.go_etcd_io.bbolt.internal.common.Pgid.ty))) (Pair (App (App (Val (GoInstruction (MethodResolve (go.GoType.PointerType _root_.Perennial.go_etcd_io.bbolt.internal.common.Page.ty) go!"Id"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType _root_.Perennial.go_etcd_io.bbolt.internal.common.Page.ty)))) (Var "p"))) (Val #())) (App (App (Val (GoInstruction (MethodResolve (go.GoType.PointerType _root_.Perennial.go_etcd_io.bbolt.internal.common.Meta.ty) go!"Pgid"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType _root_.Perennial.go_etcd_io.bbolt.internal.common.Meta.ty)))) (App (Val (GoInstruction (StructFieldRef Tx.ty go!"meta"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType Tx.ty)))) (Val #txp))))) (Val #())))))
      (App (Val doExecute)
      (Let "$a0" (App (Val (GoInstruction (Convert go.string (go.GoType.InterfaceType [])))) (Let "$a0" (Val #(go!"pgid (%d) above high water mark (%d)"))
      (Let "$a1" (Let "$sl0" (App (Val (GoInstruction (Convert _root_.Perennial.go_etcd_io.bbolt.internal.common.Pgid.ty go.any))) (App (App (Val (GoInstruction (MethodResolve (go.GoType.PointerType _root_.Perennial.go_etcd_io.bbolt.internal.common.Page.ty) go!"Id"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType _root_.Perennial.go_etcd_io.bbolt.internal.common.Page.ty)))) (Var "p"))) (Val #())))
      (Let "$sl1" (App (Val (GoInstruction (Convert _root_.Perennial.go_etcd_io.bbolt.internal.common.Pgid.ty go.any))) (App (App (Val (GoInstruction (MethodResolve (go.GoType.PointerType _root_.Perennial.go_etcd_io.bbolt.internal.common.Meta.ty) go!"Pgid"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType _root_.Perennial.go_etcd_io.bbolt.internal.common.Meta.ty)))) (App (Val (GoInstruction (StructFieldRef Tx.ty go!"meta"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType Tx.ty)))) (Val #txp))))) (Val #())))
      (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.any)))) (LiteralValue [(KeyedElement none (ElementExpression go.any (Var "$sl0"))), (KeyedElement none (ElementExpression go.any (Var "$sl1")))]))))
      (App (App (App (Val (GoInstruction (FuncResolve _root_.Perennial.fmt.Sprintf []))) (Val #())) (Var "$a0")) (Var "$a1")))))
      (App (App (Val (GoInstruction (FuncResolve go.panic []))) (Val #())) (Var "$a0"))))
      (App (Val doExecute)
      (Val #()))))))
      (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoUnOp GoNot go.bool))) (App (Val (GoInstruction (GoOp GoEquals go.error))) (Pair (App (Val (GoInstruction (GoLoad go.error))) (Var "err")) (App (Val (GoInstruction (Convert go.untypedNil go.error))) (Val UntypedNil))))))
      (Let "$r0" (App (Val (GoInstruction (GoLoad go.error))) (Var "err"))
      (App (App (Val exceptionSeq) (Lam BAnon
      (App (Val doReturn)
      (Val #()))))
      (App (Val doExecute)
      (App (Val (GoInstruction (GoStore go.error))) (Pair (Val #resp) (Var "$r0"))))))
      (App (Val doExecute)
      (Val #()))))))
      (App (Val doExecute)
      (App (Val (GoInstruction (GoStore go.error))) (Pair (Var "err") (Var "$r1")))))))
      (App (Val doExecute)
      (App (Val (GoInstruction (GoStore (go.GoType.PointerType _root_.Perennial.go_etcd_io.bbolt.internal.common.Page.ty)))) (Pair (Var "p") (Var "$r0"))))))))))))))
      (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoOp GoGt _root_.Perennial.go_etcd_io.bbolt.internal.common.Pgid.ty))) (Pair (App (Val (GoInstruction (GoLoad _root_.Perennial.go_etcd_io.bbolt.internal.common.Pgid.ty))) (App (Val (GoInstruction (StructFieldRef node.ty go!"pgid"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType node.ty)))) (Var "node")))) (Val #(W64 0)))))
      (App (App (Val exceptionSeq) (Lam BAnon
      (Let "$r0" (Val #(W64 0))
      (App (Val doExecute)
      (App (Val (GoInstruction (GoStore _root_.Perennial.go_etcd_io.bbolt.internal.common.Pgid.ty))) (Pair (App (Val (GoInstruction (StructFieldRef node.ty go!"pgid"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType node.ty)))) (Var "node"))) (Var "$r0")))))))
      (App (Val doExecute)
      (Let "$a0" (App (App (Val (GoInstruction (MethodResolve (go.GoType.PointerType _root_.Perennial.go_etcd_io.bbolt.internal.common.Meta.ty) go!"Txid"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType _root_.Perennial.go_etcd_io.bbolt.internal.common.Meta.ty)))) (App (Val (GoInstruction (StructFieldRef Tx.ty go!"meta"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType Tx.ty)))) (Val #txp))))) (Val #()))
      (Let "$a1" (Let "$a0" (App (Val (GoInstruction (GoLoad _root_.Perennial.go_etcd_io.bbolt.internal.common.Pgid.ty))) (App (Val (GoInstruction (StructFieldRef node.ty go!"pgid"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType node.ty)))) (Var "node"))))
      (App (App (Val (GoInstruction (MethodResolve (go.GoType.PointerType Tx.ty) go!"page"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType Tx.ty)))) (Val #txp))) (Var "$a0")))
      (App (App (App (Val (GoInstruction (MethodResolve _root_.Perennial.go_etcd_io.bbolt.internal.freelist.Interface.ty go!"Free"))) (App (Val (GoInstruction (GoLoad _root_.Perennial.go_etcd_io.bbolt.internal.freelist.Interface.ty))) (App (Val (GoInstruction (StructFieldRef DB.ty go!"freelist"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType DB.ty)))) (App (Val (GoInstruction (StructFieldRef Tx.ty go!"db"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType Tx.ty)))) (Val #txp))))))) (Var "$a0")) (Var "$a1"))))))
      (App (Val doExecute)
      (Val #()))))))
      (App (Val doExecute)
      (Var "$key")))))
      (App (Val doExecute)
      (App (Val (GoInstruction (GoStore (go.GoType.PointerType node.ty)))) (Pair (Var "node") (Var "$value")))))))))))))
      (App (Val doExecute)
      (App (Val (GoInstruction (GoStore (go.GoType.SliceType (go.GoType.PointerType node.ty))))) (Pair (Var "nodes") (Var "$r0")))))))))
      (App (Val doExecute)
      (App (Val (GoInstruction (GoStore nodes.ty))) (Pair (App (Val (GoInstruction (StructFieldRef node.ty go!"children"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType node.ty)))) (Val #np))) (Var "$r0"))))))

/-- **One piece's iteration of the pieces' loop** (`for _, node := range nodes`'s body, a closure
of `$key` and `$value`), the cell of `node` being `nodep`. -/
def pieceFn (txp resp nodep : Loc) : val :=
    LamV "$key"
      (Lam "$value"
      (App (App (Val exceptionSeq) (Lam BAnon
      (App (App (Val exceptionSeq) (Lam BAnon
      (App (App (Val exceptionSeq) (Lam BAnon
      (Let "__p" (Let "$a0" (App (Val (GoInstruction (GoOp GoDiv go.int))) (Pair (App (Val (GoInstruction (GoOp GoSub go.int))) (Pair (App (Val (GoInstruction (GoOp GoPlus go.int))) (Pair (App (App (Val (GoInstruction (MethodResolve (go.GoType.PointerType node.ty) go!"size"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType node.ty)))) (Val #nodep))) (Val #())) (App (Val (GoInstruction (GoLoad go.int))) (App (Val (GoInstruction (StructFieldRef DB.ty go!"pageSize"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType DB.ty)))) (App (Val (GoInstruction (StructFieldRef Tx.ty go!"db"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType Tx.ty)))) (Val #txp)))))))) (Val #(W64 1)))) (App (Val (GoInstruction (GoLoad go.int))) (App (Val (GoInstruction (StructFieldRef DB.ty go!"pageSize"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType DB.ty)))) (App (Val (GoInstruction (StructFieldRef Tx.ty go!"db"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType Tx.ty)))) (Val #txp))))))))
      (App (App (Val (GoInstruction (MethodResolve (go.GoType.PointerType Tx.ty) go!"allocate"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType Tx.ty)))) (Val #txp))) (Var "$a0")))
      (Let "$ret0" (Fst (Var "__p"))
      (Let "$ret1" (Snd (Var "__p"))
      (Let "$r0" (Var "$ret0")
      (Let "$r1" (Var "$ret1")
      (Let "err" (App (Val (GoInstruction (GoAlloc go.error))) (App (Val (GoInstruction (GoZeroVal go.error))) (Val #())))
      (Let "p" (App (Val (GoInstruction (GoAlloc (go.GoType.PointerType _root_.Perennial.go_etcd_io.bbolt.internal.common.Page.ty)))) (App (Val (GoInstruction (GoZeroVal (go.GoType.PointerType _root_.Perennial.go_etcd_io.bbolt.internal.common.Page.ty)))) (Val #())))
      (App (App (Val exceptionSeq) (Lam BAnon
      (App (App (Val exceptionSeq) (Lam BAnon
      (App (App (Val exceptionSeq) (Lam BAnon
      (App (App (Val exceptionSeq) (Lam BAnon
      (Let "$r0" (App (App (Val (GoInstruction (MethodResolve (go.GoType.PointerType _root_.Perennial.go_etcd_io.bbolt.internal.common.Page.ty) go!"Id"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType _root_.Perennial.go_etcd_io.bbolt.internal.common.Page.ty)))) (Var "p"))) (Val #()))
      (App (App (Val exceptionSeq) (Lam BAnon
      (App (App (Val exceptionSeq) (Lam BAnon
      (Let "$r0" (Val #true)
      (App (App (Val exceptionSeq) (Lam BAnon
      (App (App (Val exceptionSeq) (Lam BAnon
      (App (Val doExecute)
      (Let "$a0" (Val #(W64 1))
      (App (App (Val (GoInstruction (MethodResolve (go.GoType.PointerType TxStats.ty) go!"IncSpill"))) (App (Val (GoInstruction (StructFieldRef Tx.ty go!"stats"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType Tx.ty)))) (Val #txp)))) (Var "$a0"))))))
      (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoUnOp GoNot go.bool))) (App (Val (GoInstruction (GoOp GoEquals (go.GoType.PointerType node.ty)))) (Pair (App (Val (GoInstruction (GoLoad (go.GoType.PointerType node.ty)))) (App (Val (GoInstruction (StructFieldRef node.ty go!"parent"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType node.ty)))) (Val #nodep)))) (App (Val (GoInstruction (Convert go.untypedNil (go.GoType.PointerType node.ty)))) (Val UntypedNil))))))
      (Let "$r0" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.byte)))) (App (Val (GoInstruction (StructFieldRef node.ty go!"key"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType node.ty)))) (Val #nodep))))
      (Let "key" (App (Val (GoInstruction (GoAlloc (go.GoType.SliceType go.byte)))) (App (Val (GoInstruction (GoZeroVal (go.GoType.SliceType go.byte)))) (Val #())))
      (App (App (Val exceptionSeq) (Lam BAnon
      (App (App (Val exceptionSeq) (Lam BAnon
      (App (App (Val exceptionSeq) (Lam BAnon
      (Let "$r0" (App (App (Val (GoInstruction (MethodResolve (go.GoType.PointerType _root_.Perennial.go_etcd_io.bbolt.internal.common.Inode.ty) go!"Key"))) (App (Val (GoInstruction (IndexRef _root_.Perennial.go_etcd_io.bbolt.internal.common.Inodes.ty))) (Pair (App (Val (GoInstruction (GoLoad _root_.Perennial.go_etcd_io.bbolt.internal.common.Inodes.ty))) (App (Val (GoInstruction (StructFieldRef node.ty go!"inodes"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType node.ty)))) (Val #nodep)))) (Val #(W64 0))))) (Val #()))
      (App (App (Val exceptionSeq) (Lam BAnon
      (App (Val doExecute)
      (Let "$a0" (App (Val (GoInstruction (GoOp GoGt go.int))) (Pair (Let "$a0" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.byte)))) (App (Val (GoInstruction (StructFieldRef node.ty go!"key"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType node.ty)))) (Val #nodep))))
      (App (App (Val (GoInstruction (FuncResolve go.len [(go.GoType.SliceType go.byte)]))) (Val #())) (Var "$a0"))) (Val #(W64 0))))
      (Let "$a1" (Val #(go!"spill: zero-length node key"))
      (Let "$a2" (Val #slice.nil)
      (App (App (App (App (Val (GoInstruction (FuncResolve _root_.Perennial.go_etcd_io.bbolt.internal.common.Assert []))) (Val #())) (Var "$a0")) (Var "$a1")) (Var "$a2"))))))))
      (App (Val doExecute)
      (App (Val (GoInstruction (GoStore (go.GoType.SliceType go.byte)))) (Pair (App (Val (GoInstruction (StructFieldRef node.ty go!"key"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType node.ty)))) (Val #nodep))) (Var "$r0"))))))))
      (App (Val doExecute)
      (Let "$a0" (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.byte)))) (Var "key"))
      (Let "$a1" (App (App (Val (GoInstruction (MethodResolve (go.GoType.PointerType _root_.Perennial.go_etcd_io.bbolt.internal.common.Inode.ty) go!"Key"))) (App (Val (GoInstruction (IndexRef _root_.Perennial.go_etcd_io.bbolt.internal.common.Inodes.ty))) (Pair (App (Val (GoInstruction (GoLoad _root_.Perennial.go_etcd_io.bbolt.internal.common.Inodes.ty))) (App (Val (GoInstruction (StructFieldRef node.ty go!"inodes"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType node.ty)))) (Val #nodep)))) (Val #(W64 0))))) (Val #()))
      (Let "$a2" (App (Val (GoInstruction (Convert go.untypedNil (go.GoType.SliceType go.byte)))) (Val UntypedNil))
      (Let "$a3" (App (Val (GoInstruction (GoLoad _root_.Perennial.go_etcd_io.bbolt.internal.common.Pgid.ty))) (App (Val (GoInstruction (StructFieldRef node.ty go!"pgid"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType node.ty)))) (Val #nodep))))
      (Let "$a4" (Val #(W32 0))
      (App (App (App (App (App (App (Val (GoInstruction (MethodResolve (go.GoType.PointerType node.ty) go!"put"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType node.ty)))) (App (Val (GoInstruction (StructFieldRef node.ty go!"parent"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType node.ty)))) (Val #nodep))))) (Var "$a0")) (Var "$a1")) (Var "$a2")) (Var "$a3")) (Var "$a4")))))))))))
      (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoOp GoEquals (go.GoType.SliceType go.byte)))) (Pair (App (Val (GoInstruction (GoLoad (go.GoType.SliceType go.byte)))) (Var "key")) (App (Val (GoInstruction (Convert go.untypedNil (go.GoType.SliceType go.byte)))) (Val UntypedNil)))))
      (Let "$r0" (App (App (Val (GoInstruction (MethodResolve (go.GoType.PointerType _root_.Perennial.go_etcd_io.bbolt.internal.common.Inode.ty) go!"Key"))) (App (Val (GoInstruction (IndexRef _root_.Perennial.go_etcd_io.bbolt.internal.common.Inodes.ty))) (Pair (App (Val (GoInstruction (GoLoad _root_.Perennial.go_etcd_io.bbolt.internal.common.Inodes.ty))) (App (Val (GoInstruction (StructFieldRef node.ty go!"inodes"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType node.ty)))) (Val #nodep)))) (Val #(W64 0))))) (Val #()))
      (App (Val doExecute)
      (App (Val (GoInstruction (GoStore (go.GoType.SliceType go.byte)))) (Pair (Var "key") (Var "$r0")))))
      (App (Val doExecute)
      (Val #()))))))
      (App (Val doExecute)
      (App (Val (GoInstruction (GoStore (go.GoType.SliceType go.byte)))) (Pair (Var "key") (Var "$r0")))))))
      (App (Val doExecute)
      (Val #()))))))
      (App (Val doExecute)
      (App (Val (GoInstruction (GoStore go.bool))) (Pair (App (Val (GoInstruction (StructFieldRef node.ty go!"spilled"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType node.ty)))) (Val #nodep))) (Var "$r0"))))))))
      (App (Val doExecute)
      (Let "$a0" (App (Val (GoInstruction (GoLoad (go.GoType.PointerType _root_.Perennial.go_etcd_io.bbolt.internal.common.Page.ty)))) (Var "p"))
      (App (App (Val (GoInstruction (MethodResolve (go.GoType.PointerType node.ty) go!"write"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType node.ty)))) (Val #nodep))) (Var "$a0")))))))
      (App (Val doExecute)
      (App (Val (GoInstruction (GoStore _root_.Perennial.go_etcd_io.bbolt.internal.common.Pgid.ty))) (Pair (App (Val (GoInstruction (StructFieldRef node.ty go!"pgid"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType node.ty)))) (Val #nodep))) (Var "$r0"))))))))
      (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoOp GoGe _root_.Perennial.go_etcd_io.bbolt.internal.common.Pgid.ty))) (Pair (App (App (Val (GoInstruction (MethodResolve (go.GoType.PointerType _root_.Perennial.go_etcd_io.bbolt.internal.common.Page.ty) go!"Id"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType _root_.Perennial.go_etcd_io.bbolt.internal.common.Page.ty)))) (Var "p"))) (Val #())) (App (App (Val (GoInstruction (MethodResolve (go.GoType.PointerType _root_.Perennial.go_etcd_io.bbolt.internal.common.Meta.ty) go!"Pgid"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType _root_.Perennial.go_etcd_io.bbolt.internal.common.Meta.ty)))) (App (Val (GoInstruction (StructFieldRef Tx.ty go!"meta"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType Tx.ty)))) (Val #txp))))) (Val #())))))
      (App (Val doExecute)
      (Let "$a0" (App (Val (GoInstruction (Convert go.string (go.GoType.InterfaceType [])))) (Let "$a0" (Val #(go!"pgid (%d) above high water mark (%d)"))
      (Let "$a1" (Let "$sl0" (App (Val (GoInstruction (Convert _root_.Perennial.go_etcd_io.bbolt.internal.common.Pgid.ty go.any))) (App (App (Val (GoInstruction (MethodResolve (go.GoType.PointerType _root_.Perennial.go_etcd_io.bbolt.internal.common.Page.ty) go!"Id"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType _root_.Perennial.go_etcd_io.bbolt.internal.common.Page.ty)))) (Var "p"))) (Val #())))
      (Let "$sl1" (App (Val (GoInstruction (Convert _root_.Perennial.go_etcd_io.bbolt.internal.common.Pgid.ty go.any))) (App (App (Val (GoInstruction (MethodResolve (go.GoType.PointerType _root_.Perennial.go_etcd_io.bbolt.internal.common.Meta.ty) go!"Pgid"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType _root_.Perennial.go_etcd_io.bbolt.internal.common.Meta.ty)))) (App (Val (GoInstruction (StructFieldRef Tx.ty go!"meta"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType Tx.ty)))) (Val #txp))))) (Val #())))
      (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.any)))) (LiteralValue [(KeyedElement none (ElementExpression go.any (Var "$sl0"))), (KeyedElement none (ElementExpression go.any (Var "$sl1")))]))))
      (App (App (App (Val (GoInstruction (FuncResolve _root_.Perennial.fmt.Sprintf []))) (Val #())) (Var "$a0")) (Var "$a1")))))
      (App (App (Val (GoInstruction (FuncResolve go.panic []))) (Val #())) (Var "$a0"))))
      (App (Val doExecute)
      (Val #()))))))
      (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoUnOp GoNot go.bool))) (App (Val (GoInstruction (GoOp GoEquals go.error))) (Pair (App (Val (GoInstruction (GoLoad go.error))) (Var "err")) (App (Val (GoInstruction (Convert go.untypedNil go.error))) (Val UntypedNil))))))
      (Let "$r0" (App (Val (GoInstruction (GoLoad go.error))) (Var "err"))
      (App (App (Val exceptionSeq) (Lam BAnon
      (App (Val doReturn)
      (Val #()))))
      (App (Val doExecute)
      (App (Val (GoInstruction (GoStore go.error))) (Pair (Val #resp) (Var "$r0"))))))
      (App (Val doExecute)
      (Val #()))))))
      (App (Val doExecute)
      (App (Val (GoInstruction (GoStore go.error))) (Pair (Var "err") (Var "$r1")))))))
      (App (Val doExecute)
      (App (Val (GoInstruction (GoStore (go.GoType.PointerType _root_.Perennial.go_etcd_io.bbolt.internal.common.Page.ty)))) (Pair (Var "p") (Var "$r0"))))))))))))))
      (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoOp GoGt _root_.Perennial.go_etcd_io.bbolt.internal.common.Pgid.ty))) (Pair (App (Val (GoInstruction (GoLoad _root_.Perennial.go_etcd_io.bbolt.internal.common.Pgid.ty))) (App (Val (GoInstruction (StructFieldRef node.ty go!"pgid"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType node.ty)))) (Val #nodep)))) (Val #(W64 0)))))
      (App (App (Val exceptionSeq) (Lam BAnon
      (Let "$r0" (Val #(W64 0))
      (App (Val doExecute)
      (App (Val (GoInstruction (GoStore _root_.Perennial.go_etcd_io.bbolt.internal.common.Pgid.ty))) (Pair (App (Val (GoInstruction (StructFieldRef node.ty go!"pgid"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType node.ty)))) (Val #nodep))) (Var "$r0")))))))
      (App (Val doExecute)
      (Let "$a0" (App (App (Val (GoInstruction (MethodResolve (go.GoType.PointerType _root_.Perennial.go_etcd_io.bbolt.internal.common.Meta.ty) go!"Txid"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType _root_.Perennial.go_etcd_io.bbolt.internal.common.Meta.ty)))) (App (Val (GoInstruction (StructFieldRef Tx.ty go!"meta"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType Tx.ty)))) (Val #txp))))) (Val #()))
      (Let "$a1" (Let "$a0" (App (Val (GoInstruction (GoLoad _root_.Perennial.go_etcd_io.bbolt.internal.common.Pgid.ty))) (App (Val (GoInstruction (StructFieldRef node.ty go!"pgid"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType node.ty)))) (Val #nodep))))
      (App (App (Val (GoInstruction (MethodResolve (go.GoType.PointerType Tx.ty) go!"page"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType Tx.ty)))) (Val #txp))) (Var "$a0")))
      (App (App (App (Val (GoInstruction (MethodResolve _root_.Perennial.go_etcd_io.bbolt.internal.freelist.Interface.ty go!"Free"))) (App (Val (GoInstruction (GoLoad _root_.Perennial.go_etcd_io.bbolt.internal.freelist.Interface.ty))) (App (Val (GoInstruction (StructFieldRef DB.ty go!"freelist"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType DB.ty)))) (App (Val (GoInstruction (StructFieldRef Tx.ty go!"db"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType Tx.ty)))) (Val #txp))))))) (Var "$a0")) (Var "$a1"))))))
      (App (Val doExecute)
      (Val #()))))))
      (App (Val doExecute)
      (Var "$key")))))
      (App (Val doExecute)
      (App (Val (GoInstruction (GoStore (go.GoType.PointerType node.ty)))) (Pair (Val #nodep) (Var "$value"))))))

/-- **The inline free of a piece's page** (`if node.pgid > 0 { Free(…); node.pgid = 0 }`, the
fork's inlined `node.free()`). -/
def pieceFree (txp nodep : Loc) : Expr :=
    (If (App (Val (GoInstruction (Convert go.untypedBool go.bool))) (App (Val (GoInstruction (GoOp GoGt _root_.Perennial.go_etcd_io.bbolt.internal.common.Pgid.ty))) (Pair (App (Val (GoInstruction (GoLoad _root_.Perennial.go_etcd_io.bbolt.internal.common.Pgid.ty))) (App (Val (GoInstruction (StructFieldRef node.ty go!"pgid"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType node.ty)))) (Val #nodep)))) (Val #(W64 0)))))
      (App (App (Val exceptionSeq) (Lam BAnon
      (Let "$r0" (Val #(W64 0))
      (App (Val doExecute)
      (App (Val (GoInstruction (GoStore _root_.Perennial.go_etcd_io.bbolt.internal.common.Pgid.ty))) (Pair (App (Val (GoInstruction (StructFieldRef node.ty go!"pgid"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType node.ty)))) (Val #nodep))) (Var "$r0")))))))
      (App (Val doExecute)
      (Let "$a0" (App (App (Val (GoInstruction (MethodResolve (go.GoType.PointerType _root_.Perennial.go_etcd_io.bbolt.internal.common.Meta.ty) go!"Txid"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType _root_.Perennial.go_etcd_io.bbolt.internal.common.Meta.ty)))) (App (Val (GoInstruction (StructFieldRef Tx.ty go!"meta"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType Tx.ty)))) (Val #txp))))) (Val #()))
      (Let "$a1" (Let "$a0" (App (Val (GoInstruction (GoLoad _root_.Perennial.go_etcd_io.bbolt.internal.common.Pgid.ty))) (App (Val (GoInstruction (StructFieldRef node.ty go!"pgid"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType node.ty)))) (Val #nodep))))
      (App (App (Val (GoInstruction (MethodResolve (go.GoType.PointerType Tx.ty) go!"page"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType Tx.ty)))) (Val #txp))) (Var "$a0")))
      (App (App (App (Val (GoInstruction (MethodResolve _root_.Perennial.go_etcd_io.bbolt.internal.freelist.Interface.ty go!"Free"))) (App (Val (GoInstruction (GoLoad _root_.Perennial.go_etcd_io.bbolt.internal.freelist.Interface.ty))) (App (Val (GoInstruction (StructFieldRef DB.ty go!"freelist"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType DB.ty)))) (App (Val (GoInstruction (StructFieldRef Tx.ty go!"db"))) (App (Val (GoInstruction (GoLoad (go.GoType.PointerType Tx.ty)))) (Val #txp))))))) (Var "$a0")) (Var "$a1"))))))
      (App (Val doExecute)
      (Val #())))

end code

section ih
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `node.spill.spec'` as an Iris proposition (`node__spill`'s `spillW`). -/
def spillIH : IProp GF :=
  iprop(∀ (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (X : WX) (w : WDb) (bl n : Loc) (rn : NRec)
    (O : List Nat) (lo hi : Option (List w8)) (h : Nat) (F D : List Nat) (N : List Loc)
    (E : List El) (cs : SpCase),
    ⌜spPre X w bl n rn O lo hi h F D N E cs⌝ → ∀ Φ, (wtxW K tx r m X ∗ wdbW K tx X.v w) -∗
      ▷ (∀ err, spPost K tx r m X w bl n rn O lo hi h D N E cs err -∗ Φ #err) -∗
      WP (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"spill")) (Val #())) {{ Φ }})

end ih

end Spill

end bbolt
end EtcdGrove
end Perennial
