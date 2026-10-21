/-
Port of `election_proof/inv_logger.v` (at feb5c73d4; unchanged since `main`): the `Logger`
interface.

Every `Logger` method used on the election path returns unit and has no observable
effect; `isLogger` is that contract, as triples a client supplies (no axiom).
`Panicf`/`Panic` are only reached on paths shown unreachable, so they get no spec here.
-/
module

public import Proof.go_etcd_io.raft.v3.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section logger
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- The formatting log methods. Deliberately *not* `Panic`/`Panicf`: those do not
return, so a path that reaches one has to be shown unreachable rather than assumed
away. Only the formatting ones (2026-10-11): `isLogger` states each as a call on a
format and an argument slice, which `Info`/`Debug`/`Warning`/`Error` (one variadic
parameter) do not take -- with them in the list `isLogger` held of no `Logger`, and
`RestartNode`/`NewRawNode` (which take it) of no configuration. raft calls those four only
on paths the proof does not cover (`Error` twice: `stepFollower`'s `MsgForgetLeader`
and `releasePendingReadIndexMessages`). -/
def logMethods : List GoString :=
  [go!"Infof", go!"Debugf", go!"Warningf", go!"Errorf"]

/-- The `Logger` contract: every formatting method returns unit and has no observable
effect. A definition, not an assumption: a `Logger` method call is dispatched through
`#(methods …)` on a client-supplied interface value, so there is no Go function under
verification to specify, and the triples are what a client of raft supplies with its
`Logger` (main's notes/decisions.md, 2026-09-18: interface methods stay with their
predicate). Persistent, as `isStorageWith` is: inside `iprop(…)` a triple is `□ …`.
Until 2026-10-08 `isLogger` was an axiom, with `Logger.wp_logf` a second one. -/
def isLogger (l : GoInterfaceOk) : IProp GF :=
  iprop(∀ (meth : GoString) (_ : meth ∈ logMethods) (format : GoString) (args : GoSlice),
    {{ True }}
      (App (App (Val #(methods l.ty meth l.v)) (Val #format)) (Val #args))
    {{ RET #(); True }})

instance isLogger_persistent (l : GoInterfaceOk) : Persistent (isLogger (GF := GF) l) := by
  unfold isLogger; infer_instance

/-- A `Logger` method call, from the contract. -/
theorem Logger.wp_logf (l : GoInterfaceOk) (meth format : GoString) (args : GoSlice)
    (Hmeth : meth ∈ logMethods) :
    {{ isLogger (GF := GF) l }}
      (App (App (Val #(methods l.ty meth l.v)) (Val #format)) (Val #args))
    {{ RET #(); True }} := by
  iintro %Φ #Hlg HΦ
  unfold isLogger
  iapply Hlg $$ %meth %Hmeth %format %args %Φ [] HΦ
  ipureintro; trivial

end logger

end EtcdGrove
end Perennial
