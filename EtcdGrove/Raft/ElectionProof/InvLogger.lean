/-
Port of `election_proof/inv_logger.v` (at feb5c73d4; unchanged since `main`): the `Logger`
interface.

Every `Logger` method used on the election path returns unit and has no observable
effect. `Panicf`/`Panic` are only reached on paths shown unreachable, so they get no
spec here.
-/
import EtcdGrove.Raft.ElectionProof.Defs

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

axiom isLogger {GF : BundledGFunctors} [FfiSyntax] : GoInterfaceOk → IProp GF

axiom isLogger_persistent {GF : BundledGFunctors} [FfiSyntax] (l : GoInterfaceOk) :
  Persistent (isLogger (GF := GF) l)

attribute [instance] isLogger_persistent

section logger
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- The formatting log methods. Deliberately *not* `Panic`/`Panicf`: those do not
return, so a path that reaches one has to be shown unreachable rather than assumed
away. -/
def logMethods : List GoString :=
  [go!"Info", go!"Infof", go!"Debug", go!"Debugf",
   go!"Warning", go!"Warningf", go!"Error", go!"Errorf"]

/-- A `Logger` method call: dispatched through `#(methods …)` on a client-supplied
interface value, so there is no Go function under verification to specify (main's
notes/decisions.md, 2026-09-18: interface methods stay with their predicate). -/
axiom Logger.wp_logf (l : GoInterfaceOk) (meth format : GoString) (args : GoSlice)
    (Hmeth : meth ∈ logMethods) :
    {{ isLogger (GF := GF) l }}
      (App (App (Val #(methods l.ty meth l.v)) (Val #format)) (Val #args))
    {{ RET #(); True }}

end logger

end EtcdGrove
end Perennial
