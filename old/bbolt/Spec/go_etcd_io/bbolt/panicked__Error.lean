module
public import Proof.go_etcd_io.bbolt.Init

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- The error `e`'s `Error()` returns some string (and does not panic). -/
def errorStringOK (e : GoInterfaceOk) : IProp GF :=
  iprop(□ ∀ Φ : val → IProp GF, ▷ (∀ s : GoString, Φ #s) -∗
    WP (App (Val #(methods e.ty go!"Error" e.v)) (Val #())) {{ Φ }})

instance errorStringOK_persistent (e : GoInterfaceOk) :
    Persistent (errorStringOK (GF := GF) e) := by
  unfold errorStringOK; infer_instance

/-- What `panicked.Error` needs of the recovered value: if it is an `error`, its `Error()`
returns a string. -/
def panickedReasonOK (r : GoInterface) : IProp GF :=
  match r with
  | interface.ok ri => if go.typeSetContains ri.ty go.error then errorStringOK ri else iprop(True)
  | interface.nil => iprop(True)

/-- `p.Error()`: a string. If `p.reason` is an `error`, its `Error()` (whose behavior the caller
supplies, `panickedReasonOK`: it returns a string) is the result; otherwise
`fmt.Sprintf("panic: %v", p.reason)`. -/
abbrev panicked.Error.spec : Prop :=
  ∀ (p : panicked),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ panickedReasonOK p.reason' }}
    (App (Val (p @!! panicked.ty @!! go!"Error")) (Val #()))
  {{ (s : GoString), RET #s; True }}

end spec

end bbolt
end EtcdGrove
end Perennial
