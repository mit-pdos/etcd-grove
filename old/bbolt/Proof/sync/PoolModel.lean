/-
The model of Go's `sync.Pool` that bbolt's page pool rests on (the trust boundary: the pool's
implementation is the runtime's). `isPool p P`: the pool at `p` holds values satisfying `P`
(persistent); `Get` returns one (a pooled one, or `New`'s), `Put` takes one
(`Spec/sync/Pool__{Get,Put}.lean`, axioms). `pool_init`: a pool whose `New` makes values
satisfying `P` is such a pool.
-/
module

public import Proof.go_etcd_io.bbolt.Init

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI

section model
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

axiom isPool (p : Loc) (P : GoInterface → IProp GF) : IProp GF
axiom isPool_persistent (p : Loc) (P : GoInterface → IProp GF) : Persistent (isPool (GF := GF) p P)

attribute [instance] isPool_persistent

/-- A pool (its value `pv`) whose `New` makes values satisfying `P` holds values satisfying
`P`. -/
axiom pool_init (p : Loc) (pv : sync.Pool) (P : GoInterface → IProp GF) :
  p ↦ pv -∗
  □ (∀ Φ : val → IProp GF, (∀ v : GoInterface, P v -∗ Φ #v) -∗
      WP (App (Val #pv.New') (Val #())) {{ Φ }}) ={⊤}=∗
  isPool (GF := GF) p P

end model

end bbolt
end EtcdGrove
end Perennial
