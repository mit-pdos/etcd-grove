module
public import Proof.go_etcd_io.bbolt.internal.freelist.HashImpl

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt.internal.freelist

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.freelist.Assumptions]

/-- `f.Allocate(txid, n)`: a span of exactly `n` ids if there is one, else the first `n` ids of
a longer span (whichever the maps' iteration order meets first), now allocated by `txid`, its
first id returned; `0` if there is none. -/
abbrev hashMap.Allocate.spec : Prop :=
  ∀ (h s : Loc) (σ : FLState) (txid n : w64), 0 < sint.Z n →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ ownFL (hashMapImpl (GF := GF) h) s σ }}
    (App (App (Val (h @!! go.GoType.PointerType hashMap.ty @!! go!"Allocate")) (Val #txid)) (Val #n))
  {{ (r : w64), RET #r; ⌜r = W64 0⌝ ∗ ownFL (hashMapImpl h) s σ ∨
      ⌜σ.canAllocate r (sint.nat n)⌝ ∗ ownFL (hashMapImpl h) s (σ.allocate txid r (sint.nat n)) }}

end spec

end bbolt
end EtcdGrove
end Perennial
