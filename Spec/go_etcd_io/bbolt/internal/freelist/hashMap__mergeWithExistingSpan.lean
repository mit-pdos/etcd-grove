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

/-- `f.mergeWithExistingSpan(start, end)`: the ids `start..end` (none free, `start ≥ 1`, no free
id `0`) become free, merged with the spans just before and just after them. -/
abbrev hashMap.mergeWithExistingSpan.spec : Prop :=
  ∀ (h s : Loc) (free : List w64) (start e : w64),
  uint.Z start ≤ uint.Z e → 1 ≤ uint.Z start → (∀ x ∈ free, 1 ≤ uint.Z x) →
  (∀ x, inRun start (uint.nat (e - start) + 1) x → x ∉ free) →
  free.length + (uint.nat (e - start) + 1) < 2 ^ 63 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗ ownHashPart (GF := GF) h s free }}
    (App (App (Val (h @!! go.GoType.PointerType hashMap.ty @!! go!"mergeWithExistingSpan")) (Val #start)) (Val #e))
  {{ (free' : List w64), RET #();
      ⌜free'.Perm (free ++ runIds start (uint.nat (e - start) + 1))⌝ ∗ ownHashPart h s free' }}

end spec

end bbolt
end EtcdGrove
end Perennial
