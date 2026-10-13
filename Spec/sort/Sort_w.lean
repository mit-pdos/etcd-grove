module
public import GeneratedProof.go_etcd_io.bbolt

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `sort.Sort(pages)` for the writer's dirty pages (`common.Pages`, a slice of page pointers
whose `Less` compares the pages' ids, `Pages.Less`): the slice ends holding the pages `ys`, a
permutation of `xs` sorted by id, every page's header read (any fraction of it). The pages are
given as any list `xs` with their locations `loc` and headers `hdr` (so that what the caller
knows of each comes along). `sort.Sort` (pdqsort) is translated names-only; this spec is an
axiom (`Proof/sort/Sort_w.lean`), the second of `sort.Sort` (`Spec/sort/Sort.lean` is the
freelist's, for slices of `uint64`s). -/
abbrev sort.Sort.wspec : Prop :=
  ∀ {A : Type} (s : GoSlice) (xs : List A) (loc : A → Loc)
    (hdr : A → go_etcd_io.bbolt.internal.common.Page) (dq : DFrac),
  {{ s ↦* xs.map loc ∗ ([∗list] x ∈ xs, loc x ↦{dq} hdr x : IProp GF) }}
    (App (Val #(functions _root_.Perennial.sort.«Sort» []))
      (Val #(interface.mkOk go_etcd_io.bbolt.internal.common.Pages.ty #s)))
  {{ (ys : List A), RET #();
      ⌜ys.Perm xs ∧ ys.Pairwise (fun a b => uint.Z (hdr a).id' ≤ uint.Z (hdr b).id')⌝ ∗
      s ↦* ys.map loc ∗ [∗list] x ∈ ys, loc x ↦{dq} hdr x }}

end spec

end bbolt
end EtcdGrove
end Perennial
