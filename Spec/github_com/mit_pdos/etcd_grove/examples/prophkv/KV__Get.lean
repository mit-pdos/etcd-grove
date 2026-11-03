/- Lean-first (no Rocq counterpart).

`kv.Get(k)` (`examples/prophkv`): the caller's ghost step runs at the linearization point (inside
the lock); it sees the abstract state `m` and the answer, `k`'s value in `m` (`""` if none).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.prophkv.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace prophkv

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.prophkv

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.prophkv.Assumptions]

/-- See the file header. -/
abbrev KV__Get.spec : Prop :=
  ∀ (kv : Loc) (γ : GName) (k : GoString) (R : GoString → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.prophkv ∗
      isKV kv γ ∗ (∀ m, kvState γ m ={⊤}=∗ kvState γ m ∗ R ((m !! k).getD go!"")) }}
    (App (Val (kv @!! go.GoType.PointerType KV.ty @!! go!"Get")) (Val #k))
  {{ (r : GoString), RET #r; R r }}

end spec

end prophkv
end EtcdGrove
end Perennial
