/-
Lean-first (no Rocq counterpart).

# `Cluster.Read`, logically atomic (2026-10-30, kvreconf-final, helper TOP): **`sorry`**

`Run`'s client closure sends an `opRead` input to `c.Read(key)`, and `lintest.Run`'s `applySpec`
needs it logically atomic: an update committed at a real moment, whose output is the state's then.
The frozen `Cluster.Read.spec` gives a lower-bound answer instead (`kvLb L0` in, the value of a
history `L ⊒ L0` out), which may be older than the history at the return, so no commit point
exists. The user's decision (2026-10-30): `Cluster.Read` gets a logically atomic spec, proved with
a prophecy (the read index linearizes in the past); that spec is designed and signed off
separately. Until then this lemma is the atomic `Read` the closure needs, in `Cluster.Get.spec`'s
shape (the state unchanged, the key's value answered), with its proof a `sorry`: when the new
`Cluster.Read.spec` lands, `Run.wp_proof` takes it in place of this lemma and the swap is local.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.DefsCluster

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvreconf

open Iris Iris.BI go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvreconf.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [AllG GF] [KvrStor GF]

attribute [local instance] kvrStorageModel

/-- `c.Read(key)`, logically atomic over the store's map (see the file header): **`sorry`**,
until `Cluster.Read`'s atomic spec. -/
theorem run_apply_read :
    ∀ (γr : RNames) (vs : List w64) (c : Loc) (key : List w8) (Φ : List w8 → IProp GF),
    (key.length : Int) < 2 ^ 61 →
    {{ isClusterC γr vs c ∗
        AU <{ ∃∃ (x : KVMap), rkvVal γr x }> @ kvrMask, ∅ <{ rkvVal γr x, COMM Φ (x key) }> }}
      (App (Val (c @!! go.GoType.PointerType rClusterTy @!! go!"Read")) (Val #key))
    {{ (res : List w8), RET #res; Φ res }} := by
  sorry

end proof

end kvreconf
end EtcdGrove
end Perennial
