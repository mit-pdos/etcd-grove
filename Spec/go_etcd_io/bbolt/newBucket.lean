module
public import Proof.go_etcd_io.bbolt.Init
public import Proof.go_etcd_io.raft.v3.ProjSimps

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

/-- `DefaultFillPercent` (0.5), as its bits. -/
def defaultFillPercent : w64 := W64 4602678819172646912

/-- The bucket `newBucket(tx)` returns: of `tx`, with the default fill percent, and (for a
writable transaction) the caches `buckets` and `nodes`. -/
def newBucketOf (txl : Loc) (bm nm : GoMap) : Bucket :=
  Bucket.mk null txl bm null null nm defaultFillPercent
proj_simps newBucketOf

/-- `newBucket(tx)`: a bucket of `tx`; for a writable transaction its two caches are new empty
maps, otherwise nil. It reads only the transaction's field `writable`. -/
abbrev newBucket.spec : Prop :=
  ∀ (txl : Loc) (w : Bool) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗
      structFieldRef Tx go!"writable" txl ↦{dq} w }}
    (App (Val #(functions newBucket [])) (Val #txl))
  {{ (bm nm : GoMap), RET #(newBucketOf txl bm nm); structFieldRef Tx go!"writable" txl ↦{dq} w ∗
      (if w then bm ↦$ (∅ : GMap GoString Loc) ∗ nm ↦$ (∅ : GMap w64 Loc)
       else ⌜bm = map.nil ∧ nm = map.nil⌝) }}

end spec

end bbolt
end EtcdGrove
end Perennial
