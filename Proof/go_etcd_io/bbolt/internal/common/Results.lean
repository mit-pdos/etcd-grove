/-
The proved results of bbolt's `internal/common`: the sorted merge of page ids, the
pointer arithmetic of `unsafe.go`, and the byte view of a page header (`Bytes.lean`).
`UnsafeByteSlice` calls `UnsafeAdd` (linked here).

`#print axioms` on a result is its trust base (`sorryAx` is unfinished work).
-/
module

public import Proof.go_etcd_io.bbolt.internal.common.Mergepgids
public import Proof.go_etcd_io.bbolt.internal.common.UnsafeAdd
public import Proof.go_etcd_io.bbolt.internal.common.UnsafeIndex
public import Proof.go_etcd_io.bbolt.internal.common.UnsafeByteSlice
public import Proof.go_etcd_io.bbolt.internal.common.Bytes

@[expose] public section

namespace Perennial
namespace EtcdGrove
namespace bbolt

#print axioms Mergepgids.wp_proof
#print axioms UnsafeAdd.wp_proof
#print axioms UnsafeIndex.wp_proof

open Iris Iris.BI go_etcd_io.bbolt.internal.common

section link
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.common.Assumptions]

theorem UnsafeByteSlice.wp_linked : UnsafeByteSlice.spec (GF := GF) (hG := hG) :=
  UnsafeByteSlice.wp_proof UnsafeAdd.wp_proof

end link

#print axioms UnsafeByteSlice.wp_linked
#print axioms Page_bytes

end bbolt
end EtcdGrove
end Perennial
