/-
The proved results of bbolt (`internal/common` so far): the sorted merge of page ids,
`unsafe.go`'s pointer arithmetic, the accessors of the on-disk structs and the views of a
page's elements, keys and values (`Link.lean`, every proof linked to its callees' proofs),
and the byte view of a page header (`Bytes.lean`).

`#print axioms` on a result is its trust base (`sorryAx` is unfinished work).
-/
module

public import Proof.go_etcd_io.bbolt.internal.common.Link
public import Proof.go_etcd_io.bbolt.internal.common.Bytes

@[expose] public section

namespace Perennial
namespace EtcdGrove
namespace bbolt

#print axioms InBucket.wp_InSequence
#print axioms InBucket.wp_IncSequence
#print axioms InBucket.wp_RootPage
#print axioms InBucket.wp_SetInSequence
#print axioms InBucket.wp_SetRootPage
#print axioms Inode.wp_Flags
#print axioms Inode.wp_Key
#print axioms Inode.wp_Pgid
#print axioms Inode.wp_SetFlags
#print axioms Inode.wp_SetKey
#print axioms Inode.wp_SetPgid
#print axioms Inode.wp_SetValue
#print axioms Inode.wp_Value
#print axioms Meta.wp_Checksum
#print axioms Meta.wp_DecTxid
#print axioms Meta.wp_Flags
#print axioms Meta.wp_Freelist
#print axioms Meta.wp_IncTxid
#print axioms Meta.wp_IsFreelistPersisted
#print axioms Meta.wp_Magic
#print axioms Meta.wp_PageSize
#print axioms Meta.wp_Pgid
#print axioms Meta.wp_RootBucket
#print axioms Meta.wp_SetChecksum
#print axioms Meta.wp_SetFlags
#print axioms Meta.wp_SetFreelist
#print axioms Meta.wp_SetMagic
#print axioms Meta.wp_SetPageSize
#print axioms Meta.wp_SetPgid
#print axioms Meta.wp_SetTxid
#print axioms Meta.wp_SetVersion
#print axioms Meta.wp_Txid
#print axioms Meta.wp_Version
#print axioms wp_UnsafeIndex
#print axioms Page.wp_BranchPageElement
#print axioms wp_UnsafeAdd
#print axioms Page.wp_BranchPageElements
#print axioms Page.wp_Count
#print axioms Page.wp_Flags
#print axioms Page.wp_Id
#print axioms Page.wp_IsBranchPage
#print axioms Page.wp_IsFreelistPage
#print axioms Page.wp_IsLeafPage
#print axioms Page.wp_IsMetaPage
#print axioms Page.wp_IsValidPage
#print axioms Page.wp_LeafPageElement
#print axioms Page.wp_LeafPageElements
#print axioms Page.wp_Meta
#print axioms Page.wp_Overflow
#print axioms Page.wp_PageElementSize
#print axioms Page.wp_SetCount
#print axioms Page.wp_SetFlags
#print axioms Page.wp_SetId
#print axioms Page.wp_SetOverflow
#print axioms Pgids.wp_Len
#print axioms Pgids.wp_Less
#print axioms wp_Mergepgids
#print axioms Pgids.wp_Merge
#print axioms Pgids.wp_Swap
#print axioms wp_UnsafeByteSlice
#print axioms branchPageElement.wp_Key
#print axioms branchPageElement.wp_Ksize
#print axioms branchPageElement.wp_Pgid
#print axioms branchPageElement.wp_Pos
#print axioms branchPageElement.wp_SetKsize
#print axioms branchPageElement.wp_SetPgid
#print axioms branchPageElement.wp_SetPos
#print axioms wp_LoadBucket
#print axioms wp_LoadPage
#print axioms wp_LoadPageMeta
#print axioms leafPageElement.wp_Flags
#print axioms leafPageElement.wp_IsBucketEntry
#print axioms leafPageElement.wp_Key
#print axioms leafPageElement.wp_Ksize
#print axioms leafPageElement.wp_Pos
#print axioms leafPageElement.wp_SetFlags
#print axioms leafPageElement.wp_SetKsize
#print axioms leafPageElement.wp_SetPos
#print axioms leafPageElement.wp_SetVsize
#print axioms leafPageElement.wp_Value
#print axioms leafPageElement.wp_Vsize
#print axioms Page_bytes

end bbolt
end EtcdGrove
end Perennial
