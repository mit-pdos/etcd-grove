/-
The proved results of bbolt's `internal/freelist` (`Link.lean`, every proof linked to its
callees' proofs): the array freelist and `shared`'s methods but the four that delete from a
map while ranging over it (`Rollback`, `release`, `releaseRange`, `ReleasePendingPages`:
specs only; Perennial's map range does not allow it). `sort.Sort` is a trust-boundary axiom.

`#print axioms` on a result is its trust base (`sorryAx` is unfinished work).
-/
module

public import Proof.go_etcd_io.bbolt.internal.freelist.Link

@[expose] public section

namespace Perennial
namespace EtcdGrove
namespace bbolt

#print axioms wp_newShared
#print axioms wp_NewArrayFreelist
#print axioms array.wp_Allocate
#print axioms array.wp_FreeCount
#print axioms shared.wp_pendingPageIds
#print axioms shared.wp_reindex
#print axioms array.wp_freePageIds
#print axioms array.wp_Init
#print axioms sort.wp_Sort
#print axioms array.wp_mergeSpans
#print axioms shared.wp_AddReadonlyTXID
#print axioms shared.wp_PendingCount
#print axioms shared.wp_Copyall
#print axioms shared.wp_Count
#print axioms shared.wp_EstimatedWritePageSize
#print axioms shared.wp_Free
#print axioms shared.wp_Freed
#print axioms shared.wp_NoSyncReload
#print axioms shared.wp_Read
#print axioms shared.wp_Reload
#print axioms shared.wp_RemoveReadonlyTXID
#print axioms shared.wp_Write
#print axioms txIDx.wp_Len
#print axioms txIDx.wp_Less
#print axioms txIDx.wp_Swap

end bbolt
end EtcdGrove
end Perennial
