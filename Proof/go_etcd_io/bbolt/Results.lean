/-
The proved results of bbolt's root package (`Link.lean`: every proof linked to its callees'
results, `internal/common`'s from its own `Link.lean`), over the file and memory-map model
(`Proof/os/FileModel.lean`, whose operations' specs are axioms) and the page model
(`PageModel.lean`, `TxModel.lean`).

`#print axioms` on a result is its trust base (`sorryAx` is unfinished work); the model's
axioms (`fileBytes`, `unix.Mmap.wp_proof`, ...) appear in it.
-/
module

public import Proof.go_etcd_io.bbolt.Link

@[expose] public section

namespace Perennial
namespace EtcdGrove
namespace bbolt

#print axioms BucketStats.wp_Add
#print axioms DB.wp_page
#print axioms Tx.wp_page
#print axioms Bucket.wp_pageNode
#print axioms elemRef.wp_count
#print axioms Cursor.wp_keyValue
#print axioms Cursor.wp_nsearch
#print axioms DB.wp_GoString
#print axioms DB.wp_Info
#print axioms DB.wp_IsReadOnly
#print axioms DB.wp_Path
#print axioms DB.wp_String
#print axioms DB.wp_growSize
#print axioms DB.wp_invalidate
#print axioms DB.wp_meta
#print axioms DB.wp_mmapSize
#print axioms unix.wp_Munmap
#print axioms wp_munmap
#print axioms DB.wp_munmap
#print axioms DB.wp_pageInBuffer
#print axioms Options.wp_String
#print axioms TxStats.wp_GetPageCount
#print axioms TxStats.wp_GetPageAlloc
#print axioms TxStats.wp_GetCursorCount
#print axioms TxStats.wp_GetNodeCount
#print axioms TxStats.wp_GetNodeDeref
#print axioms TxStats.wp_GetRebalance
#print axioms wp_atomicLoadDuration
#print axioms TxStats.wp_GetRebalanceTime
#print axioms TxStats.wp_GetSplit
#print axioms TxStats.wp_GetSpill
#print axioms TxStats.wp_GetSpillTime
#print axioms TxStats.wp_GetWrite
#print axioms TxStats.wp_GetWriteTime
#print axioms TxStats.wp_Sub
#print axioms Stats.wp_Sub
#print axioms TxStats.wp_IncCursorCount
#print axioms TxStats.wp_IncNodeCount
#print axioms TxStats.wp_IncNodeDeref
#print axioms TxStats.wp_IncPageAlloc
#print axioms TxStats.wp_IncPageCount
#print axioms TxStats.wp_IncRebalance
#print axioms wp_atomicAddDuration
#print axioms TxStats.wp_IncRebalanceTime
#print axioms TxStats.wp_IncSpill
#print axioms TxStats.wp_IncSpillTime
#print axioms TxStats.wp_IncSplit
#print axioms TxStats.wp_IncWrite
#print axioms TxStats.wp_IncWriteTime
#print axioms TxStats.wp_add
#print axioms Tx.wp_DB
#print axioms Tx.wp_ID
#print axioms Tx.wp_OnCommit
#print axioms Tx.wp_Size
#print axioms Tx.wp_Stats
#print axioms Tx.wp_Writable
#print axioms wp_newBucket
#print axioms Tx.wp_init
#print axioms wp_cloneBytes
#print axioms wp_compareKeys
#print axioms os.File.wp_Fd
#print axioms unix.wp_Mmap
#print axioms unix.wp_Madvise
#print axioms wp_mmap
#print axioms elemRef.wp_isLeaf
#print axioms fs.FileInfo.wp_Size
#print axioms nodes.wp_Len
#print axioms nodes.wp_Swap
#print axioms os.File.wp_Close
#print axioms os.File.wp_Name
#print axioms os.File.wp_ReadAt
#print axioms os.File.wp_Stat
#print axioms os.File.wp_Sync
#print axioms os.File.wp_Truncate
#print axioms os.File.wp_WriteAt
#print axioms os.wp_OpenFile
#print axioms syscall.wp_Fdatasync
#print axioms syscall.wp_Flock

end bbolt
end EtcdGrove
end Perennial
