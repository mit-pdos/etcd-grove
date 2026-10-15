/-
The trust base of every btree result: `#print axioms` of each theorem of `Link.lean`
(and of `ownBTree_split`). Built with the rest; read its output to check it.
-/
module

public import Proof.k8s_io.utils.third_party.forked.golang.btree.Link
public import Proof.k8s_io.utils.third_party.forked.golang.btree.Fractional

@[expose] public section

-- `#print axioms` prints the axioms by their full names: shortening each name to the
-- shortest unambiguous one in this environment took most of this module's build (25s of
-- 31s for the server's `txn/Results.lean`).
set_option pp.fullNames true

#print axioms Perennial.EtcdGrove.btree.wp_empty
#print axioms Perennial.EtcdGrove.btree.items.wp_find
#print axioms Perennial.EtcdGrove.btree.node.wp_iterate
#print axioms Perennial.EtcdGrove.btree.BTree.wp_Ascend
#print axioms Perennial.EtcdGrove.btree.wp_optional
#print axioms Perennial.EtcdGrove.btree.BTree.wp_AscendGreaterOrEqual
#print axioms Perennial.EtcdGrove.btree.BTree.wp_AscendLessThan
#print axioms Perennial.EtcdGrove.btree.BTree.wp_AscendRange
#print axioms Perennial.EtcdGrove.btree.items.wp_truncate
#print axioms Perennial.EtcdGrove.btree.FreeList.wp_freeNode
#print axioms Perennial.EtcdGrove.btree.copyOnWriteContext.wp_freeNode
#print axioms Perennial.EtcdGrove.btree.node.wp_reset
#print axioms Perennial.EtcdGrove.btree.BTree.wp_Clear
#print axioms Perennial.EtcdGrove.btree.BTree.wp_Clone
#print axioms Perennial.EtcdGrove.btree.BTree.wp_minItems
#print axioms Perennial.EtcdGrove.btree.FreeList.wp_newNode
#print axioms Perennial.EtcdGrove.btree.copyOnWriteContext.wp_newNode
#print axioms Perennial.EtcdGrove.btree.node.wp_mutableFor
#print axioms Perennial.EtcdGrove.btree.items.wp_removeAt
#print axioms Perennial.EtcdGrove.btree.items.wp_pop
#print axioms Perennial.EtcdGrove.btree.items.wp_insertAt
#print axioms Perennial.EtcdGrove.btree.node.wp_mutableChild
#print axioms Perennial.EtcdGrove.btree.node.wp_remove
#print axioms Perennial.EtcdGrove.btree.BTree.wp_deleteItem
#print axioms Perennial.EtcdGrove.btree.BTree.wp_Delete
#print axioms Perennial.EtcdGrove.btree.BTree.wp_DeleteMax
#print axioms Perennial.EtcdGrove.btree.BTree.wp_DeleteMin
#print axioms Perennial.EtcdGrove.btree.BTree.wp_Descend
#print axioms Perennial.EtcdGrove.btree.BTree.wp_DescendGreaterThan
#print axioms Perennial.EtcdGrove.btree.BTree.wp_DescendLessOrEqual
#print axioms Perennial.EtcdGrove.btree.BTree.wp_DescendRange
#print axioms Perennial.EtcdGrove.btree.node.wp_get
#print axioms Perennial.EtcdGrove.btree.BTree.wp_Get
#print axioms Perennial.EtcdGrove.btree.BTree.wp_Has
#print axioms Perennial.EtcdGrove.btree.BTree.wp_Len
#print axioms Perennial.EtcdGrove.btree.wp_max
#print axioms Perennial.EtcdGrove.btree.BTree.wp_Max
#print axioms Perennial.EtcdGrove.btree.wp_min
#print axioms Perennial.EtcdGrove.btree.BTree.wp_Min
#print axioms Perennial.EtcdGrove.btree.BTree.wp_maxItems
#print axioms Perennial.EtcdGrove.btree.node.wp_split
#print axioms Perennial.EtcdGrove.btree.node.wp_maybeSplitChild
#print axioms Perennial.EtcdGrove.btree.node.wp_insert
#print axioms Perennial.EtcdGrove.btree.BTree.wp_ReplaceOrInsert
#print axioms Perennial.EtcdGrove.btree.wp_Less
#print axioms Perennial.EtcdGrove.btree.wp_NewFreeList
#print axioms Perennial.EtcdGrove.btree.wp_NewWithFreeList
#print axioms Perennial.EtcdGrove.btree.wp_New
#print axioms Perennial.EtcdGrove.btree.wp_NewOrdered
#print axioms Perennial.EtcdGrove.btree.wp_initialize
#print axioms Perennial.EtcdGrove.btree.node.wp_growChildAndRemove
#print axioms Perennial.EtcdGrove.btree.ownBTree_split
