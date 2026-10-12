/-
The trust base of every proved result of the interval tree (`pkg/v3/adt`) so far:
`#print axioms` of each theorem of `Link.lean`. The tree's contract (`NewIntervalTree` and the
`intervalTree` methods) is pending: specified over the opaque `ownIvt`, proved in unit 4 of the
watchable store; no result here reaches it. Built with the rest; read its output to check it.
-/
module

public import Proof.go_etcd_io.etcd.pkg.v3.adt.Link
public import Proof.go_etcd_io.etcd.pkg.v3.adt.TreeInsert
public import Proof.go_etcd_io.etcd.pkg.v3.adt.TreeDelete

@[expose] public section

#print axioms Perennial.EtcdGrove.adt.StringAffineComparable.wp_Compare
#print axioms Perennial.EtcdGrove.adt.Interval.wp_Compare
#print axioms Perennial.EtcdGrove.adt.wp_NewStringAffineInterval
#print axioms Perennial.EtcdGrove.adt.wp_NewStringAffinePoint

/-! The model's lemmas `Insert`'s contract rests on (`Model.lean`). -/
#print axioms Perennial.EtcdGrove.adt.ivtInsert_sorted
#print axioms Perennial.EtcdGrove.adt.ivtInsert_ivSorted
#print axioms Perennial.EtcdGrove.adt.mem_ivtInsert

/-! The tree model's lemmas the reads rest on (`Tree.lean`): `find`'s, `Intersects`'s and
`visit`'s descents are correct over the in-order list, and the rotations keep it. -/
#print axioms Perennial.EtcdGrove.adt.findE_some
#print axioms Perennial.EtcdGrove.adt.findE_none
#print axioms Perennial.EtcdGrove.adt.intersects_iff
#print axioms Perennial.EtcdGrove.adt.visit_stab
#print axioms Perennial.EtcdGrove.adt.RbT.inorder_rotateLeft
#print axioms Perennial.EtcdGrove.adt.RbT.inorder_rotateRight

/-! The insert's model (`TreeInsert.lean`, unit 4b): the descent inserts in the tree's order,
a subtree's max is a function of its entries (the rotations keep it), and `insertFixup`'s loop
invariant holds for the new leaf, is kept by each case of the loop and gives a red-black tree
at its exit. -/
#print axioms Perennial.EtcdGrove.adt.inorder_insertBST
#print axioms Perennial.EtcdGrove.adt.maxEnd_eq_of_inorder
#print axioms Perennial.EtcdGrove.adt.RbCtx.fixInv_start
#print axioms Perennial.EtcdGrove.adt.RbCtx.fixInv_exit
#print axioms Perennial.EtcdGrove.adt.RbCtx.fix_red_LL
#print axioms Perennial.EtcdGrove.adt.RbCtx.fix_red_RL
#print axioms Perennial.EtcdGrove.adt.RbCtx.fix_red_LR
#print axioms Perennial.EtcdGrove.adt.RbCtx.fix_red_RR
#print axioms Perennial.EtcdGrove.adt.RbCtx.fix_black_LL
#print axioms Perennial.EtcdGrove.adt.RbCtx.fix_black_RL
#print axioms Perennial.EtcdGrove.adt.RbCtx.fix_black_LR
#print axioms Perennial.EtcdGrove.adt.RbCtx.fix_black_RR

/-! The delete's model (`TreeDelete.lean`, unit 4c): the splice of a node with at most one child
and the two-children case (the successor's entry copied) remove the found entry at its index,
the splice establishes `deleteFixup`'s loop invariant (or leaves a red-black tree), each case
of the loop keeps it, and blackening `x` at the exit gives a red-black tree. -/
#print axioms Perennial.EtcdGrove.adt.RbCtx.del_inorder_one
#print axioms Perennial.EtcdGrove.adt.RbCtx.del_inorder_two
#print axioms Perennial.EtcdGrove.adt.RbCtx.rb_entry
#print axioms Perennial.EtcdGrove.adt.RbCtx.del_start
#print axioms Perennial.EtcdGrove.adt.RbCtx.delInv_exit
#print axioms Perennial.EtcdGrove.adt.RbCtx.del_case1_L
#print axioms Perennial.EtcdGrove.adt.RbCtx.del_case2_L
#print axioms Perennial.EtcdGrove.adt.RbCtx.del_case3_L
#print axioms Perennial.EtcdGrove.adt.RbCtx.del_case4_L
#print axioms Perennial.EtcdGrove.adt.RbCtx.del_case1_R
#print axioms Perennial.EtcdGrove.adt.RbCtx.del_case2_R
#print axioms Perennial.EtcdGrove.adt.RbCtx.del_case3_R
#print axioms Perennial.EtcdGrove.adt.RbCtx.del_case4_R
#print axioms Perennial.EtcdGrove.adt.maxEnd_plug
