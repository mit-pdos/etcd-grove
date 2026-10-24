/-
The trust base of the interval tree's results (`pkg/v3/adt`): `#print axioms` of the exported
theorems of `Link.lean` (the tree's contract over string-affine keys, the watchable store's, and
over bytes-affine keys, the auth store's: instances of the generic proofs, the auth plan's S2b)
and of the model's lemmas they rest on. Built with the rest; read its output to check it.
-/
module

public import Proof.go_etcd_io.etcd.pkg.v3.adt.Link
public import Proof.go_etcd_io.etcd.pkg.v3.adt.TreeInsert
public import Proof.go_etcd_io.etcd.pkg.v3.adt.TreeDelete

@[expose] public section

-- `#print axioms` prints the axioms by their full names: shortening each name to the
-- shortest unambiguous one in this environment took most of this module's build (25s of
-- 31s for the server's `txn/Results.lean`).
set_option pp.fullNames true

#print axioms Perennial.EtcdGrove.adt.StringAffineComparable.wp_Compare
#print axioms Perennial.EtcdGrove.adt.Interval.wp_Compare
#print axioms Perennial.EtcdGrove.adt.wp_NewStringAffineInterval
#print axioms Perennial.EtcdGrove.adt.wp_NewStringAffinePoint
/-! The tree's contract over string-affine keys (the watchable store's). -/
#print axioms Perennial.EtcdGrove.adt.wp_NewIntervalTree
#print axioms Perennial.EtcdGrove.adt.intervalTree.wp_Insert
#print axioms Perennial.EtcdGrove.adt.intervalTree.wp_Delete
#print axioms Perennial.EtcdGrove.adt.intervalTree.wp_Find
#print axioms Perennial.EtcdGrove.adt.intervalTree.wp_Intersects
#print axioms Perennial.EtcdGrove.adt.intervalTree.wp_Visit
#print axioms Perennial.EtcdGrove.adt.intervalTree.wp_Stab
#print axioms Perennial.EtcdGrove.adt.intervalTree.wp_Contains
#print axioms Perennial.EtcdGrove.adt.intervalTree.wp_Union
#print axioms Perennial.EtcdGrove.adt.intervalTree.wp_Len
#print axioms Perennial.EtcdGrove.adt.wp_ownIvt_split

/-! The bytes-affine comparison (the auth plan's S2, 2026-10-23), the tree's contract over
bytes-affine keys (the auth store's permission cache: the generic proofs instantiated, the auth
plan's S2b; until then axioms of `BytesIvl.lean`), the pure meaning of the coverage queries over
the model (`Contains.lean`) and the bytes-affine tree's other facts (`BytesIvl.lean`). -/
#print axioms Perennial.EtcdGrove.adt.BytesAffineComparable.wp_Compare
#print axioms Perennial.EtcdGrove.adt.intervalTree.wp_Insert_bytes
#print axioms Perennial.EtcdGrove.adt.intervalTree.wp_Intersects_bytes
#print axioms Perennial.EtcdGrove.adt.intervalTree.wp_Contains_bytes
#print axioms Perennial.EtcdGrove.adt.stab_point_iff
#print axioms Perennial.EtcdGrove.adt.containsRes_iff
#print axioms Perennial.EtcdGrove.adt.ownIvtB_of_empty
#print axioms Perennial.EtcdGrove.adt.ownIvtB_persist

/-! The model's lemmas `Insert`'s contract rests on (`Model.lean`). -/
#print axioms Perennial.EtcdGrove.adt.ivtInsert_sorted
#print axioms Perennial.EtcdGrove.adt.ivtInsert_ivSorted
#print axioms Perennial.EtcdGrove.adt.mem_ivtInsert

/-! `Union`'s count bound (`Model.lean`): the inserts, one by one, add their number. -/
#print axioms Perennial.EtcdGrove.adt.length_foldl_ivtInsert

/-! The tree model's lemmas the reads rest on (`Tree.lean`): `find`'s, `Intersects`'s and
`visit`'s descents are correct over the in-order list, and the rotations keep it. -/
#print axioms Perennial.EtcdGrove.adt.findE_some
#print axioms Perennial.EtcdGrove.adt.findE_none
#print axioms Perennial.EtcdGrove.adt.intersects_iff
#print axioms Perennial.EtcdGrove.adt.visit_stab

/-! The insert's model (`TreeInsert.lean`, unit 4b): the descent inserts in the tree's order,
a subtree's max is a function of its entries (the rotations keep it), and `insertFixup`'s loop
invariant holds for the new leaf, is kept by each case of the loop and gives a red-black tree
at its exit. -/
#print axioms Perennial.EtcdGrove.adt.inorder_insertBST
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
