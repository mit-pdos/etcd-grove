/-
The trust base of every proved result of the interval tree (`pkg/v3/adt`) so far:
`#print axioms` of each theorem of `Link.lean`. The tree's contract (`NewIntervalTree` and the
`intervalTree` methods) is pending: specified over the opaque `ownIvt`, proved in unit 4 of the
watchable store; no result here reaches it. Built with the rest; read its output to check it.
-/
module

public import Proof.go_etcd_io.etcd.pkg.v3.adt.Link

@[expose] public section

#print axioms Perennial.EtcdGrove.adt.StringAffineComparable.wp_Compare
#print axioms Perennial.EtcdGrove.adt.Interval.wp_Compare
#print axioms Perennial.EtcdGrove.adt.wp_NewStringAffineInterval
#print axioms Perennial.EtcdGrove.adt.wp_NewStringAffinePoint

/-! The model's lemmas `Insert`'s contract rests on (`Model.lean`). -/
#print axioms Perennial.EtcdGrove.adt.ivtInsert_sorted
#print axioms Perennial.EtcdGrove.adt.mem_ivtInsert

/-! The tree model's lemmas the reads rest on (`Tree.lean`): `find`'s, `Intersects`'s and
`visit`'s descents are correct over the in-order list, and the rotations keep it. -/
#print axioms Perennial.EtcdGrove.adt.findE_eq
#print axioms Perennial.EtcdGrove.adt.intersects_iff
#print axioms Perennial.EtcdGrove.adt.visit_stab
#print axioms Perennial.EtcdGrove.adt.RbT.inorder_rotateLeft
#print axioms Perennial.EtcdGrove.adt.RbT.inorder_rotateRight
