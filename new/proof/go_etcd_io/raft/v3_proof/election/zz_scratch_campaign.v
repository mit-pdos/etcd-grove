(* TEMPORARY scratch file for developing proof_raft__campaign helpers.
   Delete before finishing. *)
Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_raft__campaign.
Require Export New.proof.go_etcd_io.raft.v3_proof.election.inv_slices.

Section helpers.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : raft.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

Context (cfg : gset w64).

Lemma wp_map_len_uint64 (mref : loc) dq (m : gmap w64 unit) :
  {{{ mref ↦${dq} m }}}
    #(functions go.len [go.MapType go.uint64 (go.StructType [])]) #mref
  {{{ RET #(W64 (size m)); mref ↦${dq} m }}}.
Proof.
  wp_start as "Hm". rewrite own_map_unseal. iNamed "Hm".
  wp_apply (_internal_wp_untyped_read with "Hown") as "Hown".
  destruct (go.is_map_domain_exists _ _ His_map) as [ks Hks].
  pose proof (go.internal_map_length_step_pure mv ks Hks) as Hlenstep.
  wp_auto.
  (* nonce 3132723601 *) Show.
Admitted.

End helpers.
