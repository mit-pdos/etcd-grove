Require Export New.proof.go_etcd_io.raft.v3_proof.election.postulates_JointConfig__IDs.

Module JointConfigIDsProof (P : JOINTCONFIG__IDS_POSTULATES) : JOINTCONFIG__IDS.

  (* [Proof using Type], not the file's [W] default: [W] would force
     [package_sem] into the discharged signature, and this constant's former
     [Axiom] form did not have it.  Checked -- with [Proof using Type] the type
     of this lemma is syntactically identical to the axiom it replaces, so no
     call site changes.  See notes/gotchas.md. *)
  Lemma wp_JointConfig__IDs : wp_JointConfig__IDs_body.
  Proof.
    intros_ambient.
    intros cfg.

    (* Everything down to the [Admitted] is machine-checked. *)
    intros trk tv votes.
    wp_start as "[Htrk Hown]". iNamed "Hown".
    (* [wp_auto] reads [r.trk.Config.Voters] out of [trk ↦ tv] and reduces the
       pointer method to the value method applied to the [JointConfig] value. *)
    wp_auto.
    (* Two [wp_call]s, not one: [JointConfig'ptr_IDs_unfold] is the wrapper
       [λ: "$r", MethodResolve JointConfig "IDs" (![JointConfig] "$r")], so the
       first call enters the wrapper and the second enters [JointConfig__IDsⁱᵐᵖˡ].
       A single [wp_call] leaves [WP quorum.JointConfig__IDsⁱᵐᵖˡ …] and the next
       [wp_auto] then reports "Failed to progress", which looks like the stuck
       point below but is not. *)
    wp_method_call. wp_call. wp_call.
    (* [GoAlloc JointConfig] gives ["c" ∷ c_ptr ↦ tv.(Config').(Voters')]; note
       this does *not* hit the [alloc_array ⤳ AngelicExit] escape hatch. *)
    wp_auto.
    (* [m := map[uint64]struct{}{}] *)
    wp_apply wp_map_make1. iIntros "%mref Hmref".
    wp_auto.
    (* The array index steps now.  The [wp_auto] above reduced
       [IndexRef quorum.JointConfig (# c_ptr, # (W64 0))] to
       [# (array_index_ref map.t 0 c_ptr)] and stopped at the *load* of it:

         let: "$range" := ![quorum.MajorityConfig]
                            (# (array_index_ref map.t 0 c_ptr)) in
         (let: "id" := GoAlloc go.uint64 … in map.for_range … ) ;;;
         (the same at index 1, IndexRef not yet stepped) ;;;
         return: ![go.MapType go.uint64 (go.StructType [])] (# m_ptr)

       That load is an ownership obligation, not a missing rule: use
       [array_acc] on ["c"] to peel element 0 off, with [Hvoters_arr] for the
       lookup side condition.  See [spec_JointConfig__IDs.v] for the rest. *)
  Admitted.

End JointConfigIDsProof.
