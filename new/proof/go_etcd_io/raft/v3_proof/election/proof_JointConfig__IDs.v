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
    (* STUCK, and this is the real stuck point.  The remaining program is

         let: "$range" := ![quorum.MajorityConfig]
                            (IndexRef quorum.JointConfig
                               (# tv.(tracker.ProgressTracker.Config')
                                    .(tracker.Config.Voters'), # (W64 0))%V) in
         (let: "id" := GoAlloc go.uint64 … in map.for_range … ) ;;;
         (the same at index 1) ;;;
         return: ![go.MapType go.uint64 (go.StructType [])] (# m_ptr)

       and a further [wp_auto] fails with "Failed to progress".  See the comment
       above the statement: the operand of [IndexRef] is an array *value* and
       the model only gives [IndexRef] a step on an array *location*. *)
  Admitted.

End JointConfigIDsProof.
