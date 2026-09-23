(** [len(c)] for a [quorum.MajorityConfig].

    [MajorityConfig] is a *named* type ([go.Named
    "…/quorum.MajorityConfig"]), and [new/golang/defn/map.v] declares its
    [FuncUnfold] instances at the literal [go.MapType key elem].  So
    [wp_auto] leaves a bare [#(functions go.len [quorum.MajorityConfig])]
    untouched; [go.len_underlying] plus [go.is_underlying] is the way
    through, exactly as [wp_ProgressMap_len] ([inv_tracker.v]) does it for
    [tracker.ProgressMap].  Once the named type is unfolded the framework
    lemmas apply: [wp_map_len] for an owned map, [pure_wp_map_nil_len] for
    [map.nil].

    Proof structure only: no [Module Type], no [Parameter], no triple about a
    Go function, so only [proof_MajorityConfig__VoteResult.v] may
    [Require] it ([etc/check-module-discipline.py]'s [*_helpers] rule). *)

Require Export New.proof.go_etcd_io.raft.election_proof.defs.

Set Default Proof Using "Type".

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : raft.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

(** [len] of a [MajorityConfig] the caller owns. *)
Lemma wp_MajorityConfig_len (mref : loc) dq (m : gmap w64 unit) :
  {{{ mref ↦${dq} m }}}
    #(functions go.len [quorum.MajorityConfig]) #mref
  {{{ RET #(W64 (size m)); mref ↦${dq} m }}}.
Proof.
  wp_start_folded as "Hm".
  rewrite (go.len_underlying quorum.MajorityConfig).
  rewrite (go.is_underlying (t := quorum.MajorityConfig)
             (tunder := go.MapType go.uint64 (go.StructType []))).
  wp_apply (wp_map_len with "Hm") as "Hm".
  iApply "HΦ". iFrame.
Qed.

(** [len] of the nil [MajorityConfig]: [0], with nothing owned. *)
Lemma wp_MajorityConfig_nil_len :
  {{{ True }}}
    #(functions go.len [quorum.MajorityConfig]) #map.nil
  {{{ RET #(W64 0); True }}}.
Proof.
  wp_start_folded as "_".
  rewrite (go.len_underlying quorum.MajorityConfig).
  rewrite (go.is_underlying (t := quorum.MajorityConfig)
             (tunder := go.MapType go.uint64 (go.StructType []))).
  wp_auto. by iApply "HΦ".
Qed.

End proof.
