(** [len(c)] for a [quorum.MajorityConfig].

    Two obstacles, both already documented elsewhere and both needing a
    lemma here rather than a tactic call:

    1. [MajorityConfig] is a *named* type ([go.Named
       "…/quorum.MajorityConfig"]), and [new/golang/defn/map.v] declares its
       [FuncUnfold] instances at the literal [go.MapType key elem].  So
       [wp_auto] leaves a bare [#(functions go.len [quorum.MajorityConfig])]
       untouched; [go.len_underlying] plus [go.is_underlying] is the way
       through, exactly as [wp_ProgressMap_len] ([inv_tracker.v]) does it for
       [tracker.ProgressMap].

    2. The second component of a simple configuration is [map.nil], and
       [pure_wp_map_nil_len] ([new/golang/theory/map.v]) is closed over the
       section's [K] and [V], which its *statement* does not mention, so
       [tc_solve] cannot instantiate them and [wp_auto] never fires it (the
       same defect as [wp_map_nil_for_range]; see
       [map_for_range_keep.v] in this directory).  The specialised instance
       below fills in [K := w64], [V := unit] -- the key/value types of a
       [MajorityConfig], [map[uint64]struct{}].

    Proof structure only: no [Module Type], no [Parameter], no triple about a
    Go function, so only [proof_MajorityConfig__VoteResult.v] may
    [Require] it ([etc/check-module-discipline.py]'s [*_helpers] rule). *)

Require Export New.proof.go_etcd_io.raft.v3_proof.election.defs.

Set Default Proof Using "Type".

Section nil_len.
Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}
  {sem_fn : GoSemanticsFunctions} {pre_sem : go.PreSemantics}.

#[global] Instance pure_wp_map_nil_len_w64 key_type elem_type :
  PureWp True (#(functions go.len [go.MapType key_type elem_type]) #map.nil)
    #(W64 0) :=
  pure_wp_map_nil_len (K:=w64) (V:=unit) key_type elem_type.

End nil_len.

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
