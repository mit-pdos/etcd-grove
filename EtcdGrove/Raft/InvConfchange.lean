/-
The `confchange` package on the one path this development takes through it:
`confchange.Restore` of a voters-only `ConfState` onto the empty tracker, from `newRaft`
and `raft.restore`. Shared vocabulary of `Spec/confchange_*.lean`, `Spec/Changer__*.lean`
and `Spec/Config__Clone.lean`.

Until 2026-10-08 `confchange` was not translated (`confchange.toml` translated only the
`Changer` type) and `confchange.Restore`'s triple was an `axiom`, one of the two axioms
about core raft code (notes/STATUS.md on `main`, "The fourteen axioms"). The package is
now translated in full and `Restore` is proved from its callees, in the voters-only,
non-joint case that `Restore.spec` states. There is no Rocq counterpart: these files are
Lean-first.

The vocabulary:
* `ConfigSimple cfg v`: a voters-only, non-joint `tracker.Config` value whose incoming
  voter map is `v`. This is what `Restore` starts from (`MakeProgressTracker`'s empty
  configuration) and what every step of `chain` produces, so it is the one shape of
  `Config` the proofs see.
* `addNodeCC id`: the `ConfChangeSingle` `AddNode id`, the only change
  `toConfChangeSingle` emits for a voters-only `ConfState`.
* `opSpec f chg P Q`: the triple of one of `chain`'s ops `f`, from `P` to `Q` on the
  (`Config`, progress map) pair that `chain` threads through `chg.Tracker`.
-/
import EtcdGrove.Raft.InvTracker

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

/-- A voters-only, non-joint `Config` value: the incoming voter map is `v`; the outgoing
voter map, `Learners` and `LearnersNext` are `nil`. What `Restore.spec` says of the
configuration it starts from (`MakeProgressTracker`'s), and all `Config.Clone` reads. -/
def ConfigVotersOnly [FfiSyntax] (cfg : tracker.Config) (v : Loc) : Prop :=
  cfg.Voters'.arr = [v, map.nil] ∧ cfg.Learners' = map.nil ∧ cfg.LearnersNext' = map.nil

/-- `ConfigVotersOnly`, and `AutoLeave` off: what Go's `checkInvariants` requires of a
non-joint config, and what `Config.Clone` produces (it does not copy `AutoLeave`). -/
def ConfigSimple [FfiSyntax] (cfg : tracker.Config) (v : Loc) : Prop :=
  ConfigVotersOnly cfg v ∧ cfg.AutoLeave' = false

/-- `pb.ConfChangeSingle{Type: pb.ConfChangeAddNode, NodeID: id}`. -/
abbrev addNodeCC [FfiSyntax] (id : w64) : raftpb.ConfChangeSingle :=
  { Type' := W32 0, NodeID' := id }

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- The triple of one of `chain`'s ops. `chain` calls `op(chg)` with the `Changer`
*value* whose tracker holds the current `Config` and progress map, and stores what the
op returns back into them; so an op is specified on every such value, from `P` on the
pair it is handed to `Q` on the pair it returns, with no error. -/
def opSpec (f : GoFunc) (chg : confchange.Changer)
    (P Q : tracker.Config → Loc → IProp GF) : IProp GF :=
  iprop(∀ (cfg : tracker.Config) (prs : Loc),
    {{ P cfg prs }}
      (App (Val #f)
        (Val #({ chg with Tracker' := { chg.Tracker' with Config' := cfg, Progress' := prs } } :
          confchange.Changer)))
    {{ (cfg' : tracker.Config) (prs' : Loc), RET (PairV (PairV #cfg' #prs') #interface.nil);
        Q cfg' prs' }})

instance opSpec_persistent (f : GoFunc) (chg : confchange.Changer)
    (P Q : tracker.Config → Loc → IProp GF) : Persistent (opSpec f chg P Q) := by
  unfold opSpec; infer_instance

end defs

/-- An element of a duplicate-free list is not among the elements before it: the loop
invariants of `symdiff` and `checkAndCopy` count or copy the keys of a map in the order
`wp_map_for_range` enumerates them, and need the key at hand to be new. -/
theorem not_mem_take_of_nodup {α : Type} {l : List α} (h : l.Nodup) {i : Nat} {x : α}
    (hx : l[i]? = some x) : x ∉ l.take i := by
  intro hm
  have hsplit : l = l.take i ++ l.drop i := (List.take_append_drop i l).symm
  rw [hsplit] at h
  have hdrop : x ∈ l.drop i := by
    apply List.mem_of_getElem? (i := 0)
    rw [List.getElem?_drop]; simpa using hx
  exact (List.nodup_append.1 h).2.2 x hm x hdrop rfl

end EtcdGrove
end Perennial
