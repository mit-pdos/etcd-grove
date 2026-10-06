/-
Port of `election_proof/spec_JointConfig__IDs.v` (feb5c73d4).

Lean notes: the type of Rocq's untyped binder `tv` is written out
(`tracker.ProgressTracker`); Rocq's `trk.t` record is `Trk`.
-/
import EtcdGrove.Raft.ElectionProof.InvRaftPhys

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- The ids of the voters, in some order, as `campaign` enumerates them. `campaign`
calls this on `&r.trk.Config.Voters`, so the receiver is that field ref and not the
tracker itself.

**In scope. The translation defect that blocked this is fixed** (2026-09-17); what is
left is ordinary proof work.

Until 2026-09-17 Goose emitted the element read `c[0]` inside `JointConfig.IDs` as

    ![MajorityConfig] (IndexRef JointConfig (![JointConfig] "c", #(W64 0)))

-- it *loaded* the operand and then asked `IndexRef` for a reference into the loaded
**value**. That is right for slices and wrong for arrays:

- `index_ref_slice` (Rocq new/golang/defn/slice.v:122) takes `(#s, #i)` with
  `s : GoSlice`, a *value* -- a slice value carries `GoSlice.ptr`, so an address can be
  recovered from it;
- `index_ref_array` (Rocq new/golang/defn/array.v:50) takes `(#l, #i)` with `l : Loc`,
  a *location* -- an array value is `array.mk n (list V)` (Rocq
  src/goose_lang/lang.v:528) and carries no address at all, so there is nothing to take
  a reference into.

So the body was **stuck** there and no Hoare triple about it was provable. The fix was
in Goose (`goose/goose.go`, `exprAddr`'s `*ast.IndexExpr` case): for an array operand
take the array's address rather than loading it. The emitted code is now

    ![MajorityConfig] (IndexRef JointConfig ("c", #(W64 0)))

(Rocq new/code/go_etcd_io/raft/v3/quorum.v:82, and :94 for `c[1]`; `JointConfig.IDs.impl`
in `Perennial/Code/go_etcd_io/raft/v3/quorum.lean`), and the operand is exactly what
the receiver's `GoAlloc JointConfig` produces, so `index_ref_array` applies. Measured:
the last `wp_auto` of the banked prefix in `proof_JointConfig__IDs.v` now steps the
`IndexRef` to `#(array_index_ref map.t 0 c_ptr)` and stops at the *load* of that
location -- an ownership obligation, not a missing rule.

**What is left.** Split element 0 out of `"c" : c_ptr ↦ ...Voters'` with `array_acc`
(Rocq new/golang/theory/array.v); `Hvoters_arr` says the element is `voters_ref`, so
the load yields it. Then a `wp_map_for_range` over `voters_ref` (the `Hvoters_dom`
conjunct of `ownTracker` gives `domSet voters = cfg`), then the same at index 1, where
the element is `map.nil` and the pure step `wp_map_nil_for_range` (Rocq
new/golang/theory/map.v) applies, then `return: m`. The statement here is the right
one; do not weaken it.

`slices.Sort` is *not* involved -- that sort is in `campaign`, not in `IDs`.

`JointConfig.wp_CommittedIndex` (Perennial `v3_proof/readonly.lean`; Rocq
`v3_proof/readonly.v:718`) is still an `axiom` for what *was* this same defect:
`JointConfig.CommittedIndex` indexes the same array the same way (quorum.v:132,136).
It is now unblocked too and should be discharged. -/
abbrev quorum.JointConfig.IDs.spec : Prop :=
  ∀ (cfg : GSet w64),
  ∀ (trk : Loc) (tv : tracker.ProgressTracker) (t : Trk),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.quorum ∗ trk ↦ tv ∗
      ownTracker cfg tv t }}
    (App (Val (((trk.[tracker.ProgressTracker, go!"Config"]).[tracker.Config, go!"Voters"])
      @!! go.GoType.PointerType quorum.JointConfig.ty @!! go!"IDs")) (Val #()))
  {{ (mref : Loc) (idm : GMap w64 Unit), RET #mref;
      trk ↦ tv ∗ ownTracker cfg tv t ∗
      mref ↦$ idm ∗ ⌜domSet idm = cfg⌝ }}

end spec

end EtcdGrove
end Perennial
