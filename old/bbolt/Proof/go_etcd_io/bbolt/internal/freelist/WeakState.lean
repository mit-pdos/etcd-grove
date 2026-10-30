/-
A freelist state that may be well-formed but for its free and pending ids being disjoint
(`FLState.WFw`): what `Read(p)` leaves when the freelist page `p` holds ids that are still
pending (bbolt writes the free and the pending ids into the page; `Commit`'s rollback reloads
it while an older transaction's pending entry survives). `Reload` then drops the pending ids
again (`NoSyncReload`), back to a well-formed state.

`ownSharedW` is `ownShared` for such a state, and `FLImpl.InitSpecW` the implementation's
`Init` from and to such states. Of no ids, `Init` needs the old free ids all pending:
`hashMap.Init` then returns before `reindex`, keeping the old cache (right only then).
-/
module

public import Proof.go_etcd_io.bbolt.internal.freelist.Lemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt.internal.freelist

/-- Well-formed but for the free and pending ids being disjoint: the free ids increase, the
pending ids are distinct, all are at least 2, fewer than `2^63` in all, and each pending entry
has as many allocating transactions as ids. -/
def FLState.WFw (σ : FLState) : Prop :=
  σ.pendingIds.Nodup ∧ (∀ id ∈ σ.allIds, 2 ≤ uint.Z id) ∧ PgidsIncr σ.free ∧
  σ.allIds.length < 2 ^ 63 ∧
  (∀ t p, σ.pending !! t = some p → p.ids.length = p.alloctx.length)

theorem FLState.WF.wfw {σ : FLState} (h : σ.WF) : σ.WFw :=
  ⟨(List.nodup_append.1 h.1).2.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

/-- A weakly well-formed state whose free ids are not pending is well-formed. -/
theorem FLState.WFw.wf {σ : FLState} (h : σ.WFw) (hd : ∀ x ∈ σ.free, x ∉ σ.pendingIds) :
    σ.WF := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨?_, h2, h3, h4, h5⟩
  unfold FLState.allIds
  exact List.nodup_append.2 ⟨h3.nodup, h1, fun a ha b hb e => hd a ha (e ▸ hb)⟩

/-- The state whose free ids are the increasing ids `xs` (at least 2) but the pending ones
(`NoSyncReload`) is well-formed, from a weakly well-formed state. -/
theorem reload_WF_w {σ : FLState} {xs : List w64} (hwf : σ.WFw) (hinc : PgidsIncr xs)
    (hge : ∀ x ∈ xs, 2 ≤ uint.Z x) (hlen : xs.length + σ.pendingCount < 2 ^ 63) :
    ({ σ with free := xs.filter (fun x => decide (x ∉ σ.pendingIds)) } : FLState).WF := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hwf
  have hfs : (xs.filter (fun x => decide (x ∉ σ.pendingIds))).Sublist xs := by
    apply List.filter_sublist
  refine ⟨?_, ?_, List.Pairwise.sublist hfs hinc, ?_, h5⟩
  · show (_ ++ σ.pendingIds).Nodup
    rw [List.nodup_append]
    refine ⟨hfs.nodup hinc.nodup, h1, fun a ha b hb e => ?_⟩
    subst e
    simp only [List.mem_filter, decide_eq_true_iff] at ha
    exact ha.2 hb
  · intro id hid
    rcases List.mem_append.1 hid with h | h
    · exact hge id (hfs.subset h)
    · exact h2 id (List.mem_append_right _ h)
  · show (_ ++ σ.pendingIds).length < _
    have := hfs.length_le
    unfold FLState.pendingCount at hlen
    rw [List.length_append]; simp only; omega

section preds
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.freelist.Assumptions]

/-- The `shared` at `s` in the weakly well-formed state `σ`, its cache up to date. -/
def ownSharedW (s : Loc) (iface : GoInterface) (σ : FLState) : IProp GF :=
  iprop(∃ (sv : shared) (c : GMap w64 Unit),
    ownSharedC s sv iface σ c ∗ ⌜cacheOK c σ ∧ σ.WFw⌝)

theorem ownShared_w (s : Loc) (iface : GoInterface) (σ : FLState) :
    ownShared (GF := GF) s iface σ ⊢ ownSharedW s iface σ := by
  unfold ownShared ownSharedW
  iintro ⟨%sv, %c, H, %Hok⟩
  iexists sv, c; iframe; ipureintro; exact ⟨Hok.1, Hok.2.wfw⟩

theorem ownSharedW_wfw (s : Loc) (iface : GoInterface) (σ : FLState) :
    ownSharedW (GF := GF) s iface σ ⊢ ownSharedW s iface σ ∗ ⌜σ.WFw⌝ := by
  unfold ownSharedW
  iintro ⟨%sv, %c, H, %Hok⟩
  isplitl
  · iexists sv, c; iframe; ipureintro; exact Hok
  · ipureintro; exact Hok.2

theorem ownSharedW_wf (s : Loc) (iface : GoInterface) (σ : FLState) (h : σ.WF) :
    ownSharedW (GF := GF) s iface σ ⊢ ownShared s iface σ := by
  unfold ownShared ownSharedW
  iintro ⟨%sv, %c, H, %Hok⟩
  iexists sv, c; iframe; ipureintro; exact ⟨Hok.1, h⟩

/-- `Init(ids)` from and to weakly well-formed states: the free ids become `ids`, the cache
rebuilt (for no ids, the old free ids must all be pending). -/
def FLImpl.InitSpecW (I : FLImpl (GF := GF)) : Prop :=
  ∀ (s : Loc) (σ : FLState) (ids : GoSlice) (xs : List w64),
    ({ σ with free := xs } : FLState).WFw → (xs ≠ [] ∨ ∀ x ∈ σ.free, x ∈ σ.pendingIds) →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.freelist ∗
        I.hdl s ∗ ownSharedW s I.iface σ ∗ I.own s σ.free ∗ ids ↦* xs ∗
        ownSliceCap w64 ids (DFrac.own 1) }}
      (App (Val #(methods I.ity go!"Init" I.iv)) (Val #ids))
    {{ RET #(); ownSharedW s I.iface { σ with free := xs } ∗ I.own s xs }}

end preds

/-- The free ids replaced by increasing ids (at least 2, not too many): still weakly
well-formed. -/
theorem FLState.WFw.with_free {σ : FLState} (h : σ.WFw) {ys : List w64} (hinc : PgidsIncr ys)
    (hge : ∀ x ∈ ys, 2 ≤ uint.Z x) (hlen : ys.length + σ.pendingCount < 2 ^ 63) :
    ({ σ with free := ys } : FLState).WFw := by
  obtain ⟨h1, h2, -, -, h5⟩ := h
  refine ⟨h1, fun id hid => ?_, hinc, ?_, h5⟩
  · rcases List.mem_append.1 hid with hx | hx
    · exact hge id hx
    · exact h2 id (List.mem_append_right _ hx)
  · show (ys ++ σ.pendingIds).length < _
    rw [List.length_append]; exact hlen

end bbolt
end EtcdGrove
end Perennial
