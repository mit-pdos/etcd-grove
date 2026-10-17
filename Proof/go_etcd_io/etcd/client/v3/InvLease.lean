/-
The lease client's lock invariant (`client/v3/lease.go`'s `lessor`, etcd#22291): the vocabulary of
`lessor.closeRequireLeader`'s spec. Lean-first (no Rocq counterpart).

* `lessor.muInv R l`: what `l.mu` protects of the lessor, its `keepAlives` map: each entry a
  `*keepAlive` whose `chs` and `ctxs` slices hold a list `subs` of subscriptions (a channel and its
  subscriber's context), in order, the two slices of one length (`closeRequireLeader` and
  `keepAliveCtxCloser` index one by the other's indices). The list is **non-empty**: every entry has
  a subscriber (what etcd#22094 found broken: `closeRequireLeader` compacting an entry to no
  subscription and leaving it in the map, whose lease is then kept alive forever). No channel is
  nil, every context is stable (`metadata.outgoingStable`: its outgoing metadata does not change,
  the premise of grpc's `FromOutgoingContext` here), and the invariant holds `R ch ctx` for each
  subscription, the right to close `ch` (the caller's protocol of the channel), for the
  subscription with context `ctx`: each channel stays paired with its own subscriber's context,
  which `closeRequireLeader`'s compaction keeps only with etcd#22087's fix (`ka.ctxs[i]`;
  etcd#22081: the pinned code copies `ka.ctxs[newIdx]`, and on `pr-verify/etcd-22291` the spec needed
  the premise `R ch c -∗ R ch c'` for it).
* `lessor.ctxRequiresLeader kl hl ctx`: whether `ctx`'s outgoing metadata (`metadata.outgoingMD`,
  the abstract result of grpc's `FromOutgoingContext` on a stable context) has, for the key `kl`
  (`rpctypes.MetadataRequireLeaderKey`), a first value `hl` (`rpctypes.MetadataHasLeader`):
  `closeRequireLeader`'s test, what `WithRequireLeader` sets.

The other fields of the lessor and of a `keepAlive` (`deadline`, `nextKeepAlive`, `donec`, the
stream) are not in the invariant yet: `closeRequireLeader` does not touch them.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvClient
public import Spec.google_golang_org.grpc.metadata.FromOutgoingContext

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section pure
variable [FfiSyntax]

/-- Whether `ctx` asks for a leader (see the file header). -/
def lessor.ctxRequiresLeader (kl hl : GoString) (ctx : GoInterface) : Bool :=
  match metadata.outgoingMD ctx with
  | none => false
  | some m =>
    match m !! kl with
    | some (v :: _) => decide (v = hl)
    | _ => false

/-- Whether a subscription's context asks for a leader: `closeRequireLeader` closes its channel. -/
abbrev lessor.rlSub (kl hl : GoString) (p : GoChan × GoInterface) : Bool :=
  lessor.ctxRequiresLeader kl hl p.2

end pure

section lists

theorem lessor.take_map_append_drop_set {α β : Type} (f g : α → β) (l : List α) (n : Nat)
    (h : n < l.length) :
    ((l.take n).map f ++ (l.drop n).map g).set n (f l[n]) =
      (l.take (n + 1)).map f ++ (l.drop (n + 1)).map g := by
  have hl : ((l.take n).map f).length = n := by rw [List.length_map, List.length_take]; omega
  rw [List.drop_eq_getElem_cons h, List.take_add_one, List.getElem?_eq_getElem h]
  simp only [List.map_cons, List.map_append, Option.toList_some, List.map_cons, List.map_nil]
  rw [List.set_append_right _ _ (by omega), hl, Nat.sub_self, List.set_cons_zero,
    List.append_assoc, List.singleton_append]

theorem lessor.take_map_append_drop_same {α β : Type} (f g : α → β) (l : List α) (n : Nat)
    (h : n < l.length) (hfg : f l[n] = g l[n]) :
    (l.take n).map f ++ (l.drop n).map g = (l.take (n + 1)).map f ++ (l.drop (n + 1)).map g := by
  rw [List.drop_eq_getElem_cons h, List.take_add_one, List.getElem?_eq_getElem h]
  simp only [List.map_cons, List.map_append, Option.toList_some, List.map_cons, List.map_nil,
    List.append_assoc, List.singleton_append, hfg]

theorem lessor.take_map_append_drop_get {α β : Type} (f g : α → β) (l : List α) (n : Nat)
    (h : n < l.length) :
    ((l.take n).map f ++ (l.drop n).map g)[n]? = some (g l[n]) := by
  have hl : ((l.take n).map f).length = n := by rw [List.length_map, List.length_take]; omega
  rw [List.drop_eq_getElem_cons h, List.getElem?_append_right (by omega), hl, Nat.sub_self]
  rfl

theorem lessor.filter_take_succ {α : Type} (p : α → Bool) (l : List α) (n : Nat)
    (h : n < l.length) :
    (l.take (n + 1)).filter p = (l.take n).filter p ++ (if p l[n] then [l[n]] else []) := by
  rw [List.take_add_one, List.getElem?_eq_getElem h]
  simp only [Option.toList_some, List.filter_append]
  cases hp : p l[n] <;> simp [List.filter, hp]

/-- The marking loop's step at a kept subscription (its context does not ask for a leader). -/
theorem lessor.mark_step_keep {α β : Type} (q : α → Bool) (fst : α → β) (nil : β) (l : List α) (n : Nat)
    (h : n < l.length) (hq : q l[n] = false) :
    (l.take (n + 1)).filter (fun p => !q p) ++ l.drop (n + 1) =
        (l.take n).filter (fun p => !q p) ++ l.drop n ∧
      (l.take (n + 1)).map (fun p => if q p then nil else fst p) ++ (l.drop (n + 1)).map fst =
        (l.take n).map (fun p => if q p then nil else fst p) ++ (l.drop n).map fst ∧
      ((l.take (n + 1)).filter q).length = ((l.take n).filter q).length := by
  refine ⟨?_, ?_, ?_⟩
  · rw [lessor.filter_take_succ _ _ _ h, List.drop_eq_getElem_cons h]
    simp [hq]
  · exact (lessor.take_map_append_drop_same _ _ _ _ h (by simp [hq])).symm
  · rw [lessor.filter_take_succ _ _ _ h]; simp [hq]

/-- The marking loop's step at a closed subscription. -/
theorem lessor.mark_step_close {α β : Type} (q : α → Bool) (fst : α → β) (nil : β) (l : List α) (n : Nat)
    (h : n < l.length) (hq : q l[n] = true) :
    (l.take n).filter (fun p => !q p) ++ l.drop n =
        (l.take (n + 1)).filter (fun p => !q p) ++ l[n] :: l.drop (n + 1) ∧
      ((l.take n).map (fun p => if q p then nil else fst p) ++ (l.drop n).map fst).set n nil =
        (l.take (n + 1)).map (fun p => if q p then nil else fst p) ++ (l.drop (n + 1)).map fst ∧
      ((l.take (n + 1)).filter q).length = ((l.take n).filter q).length + 1 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [lessor.filter_take_succ _ _ _ h, List.drop_eq_getElem_cons h]
    simp [hq]
  · have := lessor.take_map_append_drop_set (fun p => if q p then nil else fst p) fst l n h
    simp only [hq, ite_true] at this
    exact this
  · rw [lessor.filter_take_succ _ _ _ h]; simp [hq]

/-- The marked list at the end of the loop. -/
theorem lessor.mark_done {α β : Type} (q : α → Bool) (fst : α → β) (nil : β) (l : List α) (n : Nat)
    (h : l.length ≤ n) :
    (l.take n).map (fun p => if q p then nil else fst p) ++ (l.drop n).map fst =
      l.map (fun p => if q p then nil else fst p) ∧
    (l.take n).filter (fun p => !q p) ++ l.drop n = l.filter (fun p => !q p) ∧
    (l.take n).filter q = l.filter q := by
  simp [List.take_of_length_le h, List.drop_of_length_le h]

theorem lessor.filter_count {α : Type} (q : α → Bool) (l : List α) :
    (l.filter (fun p => !q p)).length + (l.filter q).length = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih => cases hq : q a <;> simp [List.filter, hq] <;> omega

theorem lessor.mark_none {α β : Type} (q : α → Bool) (fst : α → β) (nil : β) (l : List α)
    (h : (l.filter q).length = 0) :
    l.map (fun p => if q p then nil else fst p) = l.map fst ∧ l.filter (fun p => !q p) = l := by
  have h' : ∀ p ∈ l, q p = false := by
    intro p hp
    cases hq : q p
    · rfl
    · exact absurd (List.length_pos_of_mem (List.mem_filter.2 ⟨hp, hq⟩)) (by omega)
  refine ⟨List.map_congr_left (fun p hp => by simp [h' p hp]), ?_⟩
  exact List.filter_eq_self.2 (fun p hp => by simp [h' p hp])

/-- The compaction loop's step. -/
theorem lessor.compact_step {α : Type} (q : α → Bool) (l : List α) (n : Nat) (h : n < l.length) :
    (l.take (n + 1)).filter (fun p => !q p) =
      (l.take n).filter (fun p => !q p) ++ (if q l[n] then [] else [l[n]]) := by
  rw [lessor.filter_take_succ _ _ _ h]; cases hq : q l[n] <;> simp [hq]

theorem lessor.set_append_replicate {α : Type} (A : List α) (x z : α) (r : Nat) (h : 0 < r) :
    (A ++ List.replicate r z).set A.length x = (A ++ [x]) ++ List.replicate (r - 1) z := by
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  simp [List.replicate_succ]

theorem lessor.length_filter_take_le {α : Type} (p : α → Bool) (l : List α) (n : Nat) :
    ((l.take n).filter p).length ≤ (l.filter p).length := by
  have := congrArg (fun l => (l.filter p).length) (List.take_append_drop n l)
  simp only [List.filter_append, List.length_append] at this
  omega

theorem lessor.length_filter_take_le_n {α : Type} (p : α → Bool) (l : List α) (n : Nat) :
    ((l.take n).filter p).length ≤ n := by
  have := List.length_filter_le p (l.take n)
  simp at this; omega

theorem lessor.compact_chs {α β : Type} (A : List (α × β)) (p : α × β) (z : α) (r : Nat) (h : 0 < r) :
    (A.map Prod.fst ++ List.replicate r z).set A.length p.1 =
      (A ++ [p]).map Prod.fst ++ List.replicate (r - 1) z := by
  have := lessor.set_append_replicate (A.map Prod.fst) p.1 z r h
  rw [List.length_map] at this
  rw [this, List.map_append]; rfl

theorem lessor.compact_snd {α β : Type} (A : List (α × β)) (p : α × β) (z : β) (r : Nat) (h : 0 < r) :
    (A.map Prod.snd ++ List.replicate r z).set A.length p.2 =
      (A ++ [p]).map Prod.snd ++ List.replicate (r - 1) z := by
  have := lessor.set_append_replicate (A.map Prod.snd) p.2 z r h
  rw [List.length_map] at this
  rw [this, List.map_append]; rfl

end lists

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- The `*keepAlive` `ka`'s subscriptions (see the file header). -/
def lessor.kaOwn (R : GoChan → GoInterface → IProp GF) (ka : Loc) : IProp GF :=
  iprop(∃ (chsSl ctxsSl : GoSlice) (subs : List (GoChan × GoInterface)),
    structFieldRef go_etcd_io.etcd.client.v3.keepAlive go!"chs" ka ↦ chsSl ∗
    structFieldRef go_etcd_io.etcd.client.v3.keepAlive go!"ctxs" ka ↦ ctxsSl ∗
    chsSl ↦* subs.map Prod.fst ∗ ownSliceCap GoChan chsSl (DFrac.own 1) ∗
    ctxsSl ↦* subs.map Prod.snd ∗ ownSliceCap GoInterface ctxsSl (DFrac.own 1) ∗
    ⌜subs ≠ [] ∧ (∀ p ∈ subs, p.1 ≠ chan.nil) ∧ ∀ p ∈ subs, metadata.outgoingStable p.2⌝ ∗
    [∗list] p ∈ subs, R p.1 p.2)

/-- **The lessor's lock invariant** (see the file header). -/
def lessor.muInv (R : GoChan → GoInterface → IProp GF) (l : Loc) : IProp GF :=
  iprop(∃ (mp : GoMap) (m : GMap w64 Loc),
    structFieldRef go_etcd_io.etcd.client.v3.lessor go!"keepAlives" l ↦ mp ∗ mp ↦$ m ∗
    [∗map] _k ↦ ka ∈ m, lessor.kaOwn R ka)

/-- The keep-alive channels' element type, `chan<- *LeaseKeepAliveResponse`. -/
abbrev lessor.kaChanTy : go.GoType :=
  go.GoType.ChannelType go.ChanDir.sendonly
    (go.GoType.PointerType go_etcd_io.etcd.client.v3.LeaseKeepAliveResponse.ty)

/-- **The right to close a subscription's channel** (persistent): with `R ch c`, `close(ch)`
succeeds (no panic: the channel is not closed yet), for a subscription whose context `c` asks for a
leader. What the channels' protocol gives `closeRequireLeader`. -/
def lessor.closeOk (R : GoChan → GoInterface → IProp GF) (kl hl : GoString) : IProp GF :=
  iprop(□ ∀ (ch : GoChan) (c : GoInterface), ⌜lessor.ctxRequiresLeader kl hl c = true⌝ -∗
    {{ R ch c }} (App (Val #(functions go.close [lessor.kaChanTy])) (Val #ch))
    {{ RET #(); True }})

instance lessor.closeOk_persistent (R : GoChan → GoInterface → IProp GF) (kl hl : GoString) :
    Persistent (lessor.closeOk R kl hl) := by
  unfold lessor.closeOk; infer_instance

end defs

end EtcdGrove
end Perennial
