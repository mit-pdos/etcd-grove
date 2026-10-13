/-
The lessor's queues as `container/heap`'s interface (2026-10-13, unit 9). Lean-first (no Rocq
counterpart).

`&q` (a `*LeaseQueue`) is a `heap.Interface` over `queueHeap qf` (the queue at `qf`, its items
each at its index): its `Len`, `Less`, `Swap` (the value methods, through the pointer) and
`Push` meet `heap.heapIface` (`queue_heapIface`), the elements `Push` takes an item the caller
owns (`queueElem`).
-/
module

public import Proof.container.heap.Defs
public import Spec.go_etcd_io.etcd.server.v3.lease.LeaseQueue__Len
public import Spec.go_etcd_io.etcd.server.v3.lease.LeaseQueue__Less
public import Spec.go_etcd_io.etcd.server.v3.lease.LeaseQueue__Swap
public import Spec.go_etcd_io.etcd.server.v3.lease.LeaseQueue__Push
public import Proof.go_etcd_io.etcd.server.v3.lease.LessorLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace lease

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.lease

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

/-- The queue at `qf` (a `LeaseQueue` variable or field) holds the items `xs`. -/
def queueHeap (qf : Loc) (xs : List (Loc × w64)) : IProp GF :=
  iprop(∃ s : GoSlice, qf ↦ s ∗ queueAt s xs 1)

/-- What `Push(x)` takes: `x` an `*LeaseWithTime` item `p` of id `id` the caller owns. -/
def queueElem (x : GoInterface) (a : Loc × w64) : IProp GF :=
  iprop(⌜x = interface.mkOk (go.GoType.PointerType LeaseWithTime.ty) #a.1⌝ ∗
    ∃ k : w64, lwtAt a.1 a.2 k 1)

/-- **`&q` is a `heap.Interface`** over `queueHeap qf`. -/
theorem queue_heapIface
    (hLen : lease.LeaseQueue.Len.spec (GF := GF) (hG := hG))
    (hLess : lease.LeaseQueue.Less.spec (GF := GF) (hG := hG))
    (hSwap : lease.LeaseQueue.Swap.spec (GF := GF) (hG := hG))
    (hPush : lease.LeaseQueue.Push.spec (GF := GF) (hG := hG))
    (qf : Loc) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.lease ⊢
      heap.heapIface (interface.mk (go.GoType.PointerType LeaseQueue.ty) #qf) (queueHeap qf)
        queueElem := by
  iintro #Hpkg
  iunfold heap.heapIface
  isplitr
  · iintro !> %xs
    wp_start as Hq
    iunfold queueHeap at Hq
    icases Hq with ⟨%s, Hqf, Hq⟩
    ihave %Hlen : ⌜(xs.length : Int) = sint.Z s.len⌝ $$ [Hq]
    · iunfold queueAt at Hq
      icases Hq with ⟨Hs, -, -⟩
      ihave %H := ownSlice_len s _ _ $$ Hs
      ipureintro; simp only [List.length_map] at H; word
    wp_auto
    wp_apply hLen
    iapply HΦ
    isplitl
    · iunfold queueHeap; iexists s; iframe
    ipureintro; omega
  isplitr
  · iintro !> %xs %i %j
    wp_start as ⟨Hq, %Hb⟩
    iunfold queueHeap at Hq
    icases Hq with ⟨%s, Hqf, Hq⟩
    wp_auto
    wp_apply (hLess s xs 1 i j Hb.1 Hb.2.1 Hb.2.2.1 Hb.2.2.2) $$ [$Hq] as %b Hq
    iapply HΦ
    iunfold queueHeap; iexists s; iframe
  isplitr
  · iintro !> %xs %i %j
    wp_start as ⟨Hq, %Hb⟩
    iunfold queueHeap at Hq
    icases Hq with ⟨%s, Hqf, Hq⟩
    wp_auto
    wp_apply (hSwap s xs i j Hb.1 Hb.2.1 Hb.2.2.1 Hb.2.2.2) $$ [$Hq] as Hq
    iapply HΦ
    iunfold queueHeap; iexists s; iframe
  · iintro !> %xs %x %a %Φ !> ⟨Hq, He⟩ HΦ
    iunfold queueHeap at Hq
    icases Hq with ⟨%s, Hqf, Hq⟩
    iunfold queueElem at He
    icases He with ⟨%Hx, %k, Hit⟩
    subst Hx
    wp_apply (hPush qf s xs a.1 a.2 k) $$ [$Hqf $Hq $Hit] as ⟨%s', Hqf, Hq⟩
    iapply HΦ
    iunfold queueHeap; iexists s'; iframe

/-- An item whose `index` the caller owns is not in a queue. -/
theorem queue_item_fresh (xs : List (Loc × w64)) (p : Loc) (k : w64) :
    ([∗list] n ↦ x ∈ xs, lwtAt (GF := GF) x.1 x.2 (W64 n) 1) ∗ lwF go!"index" p ↦ k ⊢
      ([∗list] n ↦ x ∈ xs, lwtAt (GF := GF) x.1 x.2 (W64 n) 1) ∗ lwF go!"index" p ↦ k ∗
        ⌜p ∉ xs.map Prod.fst⌝ := by
  iintro ⟨Hits, Hix⟩
  by_cases h : p ∈ xs.map Prod.fst
  · obtain ⟨x, hx, hxp⟩ := List.mem_map.mp h
    obtain ⟨n, hn, hxn⟩ := List.mem_iff_getElem.mp hx
    have hl : xs[n]? = some x := by rw [List.getElem?_eq_getElem hn, hxn]
    icases (BigSepL.bigSepL_lookup_acc hl).1 $$ Hits with ⟨Hx, -⟩
    iunfold lwtAt at Hx
    icases Hx with ⟨-, -, Hxi⟩
    subst hxp
    iexfalso
    iapply w64Field_excl $$ [$Hxi $Hix]
  · iframe
    ipureintro; exact h

end lemmas

end lease
end EtcdGrove
end Perennial
