/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Proof/queue/Queue.lean (lab master 915f964; notes/dsv-vr.md):
over any `GF`, on the net extension.
-/
/-
The proofs of `pkg/queue`: `New`, `(*Queue[T]).Push`, `(*Queue[T]).Pop`.
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.queue

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.tangledbytes.go_vsr.pkg

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

attribute [local instance] GooseGlobalGS.gooseInvGS

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : queue.Assumptions]

theorem queue.isQueue_unseal {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V]
    (T : go.GoType) [IntoValTyped (GF := GF) V T] (q : Loc) (P : V → IProp GF) :
    queue.isQueue T q P = queue.isQueueDef q P := by
  with_unfolding_all rfl

theorem queue.headOf_snoc {V : Type} (ns : List (Loc × V)) (n : Loc × V) (nxt : Loc) :
    queue.headOf (ns ++ [n]) nxt = queue.headOf ns n.1 := by
  cases ns <;> rfl

theorem queue.lastOf_snoc {V : Type} (ns : List (Loc × V)) (n : Loc × V) :
    queue.lastOf (ns ++ [n]) = n.1 := by
  simp [queue.lastOf]

theorem queue.lastOf_cons {V : Type} (m : Loc × V) (ns : List (Loc × V)) (h : ns ≠ []) :
    queue.lastOf (m :: ns) = queue.lastOf ns := by
  cases ns with
  | nil => contradiction
  | cons n ns => simp [queue.lastOf, List.getLast?_cons_cons]

theorem queue.headOf_null {V : Type} (ns : List (Loc × V)) (h : ∀ x ∈ ns, x.1 ≠ null) :
    queue.headOf ns null = null ↔ ns = [] := by
  cases ns with
  | nil => simp [queue.headOf]
  | cons n ns => simp only [queue.headOf, reduceCtorEq, iff_false]; exact h n (by simp)

theorem queue.nodesOwn_snoc_split {V : Type} [TypedPointsto (GF := GF) V]
    (P : V → IProp GF) (ns : List (Loc × V)) (n : Loc × V) (nxt : Loc) :
    queue.nodesOwn P (ns ++ [n]) nxt ⊢
      queue.nodesOwn P ns n.1 ∗ n.1 ↦ (queue.node.mk n.2 nxt : queue.node V) ∗ P n.2 := by
  induction ns with
  | nil =>
    simp only [List.nil_append, queue.nodesOwn, queue.headOf]
    iintro ⟨H1, H2, -⟩
    iframe
  | cons m ns ih =>
    simp only [List.cons_append, queue.nodesOwn, queue.headOf_snoc]
    iintro ⟨H1, H2, H3⟩
    iframe
    iapply ih
    iexact H3

theorem queue.nodesOwn_snoc_join {V : Type} [TypedPointsto (GF := GF) V]
    (P : V → IProp GF) (ns : List (Loc × V)) (n : Loc × V) (nxt : Loc) :
    queue.nodesOwn P ns n.1 ∗ n.1 ↦ (queue.node.mk n.2 nxt : queue.node V) ∗ P n.2 ⊢
      queue.nodesOwn P (ns ++ [n]) nxt := by
  induction ns with
  | nil =>
    simp only [List.nil_append, queue.nodesOwn, queue.headOf]
    iintro ⟨-, H1, H2⟩
    iframe
  | cons m ns ih =>
    simp only [List.cons_append, queue.nodesOwn, queue.headOf_snoc]
    iintro ⟨⟨H1, H2, H3⟩, H4, H5⟩
    iframe
    iapply ih
    iframe

theorem queue.New.wp_proof : queue.New.spec (GF := GF) (hG := hG) := fun {V} hz hp T hi P => by
  wp_start
  iapply wp_fupd
  wp_auto
  iStructNamed «$r0»
  imod sync.init_Mutex (queue.lockInv «$r0_ptr» P) ⊤ «$v0_ptr» $$ «$v0» [head tail len] with #Hlock
  · inext
    unfold queue.lockInv
    iexists [], W64 0
    simp only [queue.headOf, queue.lastOf, queue.nodesOwn, List.getLast?_nil]
    iframe
    ipureintro; simp
  ipersist mu
  iapply HΦ
  rw [queue.isQueue_unseal]
  unfold queue.isQueueDef
  iexists «$v0_ptr»
  iframe #

theorem queue.Queue.Push.wp_proof : queue.Queue.Push.spec (GF := GF) (hG := hG) := fun {V} hz hp T hi P q v => by
  wp_start as ⟨#Hq, HP⟩
  rw [queue.isQueue_unseal]
  iNamed Hq
  wp_apply wp_with_defer as %defer Hdefer
  wp_apply sync.Mutex.wp_Lock $$ [$Hlock] as ⟨Hlocked, Hinv⟩
  iNamed Hinv
  wp_auto
  ihave %Hr0nn := typedPointsto_not_null $$ «$r0»
  rw [show (Perennial.zero_val (queue.node V)).next' = null from rfl]
  wp_if_destruct
  · rw [queue.headOf_null ns Hnn] at Hif
    subst Hif
    wp_apply sync.Mutex.wp_Unlock $$ [$Hlock $Hlocked head tail len «$r0» HP]
    · inext
      unfold queue.lockInv
      iexists [(«$r0_ptr», v)], n + W64 1
      simp only [named, queue.headOf, queue.lastOf, queue.nodesOwn, List.getLast?_singleton]
      iframe
      ipureintro; simpa using Hr0nn
    wp_end
  · have hne : ns ≠ [] := fun h => Hif ((queue.headOf_null ns Hnn).2 h)
    obtain ⟨init, t, rfl⟩ := (List.eq_nil_or_concat ns).resolve_left hne
    simp only [List.concat_eq_append] at Hnn Hif hne ⊢
    rw [queue.lastOf_snoc]
    icases queue.nodesOwn_snoc_split P init t null $$ Hns with ⟨Hns, Ht, HPt⟩
    wp_auto
    ihave Hns := queue.nodesOwn_snoc_join P init t «$r0_ptr» $$ [$Hns $Ht $HPt]
    ihave Hns := queue.nodesOwn_snoc_join P (init ++ [t]) («$r0_ptr», v) null $$ [$Hns $«$r0» $HP]
    wp_apply sync.Mutex.wp_Unlock $$ [$Hlock $Hlocked head tail len Hns]
    · inext
      unfold queue.lockInv
      iexists init ++ [t] ++ [(«$r0_ptr», v)], n + W64 1
      simp only [named, queue.lastOf_snoc]
      rw [show queue.headOf (init ++ [t] ++ [(«$r0_ptr», v)]) null = queue.headOf (init ++ [t]) null by
        simp only [queue.headOf_snoc]]
      iframe
      ipureintro
      intro x hx
      simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with (hx | hx) | rfl
      · exact Hnn x (by simp [hx])
      · exact Hnn x (by simp [hx])
      · exact Hr0nn
    wp_end

theorem queue.Queue.Pop.wp_proof : queue.Queue.Pop.spec (GF := GF) (hG := hG) := fun {V} hz hp T hi P q => by
  wp_start as #Hq
  rw [queue.isQueue_unseal]
  iNamed Hq
  wp_auto
  wp_apply wp_with_defer as %defer Hdefer
  wp_apply sync.Mutex.wp_Lock $$ [$Hlock] as ⟨Hlocked, Hinv⟩
  iNamed Hinv
  wp_auto
  wp_if_destruct
  · rw [queue.headOf_null ns Hnn] at Hif
    subst Hif
    wp_apply sync.Mutex.wp_Unlock $$ [$Hlock $Hlocked head tail len Hns]
    · inext
      unfold queue.lockInv
      iexists [], n
      simp only [named]
      iframe
      ipureintro; simp
    wp_end
    simp only [Bool.false_eq_true, ↓reduceIte]
    itrivial
  · cases ns with
    | nil => exact absurd rfl Hif
    | cons h rest =>
    rw [show queue.headOf (h :: rest) null = h.1 from rfl]
    simp only [queue.nodesOwn]
    icases Hns with ⟨Hh, HPh, Hns⟩
    wp_auto
    have Hnn' : ∀ x ∈ rest, x.1 ≠ null := fun x hx => Hnn x (by simp [hx])
    wp_if_destruct
    · rw [queue.headOf_null rest Hnn'] at Hif
      subst Hif
      wp_apply sync.Mutex.wp_Unlock $$ [$Hlock $Hlocked head tail len Hns]
      · inext
        unfold queue.lockInv
        iexists [], n - W64 1
        simp only [named, queue.headOf, queue.lastOf, List.getLast?_nil]
        iframe
        ipureintro; simp
      wp_end
      simp only [↓reduceIte]
      iexact HPh
    · have hne : rest ≠ [] := fun h' => Hif ((queue.headOf_null rest Hnn').2 h')
      rw [queue.lastOf_cons h rest hne]
      wp_apply sync.Mutex.wp_Unlock $$ [$Hlock $Hlocked head tail len Hns]
      · inext
        unfold queue.lockInv
        iexists rest, n - W64 1
        simp only [named]
        iframe
        ipureintro; exact Hnn'
      wp_end
      simp only [↓reduceIte]
      iexact HPh

end proofs

end Perennial.github_com.tangledbytes.go_vsr.pkg
