/-
Proof of `Spec/go_etcd_io/etcd/client/v3/concurrency/Election__Observe.lean`. Lean-first (no Rocq
counterpart).

`Observe` makes an unbuffered channel, an SPSC channel of `observeElem`s (`start_spsc`) with the
revisions' monotone list started at `[lo]`, forks `observe` with the producer's half and the list's
authority, and returns the consumer's half and the list's first index.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.concurrency.Election__Observe
public import Spec.go_etcd_io.etcd.client.v3.concurrency.Election__observe

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace concurrency

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.concurrency go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.concurrency.Assumptions]

theorem Election.Observe.wp_proof (wp_observe : Election.observe.spec (GF := GF) (hG := hG)) :
    Election.Observe.spec (GF := GF) (hG := hG) := by
  intro e s γs client id pfx ctx cs lo
  wp_start as ⟨#He, #Hctx, #Hcc, #Hlo, %Hlo0⟩
  wp_auto
  wp_apply chan.wp_make1 (V := Loc) as %ch %γch ⟨#Hch, %_, Hoc⟩
  imod mono_list_own_alloc (GF := GF) [lo] with ⟨%γr, Hauth, #Hlb⟩
  imod start_spsc (V := Loc) ch
    (fun i v => observeElem (GF := GF) ⟨⟨γch, γch.1, γch.1⟩, γr⟩ pfx i v) (fun _ => iprop(True))
    γch $$ Hch [Hoc] with ⟨%γsp, #Hsp, Hprod, Hcons⟩
  · ileft; iexact Hoc
  have hP : observeElem (GF := GF) ⟨γsp, γr⟩ pfx =
      fun i v => observeElem (GF := GF) ⟨⟨γch, γch.1, γch.1⟩, γr⟩ pfx i v := rfl
  wp_apply wp_fork $$ [Hprod Hauth]
  · wp_apply wp_observe e s γs client id pfx ctx cs ch ⟨γsp, γr⟩ [] [lo] lo
      $$ [$Hpkg $He $Hctx $Hcc $Hprod $Hauth $Hlo]
    · isplitl
      · unfold isObserveChan; dsimp only; rw [hP]; iexact Hsp
      ipureintro; exact ⟨⟨rfl, rfl⟩, Hlo0⟩
    itrivial
  iapply HΦ
  iexists ⟨γsp, γr⟩
  iframe Hcons
  isplitl
  · unfold isObserveChan; dsimp only; rw [hP]; iexact Hsp
  iapply monoListIdxOwn_get 0 lo rfl $$ Hlb

end proof

end concurrency
end EtcdGrove
end Perennial
