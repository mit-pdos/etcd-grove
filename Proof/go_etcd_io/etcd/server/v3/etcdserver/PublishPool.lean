/-
The snapshot check's reader-slot pool (`InvPublish.lean`, `pubPoolInv`): set up, drawn from with a
thread token, given back (etcd-io/etcd#22525). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvStart

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **The pool, set up** with `K` slots. -/
theorem pub_pool_alloc (n : Loc) (K : Nat) :
    ([∗list] _x ∈ List.replicate K (), notifyReader (GF := GF) n) ⊢
      |={⊤}=> ∃ γ : GName, inv pubPoolN (pubPoolInv n γ K) := by
  iintro Hs
  imod ownTokAuth_alloc (GF := GF) with ⟨%γ, Hauth⟩
  imod inv_alloc pubPoolN ⊤ (pubPoolInv n γ K) $$ [Hs Hauth] with #Hinv
  · inext
    iunfold pubPoolInv
    iexists 0
    iframe Hauth
    isplitr
    · ipureintro; omega
    isplitr
    · iapply threadToks_zero
    rw [Nat.sub_zero]; iexact Hs
  imodintro
  iexists γ
  iexact Hinv

/-- **A goroutine draws a slot** with its thread token (fewer live threads than slots), getting a
receipt. -/
theorem pub_pool_take (n : Loc) (γ : GName) (K : Nat) (hK : threadBound GF ≤ K) :
    inv pubPoolN (pubPoolInv (GF := GF) n γ K) ∗ threadTok ∗ £ 1 ⊢
      |={⊤}=> notifyReader n ∗ ownToks γ 1 := by
  iintro ⟨#Hinv, Htok, Hlc⟩
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later $$ Hlc Hi with Hi
  iunfold pubPoolInv at Hi
  icases Hi with ⟨%k, %Hk, Hks, Hauth, Hs⟩
  icases threadToks_add_one_lt k $$ [$Htok $Hks] with ⟨%Hlt, Hks⟩
  icases replicate_take1 _ (K - k) (by omega) $$ Hs with ⟨Hr, Hs⟩
  imod ownTokAuth_S γ k $$ Hauth with ⟨Hauth, Hrc⟩
  imod Hclose $$ [Hks Hauth Hs] with -
  · inext
    iunfold pubPoolInv
    iexists k + 1
    iframe Hks Hauth
    isplitr
    · ipureintro; omega
    rw [show K - (k + 1) = K - k - 1 by omega]
    iexact Hs
  imodintro
  iframe Hr Hrc

/-- **A goroutine gives its slot back** with its receipt, getting its thread token. -/
theorem pub_pool_give (n : Loc) (γ : GName) (K : Nat) :
    inv pubPoolN (pubPoolInv (GF := GF) n γ K) ∗ notifyReader n ∗ ownToks γ 1 ∗ £ 1 ⊢
      |={⊤}=> threadTok := by
  iintro ⟨#Hinv, Hr, Hrc, Hlc⟩
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later $$ Hlc Hi with Hi
  iunfold pubPoolInv at Hi
  icases Hi with ⟨%k, %Hk, Hks, Hauth, Hs⟩
  icombine Hauth Hrc gives %Hle
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  icases (threadToks_add k' 1).1 $$ Hks with ⟨Hks, Htok⟩
  imod ownTokAuth_delete_S γ k' $$ Hauth Hrc with Hauth
  imod Hclose $$ [Hks Hauth Hs Hr] with -
  · inext
    iunfold pubPoolInv
    iexists k'
    iframe Hks Hauth
    isplitr
    · ipureintro; omega
    rw [show K - k' = (K - (k' + 1)) + 1 by omega, List.replicate_succ]
    iapply BigSepL.bigSepL_cons.2
    iframe Hr Hs
  imodintro
  iexact Htok

end lemmas

end EtcdGrove
end Perennial
