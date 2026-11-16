module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.consume
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.toWEvent
public import Perennial.Spec.time.NewTimer
public import Perennial.Spec.time.After
public import Perennial.Spec.time.Timer__Stop
public import Perennial.Golang.Theory.Chan.Idioms.Bag
public import Perennial.Golang.Theory.Chan.Idioms.Spsc

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode k8s
open k8s_io.apimachinery.pkg.watch (Event)
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input WEvent)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- A `select` on two time channels (`case <-timer.C`, `case <-time.After(d)`). -/
theorem wp_select_bag_bag (c1 : Loc) (γ1 : ChanNames) (c2 : Loc) (γ2 : ChanNames)
    (h1 h2 : Expr) (Φ : val → IProp GF) :
    ⊢ isChanBag (V := time.Time) γ1 c1 (fun _ => iprop(True)) -∗
      isChanBag (V := time.Time) γ2 c2 (fun _ => iprop(True)) -∗ £ 1 ∗ £ 1 -∗
      ((∀ t : time.Time, WP (App h1 (Val (PairV #t #true))) {{ Φ }}) ∧
        (∀ t : time.Time, WP (App h2 (Val (PairV #t #true))) {{ Φ }})) -∗
      WP (App (Val (GoInstruction SelectStmt)) (Val (SelectStmtClausesV none
        [CommClause (RecvCase time.Time.ty (Val #c1)) h1,
         CommClause (RecvCase time.Time.ty (Val #c2)) h2]))) {{ Φ }} := by
  iintro #Hb1 #Hb2 Hlc Hh
  iapply chan.wp_select_blocking
  iapply BigAndL.bigAndL_cons.2
  isplit
  · simp only [chan.blockingClausePre]
    iexists time.Time, inferInstance, inferInstance, inferInstance, inferInstance, c1, γ1
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply is_bag_is_chan $$ Hb1
    iapply bag_recv_au $$ Hlc Hb1
    inext
    iintro %t -
    icases Hh with ⟨Hh, -⟩
    iapply Hh
  iapply BigAndL.bigAndL_cons.2
  isplit
  · simp only [chan.blockingClausePre]
    iexists time.Time, inferInstance, inferInstance, inferInstance, inferInstance, c2, γ2
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply is_bag_is_chan $$ Hb2
    iapply bag_recv_au $$ Hlc Hb2
    inext
    iintro %t -
    icases Hh with ⟨-, Hh⟩
    iapply Hh
  · iapply BigAndL.bigAndL_nil.2
    itrivial

/-- A `select` on a time channel and an SPSC channel of watch events, of which the caller is the
consumer (`case <-timer.C`, `case ev, open := <-w.ResultChan()`). -/
theorem wp_select_bag_spsc (c1 : Loc) (γ1 : ChanNames) (γs : SpscNames) (ch : Loc)
    (P : Int → Event → IProp GF) (R : List Event → IProp GF) (recv : List Event)
    (h1 h2 : Expr) (Φ : val → IProp GF) :
    ⊢ isChanBag (V := time.Time) γ1 c1 (fun _ => iprop(True)) -∗ isSpsc γs ch P R -∗
      £ 1 ∗ £ 1 -∗ spscConsumer γs recv -∗
      ((spscConsumer γs recv -∗ ∀ t : time.Time, WP (App h1 (Val (PairV #t #true))) {{ Φ }}) ∧
        (∀ (v : Event) (ok : Bool),
          (if ok then iprop(P recv.length v ∗ spscConsumer γs (recv ++ [v]))
           else iprop(R recv ∗ ⌜v = zero_val Event⌝)) -∗
          WP (App h2 (Val (PairV #v #ok))) {{ Φ }})) -∗
      WP (App (Val (GoInstruction SelectStmt)) (Val (SelectStmtClausesV none
        [CommClause (RecvCase time.Time.ty (Val #c1)) h1,
         CommClause (RecvCase k8s_io.apimachinery.pkg.watch.Event.ty (Val #ch)) h2]))) {{ Φ }} := by
  iintro #Hb1 #Hs ⟨Hlc1, Hlc2⟩ Hc Hh
  iapply chan.wp_select_blocking
  iapply BigAndL.bigAndL_cons.2
  isplit
  · simp only [chan.blockingClausePre]
    iexists time.Time, inferInstance, inferInstance, inferInstance, inferInstance, c1, γ1
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply is_bag_is_chan $$ Hb1
    iapply bag_recv_au $$ [$Hlc1 $Hlc2] Hb1
    inext
    iintro %t -
    icases Hh with ⟨Hh, -⟩
    iapply Hh $$ Hc
  iapply BigAndL.bigAndL_cons.2
  isplit
  · simp only [chan.blockingClausePre]
    iexists Event, inferInstance, inferInstance, inferInstance, inferInstance, ch, γs.chanName
    isplitr
    · ipureintro; rfl
    isplitr
    · iunfold isSpsc at Hs
      icases Hs with ⟨#Hch, -⟩
      iexact Hch
    iapply spsc_rcv_au γs ch _ _ recv _ $$ Hs [$Hlc1 $Hlc2] Hc
    inext
    iintro %v %ok Hv
    icases Hh with ⟨-, Hh⟩
    iapply Hh $$ Hv
  · iapply BigAndL.bigAndL_nil.2
    itrivial
end proof

end k8s_etcd3
end EtcdGrove
end Perennial
