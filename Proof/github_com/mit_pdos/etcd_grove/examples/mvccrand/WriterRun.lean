/-
The writer's loop (`writer.run`, `examples/mvccrand/mvccrand.go`): the ticks channel's protocol
and the loop's state. Lean-first (no Rocq counterpart).

- **The ticks** (`w.ticks`, a buffered `chan int64`): the writer is its only sender (`w.ticks <-
  w.cur()`, then `close`), the registering goroutine its only receiver (`for pub := range ticks`),
  so it is Perennial's single-producer single-consumer channel (`isSpsc`,
  `Perennial/Golang/Theory/Chan/Idioms/Spsc.lean`) with the per-value predicate `tickP`: every
  value sent is a published revision (`monoNatLbOwn γ.pub`, a lower bound of `h.published`), and
  positive (`register`'s `intn(pub+1)`); nothing at the close (`R := True`). The writer's end is
  `ticksW` (the channel and its producer's history).
- **Between operations** (`runSt`): the writer at some state, its lessor's resources, the hook's
  counters at the index `i` last applied (`hookPre wv i s`), its `vals`, with the bounds the next
  operations need (`vals ≤ nv`, `nextID ≤ nid`, at least `k` write tokens left).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccrand.WriterLease
public import Perennial.Golang.Theory.Chan.Idioms.Spsc

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccrand

open Iris Iris.BI Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.mvccrand mvcc mvcc.api

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccrand.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **A tick** (persistent): a published revision (a lower bound of `γ.pub`), positive. -/
def tickP (γ : RandNames) (_ : Int) (v : w64) : IProp GF :=
  iprop(⌜1 ≤ sint.Z v⌝ ∗ monoNatLbOwn γ.pub (sint.nat v))

instance tickP_persistent (γ : RandNames) (i : Int) (v : w64) :
    Persistent (tickP (GF := GF) γ i v) := by
  unfold tickP; infer_instance

/-- **The ticks channel `ch`** (persistent): a single-producer single-consumer channel of ticks. -/
def isTicks (γt : SpscNames) (ch : GoChan) (γ : RandNames) : IProp GF :=
  isSpsc (V := w64) γt ch (tickP γ) (fun _ => iprop(True))

instance isTicks_persistent (γt : SpscNames) (ch : GoChan) (γ : RandNames) :
    Persistent (isTicks (GF := GF) γt ch γ) := by
  unfold isTicks; infer_instance

/-- **The writer's end of the ticks** (exclusive): the channel and the producer's history. -/
def ticksW (γt : SpscNames) (ch : GoChan) (γ : RandNames) : IProp GF :=
  iprop(isTicks γt ch γ ∗ ∃ sent : List w64, spscProducer (V := w64) γt sent)

/-- **The writer between operations of its loop** (see the file header): the index `i` last
applied, the bounds `nv` (on `vals`), `nid` (on `nextID`) and `k` (the write tokens left). -/
def runSt (w : Loc) (wv : writer) (γ : RandNames) (B : KBReal) (f : GoFunc) (q : Qp) (T R : IProp GF)
    (i : w64) (nv nid : Int) (k : Nat) : IProp GF :=
  iprop(∃ (σ : MvccState) (Hs : List HRev) (L : List w64) (n : w64) (k' : Nat) (s v : w64),
    writerOwn wv γ (etcdStorage B) q σ Hs L ∗ writerLe w wv γ B f L n k' T R ∗ hookPre wv i s ∗
    wF go!"vals" w ↦ v ∗
    ⌜0 ≤ sint.Z v ∧ sint.Z v ≤ nv ∧ sint.Z n ≤ nid ∧ k ≤ k'⌝)

/-- **The published revision is a tick** (the tester's invariant: positive, and `γ.pub` is at it). -/
theorem writer_pub_tick (hpers : mvcc.api.persistent.law (GF := GF) (hG := hG)) (h : Loc)
    (γ : RandNames) (p : w64) (j : Int) :
    inv worldN (worldInv h γ) ∗ ghostVar γ.pv (1 : Qp).half p ⊢
      |={⊤}=> ghostVar γ.pv (1 : Qp).half p ∗ tickP γ j p := by
  haveI := fun σ => hpers.2.2.2.2.2.1 γ.kv σ
  haveI := fun S => hpers.2.2.2.2.2.2.1 γ.ws S
  haveI : Timeless (worldInv (GF := GF) h γ) := by unfold worldInv; infer_instance
  iintro ⟨#Hinv, Hp⟩
  iinv Hinv with >Hi Hclose
  iunfold worldInv at Hi
  icases Hi with ⟨%σ, %S, %p', %Hl, %W, Hσ, Hgσ, HS, Hreg, Hpub, Hpv, Hpm, Hlb, %Hok⟩
  ihave %Hag := ghostVar_agree γ.pv _ _ _ _ $$ Hpv Hp
  subst Hag
  ihave #Hlbp := monoNatLbOwn_get γ.pub 1 _ $$ Hpm
  imod Hclose $$ [Hσ Hgσ HS Hreg Hpub Hpv Hpm Hlb] with -
  · inext; iunfold worldInv; iexists σ, S, p', Hl, W; iframe; ipureintro; exact Hok
  imodintro
  iframe Hp
  iunfold tickP
  iframe Hlbp
  ipureintro; exact Hok.2.1

end defs

end mvccrand
end EtcdGrove
end Perennial
