/-
**A client watch channel, generic in what a response says** (2026-10-26). Lean-first (no Rocq
counterpart).

`respElemOk γ Ok i v`: the `i`-th response `v` of a watch channel, modelled by some `r`, at the
positions `i` and `i + 1` of the stream's cursor (`γ.cur`), with the response's fact `Ok c c' v r`
from the position before (`c`) to the one after (`c'`). `isRespChan ch γ Ok`: an SPSC channel
whose element gives it (after an update). Two instances: the clients' model's
(`isEtcdWatchChan`, `Ok := watchRespOk pfx`, `isRespChan_of_etcdWatchChan`) and the client's
Watch spec's (`watchStateElem`: `Ok := ∃ σ, □ Q σ ∗ watchStateRespOk o σ`, `isRespChan_of_state`),
so `Collect` reads either.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.common.WatchBase

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace common

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section chan
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- What a response says, from the position before to the one after. -/
abbrev RespOk (GF : BundledGFunctors) :=
  w64 → w64 → go_etcd_io.etcd.client.v3.WatchResponse → RespModel → IProp GF

/-- **The `i`-th response of a watch channel** (see the file header). -/
def respElemOk (γ : EtcdWatchNames) (Ok : RespOk GF) (i : Int)
    (v : go_etcd_io.etcd.client.v3.WatchResponse) : IProp GF :=
  iprop(∃ (r : RespModel) (c c' : w64), respAt v r ∗ monoListIdxOwn γ.cur i.toNat c ∗
    monoListIdxOwn γ.cur (i.toNat + 1) c' ∗ Ok c c' v r)

/-- **A watch channel whose responses say `Ok`** (persistent; see the file header). -/
def isRespChan (ch : Loc) (γ : EtcdWatchNames) (Ok : RespOk GF) : IProp GF :=
  iprop(∃ P : Int → go_etcd_io.etcd.client.v3.WatchResponse → IProp GF,
    isSpsc γ.spsc ch P (fun _ => iprop(True)) ∗
    □ (∀ (i : Int) (v : go_etcd_io.etcd.client.v3.WatchResponse), P i v -∗
      |==> respElemOk γ Ok i v))

instance isRespChan_persistent (ch : Loc) (γ : EtcdWatchNames) (Ok : RespOk GF) :
    Persistent (isRespChan ch γ Ok) := by
  unfold isRespChan; infer_instance

/-- **Receiving from a watch channel** (the atomic update of Perennial's channel specs): with `ok`,
a response `v` modelled by `r`, its fact from the consumer's position `cursor` to a new one `c'`;
without, the channel was closed. -/
theorem respChan_recv_au (ch : Loc) (γ : EtcdWatchNames) (Ok : RespOk GF) (n : Nat)
    (cursor : w64) (Φ : go_etcd_io.etcd.client.v3.WatchResponse → Bool → IProp GF) :
    ⊢ isRespChan ch γ Ok -∗ £ 1 ∗ £ 1 -∗ etcdWatchConsumer γ n cursor -∗
      ▷ (∀ (v : go_etcd_io.etcd.client.v3.WatchResponse) (ok : Bool),
          (if ok then iprop(|==> ∃ (r : RespModel) (c' : w64), respAt v r ∗
              Ok cursor c' v r ∗ etcdWatchConsumer γ (n + 1) c')
           else iprop(⌜v = zero_val go_etcd_io.etcd.client.v3.WatchResponse⌝)) -∗ Φ v ok) -∗
      recvAu γ.spsc.chanName go_etcd_io.etcd.client.v3.WatchResponse Φ := by
  iintro #Hch Hlc Hcons HΦ
  unfold etcdWatchConsumer
  icases Hcons with ⟨%vs, Hcons, %Hlen, #Hcur⟩
  unfold isRespChan
  icases Hch with ⟨%P, #Hsp, #Hconv⟩
  iapply spsc_rcv_au γ.spsc ch P (fun _ => iprop(True)) vs Φ $$ Hsp Hlc Hcons
  inext
  iintro %v %ok H
  cases ok
  · simp only [Bool.false_eq_true, ↓reduceIte]
    icases H with ⟨-, %Hv⟩
    iapply HΦ
    simp only [Bool.false_eq_true, ↓reduceIte]
    ipureintro; exact Hv
  · simp only [↓reduceIte]
    icases H with ⟨HP, Hcons⟩
    iapply HΦ
    simp only [↓reduceIte]
    imod Hconv $$ %(vs.length : Int) %v HP with HP
    unfold respElemOk
    icases HP with ⟨%r, %c0, %c', #Hr, #Hc0, #Hc', Hok⟩
    have hi : ((vs.length : Int)).toNat = n := by rw [Hlen]; simp
    rw [hi]
    ihave %Heq := mono_list_idx_agree γ.cur n c0 cursor $$ Hc0 Hcur
    subst Heq
    imodintro
    iexists r, c'
    iframe Hr Hok
    iexists vs ++ [v]
    iframe Hcons
    iframe Hc'
    ipureintro; simp [Hlen]

/-- **Receiving from a watch channel** (`respChan_recv_au` as a triple). -/
theorem wp_respChan_receive [go_etcd_io.etcd.cache.v3.Assumptions] (ch : Loc) (γ : EtcdWatchNames) (Ok : RespOk GF) (n : Nat)
    (cursor : w64) :
    {{ isRespChan ch γ Ok ∗ etcdWatchConsumer γ n cursor }}
      (App (Val (chan.receive go_etcd_io.etcd.client.v3.WatchResponse.ty)) (Val #ch))
    {{ (v : go_etcd_io.etcd.client.v3.WatchResponse) (ok : Bool), RET (PairV #v #ok);
        (if ok then iprop(|==> ∃ (r : RespModel) (c' : w64), respAt (GF := GF) v r ∗
            Ok cursor c' v r ∗ etcdWatchConsumer γ (n + 1) c')
         else iprop(⌜v = zero_val go_etcd_io.etcd.client.v3.WatchResponse⌝)) }} := by
  iintro %Φ ⟨#Hw, Hcons⟩ HΦ
  ihave #Hch : isChan ch γ.spsc.chanName go_etcd_io.etcd.client.v3.WatchResponse $$ [Hw]
  · iunfold isRespChan at Hw
    icases Hw with ⟨%Pw, #Hsp, -⟩
    iunfold isSpsc at Hsp; icases Hsp with ⟨$, -⟩
  iapply chan.wp_receive ch γ.spsc.chanName $$ Hch
  iintro ⟨Hlc1, Hlc2, _, _⟩
  iapply respChan_recv_au ch γ Ok n cursor (fun v ok => Φ (PairV #v #ok)) $$ Hw [$Hlc1 $Hlc2] Hcons
  inext
  iintro %v %ok H
  iapply HΦ $$ %v %ok H

/-- The clients' model's watch channel is one (its element `etcdWatchElem`). -/
theorem isRespChan_of_etcdWatchChan [go_etcd_io.etcd.cache.v3.Assumptions] [EM : EtcdModel GF]
    (ch : Loc) (γ : EtcdWatchNames) (pfx : GoString) :
    isEtcdWatchChan (GF := GF) ch γ pfx ⊢ isRespChan ch γ (watchRespOk pfx) := by
  unfold isEtcdWatchChan isRespChan
  iintro ⟨%P, #Hsp, #Hconv⟩
  iexists P
  iframe Hsp
  iintro !> %i %v HP
  have e : respElemOk (GF := GF) γ (watchRespOk pfx) i v = etcdWatchElem γ pfx i v := rfl
  rw [e]
  iapply Hconv $$ HP

/-- **What a read of the KV state says** (the client's Watch spec's response, `watchStateElem`):
some firing `□ Q σ` of the read update and the response as a read of `σ`. -/
def stateOk (o : OpFull) (Q : KVState → IProp GF) : RespOk GF :=
  fun c c' v r => iprop(∃ σ : KVState, □ Q σ ∗ watchStateRespOk o σ c c' v r)

instance stateOk_persistent (o : OpFull) (Q : KVState → IProp GF) (c c' : w64)
    (v : go_etcd_io.etcd.client.v3.WatchResponse) (r : RespModel) :
    Persistent (stateOk (GF := GF) o Q c c' v r) := by
  unfold stateOk; infer_instance

/-- The client's Watch spec's channel is one (`watchStateElem`, at `stateOk`). -/
theorem isRespChan_of_state (ch : Loc) (γ : EtcdWatchNames) (o : OpFull) (Q : KVState → IProp GF) :
    isSpsc (GF := GF) γ.spsc ch (watchStateElem γ o Q) (fun _ => iprop(True)) ⊢
      isRespChan ch γ (stateOk o Q) := by
  iintro #Hsp
  unfold isRespChan
  iexists watchStateElem γ o Q
  iframe Hsp
  iintro !> %i %v HP
  unfold watchStateElem
  icases HP with ⟨%r, %σ, %c, %c', #Hr, #HQ, #Hc, #Hc', #Hok⟩
  imodintro
  unfold respElemOk stateOk
  iexists r, c, c'
  iframe Hr Hc Hc'
  iexists σ
  iframe HQ Hok

/-- A read's response's close error is one grpc's `status` accepts (`watchStateRespOk`'s error
case says so; otherwise there is none). -/
theorem stateOk_closeErr (o : OpFull) (Q : KVState → IProp GF) (c c' : w64)
    (v : go_etcd_io.etcd.client.v3.WatchResponse) (r : RespModel) :
    stateOk (GF := GF) o Q c c' v r ⊢ go_etcd_io.etcd.cache.v3.statusErrOk v.closeErr' := by
  unfold stateOk watchStateRespOk
  iintro ⟨%σ, -, (⟨%H, #He⟩ | %H | %H | ⟨%H, -⟩)⟩
  · iexact He
  all_goals
    have hn : v.closeErr' = GoInterface.nil :=
      Classical.byContradiction fun h => H.1 (Or.inl h)
    rw [hn]; iapply go_etcd_io.etcd.cache.v3.statusErrOk_nil

end chan

end common
end EtcdGrove
end Perennial
