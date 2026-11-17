/-
Lean-first (no Rocq counterpart).

# A watch's answer, accepted at its commit (stage E of 7f-6, plan §3 step 5)

The pure side of `Apply`'s watch commit: what `runWatch` returns is accepted by the driver's watch
check (`watchOkL`) at every configuration related to etcd's state at the commit. A failed or
skipped watch, at once; a watch that received only Error events, by `watchOkL_errs`; any other,
from its events' `kStreamOk` at the state its read update fired at, moved to the commit's state
(one history, not older: `kStreamOk_hist`), then the bridge (`streamOkL_of_kStreamOk`) and the
check (`watchOkL_of_stream`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.WatchQ
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.runWatch

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI k8s
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Obj)

section pure
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- An empty predicate selects every object. -/
theorem selD_of_empty (x : Input) (he : predEmptyL x = true) (o : DObj) : selD x o = true := by
  have := sel_answer x (o.toObj (W64 0))
  unfold predEmptyL at he
  simp only [selD]
  rw [← this, he]

/-- **A watch's events, accepted at the commit** (see the file header): received at the read
firing's state `σ` (`kStreamOk`) from the start firing's `σ0` (`kStartOk`), at the commit's state
`σe` of the same history, not older, related to the configuration's history `h`. -/
theorem watchOkL_stream_commit (x : Input) (k : GoString) (n : w64)
    (hk : k8s.prepareKeyM go!"/objs" x.WKey' x.Recursive' = some k) (hlk : go!"/objs/" <+: x.WKey')
    (hn : parseRVD x.MinRV' = some n) (hin : WatchInOk x (uint.nat n))
    (hb : x.SendInit' = W64 2 → x.Bookmarks' = true)
    (h1 : x.SendInit' ≠ W64 2 → x.SendInit' = W64 1 ∨ 0 < uint.nat n)
    (kes : List (KWEv DObj)) (wes : List WEv) (hws : List.Forall₂ kWEvRel kes wes)
    (hok : ∀ w ∈ wes, WEvOk w) (z : DObj)
    (σ σ0 σe : KVState) (st : Nat) (hh : kvSameHist σ σe) (hle : σ.rev ≤ σe.rev)
    (h0 : 1 ≤ σ0.rev) (hstart : kStartOk (kModeOf (sieOfL x) x.Bookmarks' n) σ0 st)
    (hs : kStreamOk driverCodec.dec (selD x) (predEmptyL x) z
      (kInScope (go!"/registry" ++ k) x.Recursive') (kModeOf (sieOfL x) x.Bookmarks' n) σ st kes)
    (h : HSt) (hrel : KRelH h σe) (hlen : h.hist.length = σe.rev) (hW : KHistW σe) :
    watchOkL x (wEventsOut (encWEventsL wes)) h = true := by
  have hs' := kStreamOk_hist hh hle hs
  have hst := streamOkL_of_kStreamOk x h σe σ0 k n _ (selD x) (predEmptyL x) z st kes wes hrel hlen
    hW hk hlk (fun _ => rfl) (fun he o => selD_of_empty x he o) (kModeOk_of x n hb h1) h0 hstart
    hs' hws
  have hwf := histWf_of_krel x h σe k hrel hlen hW hk hlk
  have hrv : uint.nat h.st.rv = h.hist.length := by
    have e := hrel.2.1.2.1
    rw [← e, hlen]
    have := hrel.1
    word
  exact watchOkL_of_stream (x := x) (hs := h.hist) _ h wes n hn hin hwf rfl hrv rfl hok hst

end pure

end k8s_etcd3
end EtcdGrove
end Perennial
