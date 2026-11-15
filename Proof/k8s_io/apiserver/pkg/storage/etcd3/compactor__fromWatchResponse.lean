/-
Lean-first (no Rocq counterpart).

The proof of `(*compactor).fromWatchResponse`: an error response returns `resp.Err()` (non-nil both
times it is called, by `Err`'s spec); otherwise the events hold `keyValOk` values (`respKeyOk`), so
the last one's value is `FormatInt(c, 10)` of a recorded, reached-or-zero `c`, which `ParseInt`
returns without error (its error branch is unreachable).
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.etcd3.compactor__fromWatchResponse
public import Spec.go_etcd_io.etcd.client.v3.WatchResponse__Err
public import Spec.strconv.ParseInt
import all Proof.k8s_io.apiserver.pkg.storage.etcd3.CompactorDefs

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : k8s_io.apiserver.pkg.storage.etcd3.Assumptions]

/-- The last index of a non-empty slice of length `l` is in bounds. -/
private theorem last_index_bounds {l : w64} (h0 : 0 ≤ sint.Z l) (hne : ¬ l = W64 0) :
    0 ≤ sint.Z (l - W64 1) ∧ sint.Z (l - W64 1) < sint.Z l := by
  have h1 : sint.Z l ≠ 0 := by intro h; apply hne; word
  constructor <;> word

theorem compactor.fromWatchResponse.wp_proof
    (wp_Err : EtcdGrove.WatchResponse.Err.spec (GF := GF) (hG := hG))
    (wp_ParseInt : EtcdGrove.strconv.ParseInt.spec (GF := GF) (hG := hG)) :
    compactor.fromWatchResponse.spec (GF := GF) (hG := hG) := by
  intro c γk recorded v
  wp_start as Hok
  simp only [respKeyOk]
  icases Hok with ⟨#Hse, %r, #Hr, Hev⟩
  (try wp_auto)
  wp_apply wp_Err resp_ptr v (DFrac.own 1) $$ [$resp $Hse] as %err1 ⟨resp, %Herr1, -⟩
  cases err1 with
  | ok e1 =>
    -- an error response: `Err()` again, non-nil too, and `fmt.argOk` (its `errStrOk`, from the
    -- close error's `statusErrOk`)
    (try wp_auto)
    wp_apply wp_Err resp_ptr v (DFrac.own 1) $$ [$resp $Hse] as %err2 ⟨resp, %Herr2, #Hes2⟩
    (try wp_auto)
    iapply HΦ
    ileft
    isplitl
    · iapply fmtArgOk_of_errStrOk
      iapply Hes2
      iapply go_etcd_io.etcd.cache.v3.errStrOk_of_statusErrOk $$ Hse
    ipureintro
    intro h2
    have := Herr1.2 (Herr2.1 h2)
    cases this
  | nil =>
  have hnw : ¬ watchErr v := by
    have h := Herr1.1 rfl
    unfold watchErr
    rintro (h' | h' | h') <;> simp_all
  icases Hev with (%Hw | #Hev)
  · exact absurd Hw hnw
  icases respAt_elim $$ Hr with ⟨#Hevs, -, -⟩
  icases eventsAt_elim $$ Hevs with ⟨%ls, #Hls, %Hlen, #Hea⟩
  ihave %Hlsl := ownSlice_len $$ Hls
  (try wp_auto)
  wp_if_destruct
  · -- no event
    (try wp_auto)
    iapply HΦ
    iright
    isplitr
    · ipureintro; rfl
    iunfold recRevOk
    ileft
    ipureintro; rfl
  have Hb : 0 ≤ sint.Z (v.Events'.len - W64 1) ∧
      sint.Z (v.Events'.len - W64 1) < sint.Z v.Events'.len := by
    exact last_index_bounds Hlsl.2 Hif
  simp only [Hb, _root_.and_self, ↓reduceIte]
  list_elem ls (sint.nat (v.Events'.len - W64 1)) as ev
  obtain ⟨e, he⟩ : ∃ e, r.events[sint.nat (v.Events'.len - W64 1)]? = some e :=
    ⟨_, List.getElem?_eq_getElem (by rw [← Hlen]; exact (List.getElem?_eq_some_iff.mp Hev_lookup).1)⟩
  wp_apply wp_load_slice_index v.Events' (sint.Z (v.Events'.len - W64 1)) ls DFrac.discard ev
    Hb.1 $$ [Hls] as -
  · iframe #; ipureintro; exact Hev_lookup
  ihave #Hev1 := Hea $$ %(sint.nat (v.Events'.len - W64 1)) %ev %e %Hev_lookup %he
  icases eventAt_elim $$ Hev1 with ⟨%keySl, -, #Hkvf, -, -, -⟩
  icases Hev $$ %(sint.nat (v.Events'.len - W64 1)) %e %he with ⟨%kvv, #Hkvv, Hval⟩
  icases kvValAt_elim $$ Hkvv with ⟨%kSl', %valSl, -, -, -, -, -, #Hvalf, #HvalS, -⟩
  (try wp_auto)
  wp_apply wp_bytes_to_string valSl kvv.value DFrac.discard $$ [HvalS] as -
  · iframe #
  (try wp_auto)
  wp_apply wp_ParseInt as %n %perr %Hparse
  iunfold keyValOk at Hval
  icases Hval with ⟨%cr, %Hcr, Hrec, #Hrev⟩
  obtain ⟨rfl, rfl⟩ := Hparse cr Hcr rfl rfl
  (try wp_auto)
  iapply HΦ
  iright
  isplitr
  · ipureintro; rfl
  iunfold revOk at Hrev
  iunfold recRevOk
  icases Hrev with (%H0 | ⟨%Hpos, #Hlb⟩)
  · ileft; ipureintro; exact H0
  · iright
    isplitl []
    · ipureintro; exact Hpos
    isplitl []
    · iexact Hrec
    iexact Hlb

end proof

end k8s
end EtcdGrove
end Perennial
