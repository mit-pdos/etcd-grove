/-
Lean-first (no Rocq counterpart).

The proof of `(*compactor).getCompactRev`: the client's `Get` of the compactors' key with no
options (`client_Get_nil`, `client_Get_kv` without the `WithRev`), through the client's KV handle
(`clientKvOk`), with the caller's read update (`keyReadOk`), whose result `keyHistOk` at the state
read gives the header's revision at least `1` and the key's value, if present, `FormatInt c` of a
recorded `c` (`keyValOk`): `ParseInt` reads `c` back (its error branch unreachable). A client error
goes into `fmt.Errorf("get %q failed: %w", ...)` (the error's `Error()`: `kvErr`'s
`statusErrOk`). The header is never nil (`rangeRespMsg`'s `hdrFull`).
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.etcd3.compactor__getCompactRev
public import Proof.go_etcd_io.etcd.client.v3.ClientPutGet
public import Spec.strconv.ParseInt
public import Spec.fmt.Errorf
import all Proof.k8s_io.apiserver.pkg.storage.etcd3.CompactorDefs

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : k8s_io.apiserver.pkg.storage.etcd3.Assumptions]

/-- `cli.Get(ctx, key)` (no options) by a client whose `KV` field is a `*kv` of etcd's KV `γ`, with
a read update (`client.client_Get_kv` without the `WithRev`): `nil` and the reply's message `m`
with the state `σ` the update fired at, the header at `σ`'s revision, `m`'s key-values the key's
in `σ`'s current store; or a client error. -/
private theorem client_Get_nil [go_etcd_io.etcd.client.v3.Assumptions] (cl api : Loc)
    (γ : KVNames) (dup : Bool) (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF))
    (key : GoString) (Q : KVState → IProp GF) (hsz : opSizeOk (opGetModel key [])) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
        structFieldRef go_etcd_io.etcd.client.v3.Client go!"KV" cl ↦□
          GoInterface.ok (client.kvIfaceOf api) ∗
        client.isKv api γ dup ∗ ctxOk ci cd ∗ ctxErrClient ci cd ∗ kvReadAu γ Q }}
      (App (App (App (Val (cl @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!!
          go!"Get")) (Val #(GoInterface.ok ci))) (Val #key)) (Val #slice.nil))
    {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err);
        (⌜err = GoInterface.nil⌝ ∗ ∃ (m : RangeRespM) (σ : KVState), rangeRespMsg resp m ∗
          □ Q σ ∗ ⌜m.hdr.revision = W64 (σ.rev : Int) ∧ kvRevFits σ.rev ∧
            m.kvs = σ.kvs.filter (fun v => decide (v.key = key))⌝) ∨
          (⌜err ≠ GoInterface.nil ∧ resp = null⌝ ∗ kvErr err) }} := by
  iintro %Φ ⟨#Pc, #Hkvf, #Hkv, #Hctx, #Hce, #Hau⟩ HΦ
  ihave #Hnil := optsAt_nil (GF := GF)
  ihave #Hopts' := optsAt_res slice.nil [] iprop(True) $$ Hnil
  rw [go_etcd_io.etcd.client.v3.Client.TypeAssumptions.ptr_Get_unfold.method_unfold]
  wp_pures
  wp_auto
  wp_apply (client.v3.kv.wp_Get api γ dup ci cd key slice.nil [] iprop(True) Q) $$ []
    as %resp %err ⟨-, Hout⟩
  · iframe #
    isplitl []
    · itrivial
    isplitl []
    · rw [show (opGetModel key []).base.sortSet = false from rfl]
      iapply sortNamesIf_false
    isplitl []
    · ipureintro
      refine ⟨?_, rfl⟩
      unfold opGetPanics opFold OpFull.newOp; simp
    isplitl []
    · imodintro
      iright
      isplitl []
      · ipureintro; rfl
      iunfold kvReadAu at Hau
      iunfold kvAu at Hau
      iexact Hau
    ipureintro; exact hsz
  iapply HΦ
  icases Hout with (⟨%Herr, %m, %σ, #Hm, #HQ, %Hs⟩ | ⟨%Herr, #Hke⟩)
  · ileft
    isplitl []
    · ipureintro; exact Herr
    iexists m, σ
    iframe Hm HQ
    ipureintro
    obtain ⟨-, hsel, -, hhdr, hfit, -⟩ := Hs
    refine ⟨hhdr, hfit, ?_⟩
    have hw : rangeWireOf (opGetModel key []) = rangeWireOf (opGetModel key [withRevM (W64 0)]) :=
      rfl
    rw [hw] at hsel
    have := client.srvRangeOk_getKeyRev key (W64 0) _ _ _ hsel
    rw [this]
    rfl
  · iright
    iframe Hke
    ipureintro; exact Herr

/-- A non-empty slice's length is not `0`, and index `0` is in bounds (standalone: proved inline,
the kernel rejected the abstracted proof term). -/
private theorem slice_nonempty_bounds (sl : GoSlice) (ps : List Loc)
    (h : ps.length = sint.nat sl.len ∧ 0 ≤ sint.Z sl.len) (hp : 0 < ps.length) :
    sl.len ≠ W64 0 ∧ (0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z sl.len) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro h0
    have h1' : ps.length = 0 := h1.trans (by rw [h0]; rfl)
    exact Nat.pos_iff_ne_zero.mp hp h1'
  · word
  · rw [show sint.nat sl.len = (sint.Z sl.len).toNat from rfl] at h1; word

/-- An empty slice's length is `0` (standalone, as above). -/
private theorem slice_empty_len (sl : GoSlice)
    (h : ([] : List Loc).length = sint.nat sl.len ∧ 0 ≤ sint.Z sl.len) : sl.len = W64 0 := by
  obtain ⟨h1, h2⟩ := h
  rw [show sint.nat sl.len = (sint.Z sl.len).toNat from rfl] at h1
  simp at h1
  word

theorem compactor.getCompactRev.wp_proof
    (wp_ParseInt : EtcdGrove.strconv.ParseInt.spec (GF := GF) (hG := hG))
    (wp_Errorf : EtcdGrove.fmt.Errorf.spec (GF := GF) (hG := hG)) :
    compactor.getCompactRev.spec (GF := GF) (hG := hG) := by
  intro _ _ c cl γk recorded γc ci cd
  wp_start as ⟨#Hc, #Hko, #Hctx, #Hce, #Hread⟩
  iunfold compactorCore at Hc
  icases Hc with ⟨%Hpers, #Hclf, -, -, -, -, -⟩
  haveI := Hpers
  ihave #Hko' := Hko
  iunfold clientKvOk at Hko'
  icases Hko' with ⟨%api, %dup, #Hkvf, #Hkv⟩
  rw [show k8s_io.apiserver.pkg.storage.etcd3.compactRevKey = #compactRevKey from rfl]
  wp_auto
  ihave #Hread' := Hread
  iunfold keyReadOk at Hread'
  wp_apply (client_Get_nil cl api γk dup ci cd compactRevKey (keyHistOk γk recorded)
      (opSizeOk_opGetModel (K := 2 ^ 27) (E := 0) (V := 0) (optsKeep_nil _ _ _)
        (by simp [compactRevKey]) (by decide))) $$ []
    as %resp %err Hout
  · iframe #
  icases Hout with (⟨%Herr, %m, %σ, #Hm, #HQ, %Hσ⟩ | ⟨%Herr, #Hke⟩)
  rotate_left
  · -- the `Get` failed: `fmt.Errorf("get %q failed: %w", key, err)`
    cases err with
    | nil => exact absurd rfl Herr.1
    | ok ei => ?_
    wp_auto
    iunfold kvErr at Hke
    icases Hke with ⟨-, #Hse, -⟩
    iunfold go_etcd_io.etcd.cache.v3.statusErrOk at Hse
    ihave ⟨⟨%em, #HeS0⟩, -, -, %HF⟩ := Hse $$ %ei %rfl
    ihave #HeS := go_etcd_io.etcd.cache.v3.errorMsgIs_errorStringSpec _ _ $$ HeS0
    ihave #HeS' : EtcdGrove.fmt.stringMethodSpec ei go!"Error" $$ []
    · rw [show EtcdGrove.fmt.stringMethodSpec ei go!"Error" =
        go_etcd_io.etcd.cache.v3.errorStringSpec ei from rfl]
      iexact HeS
    ihave #Pf : isPkgInit (PROP := IProp GF) pkg_id.fmt $$ []
    · iPkgInit
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    wp_auto
    wp_apply wp_Errorf $$ [$Hsl] as %e2 ⟨-, #He2, %He2t, -⟩
    · iframe #
      fmt_args_ok
    iapply HΦ
    ileft
    isplitl
    · -- `fmt.Errorf`'s error: `fmt.argOk` by its `Error()`
      unfold fmt.argOk
      iright; ileft
      isplitr
      · iexact He2
      · ipureintro; exact He2t.1
    ipureintro; simp
  -- the `Get` succeeded
  subst Herr
  obtain ⟨hhdr, hfit, hkvs⟩ := Hσ
  iunfold keyHistOk at HQ
  icases HQ with ⟨%Hr1, #Hval, -⟩
  iunfold rangeRespMsg at Hm
  icases Hm with ⟨%Hnn, %h, %sl, %ps, #Hh, #Hhf, #Hkvsf, #Hsl, #Hkvs, -, -⟩
  iunfold hdrFull at Hhf
  icases Hhf with ⟨%Hhn, -, -, #Hrevf, -, -⟩
  iunfold txn.kvsIs at Hkvs
  icases Hkvs with ⟨%Hlen, #Hall⟩
  ihave %Hsll := ownSlice_len _ _ _ $$ Hsl
  have hcur : 1 ≤ sint.Z m.hdr.revision := by
    rw [hhdr]; have := hfit.lt; word
  wp_auto
  cases hF : σ.kvs.filter (fun v => decide (v.key = compactRevKey)) with
  | nil =>
    -- the key is absent: `compactRev` stays `0`
    rw [hF] at hkvs
    have hps : ps = [] := by
      apply List.eq_nil_of_length_eq_zero; rw [Hlen, hkvs]; rfl
    subst hps
    wp_if_destruct
    all_goals try (exfalso; exact Hif (slice_empty_len sl Hsll); done)
    (try wp_auto)
    wp_if_destruct
    all_goals try (exfalso; first | exact Hhn rfl | exact Hhn Hif; done)
    (try wp_auto)
    iapply HΦ
    iright
    isplitr
    · ipureintro; exact ⟨rfl, hcur⟩
    unfold recRevOk; ileft; ipureintro; rfl
  | cons v0 rest =>
    -- the key's value: `FormatInt c` of a recorded `c`
    rw [hF] at hkvs
    have hkv : keyValue σ compactRevKey = some v0.value := by
      unfold keyValue; rw [hF]; rfl
    ihave #Hok := Hval $$ %v0.value %hkv
    iunfold keyValOk at Hok
    icases Hok with ⟨%cv, %Hcv, #Hrc, #Hoc⟩
    obtain ⟨p0, Hp0⟩ : ∃ p0, ps[0]? = some p0 := by
      have : 0 < ps.length := by rw [Hlen, hkvs]; simp
      exact ⟨ps[0], List.getElem?_eq_getElem this⟩
    have hv0 : m.kvs[0]? = some v0 := by rw [hkvs]; rfl
    ihave #Hk0 := Hall $$ %0 %p0 %v0 %Hp0 %hv0
    iunfold txn.kvIs at Hk0
    icases Hk0 with ⟨%keySl, %valSl, #Hkey, #Hkeys, #Hcrt, #Hmod, #Hver, #Hvalf, #Hvals, #Hlease⟩
    have hpl : 0 < ps.length := by rw [Hlen, hkvs]; simp
    have Hne := slice_nonempty_bounds sl ps Hsll hpl
    wp_if_destruct
    all_goals try (exfalso; exact Hne.1 Hif; done)
    have Hbnd0 := Hne.2
    try simp only [Hbnd0, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index _ (sint.Z (W64 0)) _ DFrac.discard p0 Hbnd0.1 $$ [Hsl] as -
    · iframe Hsl; ipureintro; exact Hp0
    (try wp_auto)
    wp_apply wp_bytes_to_string valSl v0.value DFrac.discard $$ [Hvals] as -
    · iexact Hvals
    wp_apply wp_ParseInt v0.value (W64 10) (W64 64) as %n %perr %Hp
    obtain ⟨rfl, rfl⟩ := Hp cv Hcv rfl rfl
    (try wp_auto)
    wp_if_destruct
    all_goals try (exfalso; first | exact Hhn rfl | exact Hhn Hif; done)
    (try wp_auto)
    iapply HΦ
    iright
    isplitr
    · ipureintro; exact ⟨rfl, hcur⟩
    unfold recRevOk
    iunfold revOk at Hoc
    icases Hoc with (%Hc0 | ⟨%Hcpos, #Hclb⟩)
    · ileft; ipureintro; exact Hc0
    · iright; iframe #; ipureintro; exact Hcpos

end proof

end k8s
end EtcdGrove
end Perennial
