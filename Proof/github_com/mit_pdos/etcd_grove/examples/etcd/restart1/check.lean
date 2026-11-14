/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/restart1/check.lean` (restart S7.5, step f,
2026-11-14): the `Leader()` wait (`EtcdServer.Leader.spec`), the context (`bgCtx_facts`), the request
allocated (`rangeRequestIs_alloc`), `s.Range` (`EtcdServer.Range.spec`, auth off: its read call's
resources out of the started member, `E.RD` borrowed from the revocation's inner pool; its read
deposit `restart1`'s read update, `r1ReadAu`), `cancel()`, and the check against the answer
(`srvRangeOk_r1`, `r1Ok_get`). Lean-first (no Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.restart1.check
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Range
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__Leader
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.restart1.Requests
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.restart1.put
public import Perennial.Spec.context.Background
public import Spec.context.WithTimeoutBackground
public import Perennial.Proof.time.Link

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_restart1

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.restart1.Assumptions]

/-- One item out of a big separating conjunction over `List.replicate n ()`, `1 ≤ n`. -/
theorem bigSepL_replicate_one (P : IProp GF) {n : Nat} (h : 1 ≤ n) :
    ([∗list] _x ∈ List.replicate n (), P) ⊢ P ∗ ([∗list] _x ∈ List.replicate (n - 1) (), P) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [List.replicate_succ, Nat.add_sub_cancel]
  iintro H
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H1, H2⟩
  iframe H1
  iexact H2

/-- `key(j)` at a `w64` argument. -/
theorem wp_key' (j : w64) (h0 : 0 ≤ sint.Z j) (h : sint.Z j < 256) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.restart1 }}
      (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.restart1.key)) (Val #j))
    {{ (sl : GoSlice), RET #sl; sl ↦* keyOf (sint.nat j) }} := by
  have hw := wp_key (GF := GF) (sint.nat j) (by unfold sint.nat; unfold sint.Z at h0 h; omega)
  rwa [show W64 ((sint.nat j : Nat) : Int) = j by unfold sint.nat; word] at hw

/-- `value(j)` at a `w64` argument. -/
theorem wp_value' (j : w64) (h0 : 0 ≤ sint.Z j) (h : sint.Z j < 256) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.restart1 }}
      (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.restart1.value)) (Val #j))
    {{ (sl : GoSlice), RET #sl; sl ↦* valOf (sint.nat j) }} := by
  have hw := wp_value (GF := GF) (sint.nat j) (by unfold sint.nat; unfold sint.Z at h0 h; omega)
  rwa [show W64 ((sint.nat j : Nat) : Int) = j by unfold sint.nat; word] at hw

/-- A started server's leader field (what `Leader` reads), from its request view. -/
theorem leadInv_of_req (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) :
    isServerReq (GF := GF) s E ρ ⊢ srvLeadInv s := by
  iintro #Hreq
  iunfold isServerReq at Hreq
  icases Hreq with ⟨⟨%v, #Hv⟩, -⟩
  iunfold srvReqFieldsAt at Hv
  icases Hv with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #Hlead, -⟩
  iunfold srvLeadInv
  iunfold srvAtomicU64 at Hlead
  iexact Hlead

/-- **What the `Range`'s answer says** (see the file header): the response's key-values are the
`NPuts` pairs `keyOf i ↦ valOf i`, in order, each at version `1`, and its header revision `1 + NPuts`. -/
theorem r1RangeReply (E : apply.AEnv GF) (γr : ReadNames) (resp : Loc) (hnn : resp ≠ null) :
    rangeReadOk E γr (W64 0) [] r1RangeOp resp
        (fun L => iprop(□ ⌜r1Ok (kvStOff γr.kv L) r1NPuts⌝)) ⊢
      ∃ (kvs : List EtcdKv) (more : Bool) (count : w64),
        txn.rangeResponseIs resp (W64 (1 + r1NPuts : Nat)) kvs more count ∗
        ⌜kvs.length = r1NPuts ∧
          ∀ i (hi : i < r1NPuts) v, kvs[i]? = some v →
            v.key = keyOf i ∧ v.value = valOf i ∧ v.version = W64 1⌝ := by
  have hs : r1RangeOp.base.serializable = false := rfl
  iintro H
  iunfold rangeReadOk at H
  simp only [hs, Bool.false_eq_true, ↓reduceIte]
  icases H with ⟨%log, -, -, -, %Hl, -, ⟨%L, -, %HL, %HQ⟩, ⟨%crev, #Hres⟩, -⟩
  obtain ⟨-, hlen, hlen', -⟩ := Hl
  have Hok : r1Ok (kvStateOf log) r1NPuts := by
    unfold kvStOff at HQ; rw [HL] at HQ; exact HQ
  iunfold txn.rangeResult at Hres
  icases Hres with (⟨⟨-, %Hn⟩, -⟩ | ⟨⟨-, -, -, %Hn, -⟩, -⟩ | ⟨-, %kvs, %more, #Hr, %Hsel⟩ |
    ⟨⟨-, -, %Hn⟩, -⟩)
  · exact absurd Hn hnn
  · exact absurd Hn hnn
  rotate_left
  · exact absurd Hn hnn
  have hrev : sint.nat (mvcc.rangeRev (W64 ((log.length : Int) - 1)) r1RangeOp.base.rev) =
      log.length - 1 := by
    have h1 : mvcc.rangeRev (W64 ((log.length : Int) - 1)) r1RangeOp.base.rev =
        W64 ((log.length : Int) - 1) := by simp [mvcc.rangeRev]
    rw [h1]; unfold sint.nat; word
  rw [hrev, mvcc.stateAt_last] at Hsel
  have hk := srvRangeOk_r1 _ _ _ Hsel
  rw [← kvStateOf_kvs (lt := [])] at hk
  obtain ⟨h1, h2⟩ := r1Ok_get _ Hok
  have hl : ((log.length : Int) - 1) = ((1 + r1NPuts : Nat) : Int) := by
    have := Hok.2; rw [kvStateOf_rev] at this; omega
  rw [show W64 ((1 + r1NPuts : Nat) : Int) = W64 ((log.length : Int) - 1) by rw [hl]]
  iexists kvs, more, _
  iframe Hr
  ipureintro
  rw [hk]
  exact ⟨h1, h2⟩

set_option maxHeartbeats 1000000 in
theorem check.wp_proof
    (wp_Range : EtcdServer.Range.spec (GF := GF) (hG := hG))
    (wp_Leader : EtcdServer.Leader.spec (GF := GF) (hG := hG))
    (wp_Background : context.Background.spec (GF := GF) (hG := hG))
    (hWT : context.WithTimeoutBackground.spec (GF := GF) (hG := hG)) :
    check.spec (GF := GF) (hG := hG) := by
  intro s ρ E₀ lg γn id γc hlv
  wp_start as ⟨Hup, #Hinv, #Hlb⟩
  iunfold etcdstart.memberUp at Hup
  icases Hup with ⟨%E, %cfg, %γw, %HEc, Hstk, -, #Hreq, #Hrd, Hgo, Hlgr, Hrds, -, -, -, -, -, -⟩
  have hoff : E.authMode = .off := by
    have h := HEc.2.1
    unfold apply.AEnv.authOn at h
    cases hM : E.authMode <;> simp_all [auth.AuthMode.isOn]
  ihave #Pctx : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  ihave #Psrv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver $$ []
  · iPkgInit
  ihave #Hcci : _root_.Perennial.context.isClosedchanInit (GF := GF) $$ []
  · iapply _root_.Perennial.context.isClosedchanInit_of_init
    iexact Pctx
  ihave #Hlead := leadInv_of_req s E _ $$ Hreq
  wp_auto
  -- the wait: `for s.Leader() == 0 { time.Sleep(time.Millisecond) }`
  wp_for s
  wp_apply (wp_Leader s) as %l -
  · iframe #
  (try wp_auto)
  wp_if_destruct
  · wp_apply time.wp_Sleep
    (try wp_auto)
    wp_for_post
    iframe
  have Hl : ¬ l = W64 0 := by intro h; apply Hif; subst h; rfl
  rw [if_neg (by simpa using Hl)]
  wp_auto
  -- `ctx, cancel := context.WithTimeout(context.Background(), etcdstart.RequestTimeout)`
  wp_apply wp_Background
  (try wp_auto)
  wp_apply hWT $$ [] as %ctx %cd %cancel ⟨#Hcancel, #Hctx, #Hfrom⟩
  · iframe #
  ihave ⟨#Hlib, -, #Htr⟩ := bgCtx_facts ctx $$ []
  · iframe #
  (try wp_auto)
  -- `&pb.RangeRequest{Key: []byte(RangeKey), RangeEnd: []byte(RangeEnd)}`
  wp_apply (wp_string_to_bytes go!"k") as %ks ⟨Hks, -⟩
  (try wp_auto)
  wp_apply (lc := 1) (wp_string_to_bytes go!"l") as %es ⟨Hes, -⟩
  (try wp_auto)
  imod ownSlice_persist _ _ _ $$ Hks with #Hks
  imod ownSlice_persist _ _ _ $$ Hes with #Hes
  ihave %Hkl := ownSlice_len _ _ _ $$ Hks
  ihave %Hel := ownSlice_len _ _ _ $$ Hes
  have hkl : sint.Z ks.len < 2 ^ 63 - 1 := by
    obtain ⟨h1, h2⟩ := Hkl
    have h4 : sint.Z ks.len = 1 := by
      simp only [List.length_singleton] at h1; unfold sint.nat at h1; unfold sint.Z; omega
    omega
  have hes : es ≠ slice.nil := by
    intro h
    obtain ⟨h1, -⟩ := Hel
    subst h
    simp [slice.nil, sint.nat] at h1
  have Ha := rangeRequestIs_alloc (GF := GF) «$a1_ptr»
    { state' := zeroValDef, Key' := ks, RangeEnd' := es, Limit' := W64 0, Revision' := W64 0,
      SortOrder' := W32 0, SortTarget' := W32 0, Serializable' := false, KeysOnly' := false,
      CountOnly' := false, MinModRevision' := W64 0, MaxModRevision' := W64 0,
      MinCreateRevision' := W64 0, MaxCreateRevision' := W64 0, unknownFields' := slice.nil,
      sizeCache' := W32 0 } go!"k" go!"l" hkl
  imod Ha $$ [«$a1»] with #Hr
  · isplitl [«$a1»]
    · iExactEq «$a1»
      congr 1
    isplitl
    · iexact Hks
    · iexact Hes
  ihave #Hr' : txn.rangeRequestIs «$a1_ptr» r1RangeOp $$ []
  · iExactEq Hr
    simp only [txn.rangeEndOf, hes, ↓reduceIte]
    rfl
  iclear Hr
  clear Ha
  -- the read call's resources (`srvRdCall`)
  iunfold srvServeStock at Hstk
  icases Hstk with ⟨#Hb, Hpool⟩
  have h1p : 1 ≤ srvRevokePoolN := by unfold srvRevokePoolN backend.rdPoolN; omega
  icases bigSepL_replicate_one _ h1p $$ Hpool with ⟨⟨Hmr, -⟩, -⟩
  icases bigSepL_replicate_one _ etcdstart.one_le_memberReadN $$ Hrds with ⟨Hrr, -⟩
  imod monoNatLbOwn_0 (GF := GF) ρ.rd.committed with #Hc0
  iunfold srvGoRes at Hgo
  icases Hgo with ⟨-, Htok⟩
  have h3 : 3 ≤ threadBound GF := by
    unfold srvLevels at hlv; unfold srvLevelK srvRevokeK at hlv; omega
  icases threadTok_lend2 h3 $$ Htok with ⟨H2, -⟩
  imod srvRevokeBuilt_innerBorrow s E ⊤ (fun _ _ => CoPset.mem_full) $$ [Hlc1 H2]
    with ⟨⟨-, HRD⟩, -⟩
  · iframe Hlc1 H2; iexact Hb
  ihave Hcall : srvRdCall s E ρ.rd (W64 0) $$ [Hmr Hlgr Hrr HRD]
  · iunfold srvRdCall
    iframe Hmr Hlgr Hrr HRD
    iunfold committedAtLeast; ileft
    iExactEq Hc0; rfl
  -- the read deposit: `restart1`'s read update
  ihave #Hdep : kvDep ρ.rd.kv
      (fun L => iprop(□ (fun σ => iprop(⌜r1Ok σ r1NPuts⌝) : KVState → IProp GF)
        (kvStOff ρ.rd.kv L))) (kvStOff ρ.rd.kv) $$ []
  · iunfold kvDep
    ileft
    iexists (fun σ => iprop(⌜r1Ok σ r1NPuts⌝) : KVState → IProp GF)
    isplitr; · ipureintro; rfl
    iapply r1ReadAu
    iframe #
  imod (show ⊢ |==> srvApi.kvLogLb (GF := GF) E.γs [] by
    unfold srvApi.kvLogLb; exact monoListLbOwn_nil _) with #HF0
  -- `resp, err := s.Range(ctx, &pb.RangeRequest{...})`
  have hany : E.authMode ≠ .any := by rw [hoff]; intro h; cases h
  wp_apply (wp_Range s E { ρ with wait := γw } ρ.rd (W64 0) ctx cd «$a1_ptr» r1RangeOp none false
      (fun L => iprop(□ (fun σ => iprop(⌜r1Ok σ r1NPuts⌝) : KVState → IProp GF)
        (kvStOff ρ.rd.kv L))) [] 0 hany) $$ [Hcall] as %resp %err ⟨-, Hout⟩
  · rw [HEc.2.1]
    simp only [isServerReqM_false, isServerReadM_false, kvStM_false]
    iframe Hcall
    iframe #
    isplitr; · iapply srvAuthLb_off s E _ $$ Hreq
    isplitr; · rw [hoff]; iunfold auth.authPubLbM; itrivial
    isplitr; · iunfold traceutil.ownTraceOpt; itrivial
    ipureintro; unfold txn.validSortTarget; simp [txn.rangeOpOf]
  (try wp_auto)
  -- `cancel()`
  wp_apply Hcancel
  (try wp_auto)
  icases Hout with (⟨⟨%Herr, %Hnn⟩, -, Hok⟩ | ⟨⟨-, %Herr⟩, -⟩)
  rotate_left
  · cases err with
    | nil => exact absurd rfl Herr
    | ok ei => ?_
    wp_auto
    iapply HΦ; itrivial
  subst Herr
  rw [HEc.2.1, rangeReadOkM_false]
  icases r1RangeReply E ρ.rd resp Hnn $$ Hok with ⟨%kvs, %more, %count, #Hr, %Hkv⟩
  iunfold txn.rangeResponseIs at Hr
  icases Hr with ⟨-, %h, %sl, %ps, #Hh, %Hhn, #Hrev, #Hkvf, #Hsl, #Hkvs, -, -⟩
  iunfold txn.kvsIs at Hkvs
  icases Hkvs with ⟨%Hlen, #Hall⟩
  ihave %Hsll := ownSlice_len _ _ _ $$ Hsl
  wp_auto
  have hsl : sl.len = W64 11 := by
    have h1 := Hsll.1
    rw [Hlen, Hkv.1] at h1
    have h2 := Hsll.2
    unfold sint.nat at h1
    apply BitVec.eq_of_toInt_eq
    unfold sint.Z at h2
    simp only [r1NPuts] at h1
    have : sl.len.toInt = 11 := by omega
    rw [this]; rfl
  rw [show decide (sl.len = W64 11) = true from by simp [hsl]]
  wp_auto
  ihave HI : (∃ j : w64, "i" ∷ i_ptr ↦ j ∗ "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ 11⌝ : IProp GF) $$ [i]
  · iexists W64 0; iframe; ipureintro; constructor <;> word
  wp_for HI
  wp_if_destruct
  · have Hb : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z sl.len := by
      rw [hsl]; exact ⟨Hj.1, Hif⟩
    simp only [Hb, _root_.and_self, ↓reduceIte]
    have hjn : sint.nat j < r1NPuts := by
      have h1 := Hif; have h2 := Hj.1
      simp only [show sint.Z (W64 11) = 11 by rfl] at h1
      simp only [r1NPuts]; unfold sint.nat; unfold sint.Z at h1 h2; omega
    obtain ⟨v, Hv⟩ : ∃ v, kvs[sint.nat j]? = some v :=
      ⟨_, List.getElem?_eq_getElem (by rw [Hkv.1]; exact hjn)⟩
    obtain ⟨p, Hp⟩ : ∃ p, ps[sint.nat j]? = some p :=
      ⟨_, List.getElem?_eq_getElem (by rw [Hlen, Hkv.1]; exact hjn)⟩
    wp_apply wp_load_slice_index _ (sint.Z j) _ DFrac.discard p Hb.1 $$ [Hsl] as -
    · iframe Hsl; ipureintro; exact Hp
    ihave #Hkvp := Hall $$ %(sint.nat j) %p %v %Hp %Hv
    iunfold txn.kvIs at Hkvp
    icases Hkvp with ⟨%kSl, %vSl, #HkF, #HkS, -, -, #HVer, #HvF, #HvS, -, -⟩
    obtain ⟨hk, hv, hver⟩ := Hkv.2 (sint.nat j) hjn v Hv
    have h256 : sint.Z j < 256 := by have := Hif; simp only [show sint.Z (W64 11) = 11 by rfl] at this; omega
    wp_auto
    -- `string(kv.Key) != string(key(i))`: equal
    wp_apply wp_bytes_to_string kSl v.key DFrac.discard $$ [HkS] as -
    · iframe #
    (try wp_auto)
    wp_apply (wp_key' j Hj.1 h256) as %ks2 Hks2
    wp_apply wp_bytes_to_string ks2 _ (DFrac.own 1) $$ [Hks2] as -
    · iframe
    (try wp_auto)
    rw [hk]
    simp only [decide_true, Bool.not_true]
    wp_auto
    -- `string(kv.Value) != string(value(i))`: equal
    wp_apply wp_bytes_to_string vSl v.value DFrac.discard $$ [HvS] as -
    · iframe #
    (try wp_auto)
    wp_apply (wp_value' j Hj.1 h256) as %vs2 Hvs2
    wp_apply wp_bytes_to_string vs2 _ (DFrac.own 1) $$ [Hvs2] as -
    · iframe
    (try wp_auto)
    rw [hv]
    simp only [decide_true, Bool.not_true]
    wp_auto
    -- `kv.Version != 1`: equal
    rw [hver]
    simp only [decide_true, Bool.not_true]
    wp_auto
    wp_for_post
    iframe
    iexists j + W64 1
    iframe
    ipureintro; constructor <;> word
  · iapply HΦ; itrivial

end proof

end etcd_restart1
end EtcdGrove
end Perennial
