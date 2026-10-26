/-
The apply thread across an applied snapshot (D22 receiver epochs, S8d, 2026-10-24;
`notes/snapshot-s8-plan.md`, item 18, W4): lemmas `applySnapshot`'s proof uses, outside the
spec/proof discipline (ghost steps, no code).

* `kv_cert_jump`: the apply thread's KV ghost state (`kvAppliedL`) moves from the applied raft log
  `A` to a longer committed one `A'` (the snapshot image's prefix) in one step, the image's KV model
  certified there (as `kv_cert_step` does one entry at a time).
* `srv_be_swap`: `s.be`'s swap under `bemu`'s write side (S7's "What S8 uses", 1): the current
  backend's ghost variable gathered whole (`bemuP 1`'s half, the apply thread's quarter
  `srvBeOwn`, the write budget's quarter: a session's checked-out part would make more than the
  whole), moved to the new backend, the write budget refilled with its tokens and the monitor's read
  token, the old backend's tokens and the monitor's old token out for the old backend's `Close`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVLemmas
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApplyAll

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode Iris.Std go_etcd_io.etcd.server.v3.etcdserver

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The apply thread certifies a longer committed log at once** (D22 receiver epochs, S8d, W4):
from its KV ghost state at the raft log `A` and the KV log `l`, a committed raft log `A'` extending
`A` (the snapshot image's prefix: `dbImage`'s `srvRLogLb`) gives its state at `A'`, the model
`kvModel γk A'` certified, at a length not below every certified one. -/
theorem kv_cert_jump (γ : ServerRaftNames) (γk : KVNames) (E : CoPset) (hE : ↑kvcN ⊆ E)
    (A A' : List EntryModel) (l : mvcc.Log) (hA : A <+: A')
    (hlen : (kvModel γk A').length < 2 ^ 63) :
    ⊢ kvCertInv (GF := GF) γ γk -∗ kvAppliedL γ γk A l -∗ srvRLogLb γ A' ={E}=∗
      kvAppliedL γ γk A' (kvModel γk A') := by
  iintro #Hinv Ha #Hlb
  iunfold kvAppliedL at Ha
  icases Ha with ⟨#HA, Hhi, #Hc, %Hl⟩
  subst Hl
  have hpre : kvModel γk A <+: kvModel γk A' := kvRaftOf_prefix _ _ _ _ _ hA
  by_cases heq : (kvModel γk A).length = (kvModel γk A').length
  · have he : kvModel γk A = kvModel γk A' := hpre.eq_of_length heq
    imodintro
    iunfold kvAppliedL
    rw [← he]
    iframe Hlb Hhi Hc
    ipureintro; rfl
  · have hlt : (kvModel γk A).length < (kvModel γk A').length := by
      have := hpre.length_le; omega
    iunfold kvCertInv at Hinv
    iinv Hinv with >Hi Hclose
    icases Hi with ⟨%C, %hi, %Lb, HC, Hhi', #HLb, %Hok⟩
    ihave %Hhe := ghostVar_agree γk.hi _ _ _ _ $$ Hhi Hhi'
    have hfresh : C.lookup (W64 ((kvModel γk A').length : Int)) = none := by
      cases h : C.lookup (W64 ((kvModel γk A').length : Int)) with
      | none => rfl
      | some l'' =>
        obtain ⟨h1, h2, h3, -⟩ := Hok.1 _ _ h
        have := w64_len_inj _ _ hlen h3 h2
        omega
    imod ghost_map_insert_persist _ (kvModel γk A') hfresh $$ HC with ⟨HC, #He⟩
    imod ghostVar_update_halves (kvModel γk A').length γk.hi _ _ $$ Hhi Hhi' with ⟨Hhi, Hhi'⟩
    ihave %Hcmp := srvRLogLb_prefix γ A' Lb $$ [Hlb HLb]
    · iframe Hlb HLb
    have hold : ∀ n l2, C.lookup n = some l2 → l2.length ≤ (kvModel γk A').length := by
      intro n l2 hn
      have := (Hok.1 n l2 hn).1
      omega
    imod Hclose $$ [HC Hhi'] with -
    · inext
      rcases Hcmp with h | h
      · iexists C.insert (W64 ((kvModel γk A').length : Int)) (kvModel γk A'),
          (kvModel γk A').length, Lb
        iframe HC Hhi' HLb
        ipureintro
        refine ⟨?_, Hok.2⟩
        intro n l2 hn
        rw [GMap.lookup_insert_Some] at hn
        rcases hn with ⟨rfl, rfl⟩ | ⟨-, hn⟩
        · exact ⟨Nat.le_refl _, rfl, hlen, A', h, rfl⟩
        · obtain ⟨-, h2, h3, A'', h4, h5⟩ := Hok.1 n l2 hn
          exact ⟨hold n l2 hn, h2, h3, A'', h4, h5⟩
      · iexists C.insert (W64 ((kvModel γk A').length : Int)) (kvModel γk A'),
          (kvModel γk A').length, A'
        iframe HC Hhi' Hlb
        ipureintro
        refine ⟨?_, Hok.2⟩
        intro n l2 hn
        rw [GMap.lookup_insert_Some] at hn
        rcases hn with ⟨rfl, rfl⟩ | ⟨-, hn⟩
        · exact ⟨Nat.le_refl _, rfl, hlen, A', List.prefix_refl _, rfl⟩
        · obtain ⟨-, h2, h3, A'', h4, h5⟩ := Hok.1 n l2 hn
          exact ⟨hold n l2 hn, h2, h3, A'', h4.trans h, h5⟩
    imodintro
    iunfold kvAppliedL
    iframe Hlb Hhi
    isplitr
    · iunfold kvCert; iright; iexact He
    ipureintro; rfl

/-- **`s.be`'s swap** (D22 receiver epochs, S8d; see the file header): under `bemu`'s write side
(`bemuP s E.γbe 1`) with the apply thread's part of `s.be` (`srvBeOwn`), the write budget's
invariant (`srvWTPool`) moved from the current backend `d` (the apply thread's, `E.γ.kb`) to the
new one `d'` (its facts `srvBeRO d'`, write-back tokens `n'` past the receipts' bound, the
storage-version monitor's read token): `s.be` whole (at `d`), the old backend's tokens and the
monitor's old read token out, and, once `s.be` holds `d'`, `bemu`'s lock invariant and the apply
thread's half of `s.be` and quarter of the ghost variable at `d'`. -/
theorem srv_be_swap (s : Loc) (E : apply.AEnv GF) (γp : GName) (d' : mvcc.KBReal) (n' : Nat)
    (hn : receiptBound GF ≤ n' + 1) :
    srvWTPool E γp ⊢ bemuP s E.γbe 1 -∗ srvBeOwn s E -∗ srvBeRO d' -∗ ownToks d'.γB.wb n' -∗
      mvcc.bkRTx d'.γB d'.P d'.be -∗ £ 1 -∗
      |={⊤}=> ∃ d : mvcc.KBReal, ⌜E.γ.kb = some d⌝ ∗ srvBeAddr s ↦ srvBeIface d.be ∗
        (∃ n : Nat, ownToks d.γB.wb n) ∗ mvcc.bkRTx d.γB d.P d.be ∗
        (srvBeAddr s ↦ srvBeIface d'.be -∗ bemuP s E.γbe 1 ∗
          srvBeAddr s ↦{DFrac.own (1 : Qp).half} srvBeIface d'.be ∗
          dghostVar E.γbe (DFrac.own (1 : Qp).half.half) d') := by
  iintro #Hp Hbm Hbo #Hro' Htk' Hrt' Hlc
  iunfold bemuP at Hbm
  icases Hbm with ⟨%d1, Hbe1, Hg1, #Hro1⟩
  iunfold srvBeOwn at Hbo
  icases Hbo with ⟨%d, %Hd, Hbe2, Hg2⟩
  icombine Hg1 Hg2 gives %Hag
  obtain ⟨-, rfl⟩ := Hag
  icombine Hbe1 Hbe2 as Hbe
  unfold srvWTPool
  iinv Hp with ⟨%a, %n, %d2, >Ha, >Hg3, >Hn, >Hc, >%Hb, Hrt⟩ Hclose
  icombine Hg1 Hg3 gives %Hag2
  obtain ⟨-, rfl⟩ := Hag2
  icombine Hg2 Hg3 as Hg23
  icombine Hg1 Hg23 as Hg
  imod lc_fupd_elim_later (E := ⊤ \ ↑srvWTN) $$ Hlc Hrt with Hrt
  icases Hrt with (Hrt | ⟨%q, Hq⟩)
  rotate_left
  · iexfalso
    icombine Hg Hq gives %Hv
    obtain ⟨Hv, -⟩ := Hv
    exact absurd (DFrac.valid_own.1 Hv) (Qp_one_add_not_le q)
  icases (typedPointsto_half_combine (srvBeAddr s) (srvBeIface d1.be) (srvBeIface d1.be) 1)
    $$ Hbe with ⟨-, Hbe⟩
  imod dghostVar_update d' E.γbe d1 $$ Hg with Hg
  icases (dghostVar_split (GF := GF) E.γbe d' (DFrac.own (1 : Qp).half) (DFrac.own (1 : Qp).half))
    $$ [Hg] with ⟨Hgm, Hg⟩
  · rw [DFrac.op_own, Qp.half_add_half]; iexact Hg
  icases (dghostVar_split (GF := GF) E.γbe d' (DFrac.own (1 : Qp).half.half)
      (DFrac.own (1 : Qp).half.half)) $$ [Hg] with ⟨HgA, HgW⟩
  · rw [DFrac.op_own, Qp.half_add_half]; iexact Hg
  imod Hclose $$ [Ha HgW Htk' Hc Hrt'] with -
  · inext
    iexists a, n', d'
    iframe Ha HgW Htk' Hc
    isplitr
    · ipureintro; omega
    ileft; iexact Hrt'
  imodintro
  iexists d1
  iframe Hbe Hrt
  isplitr
  · ipureintro; exact Hd
  isplitl [Hn]
  · iexists n; iexact Hn
  iintro Hbe
  icases (typedPointsto_half_split (srvBeAddr s) (srvBeIface d'.be) 1).1 $$ Hbe with ⟨Hb1, Hb2⟩
  iframe Hb2 HgA
  iunfold bemuP
  iexists d'
  iframe Hb1 Hgm Hro'

end lemmas

end EtcdGrove
end Perennial
