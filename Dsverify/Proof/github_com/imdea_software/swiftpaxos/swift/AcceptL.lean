/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/AcceptL.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`acceptL`'s users on the descriptor side (swift.go, N2): `depsAccepted(deps, cmdId)` and
`markAccepted(cmdId)`, over `acceptL`'s lock invariant `swift.acceptInv` (Deliver.lean, round 8).
The internal specs (the swift group's, not frozen; notes/prove-swift.md §14):

* `depsAccepted` by a follower's descriptor of epoch `b` (its epoch pin): `true` only if each
  dependency but `x` itself is accepted here in `b` (a key of `accepted`, whose epoch is `b` by
  the pin and `delivInv`'s link `delivX`) or committed here in `b` (a `delivered` hit: the
  record's command, `exOk`, and not the leader's own since the replica is not `b`'s leader);
  `false` records `x` as waiting (no fact).
* `markAccepted(x, inLoop)` with `accepted γ r b x` (the caller's acceptance in `b`) and the pin
  (round 43, D51 (c): `epochPinQ` at the caller's `shOwnR`'s `q`, returned at that `q`): `x`
  joins `accepted`; the waiting commands go to `rechecks` (N2-loop: `inLoop`, the run loop's
  sequential descriptor; ids only, `swift.recheckOwn`) or to `recheckChan` (each by a new
  goroutine). The spec holds for either value of `inLoop`: no fact depends on the wake-up path.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.AcksSpecs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section specs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [swift.Assumptions]

/-- N2's facts of the dependencies `D` of `x` (all but `x`) in `b`. -/
def swift.depsOk (c : swift.DC) (b : Nat) (D : List swift.CommandId) (x : swift.CommandId) :
    IProp netDistGF :=
  iprop([∗list] d ∈ D, ⌜d = x⌝ ∨ sp.accepted c.γ c.r b (toCmdId d) ∨
    sp.committed c.γ c.r b (toCmdId d))

instance swift.depsOk_persistent (c : swift.DC) (b : Nat) (D : List swift.CommandId)
    (x : swift.CommandId) : Persistent (swift.depsOk c b D x) := by
  unfold swift.depsOk; infer_instance

/-- `r.depsAccepted(deps, cmdId)` (see the file header). -/
abbrev swift.Replica.depsAccepted.specIc (c : swift.DC) : Prop :=
  ∀ (b : Nat) (dsl : GoSlice) (D : List swift.CommandId) (x : swift.CommandId)
    (q : Qp),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      c.ctx ∗ swift.epochPinQ c.γxp q b ∗ swift.ownRdr c.rp c.γdl ∗ dsl ↦*□ D ∗
      ⌜c.r ≠ sp.leaderOf c.N b⌝ }}
    (App (App (Val (c.rp @!! go.GoType.PointerType swift.Replica.ty @!! go!"depsAccepted"))
      (Val #dsl)) (Val #x))
  {{ (ok : Bool), RET #ok; swift.epochPinQ c.γxp q b ∗ swift.ownRdr c.rp c.γdl ∗
      (⌜ok = false⌝ ∨ swift.depsOk c b D x) }}

/-- `swift.Replica.depsAccepted.specI` at every record (round 44, D53 (1): the per-record form `swift.Replica.depsAccepted.specIc`). -/
abbrev swift.Replica.depsAccepted.specI : Prop :=
  ∀ c : swift.DC, swift.Replica.depsAccepted.specIc c

/-- `r.markAccepted(x)` (see the file header). -/
abbrev swift.Replica.markAccepted.specI : Prop :=
  ∀ (c : swift.DC) (b : Nat) (x : swift.CommandId) (inLoop : Bool) (q : Qp),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      c.ctx ∗ swift.epochPinQ c.γxp q b ∗ sp.accepted c.γ c.r b (toCmdId x) }}
    (App (App (Val (c.rp @!! go.GoType.PointerType swift.Replica.ty @!! go!"markAccepted"))
      (Val #x)) (Val #inLoop))
  {{ RET #(); swift.epochPinQ c.γxp q b }}

end specs

section lemmas
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics]
variable [swift.Assumptions]

/-- The accepted map's epoch is the pin's: `delivInv` links `γa` to the record's epoch, which
the pin fixes. -/
theorem swift.acceptEpoch (γ : sp.Names) (N r : Nat) (γdl γx γxp γxm γa γxe γrm : GName)
    (str : swift.CommandId → GoString) (q : Qp) (b bA : Nat) :
    inv swift.delivN (swift.delivInv γ N r γdl γx γxp γxm γa γxe γrm str) ∗ swift.epochPinQ γxp q b ∗
      ghostVar γa (1 : Qp).half bA ⊢
    |={⊤}=> swift.epochPinQ γxp q b ∗ ghostVar γa (1 : Qp).half bA ∗ ⌜bA = b⌝ := by
  iintro ⟨#HdI, Hpin, Ha⟩
  iinv HdI with Hi Hclose
  iunfold swift.delivInv at Hi
  icases Hi with ⟨%M, %bX, %X, %Mx, %rm, >HV, >HXi, >HXeD, >HMx, >HXx, >%HM⟩
  icases HXx with ⟨HXx, HFz⟩
  ihave ⟨Hpin, HXeD, %Hag⟩ := swift.epochPinQ_agree γxp q b bX rm $$ [Hpin HXeD]
  · iframe Hpin HXeD
  iunfold swift.delivX at HXx
  icases HXx with ⟨%bA', Ha', HXok, %HbA, HRm⟩
  ihave %Hag2 := ghostVar_agree γa bA (1 : Qp).half bA' (1 : Qp).half $$ Ha Ha'
  imod Hclose $$ [HV HXi HXeD HMx Ha' HXok HRm HFz] with -
  · inext; iunfold swift.delivInv; iexists M, bX, X, Mx, rm; iframe
    isplitl
    · iunfold swift.delivX; iexists bA'; iframe; ipureintro; exact HbA
    · ipureintro; exact HM
  imodintro
  iframe
  ipureintro
  rw [Hag2, HbA Hag.1, Hag.2]

end lemmas

section proofs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [swift.Assumptions]

set_option goose.wp.extras true

theorem swift.Replica.markAccepted.wp_proof : swift.Replica.markAccepted.specI := by
  intro c b x inLoop q
  haveI := swift.hlog.cmdId_intoValInj (sem := sem)
  wp_start as ⟨#Hctx, Hpin, #Hacc⟩
  ihave #Hctx2 := Hctx
  iunfold swift.DC.ctx at Hctx2
  iunfold swift.descCtxE at Hctx2
  icases Hctx2 with ⟨%me, %fr, %lg, %dm, %dc, %ex, %dr, %oe, %γa, %γrm, %rc, %γrc, -, -, %Hids, -, -, -,
    -, -, -, -, -, #HdI, -, -, -, -, #HacL, #Hrcf, #Hrcb, -⟩
  wp_auto
  wp_apply sync.Mutex.wp_Lock $$ [$HacL] as ⟨Hlk, HA⟩
  iunfold swift.acceptInv at HA
  icases HA with ⟨%am, %wm, %A, %W, %bA, Haf, HAm, Hwf, HWm, HWents, Ha, #HAents, Hrk⟩
  iapply fupd_wp
  imod swift.acceptEpoch c.γ c.N c.r c.γdl c.γx c.γxp c.γxm γa c.γxe γrm c.str q b bA $$ [HdI Hpin Ha]
    with ⟨Hpin, Ha, %HbA⟩
  · iframe HdI Hpin Ha
  imodintro
  subst HbA
  wp_auto
  wp_apply wp_mapInsert $$ [$HAm] as HAm
  try wp_auto
  wp_apply wp_map_lookup1 $$ [$HWm] as HWm
  try wp_auto
  wp_apply wp_mapDelete $$ [$HWm] as HWm
  ihave ⟨⟨%ids0, Hws, Hwscap⟩, HWents⟩ : (∃ ids : List swift.CommandId,
      ((W !! x).getD (Perennial.zero_val GoSlice)) ↦* ids ∗
      ownSliceCap swift.CommandId ((W !! x).getD (Perennial.zero_val GoSlice)) (DFrac.own 1)) ∗
    ([∗map] _w ↦ sl ∈ GMap.delete x W, ∃ ids : List swift.CommandId, sl ↦* ids ∗
      ownSliceCap swift.CommandId sl (DFrac.own 1)) $$ [HWents]
  · cases hW : W !! x with
    | none =>
      rw [GMap.delete_notin W x hW]
      iframe HWents
      iexists []
      simp only [Option.getD_none]
      isplitl
      · iapply (ownSlice_nil (V := swift.CommandId))
      · iapply (ownSliceCap_nil (V := swift.CommandId))
    | some sl =>
      iapply (BigSepM.bigSepM_delete hW).1 $$ HWents
  try wp_auto
  ipersist r
  -- N2-loop: `inLoop`: the waiting commands join `rechecks` and `ws` becomes nil
  wp_join (iprop(∃ (wsl : GoSlice) (ids : List swift.CommandId),
      "ws" ∷ ws_ptr ↦ wsl ∗ "Hws" ∷ wsl ↦* ids ∗ "Hrk" ∷ swift.recheckOwn c.rp) : IProp netDistGF)
    with [ws Hws Hwscap Hrk] as ⟨%wsl, %ids, ws, Hws, Hrk⟩
  · iunfold swift.recheckOwn at Hrk
    icases Hrk with ⟨%rk, %rids, Frk, Hrks, Hrkcap⟩
    try wp_auto
    wp_apply wp_slice_append $$ [Hrks Hrkcap Hws] as %rk' ⟨Hrks, Hrkcap, -⟩
    · iframe
    try wp_auto
    try wp_join_done
    iexists slice.nil, ([] : List swift.CommandId)
    iframe ws
    isplitr
    · iapply (ownSlice_nil (V := swift.CommandId) (DFrac.own 1))
    iunfold swift.recheckOwn
    iexists rk', _
    iframe
  wp_apply sync.Mutex.wp_Unlock $$ [$HacL $Hlk Haf HAm Hwf HWm HWents Ha Hrk]
  · iunfold swift.acceptInv
    iexists am, wm, _, _, bA
    iframe
    imodintro
    iintro %d %hd
    by_cases e : d = x
    · subst e; iexact Hacc
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm e)] at hd
      iapply HAents $$ %d %hd
  try wp_auto
  ihave %Hwl := ownSlice_len _ _ _ $$ Hws
  ihave HL : (∃ (i : w64) (wv : swift.CommandId),
      "i" ∷ i_ptr ↦ i ∗ "w" ∷ w_ptr ↦ wv ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z wsl.len⌝ : IProp netDistGF) $$ [i w]
  · iexists (W64 0), _; iframe; ipureintro; exact ⟨by decide, by word⟩
  wp_for HL
  wp_if_destruct
  · have hlt : sint.Z i < sint.Z wsl.len := by
      exact Hif
    have hiD : sint.nat i < ids.length := by rw [Hwl.1]; word
    have hb : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z wsl.len := ⟨Hi.1, hlt⟩
    rw [ite_eq_left hb]
    wp_apply wp_load_slice_index (t := swift.CommandId.ty) wsl (sint.Z i) ids _ ids[sint.nat i]
      Hi.1 $$ [Hws] as Hws
    · iframe Hws; ipureintro; exact List.getElem?_eq_getElem hiD
    try wp_auto
    wp_apply wp_fork
    · wp_auto
      wp_apply wp_bag_send (t := swift.CommandId.ty) γrc rc _ (fun (_ : swift.CommandId) => iprop(True))
        $$ [$Hrcb]
      itrivial
    try wp_auto
    wp_for_post
    iframe
    iexists _, _
    iframe
    ipureintro; exact ⟨by word, by word⟩
  · try wp_auto
    iapply HΦ
    iexact Hpin

/-- At the records of one `str` (round 44, D53 (1)). -/
theorem swift.Replica.depsAccepted.wp_proof (str : swift.CommandId → GoString)
    (hinj : Function.Injective str)
    (wp_String0 : swift.CommandId.String.specS str)
    (wp_HasV : ∀ dm γdl, swift.cmapHasV.spec dm γdl) :
    ∀ c : swift.DC, c.str = str → swift.Replica.depsAccepted.specIc c := by
  intro c hc b dsl D x q
  have hstr : ∀ _c : swift.DC, Function.Injective c.str := fun _ => hc ▸ hinj
  have wp_String : ∀ _c : swift.DC, swift.CommandId.String.specS c.str := fun _ => hc ▸ wp_String0
  haveI := swift.hlog.cmdId_intoValInj (sem := sem)
  wp_start as ⟨#Hctx, Hpin, HrdR, #HD, %Hnl⟩
  ihave #Hctx2 := Hctx
  iunfold swift.DC.ctx at Hctx2
  iunfold swift.descCtxE at Hctx2
  icases Hctx2 with ⟨%me, %fr, %lg, %dm, %dc, %ex, %dr, %oe, %γa, %γrm, %rc, %γrc, -, -, %Hids, -, -, -,
    -, -, -, #Hdm, #Hcm, #HdI, -, -, -, -, #HacL, -, -, -⟩
  wp_auto
  wp_apply wp_with_defer as %defer Hdefer
  try wp_auto
  wp_apply sync.Mutex.wp_Lock $$ [$HacL] as ⟨Hlk, HA⟩
  iunfold swift.acceptInv at HA
  icases HA with ⟨%am, %wm, %A, %W, %bA, Haf, HAm, Hwf, HWm, HWents, Ha, #HAents, Hrk⟩
  iapply fupd_wp
  imod swift.acceptEpoch c.γ c.N c.r c.γdl c.γx c.γxp c.γxm γa c.γxe γrm c.str q b bA $$ [HdI Hpin Ha]
    with ⟨Hpin, Ha, %HbA⟩
  · iframe HdI Hpin Ha
  imodintro
  subst HbA
  try wp_auto
  ihave %HDl := ownSlice_len _ _ _ $$ HD
  ipersist r
  ipersist cmdId
  ihave HL : (∃ (i : w64) (dv : swift.CommandId),
      "i" ∷ i_ptr ↦ i ∗ "d" ∷ d_ptr ↦ dv ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z dsl.len⌝ ∗
      "#Hok" ∷ swift.depsOk c bA (D.take (sint.nat i)) x : IProp netDistGF) $$ [i d]
  · iexists (W64 0), _; iframe
    isplitr
    · ipureintro; exact ⟨by decide, by word⟩
    · rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero]
      iunfold swift.depsOk
      iapply BigSepL.bigSepL_nil.2
      itrivial
  wp_for HL
  wp_if_destruct
  · have hlt : sint.Z i < sint.Z dsl.len := by
      first | exact Hif | exact of_decide_eq_true (go.intoVal_inj Hif)
    have hiD : sint.nat i < D.length := by rw [HDl.1]; word
    rw [ite_eq_left ⟨Hi.1, hlt⟩]
    wp_apply wp_load_slice_index (t := swift.CommandId.ty) dsl (sint.Z i) D _ D[sint.nat i]
      Hi.1 $$ [HD] as -
    · iframe HD; ipureintro; exact List.getElem?_eq_getElem hiD
    try wp_auto
    have htake : D.take (sint.nat (i + W64 1)) = D.take (sint.nat i) ++ [D[sint.nat i]] := by
      rw [show sint.nat (i + W64 1) = sint.nat i + 1 by word, List.take_add_one,
        List.getElem?_eq_getElem hiD]; rfl
    generalize hdj : D[sint.nat i] = dj at *
    -- `d == cmdId`: continue with `d = x`
    wp_join (v := #(decide (dj = x))) iprop(True) at (if: #(decide (dj.ClientId' = x.ClientId')) then _ else _)
    · by_cases hc : dj.ClientId' = x.ClientId'
      · rw [decide_eq_true hc]
        wp_auto
        isplitr
        · ipureintro
          have : (dj.SeqNum' = x.SeqNum') ↔ (dj = x) := by
            cases dj; cases x; simp_all
          rw [decide_eq_decide.mpr this]
        · itrivial
      · rw [decide_eq_false hc]
        wp_auto
        isplitr
        · ipureintro
          rw [decide_eq_false (show ¬ dj = x by intro h; exact hc (h ▸ rfl))]
        · itrivial
    iintro -
    try wp_auto
    by_cases hyx : dj = x
    · rw [decide_eq_true hyx]
      try wp_auto
      wp_for_post
      iframe
      iexists _, _
      iframe
      isplitr
      · ipureintro; exact ⟨by word, by word⟩
      · rw [htake]; iunfold swift.depsOk; iunfold swift.depsOk at Hok
        iapply BigSepL.bigSepL_snoc.2
        iframe Hok
        ileft; ipureintro; exact hyx
    rw [decide_eq_false hyx]
    try wp_auto
    wp_apply wp_map_lookup2 $$ [$HAm] as HAm
    try wp_auto
    cases hA : (A !! dj).isSome
    · try rw [hA]
      try wp_auto
      wp_apply (wp_String c) $$ [$d] as d
      ihave Hb : iprop(|={⊤}=> github_com.orcaman.concurrent_map.readerV dm c.γdl swift.deliveredR ∗
          (github_com.orcaman.concurrent_map.readerV dm c.γdl swift.deliveredR ={⊤}=∗ swift.ownRdr c.rp c.γdl)) $$ [HrdR]
      · iapply swift.ownRdr_take; iframe Hdm HrdR
      iapply fupd_wp
      imod Hb with ⟨Hrdr, Hback⟩
      imodintro
      wp_method_call
      try wp_auto
      try wp_method_call
      try wp_auto
      wp_apply (wp_HasV dm c.γdl (c.str dj)
          ((⊤ \ ↑github_com.orcaman.concurrent_map.cmapN) \ (↑swift.delivN : CoPset))
          (fun ok => iprop((⌜ok = false⌝ ∨ sp.committed c.γ c.r bA (toCmdId dj)) ∗
            swift.epochPinQ c.γxp q bA))) $$ [$Hrdr Hpin] as %ok ⟨Hrdr, #Hcom, Hpin⟩
      · imod (inv_acc (E := ⊤ \ ↑github_com.orcaman.concurrent_map.cmapN) (N := swift.delivN)
          swift.delivN_sub) $$ HdI with ⟨Hi, Hclose⟩
        iunfold swift.delivInv at Hi
        icases Hi with ⟨%M, %bX', %X', %Mx, %rm, >HV, >HXi, >HXeD, >HMx, >HXx, >%HM⟩
        icases HXx with ⟨HXx, HFz⟩
        ihave ⟨Hpin, HXeD, %Hag⟩ := swift.epochPinQ_agree c.γxp q bA bX' rm $$ [Hpin HXeD]
        · iframe Hpin HXeD
        obtain ⟨rfl, rfl⟩ := Hag
        ihave #Hcom : iprop(⌜(M.lookup (c.str dj)).isSome = false⌝ ∨
            sp.committed c.γ c.r bX' (toCmdId dj)) $$ [HXx]
        · cases hM : (M.lookup (c.str dj)) with
          | none => ileft; ipureintro; rfl
          | some v =>
            iright
            obtain ⟨e, he, hk⟩ := HM.1 _ v hM
            have hej : e.1 = dj := (hstr c hk).symm
            obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp he
            iunfold swift.delivX at HXx
            icases HXx with ⟨%bA', -, HXok, -⟩
            ihave Hej := (BigSepL.bigSepL_lookup hj) $$ HXok
            iunfold swift.exOk at Hej
            icases Hej with (#Hc | %Hl)
            · rw [hej]; iexact Hc
            · exact absurd Hl Hnl
        imodintro
        iexists M
        iframe HV
        iintro HV
        imod Hclose $$ [HV HXi HXeD HMx HXx HFz] with -
        · inext; iunfold swift.delivInv; iexists M, bX', X', Mx, false; iframe; ipureintro; exact HM
        imodintro
        iframe Hpin
        icases Hcom with (%Hn | #Hc)
        · ileft; ipureintro; exact Hn
        · iright; iexact Hc
      iapply fupd_wp
      imod Hback $$ Hrdr with HrdR
      imodintro
      cases ok
      · -- not accepted, not delivered: `x` waits for `d`
        try wp_auto
        wp_apply wp_map_lookup1 $$ [$HWm] as HWm
        ihave ⟨⟨%ids, Hws, Hwscap⟩, HWents⟩ : (∃ ids : List swift.CommandId,
            ((W !! dj).getD (Perennial.zero_val GoSlice)) ↦* ids ∗
            ownSliceCap swift.CommandId ((W !! dj).getD (Perennial.zero_val GoSlice)) (DFrac.own 1)) ∗
          ([∗map] _w ↦ sl ∈ GMap.delete dj W, ∃ ids : List swift.CommandId, sl ↦* ids ∗
            ownSliceCap swift.CommandId sl (DFrac.own 1)) $$ [HWents]
        · cases hW : W !! dj with
          | none =>
            rw [GMap.delete_notin W dj hW]
            iframe HWents
            iexists []
            simp only [Option.getD_none]
            isplitl
            · iapply (ownSlice_nil (V := swift.CommandId))
            · iapply (ownSliceCap_nil (V := swift.CommandId))
          | some sl =>
            iapply (BigSepM.bigSepM_delete hW).1 $$ HWents
        try wp_auto
        wp_apply wp_slice_literal (V := swift.CommandId) [x]
        isplitr
        · ipureintro; rfl
        iintro %s1 ⟨Hs1, -⟩
        try wp_auto
        wp_apply wp_slice_append $$ [Hws Hwscap Hs1] as %nsl ⟨Hws, Hwscap, -⟩
        · iframe
        try wp_auto
        wp_apply wp_mapInsert $$ [$HWm] as HWm
        try wp_auto
        wp_for_post
        simp only [sync.isMutex_unseal, sync.isMutexDef, sync.ownMutex_unseal, sync.ownMutexDef]
        wp_apply wp_lock_unlock $$ [$HacL $Hlk Haf HAm Hwf HWm HWents Ha Hws Hwscap Hrk]
        · iunfold swift.acceptInv
          iexists am, wm, A, _, bA
          iframe
          isplitl
          · iapply (BigSepM.bigSepM_insert_delete (Φ := fun (_ : swift.CommandId) (sl : GoSlice) =>
              iprop(∃ ids : List swift.CommandId, sl ↦* ids ∗
                ownSliceCap swift.CommandId sl (DFrac.own 1)))).2
            iframe HWents
            iexists _; iframe
          · first | iexact HAents | (inext; imodintro; iexact HAents) | (imodintro; iexact HAents)
        iapply HΦ
        iframe Hpin HrdR
        ileft; ipureintro; rfl
      · -- delivered: committed here in `b`
        try wp_auto
        wp_for_post
        iframe
        iexists _, _
        iframe
        isplitr
        · ipureintro; exact ⟨by word, by word⟩
        · rw [htake]; iunfold swift.depsOk; iunfold swift.depsOk at Hok
          iapply BigSepL.bigSepL_snoc.2
          iframe Hok
          iright; iright
          icases Hcom with (%Hn | #Hc)
          · exact absurd Hn (by decide)
          · iexact Hc
    · -- accepted in `b`
      try rw [hA]
      try wp_auto
      wp_for_post
      iframe
      iexists _, _
      iframe
      isplitr
      · ipureintro; exact ⟨by word, by word⟩
      · rw [htake]; iunfold swift.depsOk; iunfold swift.depsOk at Hok
        iapply BigSepL.bigSepL_snoc.2
        iframe Hok
        iright; ileft
        iapply HAents $$ %dj %hA
  · -- the loop ends: every dependency checked
    have hn : ¬ sint.Z i < sint.Z dsl.len := by
      first | exact Hif | (intro h; exact Hif (by rw [decide_eq_true h])) | simpa using Hif
    have hge : D.length ≤ sint.nat i := by rw [HDl.1]; word
    try (rw [decide_eq_false hn]; simp only [decide_true, ite_true, ↓reduceIte])
    try wp_auto
    wp_apply sync.Mutex.wp_Unlock $$ [$HacL $Hlk Haf HAm Hwf HWm HWents Ha Hrk]
    · iunfold swift.acceptInv
      iexists am, wm, A, W, bA
      iframe
      first | iexact HAents | (inext; imodintro; iexact HAents) | (imodintro; iexact HAents)
    iapply HΦ
    iframe Hpin HrdR
    iright
    rw [List.take_of_length_le hge] at *
    iexact Hok

end proofs

end Perennial.github_com.imdea_software.swiftpaxos
