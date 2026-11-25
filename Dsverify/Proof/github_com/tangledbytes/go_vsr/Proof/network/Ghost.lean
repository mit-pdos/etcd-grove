/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Proof/network/Ghost.lean (lab master 915f964;
notes/dsv-vr.md): over any `GF`, on the net extension. What changed: a connection end is
`network.connL c cn s` (some `net.connAt c cn s a la ra`, persistent; ids `Nat`), whose agreement
(`connAt_agree`) is the `*TCPConn`'s read-only `conn` field and `endId`'s injectivity, instead of
the lab's `net.ownTCPConn_agree`; the net model's errors are `net.resErr`'s (`resErr_errOrNil`: an
`*OpError`, whose `Error()` is the extension's `AnyString`), instead of the lab's `net.opErr`/
`net.connErr`; `slog.Debug` is the hypothesis `log.slog.Debug.spec` (`wp_Debug`, LibHyps.lean),
instead of the lab model's `wp_Debug_gen`.
-/
/-
Ghost lemmas of the network package (the names' agreement, the lock's resource, the
registry, the sender's pool).
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.network
public import Dsverify.Spec.log.slog.Logger
public import Net.Proof.net.Errors
public import Proof.net.ErrOrNil

@[expose] public section

noncomputable section

namespace Perennial.github_com.tangledbytes.go_vsr.pkg

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net VsrModel

-- (no local `gooseInvGS` instance: the lemmas' update modalities are `HeapGS`'s, the WP's)

section connL
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]

/-- The `*TCPConn` `c` is the end `s` of `cn` (some dialed address and local/remote addresses;
persistent): what `Defs.lean`'s registry and pool keep of a connection. -/
abbrev network.connL (c : Loc) (cn : Nat) (s : Bool) : IProp GF :=
  iprop(∃ (a : GoString) (la ra : GoInterface), net.connAt c cn s a la ra)

end connL

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : network.Assumptions] [π : NetProtoGS]

theorem network.threeQuarters_invalid :
    ¬ ((((1 : Qp).half + (1 : Qp).half.half) + ((1 : Qp).half + (1 : Qp).half.half)).val ≤ 1) := by
  intro h
  have h1 : ((1 : Qp).half + (1 : Qp).half.half) + ((1 : Qp).half + (1 : Qp).half.half) =
      1 + (1 : Qp).half := by
    rw [show ((1 : Qp).half + (1 : Qp).half.half) + ((1 : Qp).half + (1 : Qp).half.half) =
      ((1 : Qp).half + (1 : Qp).half) + ((1 : Qp).half.half + (1 : Qp).half.half) by
        apply Subtype.ext; simp; grind]
    rw [Qp.half_add_half, Qp.half_add_half]
  rw [h1] at h
  exact Qp_one_add_not_le _ h

/-- Two shares of a pointer's points-to sum to at most one. -/
theorem network.loc_pointsto_frac_valid (l : Loc) (q1 q2 : Qp) (v1 v2 : Loc) :
    typedPointsto l v1 (DFrac.own q1) ∗ typedPointsto l v2 (DFrac.own q2) ⊢
      (⌜(q1 + q2).val ≤ 1⌝ : IProp GF) := by
  have e1 : ∀ (v : Loc) (q : Qp), typedPointstoDef (GF := GF) l v (DFrac.own q) =
      heapPointsto l (DFrac.own q) #v := fun _ _ => rfl
  rw [typedPointsto_unseal]
  unfold typedPointstoWrap
  simp only [e1]
  iintro ⟨⟨H1', -⟩, ⟨H2', -⟩⟩
  icombine H1' H2' gives % ⟨h, -⟩
  ipureintro
  exact h

theorem network.mask_ndot_ne {A : Type} [Pos.Countable A] (N : Namespace) (x y : A)
    (h : x ≠ y) : (↑(N.@x) : CoPset) ⊆ ⊤ \ ↑(N.@y) := by
  intro p hp
  rw [LawfulSet.mem_diff]
  exact ⟨CoPset.mem_full, fun h' => ndot_ne_disjoint N h p ⟨hp, h'⟩⟩

/-- The names of a TCP agree. -/
theorem network.rootInv_agree (tcp : Loc) (ns1 ns2 : network.TcpNames) :
    network.rootInv (GF := GF) tcp ns1 ∗ network.rootInv tcp ns2 ⊢ |={⊤}=> ⌜ns1 = ns2⌝ := by
  by_cases h : ns1.toList = ns2.toList
  · iintro -; imodintro; ipureintro; exact network.TcpNames.toList_inj h
  unfold network.rootInv
  iintro ⟨#H1, #H2⟩
  iinv H1 with ⟨%m1, >Hm1⟩ Hclose1
  have hm : (↑(network.rootN ns2) : CoPset) ⊆ ⊤ \ ↑(network.rootN ns1) :=
    network.mask_ndot_ne _ _ _ (Ne.symm h)
  iinv H2 with ⟨%m2, >Hm2⟩ Hclose2
  ihave %hv := network.loc_pointsto_frac_valid _ _ _ m1 m2 $$ [$Hm1 $Hm2]
  exact absurd hv network.threeQuarters_invalid

instance network.srcMarks_timeless (ns : network.TcpNames) (S : GMap GoString Unit) :
    Timeless (iprop([∗map] s ↦ _u ∈ S, network.srcMark (GF := GF) ns s)) := by
  apply BigSepM.bigSepM_timeless_inst

set_option synthInstance.maxHeartbeats 400000 in
set_option synthInstance.maxSize 512 in
instance network.lockP_timeless (ns : network.TcpNames) (cm sm : Loc) (q : Qp) :
    Timeless (network.lockP (GF := GF) ns cm sm q) := by
  unfold network.lockP network.entryOk; infer_instance

theorem network.wholeLines_nil (γ : VsrGhost.Names) :
    ⊢ network.wholeLines (GF := GF) γ [] := by
  unfold network.wholeLines
  iexists []
  isplit
  · ipureintro; rfl
  isplit
  · ipureintro; intro m hm; cases hm
  · iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2
    itrivial

/-- The sender takes the send token of `c`, a connection in the map (registered, not dead):
from its pool, or from the registry (then it is in its pool from now on). Its stream is whole
lines (a dead connection is not in the map). -/
theorem network.take_conn (ns : network.TcpNames) (c : Loc) (x : network.ConnRec) (q : Qp)
    (D T : GMap Loc Unit) (hD : D.lookup c = none) :
    inv network.regN (network.regInv ns) ∗ £ 1 ∗ network.regd ns c x ∗
      ghostMapAuth ns.dead q D ∗ ghostMapAuth ns.held 1 T ∗
      ([∗map] c' ↦ _u ∈ T, network.poolEntry ns c') ⊢
    |={⊤}=> ghostMapAuth ns.dead q D ∗ ∃ (T' : GMap Loc Unit) (W : List w8),
      ghostMapAuth ns.held 1 T' ∗ network.connL c x.1 x.2.1 ∗
      sendTok x.1 x.2.1 (VsrWire.protoOf ns.sys) W ∗ network.wholeLines ns.sys W ∗
      (network.poolEntry ns c -∗ [∗map] c' ↦ _u ∈ T', network.poolEntry ns c') := by
  iintro ⟨#Hreg, Hlc, #Hx, HD, HT, Hpool⟩
  cases hT : T.lookup c with
  | some u =>
    icases (BigSepM.bigSepM_lookup_acc (PROP := IProp GF) (Φ := fun c' (_u : Unit) => network.poolEntry ns c')
      (m := T) (i := c) (x := u) hT).1 $$ Hpool with ⟨He, Hback⟩
    unfold network.poolEntry
    icases He with ⟨%x', %W, #Hx', #Hc, Hs, Hw⟩
    icombine Hx Hx' gives % ⟨-, hxx⟩
    subst hxx
    icases Hw with (Hw | #Hd)
    · imodintro
      iframe HD
      iexists T, W
      iframe
      iframe Hc
    · icombine HD Hd gives %hd
      rw [hD] at hd
      cases hd
  | none =>
    have hm : (↑network.regN : CoPset) ⊆ ⊤ := CoPset.subseteq_top
    iinv Hreg with Hi Hclose
    imod lc_fupd_elim_later $$ Hlc Hi with Hi
    unfold network.regInv
    icases Hi with ⟨%R, HR, HRm⟩
    icombine HR Hx gives %hR
    icases (BigSepM.bigSepM_lookup_acc (PROP := IProp GF) (Φ := fun c' x' => network.regEntry ns c' x')
      (m := R) (i := c) (x := x) hR).1 $$ HRm with ⟨He, Hback⟩
    unfold network.regEntry
    icases He with ⟨Hfr, #Hc, (Hs | #Hh)⟩
    · imod ghost_map_insert_persist c () hT $$ HT with ⟨HT, #Hh⟩
      imod Hclose $$ [HR Hback Hfr] with -
      · inext
        iexists R
        iframe HR
        iapply Hback
        iframe Hfr Hc Hh
      imodintro
      iframe HD
      iexists _, []
      iframe HT Hc Hs
      isplitr
      · iapply network.wholeLines_nil
      · iintro He
        iapply (BigSepM.bigSepM_insert (PROP := IProp GF) (Φ := fun c' (_u : Unit) => network.poolEntry ns c')
          (m := T) (i := c) (x := ()) hT).2
        iframe
    · icombine HT Hh gives %hh
      rw [hT] at hh
      cases hh

/-- A connection's ends' ids are in range (`netConnAt`). -/
theorem network.connAt_bound (c : Loc) (cn : Nat) (s : Bool) (a : GoString) (la ra : GoInterface) :
    net.connAt (GF := GF) c cn s a la ra ⊢ ⌜2 * cn + 1 < 2 ^ 64⌝ := by
  iintro #H
  ihave #Hc := net.connAt_conn c cn s a la ra $$ H
  unfold netConnAt
  icases Hc with ⟨%γ, -, %h⟩
  ipureintro; exact h.2.2

/-- An end determines its connection and side (the `*TCPConn`'s read-only `conn` holds the end's
id, `endId`, injective in range). -/
theorem network.connAt_agree (c : Loc) (cn1 cn2 : Nat) (s1 s2 : Bool) (a1 a2 : GoString)
    (la1 ra1 la2 ra2 : GoInterface) :
    net.connAt (GF := GF) c cn1 s1 a1 la1 ra1 ∗ net.connAt c cn2 s2 a2 la2 ra2 ⊢
      ⌜cn1 = cn2 ∧ s1 = s2⌝ := by
  iintro ⟨#H1, #H2⟩
  ihave %hb1 := network.connAt_bound c cn1 s1 a1 la1 ra1 $$ H1
  ihave %hb2 := network.connAt_bound c cn2 s2 a2 la2 ra2 $$ H2
  unfold net.connAt
  icases H1 with ⟨%nw1, -, #Ht1, -⟩
  icases H2 with ⟨%nw2, -, #Ht2, -⟩
  icombine Ht1 Ht2 gives %h
  ipureintro
  simp only [net.TCPConn.mk.injEq, net.conn.mk.injEq] at h
  exact endId_inj hb1 hb2 h.1

/-- `connL` agreement. -/
theorem network.connL_agree (c : Loc) (cn1 cn2 : Nat) (s1 s2 : Bool) :
    network.connL (GF := GF) c cn1 s1 ∗ network.connL c cn2 s2 ⊢ ⌜cn1 = cn2 ∧ s1 = s2⌝ := by
  iintro ⟨⟨%a1, %la1, %ra1, #H1⟩, ⟨%a2, %la2, %ra2, #H2⟩⟩
  iapply network.connAt_agree c cn1 cn2 s1 s2 a1 a2 la1 ra1 la2 ra2 $$ [$H1 $H2]

/-- A held connection's stream, whole, as `Send`'s callback takes it. -/
theorem network.wstream_of_pool (ns : network.TcpNames) (c : Loc) (x : network.ConnRec)
    (W : List w8) :
    isPkgInit (PROP := IProp GF) pkg_id.net ∗
    network.connL (GF := GF) c x.1 x.2.1 ∗ sendTok x.1 x.2.1 (VsrWire.protoOf ns.sys) W ∗
      network.wholeLines ns.sys W ⊢
    events.wstream ns.sys (interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #c) true := by
  unfold events.wstream network.wholeLines
  iintro ⟨#Hnet, ⟨%a, %la, %ra, #Hc⟩, Hs, Hw⟩
  iexists x.1, x.2.1, a, W
  iframe Hs Hnet
  isplitr
  · unfold net.isConn
    iexists c, la, ra
    iframe Hc
    ipureintro; rfl
  simp only [ite_true]
  iexact Hw

/-- The stream back from the callback, into the pool: whole, or the connection is dead. -/
theorem network.pool_of_wstream (ns : network.TcpNames) (c : Loc) (x : network.ConnRec)
    (b : Bool) :
    events.wstream ns.sys (interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #c) b ∗
      network.regd (GF := GF) ns c x ∗ network.connL c x.1 x.2.1 ∗ (⌜b = true⌝ ∨ network.deadMark ns c) ⊢
    network.poolEntry ns c := by
  unfold events.wstream network.poolEntry
  iintro ⟨⟨%cid, %side, %a', %W, #Hic, -, Hs, Hw⟩, #Hx, #Hc, Hb⟩
  unfold net.isConn
  icases Hic with ⟨%c', %la', %ra', %hw, #Hc'⟩
  have hc : c' = c := by
    simp [interface.mkOk] at hw
    exact (go.intoVal_inj hw).symm
  subst hc
  ihave %hag := network.connL_agree c' x.1 cid x.2.1 side $$ [$Hc]
  · iexists a', la', ra'; iexact Hc'
  obtain ⟨h1, h2⟩ := hag
  subst h1 h2
  iexists x, W
  iframe Hx Hc Hs
  icases Hb with (%hb | #Hd)
  · subst hb
    simp only [ite_true]
    ileft
    unfold network.wholeLines
    iexact Hw
  · iright; iexact Hd

/-- An error result is a log argument. -/
theorem network.argOk_of_errOrNil (e : GoInterface) :
    bufio.errOrNil (GF := GF) e ⊢ log.slog.argOk e := by
  unfold bufio.errOrNil log.slog.argOk
  iintro (%he | ⟨#Ha, -⟩)
  · ileft; ipureintro; intro ii h; subst he; cases h
  · iright; ileft; iexact Ha

/-- Arguments that are all `nil` or `fmt.ArgWf`-ok are log arguments. -/
theorem network.argsOk_of_wf (xs : List GoInterface) (h : fmt.ArgsWf xs) :
    ⊢ [∗list] x ∈ xs, log.slog.argOk (GF := GF) x := by
  induction xs with
  | nil => iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2; itrivial
  | cons x xs ih =>
    iapply (BigSepL.bigSepL_cons (PROP := IProp GF)).2
    isplitr
    · unfold log.slog.argOk; ileft; ipureintro
      intro ii hx; subst hx; exact h ii (List.mem_cons_self ..)
    · iapply ih (fun ii hi => h ii (List.mem_cons_of_mem _ hi))

/-- `slog.Debug(msg, args...)`, the arguments all `nil` or `fmt.ArgWf`-ok. -/
theorem network.wp_debug_wf (wp_Debug : log.slog.Debug.spec (GF := GF) (hG := hG))
    (msg : GoString) (sl : GoSlice) (xs : List GoInterface) (h : fmt.ArgsWf xs) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.log.slog ∗ sl ↦* xs }}
      (App (App (Val (@! log.slog.Debug)) (Val #msg)) (Val #sl))
    {{ RET #(); True }} := by
  wp_start_folded as Hsl
  ihave #Ha := network.argsOk_of_wf xs h
  wp_apply wp_Debug msg sl xs (DFrac.own 1) $$ [$Hsl $Ha]
  iintro -
  iapply HΦ; itrivial

/-- `slog.Debug(msg, "err", e)` for an error result `e`. -/
theorem network.wp_debug_err (wp_Debug : log.slog.Debug.spec (GF := GF) (hG := hG))
    (msg s : GoString) (sl : GoSlice) (e : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.log.slog ∗ bufio.errOrNil e ∗
        sl ↦* [interface.mkOk go.string #s, e] }}
      (App (App (Val (@! log.slog.Debug)) (Val #msg)) (Val #sl))
    {{ RET #(); True }} := by
  wp_start_folded as ⟨#He, Hsl⟩
  ihave #Ha := network.argOk_of_errOrNil e $$ He
  wp_apply wp_Debug msg sl _ (DFrac.own 1) $$ [$Hsl]
  · iapply (BigSepL.bigSepL_cons (PROP := IProp GF)).2
    isplitr
    · unfold log.slog.argOk; ileft; ipureintro
      intro ii h
      simp [interface.mkOk] at h
      subst h
      exact ⟨fun _ => ⟨s, rfl⟩, fun hi => absurd hi fmt.not_isIntArgType_string, Or.inl (Or.inl rfl)⟩
    iapply (BigSepL.bigSepL_cons (PROP := IProp GF)).2
    iframe Ha
    iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2
    itrivial
  iintro -
  iapply HΦ; itrivial

/-- An `*OpError` of the net model is an error result (`net.opErr_errOrNil`). -/
theorem network.opErr_errOrNil (op : GoString) (src addr e err : GoInterface) :
    net.opErr op src addr e err ⊢ bufio.errOrNil (GF := GF) err :=
  net.opErr_errOrNil op src addr e err

/-- A net operation's error (`net.resErr`) is an error result (`net.resErr_errOrNil`). -/
theorem network.resErr_errOrNil (res : Option NetErr) (op : GoString) (src addr : GoInterface)
    (ed : Option GoInterface) (nm : GoString → Prop) (err : GoInterface) :
    net.resErr (GF := GF) res op src addr ed nm err ⊢ bufio.errOrNil err :=
  net.resErr_errOrNil res op src addr ed nm err

/-- Learn the source `s` (under the write lock). -/
theorem network.src_learn (ns : network.TcpNames) (S : GMap GoString Unit) (s : GoString) :
    ghostMapAuth ns.src 1 S ∗ ([∗map] s' ↦ _u ∈ S, network.srcMark ns s') ⊢
    |==> ∃ S' : GMap GoString Unit, ghostMapAuth ns.src 1 S' ∗
      ⌜∀ s', S'.lookup s' = some () → s' = s ∨ S.lookup s' = some ()⌝ ∗
      ([∗map] s' ↦ _u ∈ S', network.srcMark ns s') ∗ network.srcMark ns s := by
  iintro ⟨HS, #Hm⟩
  cases hS : S.lookup s with
  | some u =>
    ihave #Hs := (BigSepM.bigSepM_lookup (PROP := IProp GF)
      (Φ := fun s' (_u : Unit) => network.srcMark ns s') (m := S) (i := s) (x := u) hS) $$ Hm
    imodintro
    iexists S
    iframe HS Hm Hs
    ipureintro; intro s' h; exact Or.inr h
  | none =>
    imod ghost_map_insert_persist s () hS $$ HS with ⟨HS, #Hs⟩
    imodintro
    iexists (S.insert s ())
    iframe HS Hs
    isplitr
    · ipureintro
      intro s' h
      change (GMap.insert s () S) !! s' = some () at h
      by_cases hss : s = s'
      · exact Or.inl hss.symm
      · rw [GMap.lookup_insert_ne _ _ hss] at h; exact Or.inr h
    · iapply (BigSepM.bigSepM_insert (PROP := IProp GF)
        (Φ := fun s' (_u : Unit) => network.srcMark ns s') (m := S) (i := s) (x := ()) hS).2
      iframe Hs Hm

/-- An `addrOk` source of the TCP with names `ns` is `addrOkN ns`. -/
theorem network.addrOkN_of_def (tcp : Loc) (ns : network.TcpNames) (a : ipv4port.IPv4Port) :
    network.rootInv (GF := GF) tcp ns ∗ network.addrOkDef tcp a ⊢ |={⊤}=> network.addrOkN ns a := by
  unfold network.addrOkDef network.addrOkN
  iintro ⟨#Hroot, ⟨%s, %hs, (%hc | ⟨%ns', #Hroot', #Hm⟩)⟩⟩
  · imodintro; iexists s
    isplitr
    · ipureintro; exact hs
    · ileft; ipureintro; exact hc
  · imod network.rootInv_agree tcp ns ns' $$ [$Hroot $Hroot'] with %hns
    subst hns
    imodintro
    iexists s
    isplitr
    · ipureintro; exact hs
    · iright; iexact Hm

/-- An `addrOkN` source of the TCP with names `ns` is `addrOk`. -/
theorem network.def_of_addrOkN (tcp : Loc) (ns : network.TcpNames) (a : ipv4port.IPv4Port) :
    network.rootInv (GF := GF) tcp ns ∗ network.addrOkN ns a ⊢ network.addrOkDef tcp a := by
  unfold network.addrOkDef network.addrOkN
  iintro ⟨#Hroot, ⟨%s, %hs, (%hc | #Hm)⟩⟩
  · iexists s
    isplitr
    · ipureintro; exact hs
    · ileft; ipureintro; exact hc
  · iexists s
    isplitr
    · ipureintro; exact hs
    · iright; iexists ns; iframe Hroot Hm

theorem network.ownMap_agree' {V : Type} [ZeroVal V] [go.IntoValInj V]
    (m : Loc) (p q : Qp) (a b : GMap GoString V) :
    ownMap (GF := GF) m (DFrac.own p) a ∗ ownMap m (DFrac.own q) b ⊢
      (ownMap m (DFrac.own p) a ∗ ownMap m (DFrac.own q) b) ∗ ⌜a = b⌝ :=
  persistent_entails_left (ownMap_agree m _ _ a b)

theorem network.ghostMapAuth_agree' {K V : Type} [DecidableEq K] [Pos.Countable K]
    [Pos.Countable V] (γ : GName) (p q : Qp) (a b : GMap K V) :
    ghostMapAuth (GF := GF) γ p a ∗ ghostMapAuth γ q b ⊢
      (ghostMapAuth γ p a ∗ ghostMapAuth γ q b) ∗ ⌜a = b⌝ := by
  refine persistent_entails_left (Q := iprop(⌜a = b⌝)) ?_
  iintro ⟨H1, H2⟩
  iapply ghostMapAuth_agree $$ H1 H2

/-- The lock's resource is fractional (the `RWMutex`'s guarded resource). -/
instance network.lockP_fractional (ns : network.TcpNames) (cm sm : Loc) :
    Fractional (network.lockP (GF := GF) ns cm sm) where
  fractional p q := by
    constructor
    · iintro ⟨%mc, %ms, %D, %S, Hcm, Hsm, HD, HS, %hS, #He, #Hd, #Hs⟩
      icases (ownMap_fractional (GF := GF) cm mc).fractional p q |>.1 $$ Hcm with ⟨Hcm1, Hcm2⟩
      icases (ownMap_fractional (GF := GF) sm ms).fractional p q |>.1 $$ Hsm with ⟨Hsm1, Hsm2⟩
      icases (ghostMapAuth_fractional (GF := GF) ns.dead D).fractional p q |>.1 $$ HD
        with ⟨HD1, HD2⟩
      icases (ghostMapAuth_fractional (GF := GF) ns.src S).fractional p q |>.1 $$ HS
        with ⟨HS1, HS2⟩
      isplitl [Hcm1 Hsm1 HD1 HS1]
      · iexists mc, ms, D, S
        iframe
        iframe He Hd Hs
        ipureintro; exact hS
      · iexists mc, ms, D, S
        iframe
        iframe He Hd Hs
        ipureintro; exact hS
    · iintro ⟨⟨%mc, %ms, %D, %S, Hcm, Hsm, HD, HS, %hS, #He, #Hd, #Hs⟩,
        ⟨%mc', %ms', %D', %S', Hcm', Hsm', HD', HS', %hS', #He', #Hd', #Hs'⟩⟩
      icases network.ownMap_agree' cm p q mc mc' $$ [$Hcm $Hcm'] with ⟨⟨Hcm, Hcm'⟩, %e1⟩
      icases network.ownMap_agree' sm p q ms ms' $$ [$Hsm $Hsm'] with ⟨⟨Hsm, Hsm'⟩, %e2⟩
      icases network.ghostMapAuth_agree' ns.dead p q D D' $$ [$HD $HD'] with ⟨⟨HD, HD'⟩, %e3⟩
      icases network.ghostMapAuth_agree' ns.src p q S S' $$ [$HS $HS'] with ⟨⟨HS, HS'⟩, %e4⟩
      subst e1 e2 e3 e4
      iexists mc, ms, D, S
      iframe He Hd Hs
      isplitl [Hcm Hcm']
      · iapply ((ownMap_fractional (GF := GF) cm mc).fractional p q).2; iframe
      isplitl [Hsm Hsm']
      · iapply ((ownMap_fractional (GF := GF) sm ms).fractional p q).2; iframe
      isplitl [HD HD']
      · iapply ((ghostMapAuth_fractional (GF := GF) ns.dead D).fractional p q).2; iframe
      isplitl [HS HS']
      · iapply ((ghostMapAuth_fractional (GF := GF) ns.src S).fractional p q).2; iframe
      ipureintro; exact hS

/-- `slog.Debug(msg, "err", e)` for a net operation's error. -/
theorem network.wp_debug_resErr (wp_Debug : log.slog.Debug.spec (GF := GF) (hG := hG))
    (msg s : GoString) (sl : GoSlice) (res : Option NetErr) (op : GoString)
    (src addr : GoInterface) (ed : Option GoInterface) (nm : GoString → Prop) (e : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.log.slog ∗ net.resErr res op src addr ed nm e ∗
        sl ↦* [interface.mkOk go.string #s, e] }}
      (App (App (Val (@! log.slog.Debug)) (Val #msg)) (Val #sl))
    {{ RET #(); True }} := by
  wp_start_folded as ⟨#He, Hsl⟩
  ihave #He' := network.resErr_errOrNil res op src addr ed nm e $$ He
  wp_apply network.wp_debug_err wp_Debug msg s sl e $$ [$He' $Hsl]
  iapply HΦ; itrivial

/-- The dead set's facts (persistent). -/
abbrev network.deadOk (ns : network.TcpNames) (D : GMap Loc Unit) : IProp GF :=
  iprop([∗map] c ↦ _u ∈ D, network.deadMark ns c ∗ ∃ x, network.regd ns c x)

/-- A source that `srcs` does not hold is configured. -/
theorem network.cfg_of_not_src (tcp : Loc) (ns : network.TcpNames) (q : Qp)
    (S : GMap GoString Unit) (ms : GMap GoString Bool) (a : ipv4port.IPv4Port) (s : GoString)
    (hS : ∀ s', S.lookup s' = some () → ms !! s' = some true) (hs : ipv4port.ipOwn a s)
    (hms : ms !! s ≠ some true) :
    network.rootInv tcp ns ∗ network.addrOkDef tcp a ∗ ghostMapAuth ns.src q S ⊢
      |={⊤}=> ⌜s ∈ VsrWire.addrs⌝ ∗ ghostMapAuth ns.src q S := by
  unfold network.addrOkDef
  iintro ⟨#Hroot, ⟨%s', %hs', Ha⟩, HS⟩
  have hss : s' = s := by unfold ipv4port.ipOwn at hs hs'; rw [← hs, ← hs']
  subst hss
  icases Ha with (%hcfg | ⟨%ns', #Hroot', #Hm⟩)
  · imodintro; iframe HS; ipureintro; exact hcfg
  · imod network.rootInv_agree tcp ns ns' $$ [$Hroot $Hroot'] with %hns
    subst hns
    icombine HS Hm gives %hl
    exact absurd (hS _ hl) hms

/-- A connection with its fresh token is not registered. -/
theorem network.reg_fresh (ns : network.TcpNames) (R : GMap Loc network.ConnRec) (c : Loc)
    (cid : Nat) (side : Bool) :
    ([∗map] c' ↦ x ∈ R, network.regEntry (GF := GF) ns c' x) ∗ connFresh cid side ∗
      network.connL c cid side ⊢
    ⌜R.lookup c = none⌝ ∗ ([∗map] c' ↦ x ∈ R, network.regEntry ns c' x) ∗ connFresh cid side := by
  iintro ⟨HRm, Hfr, #Hc⟩
  cases hR : R.lookup c with
  | none => iframe; ipureintro; rfl
  | some x =>
    icases (BigSepM.bigSepM_lookup_acc (PROP := IProp GF)
      (Φ := fun c' x' => network.regEntry ns c' x') (m := R) (i := c) (x := x) hR).1 $$ HRm
      with ⟨He, -⟩
    unfold network.regEntry
    icases He with ⟨Hfr', #Hc', -⟩
    ihave %hag := network.connL_agree c cid x.1 side x.2.1 $$ [$Hc $Hc']
    obtain ⟨h1, h2⟩ := hag
    rw [← h1, ← h2] at *
    iexfalso
    iapply connFresh_excl $$ [$Hfr $Hfr']

/-- Register a dialed connection (under the write lock): fresh, so not registered and not dead;
the sender holds it from now on. -/
theorem network.register_dialed (ns : network.TcpNames) (c : Loc) (cid : Nat) (s : GoString)
    (D T : GMap Loc Unit) :
    inv network.regN (network.regInv ns) ∗ £ 1 ∗ connFresh cid false ∗
      network.connL c cid false ∗ network.deadOk ns D ∗ ghostMapAuth ns.held 1 T ∗
      ([∗map] c' ↦ _u ∈ T, network.poolEntry ns c') ⊢
    |={⊤}=> network.regd ns c (cid, false, s) ∗ ⌜D.lookup c = none⌝ ∗
      ∃ T' : GMap Loc Unit, ghostMapAuth ns.held 1 T' ∗
        (network.poolEntry ns c -∗ [∗map] c' ↦ _u ∈ T', network.poolEntry ns c') := by
  iintro ⟨#Hreg, Hlc, Hfr, #Hc, #Hdead, HT, Hpool⟩
  have hm : (↑network.regN : CoPset) ⊆ ⊤ := CoPset.subseteq_top
  iinv Hreg with Hi Hclose
  imod lc_fupd_elim_later $$ Hlc Hi with Hi
  unfold network.regInv
  icases Hi with ⟨%R, HR, HRm⟩
  icases network.reg_fresh ns R c cid false $$ [$HRm $Hfr $Hc] with ⟨%hR, HRm, Hfr⟩
  -- not dead: every dead connection is registered
  ihave %hDc : ⌜D.lookup c = none⌝ $$ [HR]
  · cases hDl : D.lookup c with
    | none => ipureintro; rfl
    | some u =>
      ihave #Hd := (BigSepM.bigSepM_lookup (PROP := IProp GF)
        (Φ := fun c' (_u : Unit) => iprop(network.deadMark ns c' ∗ ∃ x, network.regd ns c' x))
        (m := D) (i := c) (x := u) hDl) $$ Hdead
      icases Hd with ⟨-, %x', #Hx'⟩
      icombine HR Hx' gives %hl
      rw [hR] at hl; cases hl
  -- not held: every held connection is registered
  ihave %hTc : ⌜T.lookup c = none⌝ $$ [HR Hpool]
  · cases hTl : T.lookup c with
    | none => ipureintro; rfl
    | some u =>
      icases (BigSepM.bigSepM_lookup_acc (PROP := IProp GF)
        (Φ := fun c' (_u : Unit) => network.poolEntry ns c') (m := T) (i := c) (x := u) hTl).1
        $$ Hpool with ⟨He, -⟩
      unfold network.poolEntry
      icases He with ⟨%x', %W, #Hx', -⟩
      icombine HR Hx' gives %hl
      rw [hR] at hl; cases hl
  imod ghost_map_insert_persist c (cid, false, s) hR $$ HR with ⟨HR, #Hx⟩
  imod ghost_map_insert_persist c () hTc $$ HT with ⟨HT, #Hh⟩
  imod Hclose $$ [HR HRm Hfr] with -
  · inext
    iexists (R.insert c (cid, false, s))
    iframe HR
    iapply (BigSepM.bigSepM_insert (PROP := IProp GF)
      (Φ := fun c' x' => network.regEntry ns c' x') (m := R) (i := c) (x := (cid, false, s)) hR).2
    iframe HRm
    unfold network.regEntry
    iframe Hfr Hc
    iright; iexact Hh
  imodintro
  iframe Hx
  isplitr
  · ipureintro; exact hDc
  iexists (T.insert c ())
  iframe HT
  iintro He
  iapply (BigSepM.bigSepM_insert (PROP := IProp GF)
    (Φ := fun c' (_u : Unit) => network.poolEntry ns c') (m := T) (i := c) (x := ()) hTc).2
  iframe

/-- Register an accepted connection (under the write lock): fresh, so not registered and not
dead; its send token waits in the registry. -/
theorem network.register_accepted (ns : network.TcpNames) (c : Loc) (cid : Nat) (s : GoString)
    (D : GMap Loc Unit) :
    inv network.regN (network.regInv (GF := GF) ns) ∗ £ 1 ∗ connFresh cid true ∗
      network.connL c cid true ∗ sendTok cid true (VsrWire.protoOf ns.sys) [] ∗
      network.deadOk ns D ⊢
    |={⊤}=> network.regd ns c (cid, true, s) ∗ ⌜D.lookup c = none⌝ := by
  iintro ⟨#Hreg, Hlc, Hfr, #Hc, Hs, #Hdead⟩
  have hm : (↑network.regN : CoPset) ⊆ ⊤ := CoPset.subseteq_top
  iinv Hreg with Hi Hclose
  imod lc_fupd_elim_later $$ Hlc Hi with Hi
  unfold network.regInv
  icases Hi with ⟨%R, HR, HRm⟩
  icases network.reg_fresh ns R c cid true $$ [$HRm $Hfr $Hc] with ⟨%hR, HRm, Hfr⟩
  ihave %hDc : ⌜D.lookup c = none⌝ $$ [HR]
  · cases hDl : D.lookup c with
    | none => ipureintro; rfl
    | some u =>
      ihave #Hd := (BigSepM.bigSepM_lookup (PROP := IProp GF)
        (Φ := fun c' (_u : Unit) => iprop(network.deadMark ns c' ∗ ∃ x, network.regd ns c' x))
        (m := D) (i := c) (x := u) hDl) $$ Hdead
      icases Hd with ⟨-, %x', #Hx'⟩
      icombine HR Hx' gives %hl
      rw [hR] at hl; cases hl
  imod ghost_map_insert_persist c (cid, true, s) hR $$ HR with ⟨HR, #Hx⟩
  imod Hclose $$ [HR HRm Hfr Hs] with -
  · inext
    iexists (R.insert c (cid, true, s))
    iframe HR
    iapply (BigSepM.bigSepM_insert (PROP := IProp GF)
      (Φ := fun c' x' => network.regEntry ns c' x') (m := R) (i := c) (x := (cid, true, s)) hR).2
    iframe HRm
    unfold network.regEntry
    iframe Hfr Hc
    ileft; iexact Hs
  imodintro
  iframe Hx
  ipureintro; exact hDc

/-- Insert an entry into `conns`'s facts. -/
theorem network.entries_insert (ns : network.TcpNames) (D : GMap Loc Unit)
    (mc : GMap GoString GoInterface) (k : GoString) (v : GoInterface) :
    ([∗map] k' ↦ v' ∈ mc, network.entryOk (GF := GF) ns D k' v') ∗ network.entryOk ns D k v ⊢
      [∗map] k' ↦ v' ∈ (<[k := v]> mc), network.entryOk ns D k' v' := by
  iintro ⟨#Hm, #He⟩
  ihave #Hf := (BigSepM.bigSepM_forall_intro (PROP := IProp GF)
    (Φ := fun k' v' => network.entryOk ns D k' v') (m := mc)) $$ Hm
  iapply (BigSepM.bigSepM_forall_elim (PROP := IProp GF)
    (Φ := fun k' v' => network.entryOk ns D k' v'))
  iintro %k' %v' %hk
  change (<[k := v]> mc) !! k' = some v' at hk
  rw [GMap.lookup_insert_eq_iff] at hk
  by_cases hkk : k = k'
  · subst hkk
    simp only [ite_true, Option.some.injEq] at hk
    subst hk
    iexact He
  · simp only [hkk, ite_false] at hk
    iapply Hf
    ipureintro; exact hk

/-- Delete an entry from `conns`'s facts. -/
theorem network.entries_delete (ns : network.TcpNames) (D : GMap Loc Unit)
    (mc : GMap GoString GoInterface) (k : GoString) :
    ([∗map] k' ↦ v' ∈ mc, network.entryOk (GF := GF) ns D k' v') ⊢
      [∗map] k' ↦ v' ∈ (GMap.delete k mc), network.entryOk ns D k' v' := by
  iintro #Hm
  ihave #Hf := (BigSepM.bigSepM_forall_intro (PROP := IProp GF)
    (Φ := fun k' v' => network.entryOk ns D k' v') (m := mc)) $$ Hm
  iapply (BigSepM.bigSepM_forall_elim (PROP := IProp GF)
    (Φ := fun k' v' => network.entryOk ns D k' v'))
  iintro %k' %v' %hk
  change (GMap.delete k mc) !! k' = some v' at hk
  by_cases hkk : k = k'
  · subst hkk
    rw [GMap.lookup_delete] at hk
    cases hk
  · rw [GMap.lookup_delete_ne _ hkk] at hk
    iapply Hf
    ipureintro; exact hk

/-- Mark `c` dead (under the write lock): it is not in the map (not under its key `s`, and a
connection is only ever under its key). -/
theorem network.mark_dead (ns : network.TcpNames) (D : GMap Loc Unit)
    (mc : GMap GoString GoInterface) (c : Loc) (x : network.ConnRec)
    (hc : mc !! x.2.2 ≠ some (interface.mkOk (go.GoType.PointerType net.TCPConn.ty) #c)) :
    ghostMapAuth ns.dead 1 D ∗ network.deadOk ns D ∗
      ([∗map] k' ↦ v' ∈ mc, network.entryOk ns D k' v') ∗ network.regd ns c x ⊢
    |==> ∃ D' : GMap Loc Unit, ghostMapAuth ns.dead 1 D' ∗ network.deadOk ns D' ∗
      ([∗map] k' ↦ v' ∈ mc, network.entryOk ns D' k' v') ∗ network.deadMark ns c := by
  iintro ⟨HD, #Hdead, #Hm, #Hx⟩
  cases hD : D.lookup c with
  | some u =>
    ihave #Hd := (BigSepM.bigSepM_lookup (PROP := IProp GF)
      (Φ := fun c' (_u : Unit) => iprop(network.deadMark ns c' ∗ ∃ x, network.regd ns c' x))
      (m := D) (i := c) (x := u) hD) $$ Hdead
    icases Hd with ⟨#Hd, -⟩
    imodintro
    iexists D
    iframe HD Hdead Hm Hd
  | none =>
    imod ghost_map_insert_persist c () hD $$ HD with ⟨HD, #Hd⟩
    imodintro
    iexists (D.insert c ())
    iframe HD Hd
    isplitl
    · unfold network.deadOk
      ihave #Hf := (BigSepM.bigSepM_forall_intro (PROP := IProp GF)
        (Φ := fun c' (_u : Unit) => iprop(network.deadMark ns c' ∗ ∃ x, network.regd ns c' x))
        (m := D)) $$ Hdead
      iapply (BigSepM.bigSepM_forall_elim (PROP := IProp GF)
        (Φ := fun c' (_u : Unit) => iprop(network.deadMark ns c' ∗ ∃ x, network.regd ns c' x)))
      iintro %c' %u' %hk
      change (GMap.insert c () D) !! c' = some u' at hk
      by_cases hcc : c = c'
      · subst hcc
        iframe Hd
        iexists x; iexact Hx
      · rw [GMap.lookup_insert_ne _ _ hcc] at hk
        iapply Hf
        ipureintro; exact hk
    · ihave #Hf := (BigSepM.bigSepM_forall_intro (PROP := IProp GF)
        (Φ := fun k' v' => network.entryOk ns D k' v') (m := mc)) $$ Hm
      iapply (BigSepM.bigSepM_forall_elim (PROP := IProp GF)
        (Φ := fun k' v' => network.entryOk ns (D.insert c ()) k' v'))
      iintro %k' %v' %hk
      ihave #He := Hf $$ %k' %v' %hk
      icases He with ⟨%c', %x', %hcx, #Hx'⟩
      obtain ⟨hv, hxk, hD'⟩ := hcx
      by_cases hcc : c = c'
      · subst hcc
        icombine Hx Hx' gives % ⟨-, hxx⟩
        subst hxx
        exfalso
        apply hc
        rw [hxk, ← hv]
        exact hk
      · iexists c', x'
        iframe Hx'
        ipureintro
        refine ⟨hv, hxk, ?_⟩
        change (GMap.insert c () D) !! c' = none
        rw [GMap.lookup_insert_ne _ _ hcc]
        exact hD'

end ghost

end Perennial.github_com.tangledbytes.go_vsr.pkg
