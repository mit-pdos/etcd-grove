/-
The connection's helpers (`ServerConn.lean`): `Server.trackConn` and `conn.setState` (with no
`ConnState` hook), for the proofs of the server's methods.
-/
module

public import Net.Proof.net.http.ServerConn
public import Perennial.Proof.sync.Link
public import Perennial.Proof.sync.atomic.Link
public import Perennial.Proof.time.Link

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace net.http

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [package_sem' : net.http.Assumptions]
variable [π : NetProtoGS]

/-- `s.trackConn(c, add)`. -/
theorem wp_trackConn (s c : Loc) (add : Bool) :
    {{ srvConst (GF := GF) s }}
      (App (App (Val (s @!! go.GoType.PointerType net.http.Server.ty @!! go!"trackConn")) (Val #c))
        (Val #add))
    {{ RET #(); True }} := by
  wp_start as #Hs
  iunfold srvConst at Hs
  icases Hs with ⟨#Htime, #Hsync, #Hatomic, #Hmu, #Hcs⟩
  wp_apply wp_with_defer as %defer defer
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hown, Hinv⟩
  iunfold srvMuInv at Hinv
  icases Hinv with ⟨Hac, Hls⟩
  iunfold mapField at Hac
  icases Hac with ⟨%m, Hm, Hmm⟩
  wp_auto
  icases Hmm with (%Hnil | ⟨%g, Hg⟩)
  · subst Hnil
    simp only [decide_true]
    wp_apply (wp_map_make1 (K := Loc) (V := Unit) _ _) as %m' Hg
    cases add
    · wp_auto
      wp_apply (wp_mapDelete (K := Loc) (V := Unit) _ _ c _ _) $$ [$Hg] as Hg
      wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hown Hm Hg Hls]
      · inext; iunfold srvMuInv; iframe Hls; iunfold mapField; iexists _; iframe Hm; iright; iexists _; iexact Hg
      iapply HΦ; itrivial
    · wp_auto
      wp_apply (wp_mapInsert (K := Loc) (V := Unit) _ _ _ c ()) $$ [$Hg] as Hg
      wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hown Hm Hg Hls]
      · inext; iunfold srvMuInv; iframe Hls; iunfold mapField; iexists _; iframe Hm; iright; iexists _; iexact Hg
      iapply HΦ; itrivial
  · ihave %Hnn := ownMap_not_nil _ _ _ $$ Hg
    simp only [Hnn, decide_false]
    wp_auto
    cases add
    · wp_auto
      wp_apply (wp_mapDelete (K := Loc) (V := Unit) _ _ c _ _) $$ [$Hg] as Hg
      wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hown Hm Hg Hls]
      · inext; iunfold srvMuInv; iframe Hls; iunfold mapField; iexists _; iframe Hm; iright; iexists _; iexact Hg
      iapply HΦ; itrivial
    · wp_auto
      wp_apply (wp_mapInsert (K := Loc) (V := Unit) _ _ _ c ()) $$ [$Hg] as Hg
      wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hown Hm Hg Hls]
      · inext; iunfold srvMuInv; iframe Hls; iunfold mapField; iexists _; iframe Hm; iright; iexists _; iexact Hg
      iapply HΦ; itrivial


/-- `c.setState(nc, st, runHooks)`, with no `ConnState` hook: the connection tracked or
untracked, its packed state stored. -/
theorem wp_setState (c s : Loc) (nc : GoInterface) (st : w64)
    (hst : 0 ≤ sint.Z st ∧ sint.Z st ≤ 255) :
    {{ structFieldRef net.http.conn go!"server" c ↦□ s ∗ srvConst (GF := GF) s ∗
        (∃ v : w64, sync.atomic.ownUint64 (structFieldRef net.http.conn go!"curState" c)
          (DFrac.own 1) v) }}
      (App (App (App (Val (c @!! go.GoType.PointerType net.http.conn.ty @!! go!"setState"))
        (Val #nc)) (Val #st)) (Val #true))
    {{ RET #(); ∃ v : w64, sync.atomic.ownUint64 (structFieldRef net.http.conn go!"curState" c)
          (DFrac.own 1) v }} := by
  wp_start as ⟨#Hsrv, #Hs, %v, Hst⟩
  have h1 : ¬ (sint.Z (W64 255) < sint.Z st) := by
    have : sint.Z (W64 255) = 255 := by decide
    omega
  have h2 : ¬ (sint.Z st < sint.Z (W64 0)) := by
    have : sint.Z (W64 0) = 0 := by decide
    omega
  ihave #Hs' := Hs
  iunfold srvConst at Hs'
  icases Hs' with ⟨#Htime, #Hsync, #Hatomic, #Hmu, #Hcs⟩
  wp_auto
  all_goals repeat (first | wp_if_destruct | (wp_apply wp_trackConn $$ [$Hs]) |
    (wp_apply time.wp_Now as %tn -) | (wp_apply time.Time.wp_Unix as %x -) | wp_auto)
  all_goals try (by_cases h4 : st = W64 4 <;> simp only [h4, decide_true, decide_false])
  all_goals repeat (first | wp_if_destruct | (wp_apply wp_trackConn $$ [$Hs]) |
    (wp_apply time.wp_Now as %tn -) | (wp_apply time.Time.wp_Unix as %x -) | wp_auto)
  all_goals try simp only [h1, decide_false]
  all_goals repeat (first | wp_if_destruct | (wp_apply wp_trackConn $$ [$Hs]) |
    (wp_apply time.wp_Now as %tn' -) | (wp_apply time.Time.wp_Unix as %x' -) | wp_auto)
  all_goals try (exfalso; omega)
  all_goals try (wp_apply time.wp_Now as %tn'' -)
  all_goals try (wp_apply time.Time.wp_Unix as %x'' -)
  all_goals try wp_auto
  all_goals try (
    wp_bind (App (Val #(methods _ _ _)) _)
    iapply (sync.atomic.Uint64.wp_Store (structFieldRef net.http.conn go!"curState" c) _)
    · iPkgInit
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hmask
    inext
    iexists v
    iframe Hst
    iintro Hst
    imod Hmask
    imodintro
    wp_auto
    iapply HΦ; iexists _; iexact Hst)
  all_goals sorry

end lemmas

end net.http
end Perennial
